import Langlands.AbelianScheme.LieRationalTrace
import Langlands.AbelianScheme.LieRankProof
import Langlands.Shimura.Unitary.CMData
import Langlands.Shimura.PEL.ReflexSectionPullback

/-! # Harris–Taylor central Lie traces and prescribed relative dimension -/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite NumberField _root_.Algebra
open Langlands.AbelianScheme
open Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.HarrisTaylor

variable (L K : Type) [Field L] [NumberField L] [IsCMField L]
    [Field K] [NumberField K] [IsCMField K]
    [Algebra L K]

/-- The central trace prescribed in Harris–Taylor III.1, Lemma III.1.2(3). -/
def lieTraceValue (n : ℕ) (a : K) : K :=
  algebraMap L K (IsCMField.complexConj L (_root_.Algebra.trace L K ((n : K) ^ 2 * a))) +
    (n : K) * a - IsCMField.complexConj K ((n : K) * a)

@[simp]
theorem lieTraceValue_zero (n : ℕ) : lieTraceValue L K n 0 = 0 := by
  simp [lieTraceValue]

/-- The prescribed central trace is additive. -/
theorem lieTraceValue_add (n : ℕ) (a b : K) :
    lieTraceValue L K n (a + b) = lieTraceValue L K n a + lieTraceValue L K n b := by
  simp only [lieTraceValue, mul_add, map_add]
  ring

/-- At the identity the formula gives the actual extension degree times `n²`. -/
@[simp]
theorem lieTraceValue_one (n : ℕ) :
    lieTraceValue L K n 1 = (Module.finrank L K : K) * (n : K) ^ 2 := by
  have ht : _root_.Algebra.trace L K ((n : K) ^ 2) =
      (Module.finrank L K : L) * (n : L) ^ 2 := by
    rw [← map_natCast (algebraMap L K) n, ← map_pow, _root_.Algebra.trace_algebraMap,
      nsmul_eq_mul]
  simp [lieTraceValue, ht]

omit [IsCMField L] [IsCMField K] in
/-- The two quadratic degree conditions identify the dimension factor in the trace formula. -/
theorem finrank_imaginary_eq_totallyReal
    [IsQuadraticExtension ℚ L] [IsScalarTower ℚ L K]
    (E : Type) [Field E] [NumberField E] [IsTotallyReal E]
    [Algebra E K] [IsQuadraticExtension E K] [IsScalarTower ℚ E K] :
    Module.finrank L K = Module.finrank ℚ E := by
  have hL := Module.finrank_mul_finrank ℚ L K
  have hE := Module.finrank_mul_finrank ℚ E K
  rw [IsQuadraticExtension.finrank_eq_two ℚ L] at hL
  rw [IsQuadraticExtension.finrank_eq_two E K] at hE
  omega

variable {K} {S T : AlgebraicGeometry.Scheme.{0}}
    (s : S ⟶ Spec (CommRingCat.of K))

/-- The prescribed arithmetic trace as an actual structure-sheaf section. -/
def lieTraceSection (n : ℕ) (a : K) (U : S.Opens) : Γ(S, U) :=
  secHom s U (lieTraceValue L K n a)

/-- The prescribed arithmetic sections commute with actual smaller-open restriction. -/
theorem lieTraceSection_restrict (n : ℕ) (a : K)
    {U : S.Opens} {V W : Over U} (j : V ⟶ W) :
    S.presheaf.map j.left.op (lieTraceSection L s n a W.left) =
      lieTraceSection L s n a V.left := by
  exact congrArg (fun g : CommRingCat.of K ⟶ Γ(S, V.left) =>
    g (lieTraceValue L K n a)) (secHom_map s (leOfHom j.left))

/-- The prescribed arithmetic sections pull back through the actual structure morphism. -/
theorem lieTraceSection_pullbackLE (f : T ⟶ S) (n : ℕ) (a : K)
    (U : S.Opens) (W : T.Opens) (h : W ≤ f ⁻¹ᵁ U) :
    f.appLE U W h (lieTraceSection L s n a U) =
      lieTraceSection L (f ≫ s) n a W := by
  exact congrArg (fun g : CommRingCat.of K ⟶ Γ(T, W) =>
    g (lieTraceValue L K n a)) (secHom_comp_appLE s f U W h)

variable {A : Type} [Ring A] [Algebra ℚ A] [Algebra K A]

/-- Restrict the actual rational algebra action to its actual CM centre. -/
def centralAction (B : AbelianScheme S) (i : A →ₐ[ℚ] End0 B) : K →+* End0 B :=
  i.toRingHom.comp (algebraMap K A)

omit [NumberField K] [IsCMField K] in
@[simp]
theorem centralAction_apply (B : AbelianScheme S) (i : A →ₐ[ℚ] End0 B) (a : K) :
    centralAction B i a = i (algebraMap K A a) := rfl

variable (B : AbelianScheme S) (i : A →ₐ[ℚ] End0 B) (n : ℕ)
    {U : S.Opens} {J : Type} [Fintype J]

/-- The exact central trace identity on an actual finite Lie chart and smaller open. -/
def CentralLieTraceConditionAt
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) J ≅ B.Lie.over U)
    (a : K) (V : Over U) : Prop :=
  lieRationalSectionTrace s B (centralAction B i) e a V =
    lieTraceSection L s n a V.left

/-- The central trace identity restricts through every actual smaller-open inclusion. -/
theorem centralLieTraceConditionAt_restrict
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) J ≅ B.Lie.over U)
    (a : K) {V W : Over U} (j : V ⟶ W)
    (h : CentralLieTraceConditionAt L s B i n e a W) :
    CentralLieTraceConditionAt L s B i n e a V := by
  unfold CentralLieTraceConditionAt at h ⊢
  rw [← lieRationalSectionTrace_restrict s B _ e a j, h, lieTraceSection_restrict]

/-- The source's central trace identity is required in every finite chart and smaller open. -/
def CentralLieTraceCondition : Prop :=
  ∀ (U : S.Opens) (J : Type) [Fintype J]
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) J ≅ B.Lie.over U)
    (a : K) (V : Over U), CentralLieTraceConditionAt L s B i n e a V

variable {B}

/-- Actual equivariant rational isomorphisms preserve the central identity in arbitrary charts. -/
theorem centralLieTraceConditionAt_iso
    {B' : AbelianScheme S} (i' : A →ₐ[ℚ] End0 B')
    (e : Langlands.Rationalization.of B ≅ Langlands.Rationalization.of B')
    (he : ∀ a : A, comp0 B B B' (i a) e.hom = comp0 B B' B' e.hom (i' a))
    (eB : SheafOfModules.free (R := S.ringCatSheaf.over U) J ≅ B.Lie.over U)
    {J' : Type} [Fintype J']
    (eB' : SheafOfModules.free (R := S.ringCatSheaf.over U) J' ≅ B'.Lie.over U)
    (a : K) (V : Over U) :
    CentralLieTraceConditionAt L s B i n eB a V ↔
      CentralLieTraceConditionAt L s B' i' n eB' a V := by
  unfold CentralLieTraceConditionAt
  rw [lieRationalSectionTrace_iso s (centralAction B i) (centralAction B' i') e
    (fun a => he (algebraMap K A a)) eB eB' a V]

/-- The all-chart central trace condition is invariant under actual rational action isomorphism. -/
theorem centralLieTraceCondition_iso
    {B' : AbelianScheme S} (i' : A →ₐ[ℚ] End0 B')
    (e : Langlands.Rationalization.of B ≅ Langlands.Rationalization.of B')
    (he : ∀ a : A, comp0 B B B' (i a) e.hom = comp0 B B' B' e.hom (i' a)) :
    CentralLieTraceCondition L s B i n ↔ CentralLieTraceCondition L s B' i' n := by
  constructor
  · intro h U J _ eB' a V
    let eB := eB' ≪≫ (lieLocalIso0 s e U).symm
    exact (centralLieTraceConditionAt_iso L s i n i' e he eB eB' a V).mp
      (h U J eB a V)
  · intro h U J _ eB a V
    let eB' := eB ≪≫ lieLocalIso0 s e U
    exact (centralLieTraceConditionAt_iso L s i n i' e he eB eB' a V).mpr
      (h U J eB' a V)

/-- At the identity the trace condition imposes the numerical rank equality in sections. -/
theorem centralLieTraceConditionAt_one
    (eB : SheafOfModules.free (R := S.ringCatSheaf.over U) J ≅ B.Lie.over U)
    (V : Over U) (h : CentralLieTraceConditionAt L s B i n eB 1 V) :
    (Fintype.card J : Γ(S, V.left)) =
      (Module.finrank L K : Γ(S, V.left)) * (n : Γ(S, V.left)) ^ 2 := by
  simpa [CentralLieTraceConditionAt, lieTraceSection] using h

variable (E : Type) [Field E] [NumberField E]

/-- The source's actual geometric dimension `d n²`, with `d = [E : ℚ]`. -/
def PrescribedRelativeDimension (B : AbelianScheme S) (n : ℕ) : Prop :=
  B.HasRelativeDimension (Module.finrank ℚ E * n ^ 2)

/-- The prescribed dimension is preserved by arbitrary actual scheme base change. -/
theorem prescribedRelativeDimension_baseChange (B : AbelianScheme S) (n : ℕ)
    (h : PrescribedRelativeDimension E B n) (f : T ⟶ S) :
    PrescribedRelativeDimension E ((AbelianScheme.baseChange f).obj B) n :=
  hasRelativeDimension_baseChange B _ h f

/-- The prescribed geometric dimension gives that rank for the actual relative Lie sheaf. -/
theorem prescribedRelativeDimension_lieRank (B : AbelianScheme S) (n : ℕ)
    (h : PrescribedRelativeDimension E B n) :
    Langlands.Scheme.Modules.IsLocallyFreeOfRank B.Lie
      (Module.finrank ℚ E * n ^ 2) :=
  (lieLocalFreenessRank B).2 _ h

/-- The dimension and the exact central trace test, without asserting the Lie-plus equivalence. -/
def NumericalCondition (B : AbelianScheme S) (i : A →ₐ[ℚ] End0 B) (n : ℕ) : Prop :=
  PrescribedRelativeDimension E B n ∧ CentralLieTraceCondition L s B i n

end Langlands.Shimura.HarrisTaylor
