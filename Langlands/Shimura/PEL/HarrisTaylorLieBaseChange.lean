import Langlands.AbelianScheme.LieRationalTraceBaseChange
import Langlands.Shimura.PEL.HarrisTaylorNumericalClasses
import Mathlib.CategoryTheory.Subfunctor.Basic

/-! # Harris–Taylor numerical pullback and actual moduli presheaf -/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite NumberField _root_.Algebra
open Langlands.AbelianScheme Langlands.Scheme.Modules

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.HarrisTaylor

variable (L K : Type) [Field L] [NumberField L] [IsCMField L]
    [Field K] [NumberField K] [IsCMField K] [Algebra L K]
    {S T : Scheme.{0}} (s : S ⟶ Spec (.of K))
    {A : Type} [Ring A] [Algebra ℚ A] [Algebra K A]
    (B : AbelianScheme S) (i : A →ₐ[ℚ] End0 B) (n : ℕ)
    {U : S.Opens} {J : Type} [Fintype J]

/-- The central trace test agrees on the overlap of any two actual finite Lie charts. -/
theorem centralLieTraceConditionAt_overlap
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) J ≅ B.Lie.over U)
    {U' W : S.Opens} {J' : Type} [Fintype J']
    (e' : SheafOfModules.free (R := S.ringCatSheaf.over U') J' ≅ B.Lie.over U')
    (a : K) (j : W ⟶ U) (j' : W ⟶ U') :
    CentralLieTraceConditionAt L s B i n e a (Over.mk j) ↔
      CentralLieTraceConditionAt L s B i n e' a (Over.mk j') := by
  unfold CentralLieTraceConditionAt
  rw [lieRationalSectionTrace_overlap s B (centralAction B i) e e' a j j']
  rfl

/-- Structure-sheaf separation checks the actual central trace test on an open cover. -/
theorem centralLieTraceConditionAt_of_cover
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) J ≅ B.Lie.over U)
    (a : K) (V : Over U)
    {κ : Type*} (W : κ → S.Opens) (jW : ∀ k, W k ⟶ V.left)
    (hcov : V.left ≤ iSup W)
    (h : ∀ k, CentralLieTraceConditionAt L s B i n e a
      (Over.mk (jW k ≫ V.hom))) :
    CentralLieTraceConditionAt L s B i n e a V := by
  apply S.sheaf.eq_of_locally_eq' W V.left jW hcov
  intro k
  let j : Over.mk (jW k ≫ V.hom) ⟶ V := Over.homMk (jW k)
  change (S.presheaf.map (jW k).op)
      (lieRationalSectionTrace s B (centralAction B i) e a V) =
    (S.presheaf.map (jW k).op) (lieTraceSection L s n a V.left)
  calc
    _ = lieRationalSectionTrace s B (centralAction B i) e a
        (Over.mk (jW k ≫ V.hom)) :=
      lieRationalSectionTrace_restrict s B _ e a j
    _ = lieTraceSection L s n a (W k) := h k
    _ = _ := (lieTraceSection_restrict L s n a j).symm

variable (b : T ⟶ S)

omit [NumberField K] [IsCMField K] in
/-- The pulled-back rational algebra action restricts to the pulled-back central action. -/
theorem centralAction_baseChange :
    centralAction (K := K) ((baseChange b).obj B)
        ((rationalBaseChangeEnd b B).comp i) =
      baseChangeRationalOrderAction b B (centralAction (K := K) B i) := rfl

variable (naturality : LieBaseChangeNaturalityStatement S)

include naturality

/-- The central trace identity transports to the constructed inverse-image Lie chart. -/
theorem centralLieTraceConditionAt_baseChange_of_naturality
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) J ≅ B.Lie.over U)
    (a : K) (V : Over U)
    (h : CentralLieTraceConditionAt L s B i n e a V) :
    CentralLieTraceConditionAt L (b ≫ s) ((baseChange b).obj B)
      ((rationalBaseChangeEnd b B).comp i) n (lieBaseChangeChart b B e) a
      (Over.mk ((TopologicalSpace.Opens.map b.base).map V.hom)) := by
  unfold CentralLieTraceConditionAt at h ⊢
  rw [centralAction_baseChange,
    ← lieRationalSectionTrace_baseChange_of_naturality s b B _ naturality e a V, h]
  change b.app V.left (lieTraceSection L s n a V.left) =
    lieTraceSection L (b ≫ s) n a (b ⁻¹ᵁ V.left)
  simpa only [Scheme.Hom.appLE_eq_app] using
    lieTraceSection_pullbackLE L s b n a V.left (b ⁻¹ᵁ V.left) le_rfl

/-- The exact central trace test survives arbitrary base change on every target Lie chart. -/
theorem centralLieTraceCondition_baseChange_of_naturality
    (h : CentralLieTraceCondition L s B i n) :
    CentralLieTraceCondition L (b ≫ s) ((baseChange b).obj B)
      ((rationalBaseChangeEnd b B).comp i) n := by
  intro U J _ e a V
  let q := lieFiniteLocalBasisData B
  have hq : (⨆ k, q.X k) = ⊤ := by
    have hcover := q.coversTop
    rwa [_root_.Opens.coversTop_iff, TopologicalSpace.IsOpenCover] at hcover
  apply centralLieTraceConditionAt_of_cover L K (b ≫ s)
    ((baseChange b).obj B) ((rationalBaseChangeEnd b B).comp i) n e a V
    (fun k => V.left ⊓ b ⁻¹ᵁ q.X k) (fun _ => homOfLE inf_le_left)
  · intro x hx
    have hxq : b.base x ∈ ⨆ k, q.X k := by rw [hq]; trivial
    obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.mp hxq
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨k, hx, hk⟩
  · intro k
    let e' := lieBaseChangeChart b B (lieFiniteLocalBasisTrivialization B k)
    have hk := centralLieTraceConditionAt_baseChange_of_naturality L K s B i n b
      naturality (lieFiniteLocalBasisTrivialization B k) a (Over.mk (𝟙 _))
      (h _ _ (lieFiniteLocalBasisTrivialization B k) a (Over.mk (𝟙 _)))
    have hk' : CentralLieTraceConditionAt L (b ≫ s) ((baseChange b).obj B)
        ((rationalBaseChangeEnd b B).comp i) n e' a
        (Over.mk (𝟙 (b ⁻¹ᵁ q.X k))) := hk
    have hsmall := centralLieTraceConditionAt_restrict L (b ≫ s)
      ((baseChange b).obj B) ((rationalBaseChangeEnd b B).comp i) n e' a
      (Over.homMk (homOfLE inf_le_right) :
        Over.mk (homOfLE (inf_le_right : V.left ⊓ b ⁻¹ᵁ q.X k ≤ b ⁻¹ᵁ q.X k)) ⟶
          Over.mk (𝟙 (b ⁻¹ᵁ q.X k))) hk'
    exact (centralLieTraceConditionAt_overlap L K (b ≫ s)
      ((baseChange b).obj B) ((rationalBaseChangeEnd b B).comp i) n e e' a
      (homOfLE inf_le_left ≫ V.hom) (homOfLE inf_le_right)).mpr hsmall

variable (E : Type) [Field E] [NumberField E]

/-- Both the geometric dimension and actual central trace survive arbitrary base change. -/
theorem numericalCondition_baseChange_of_naturality
    (h : NumericalCondition L s E B i n) :
    NumericalCondition L (b ≫ s) E ((baseChange b).obj B)
      ((rationalBaseChangeEnd b B).comp i) n :=
  ⟨prescribedRelativeDimension_baseChange E B n h.1 b,
    centralLieTraceCondition_baseChange_of_naturality L K s B i n b naturality h.2⟩

/-- The existing well-defined central trace predicate on actual classes survives pullback. -/
theorem centralLieTraceClassCondition_baseChange_of_naturality
    (q : RationalAlgebraAction.IsoClass S A)
    (h : CentralLieTraceClassCondition L K s n q) :
    CentralLieTraceClassCondition L K (b ≫ s) n
      (RationalAlgebraAction.pullbackClass b q) := by
  obtain ⟨X, rfl⟩ := RationalAlgebraAction.classOf_surjective q
  exact centralLieTraceCondition_baseChange_of_naturality L K s X.abelianScheme
    X.action n b naturality h

/-- Pulling back a satisfying actual representative preserves the numerical class image. -/
theorem numericalActionClassCondition_baseChange_of_naturality
    (q : RationalAlgebraAction.IsoClass S A)
    (h : NumericalActionClassCondition L K s n E q) :
    NumericalActionClassCondition L K (b ≫ s) n E
      (RationalAlgebraAction.pullbackClass b q) := by
  obtain ⟨X, hX, hnum⟩ := h
  refine ⟨(RationalAlgebraAction.pullback b).obj X, ?_, ?_⟩
  · rw [← hX]
    rfl
  · exact numericalCondition_baseChange_of_naturality L K s X.abelianScheme
      X.action n b naturality E hnum

omit naturality

/-- Actual classes with a numerically satisfying representative form a moduli subfunctor. -/
def numericalActionSubfunctor
    (allNaturality : ∀ X : Scheme.{0}, LieBaseChangeNaturalityStatement X) :
    Subfunctor (RationalAlgebraAction.isoClassOverPresheaf
      (Spec (CommRingCat.of K)) A) where
  obj X := {q | NumericalActionClassCondition L K X.unop.hom n E q}
  map {X Y} f q hq := by
    change NumericalActionClassCondition L K Y.unop.hom n E
      (RationalAlgebraAction.pullbackClass f.unop.left q)
    rw [← Over.w f.unop]
    exact numericalActionClassCondition_baseChange_of_naturality L K X.unop.hom n
      f.unop.left (allNaturality X.unop.left) E q hq

/-- The actual Harris–Taylor numerical moduli presheaf over the CM spectrum. -/
def numericalActionPresheaf
    (allNaturality : ∀ X : Scheme.{0}, LieBaseChangeNaturalityStatement X) :
    (Over (Spec (CommRingCat.of K)))ᵒᵖ ⥤ Type 1 :=
  (numericalActionSubfunctor L K n E (A := A) allNaturality).toFunctor

/-- Forgetting the numerical requirement is the actual natural subtype inclusion. -/
def numericalActionPresheafInclusion
    (allNaturality : ∀ X : Scheme.{0}, LieBaseChangeNaturalityStatement X) :
    numericalActionPresheaf L K n E (A := A) allNaturality ⟶
      RationalAlgebraAction.isoClassOverPresheaf (Spec (CommRingCat.of K)) A :=
  (numericalActionSubfunctor L K n E allNaturality).ι

@[simp]
theorem numericalActionPresheaf_obj
    (allNaturality : ∀ X : Scheme.{0}, LieBaseChangeNaturalityStatement X)
    (X : Over (Spec (CommRingCat.of K))) :
    (numericalActionPresheaf L K n E (A := A) allNaturality).obj (op X) =
      NumericalActionClass L K X.hom n E (A := A) := rfl

@[simp]
theorem numericalActionPresheaf_map_val
    (allNaturality : ∀ X : Scheme.{0}, LieBaseChangeNaturalityStatement X)
    {X Y : Over (Spec (CommRingCat.of K))} (f : Y ⟶ X)
    (q : NumericalActionClass L K X.hom n E (A := A)) :
    ((numericalActionPresheaf L K n E allNaturality).map f.op q).val =
      RationalAlgebraAction.pullbackClass f.left q.val := rfl

@[simp]
theorem numericalActionPresheaf_map_classOf_val
    (allNaturality : ∀ X : Scheme.{0}, LieBaseChangeNaturalityStatement X)
    {X Y : Over (Spec (CommRingCat.of K))} (f : Y ⟶ X)
    (Z : RationalAlgebraAction X.left A)
    (hZ : NumericalCondition L X.hom E Z.abelianScheme Z.action n) :
    ((numericalActionPresheaf L K n E allNaturality).map f.op
      (numericalActionClassOf L K X.hom n E Z hZ)).val =
        RationalAlgebraAction.classOf ((RationalAlgebraAction.pullback f.left).obj Z) := rfl

theorem numericalActionPresheafInclusion_injective
    (allNaturality : ∀ X : Scheme.{0}, LieBaseChangeNaturalityStatement X)
    (X : Over (Spec (CommRingCat.of K))) :
    Function.Injective
      ((numericalActionPresheafInclusion L K n E (A := A) allNaturality).app (op X)) :=
  Subtype.val_injective

end Langlands.Shimura.HarrisTaylor
