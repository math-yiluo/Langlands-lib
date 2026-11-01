import Langlands.Shimura.PEL.HarrisTaylorCMLieDeterminant
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # Finite generating families for the normalized Harris determinant test -/

noncomputable section

open CategoryTheory _root_.AlgebraicGeometry MvPolynomial
open Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.SmoothProperConnectedGlobalFunctionsProof
open scoped TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v w t s

namespace Langlands.Shimura.HodgeDeterminant

variable {R : Type u} [CommRing R]
    {ι : Type v} [Fintype ι] {η : Type w}

/-- The variable substitution associated to a matrix of linear combinations. -/
def linearVariables (r : ι → η → R) :
    MvPolynomial η R →+* MvPolynomial ι R :=
  eval₂Hom C (fun j => ∑ i, C (r i j) * X i)

/-- Coefficient maps commute with linear substitution over arbitrary rings. -/
theorem map_linearVariables {T : Type t} [CommRing T] (f : R →+* T)
    (r : ι → η → R) (q : MvPolynomial η R) :
    MvPolynomial.map f (linearVariables r q) =
      linearVariables (fun i j => f (r i j)) (MvPolynomial.map f q) := by
  change MvPolynomial.map f (eval₂ C (fun j => ∑ i, C (r i j) * X i) q) =
    eval₂ C (fun j => ∑ i, C (f (r i j)) * X i) (MvPolynomial.map f q)
  rw [MvPolynomial.map_eval₂]
  congr 1
  funext j
  change MvPolynomial.map f (∑ i, C (r i j) * X i) =
    ∑ i, C (f (r i j)) * X i
  simp only [map_sum, map_mul, map_C, map_X]

variable {M : Type t} [AddCommGroup M] [Module R M] [Fintype η]
    {κ : Type s} [Fintype κ] [DecidableEq κ]

/-- Every finite linear combination of an endomorphism family is obtained by
linear substitution in its universal determinant polynomial. -/
theorem polynomial_sum_smul_family (b : Module.Basis κ R M)
    (f : η → Module.End R M) (r : ι → η → R) :
    polynomial b (fun i => ∑ j, r i j • f j) =
      linearVariables r (polynomial b f) := by
  unfold polynomial linearVariables
  rw [RingHom.map_det, RingHom.mapMatrix_apply]
  apply congrArg Matrix.det
  apply Matrix.ext
  intro k l
  simp only [matrix, Matrix.map_apply, map_sum, map_mul, eval₂Hom_C,
    eval₂Hom_X', map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    C.map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The same identity for integer combinations needs no coefficient algebra. -/
theorem polynomial_sum_zsmul_family (b : Module.Basis κ R M)
    (f : η → Module.End R M) (r : ι → η → ℤ) :
    polynomial b (fun i => ∑ j, r i j • f j) =
      linearVariables (fun i j => (r i j : R)) (polynomial b f) := by
  simpa only [Int.cast_smul_eq_zsmul] using
    polynomial_sum_smul_family b f (fun i j => (r i j : R))

/-- A finite coefficient index set, depending only on the variables and the
two homogeneous degrees. -/
def homogeneousEquationIndices (σ : Type v) [Finite σ] (m n : ℕ) :
    Finset (σ →₀ ℕ) :=
  ((Finsupp.finite_of_degree_eq (σ := σ) m).union
    (Finsupp.finite_of_degree_eq (σ := σ) n)).toFinset

theorem mem_homogeneousEquationIndices (σ : Type v) [Finite σ]
    (m n : ℕ) (d : σ →₀ ℕ) :
    d ∈ homogeneousEquationIndices σ m n ↔ d.degree = m ∨ d.degree = n := by
  simp [homogeneousEquationIndices]

/-- Two homogeneous polynomials, even of different degrees, are equal exactly
when their coefficients agree on this finite index set. -/
theorem eq_iff_finite_coeff {p q : MvPolynomial ι R} {m n : ℕ}
    (hp : p.IsHomogeneous m) (hq : q.IsHomogeneous n) :
    p = q ↔ ∀ d ∈ homogeneousEquationIndices ι m n, p.coeff d = q.coeff d := by
  constructor
  · intro h d _
    rw [h]
  · intro h
    ext d
    by_cases hd : d ∈ homogeneousEquationIndices ι m n
    · exact h d hd
    · rw [mem_homogeneousEquationIndices] at hd
      rw [hp.coeff_eq_zero (fun hm => hd (Or.inl hm)),
        hq.coeff_eq_zero (fun hn => hd (Or.inr hn))]

end Langlands.Shimura.HodgeDeterminant

namespace Langlands.AbelianScheme

variable {S : Scheme.{u}} {R : CommRingCat.{u}} [Algebra ℚ R]
    (p : S ⟶ Spec R) (B : AbelianScheme S)
    {O : Type v} [Ring O] (α : O →+* End0 B)
    {ι : Type w} [Fintype ι] {η : Type t} [Fintype η]
    {U : S.Opens} {I : Type u} [Fintype I]

/-- Integer combinations of the actual rational Lie family induce the same
linear substitution on its section determinant. -/
theorem lieRationalSectionDeterminant_sum_zsmul_family
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ B.Lie.over U)
    (a : η → O) (r : ι → η → ℤ) (V : Over U) :
    lieRationalSectionDeterminant p B α e (fun i => ∑ j, r i j • a j) V =
      Langlands.Shimura.HodgeDeterminant.linearVariables
        (fun i j => (r i j : Γ(S, V.left)))
        (lieRationalSectionDeterminant p B α e a V) := by
  classical
  rw [lieRationalSectionDeterminant_eq_basis p B α e _ V (localSectionBasis e V),
    lieRationalSectionDeterminant_eq_basis p B α e a V (localSectionBasis e V)]
  simp only [map_sum, map_zsmul]
  exact Langlands.Shimura.HodgeDeterminant.polynomial_sum_zsmul_family _ _ r

/-- The rational Lie determinant has the degree of the actual free chart. -/
theorem lieRationalSectionDeterminant_isHomogeneous
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ B.Lie.over U)
    (a : η → O) (V : Over U) :
    (lieRationalSectionDeterminant p B α e a V).IsHomogeneous (Fintype.card I) :=
  localSectionDeterminant_isHomogeneous e _ V

end Langlands.AbelianScheme

namespace Langlands.Shimura.CentralSimpleUnitaryData

open NumberField _root_.Algebra Langlands.AbelianScheme

variable {E K A : Type}
    [Field E] [NumberField E] [IsTotallyReal E]
    [Field K] [NumberField K] [IsTotallyComplex K]
    [Algebra E K] [IsQuadraticExtension E K]
    [Ring A] [Algebra E A] [Algebra K A] [IsScalarTower E K A]
    [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ K A]
    {n : ℕ} (D : CentralSimpleUnitaryData E K A n)
    {Φ : (E →+* ℝ) → (K →+* ℂ)}
    (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)
    {ι η : Type} [Fintype ι] [Fintype η]

/-- The actual regular Hodge polynomial obeys integer linear substitution. -/
theorem kottwitzHodgeDeterminant_sum_zsmul_family (a : η → A) (r : ι → η → ℤ) :
    D.kottwitzHodgeDeterminant C (fun i => ∑ j, r i j • a j) =
      HodgeDeterminant.linearVariables (fun i j => (r i j : ℂ))
        (D.kottwitzHodgeDeterminant C a) := by
  let : FiniteDimensional K A := D.finite
  let : FiniteDimensional ℚ A := FiniteDimensional.trans ℚ K A
  let h := (D.realPositiveKottwitzHom C).val.hom
  let φ : A →+* ℂ ⊗[ℝ] (ℝ ⊗[ℚ] A) :=
    (TensorProduct.includeRight :
      (ℝ ⊗[ℚ] A) →ₐ[ℝ] ℂ ⊗[ℝ] (ℝ ⊗[ℚ] A)).toRingHom.comp
      (TensorProduct.includeRight : A →ₐ[ℚ] ℝ ⊗[ℚ] A).toRingHom
  change HodgeDeterminant.polynomial (Module.finBasis ℂ (RegularHodge.submodule h))
      (fun i => RegularHodge.leftAction h (φ (∑ j, r i j • a j))) = _
  simp only [map_sum, map_zsmul]
  exact HodgeDeterminant.polynomial_sum_zsmul_family _ _ r

variable (hΦ : IsCMSection E K Φ)

/-- The same identity descends coefficientwise to the actual reflex field. -/
theorem kottwitzReflexDeterminant_sum_zsmul_family (a : η → A)
    (r : ι → η → ℤ) :
    D.kottwitzReflexDeterminant C hΦ (fun i => ∑ j, r i j • a j) =
      HodgeDeterminant.linearVariables
        (fun i j => (r i j : D.kottwitzCocharacterReflexField C))
        (D.kottwitzReflexDeterminant C hΦ a) := by
  apply MvPolynomial.map_injective
    (D.kottwitzCocharacterReflexField C).val.toRingHom Subtype.val_injective
  rw [D.map_kottwitzReflexDeterminant,
    HodgeDeterminant.map_linearVariables, D.map_kottwitzReflexDeterminant]
  simpa only [map_intCast] using D.kottwitzHodgeDeterminant_sum_zsmul_family C a r

/-- Integer linear substitution commutes with every reflex coefficient map. -/
theorem kottwitzReflexDeterminantBaseChange_sum_zsmul_family
    {T : Type*} [CommRing T] (a : η → A) (r : ι → η → ℤ)
    (f : D.kottwitzCocharacterReflexField C →+* T) :
    D.kottwitzReflexDeterminantBaseChange C hΦ (fun i => ∑ j, r i j • a j) f =
      HodgeDeterminant.linearVariables (fun i j => (r i j : T))
        (D.kottwitzReflexDeterminantBaseChange C hΦ a f) := by
  unfold kottwitzReflexDeterminantBaseChange
  rw [D.kottwitzReflexDeterminant_sum_zsmul_family C hΦ,
    HodgeDeterminant.map_linearVariables]
  simp only [map_intCast]

end Langlands.Shimura.CentralSimpleUnitaryData

namespace Langlands.Shimura.CentralSimpleUnitaryData

open NumberField _root_.Algebra Langlands.AbelianScheme

variable {E F A : Type}
    [Field E] [NumberField E] [IsTotallyReal E]
    [Field F] [NumberField F] [IsTotallyComplex F]
    [Algebra E F] [IsQuadraticExtension E F]
    [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
    [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ F A]
    {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
    {L : Type} [Field L] [NumberField L] [IsCMField L]
    [IsQuadraticExtension ℚ L] [Algebra L F]
    {τ₀ : L →+* ℂ}
    (C : HarrisSignatureCharts D.toSecondKindInvolution n
      (harrisCMSection E (algebraMap L F) τ₀))
    {S : Scheme.{0}} (p : S ⟶ Spec (.of F))
    (B : AbelianScheme S) (i : A →ₐ[ℚ] End0 B)
    {ι η : Type} [Fintype ι] [Fintype η]
    {U : S.Opens} {I : Type} [Fintype I]

local notation "hΦ" => isCMSection_harrisCMSection E (algebraMap L F) τ₀

/-- A determinant identity for one family implies the identity for each of its
integer-linear combination families at the same chart and smaller open. -/
theorem harrisTaylorCMRationalLieDeterminantConditionAt_sum_zsmul
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ B.Lie.over U)
    (g : η → D.harrisHodgePELIntegralOrder C) (r : ι → η → ℤ) (V : Over U)
    (h : D.HarrisTaylorCMRationalLieDeterminantConditionAt C p B i e g V) :
    D.HarrisTaylorCMRationalLieDeterminantConditionAt C p B i e
      (fun k => ∑ j, r k j • g j) V := by
  unfold HarrisTaylorCMRationalLieDeterminantConditionAt at h ⊢
  rw [lieRationalSectionDeterminant_sum_zsmul_family]
  have hfamily :
      (fun k => ((∑ j, r k j • g j : D.harrisHodgePELIntegralOrder C) : A)) =
        (fun k => ∑ j, r k j • (g j : A)) := by
    funext k
    change (D.harrisHodgePELIntegralOrder C).val (∑ j, r k j • g j) = _
    simp only [map_sum, map_zsmul]
    rfl
  rw [hfamily, D.kottwitzReflexDeterminantBaseChange_sum_zsmul_family,
    HodgeDeterminant.map_linearVariables, h]
  simp only [map_intCast]

/-- A finite integer module-generating family suffices on the same fixed chart
and the same smaller open. -/
theorem harrisTaylorCMRationalLieDeterminantConditionAt_iff_generators
    (g : η → D.harrisHodgePELIntegralOrder C)
    (hg : Submodule.span ℤ (Set.range g) = ⊤)
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ B.Lie.over U)
    (V : Over U) :
    (∀ (κ : Type) [Fintype κ] (a : κ → D.harrisHodgePELIntegralOrder C),
      D.HarrisTaylorCMRationalLieDeterminantConditionAt C p B i e a V) ↔
      D.HarrisTaylorCMRationalLieDeterminantConditionAt C p B i e g V := by
  constructor
  · intro h
    exact h η g
  · intro h κ _ a
    classical
    have hs := (span_range_eq_top_iff_surjective_fintypeLinearCombination ℤ g).mp hg
    choose r hr using fun k => hs (a k)
    have ha : (fun k => ∑ j, r k j • g j) = a := funext hr
    rw [← ha]
    exact D.harrisTaylorCMRationalLieDeterminantConditionAt_sum_zsmul C p B i e g r V h

/-- The chosen number of integer module generators of the actual Harris order. -/
def harrisHodgePELOrderGeneratorCount : ℕ :=
  (Module.Finite.exists_fin
    (R := ℤ) (M := D.harrisHodgePELIntegralOrder C)).choose

/-- A fixed finite generating family, chosen once from the actual Harris order. -/
def harrisHodgePELOrderGenerators :
    Fin (D.harrisHodgePELOrderGeneratorCount C) → D.harrisHodgePELIntegralOrder C :=
  (Module.Finite.exists_fin
    (R := ℤ) (M := D.harrisHodgePELIntegralOrder C)).choose_spec.choose

omit [IsScalarTower ℚ F A] in
theorem span_harrisHodgePELOrderGenerators :
    Submodule.span ℤ (Set.range (D.harrisHodgePELOrderGenerators C)) = ⊤ :=
  (Module.Finite.exists_fin
    (R := ℤ) (M := D.harrisHodgePELIntegralOrder C)).choose_spec.choose_spec

/-- The normalized determinant condition on one fixed finite integer
module-generating family, retaining every finite Lie chart and smaller open. -/
def HarrisTaylorCMGeneratorLieDeterminantCondition : Prop :=
  ∀ (U : S.Opens) (I : Type) [Fintype I]
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ B.Lie.over U)
    (V : Over U),
    D.HarrisTaylorCMRationalLieDeterminantConditionAt C p B i e
      (D.harrisHodgePELOrderGenerators C) V

/-- One fixed finite order family recovers the entire normalized condition. -/
theorem harrisTaylorCMGeneratorLieDeterminantCondition_iff :
    D.HarrisTaylorCMGeneratorLieDeterminantCondition C p B i ↔
      D.HarrisTaylorCMRationalLieDeterminantCondition C p B i := by
  constructor
  · intro h κ _ a U I _ e V
    exact (D.harrisTaylorCMRationalLieDeterminantConditionAt_iff_generators C p B i
      (D.harrisHodgePELOrderGenerators C) (D.span_harrisHodgePELOrderGenerators C) e V).mpr
        (h U I e V) κ a
  · intro h U I _ e V
    exact h _ (D.harrisHodgePELOrderGenerators C) U I e V

/-- The fixed-generator condition retains the exact normalized reflex-base test. -/
theorem harrisTaylorCMGeneratorLieDeterminantCondition_iff_reflex :
    D.HarrisTaylorCMGeneratorLieDeterminantCondition C p B i ↔
      D.HarrisRationalLieDeterminantCondition C hΦ (D.harrisTaylorReflexStructure C p) B i :=
  (D.harrisTaylorCMGeneratorLieDeterminantCondition_iff C p B i).trans
    (D.harrisTaylorCMRationalLieDeterminantCondition_iff C p B i)

/-- Every local family test is a finite list of coefficient equations; its
index set depends only on the family size and the two actual module ranks. -/
theorem harrisTaylorCMRationalLieDeterminantConditionAt_iff_finite_coeff
    (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ B.Lie.over U)
    (g : η → D.harrisHodgePELIntegralOrder C) (V : Over U) :
    D.HarrisTaylorCMRationalLieDeterminantConditionAt C p B i e g V ↔
      ∀ d ∈ HodgeDeterminant.homogeneousEquationIndices η (Fintype.card I)
          (Module.finrank ℂ (D.kottwitzHodgeModule C)),
        (lieRationalSectionDeterminant p B (D.harrisRationalOrderAction C B i) e g V).coeff d =
          (secHom p V.left).hom
            ((D.kottwitzReflexDeterminantBaseChange C hΦ (fun k => (g k : A))
              (D.harrisTaylorReflexToCM C).toRingHom).coeff d) := by
  unfold HarrisTaylorCMRationalLieDeterminantConditionAt
  rw [HodgeDeterminant.eq_iff_finite_coeff
    (lieRationalSectionDeterminant_isHomogeneous p B (D.harrisRationalOrderAction C B i) e g V)
    ((D.kottwitzReflexDeterminantBaseChange_isHomogeneous C hΦ _
      (D.harrisTaylorReflexToCM C).toRingHom).map (secHom p V.left).hom)]
  simp only [MvPolynomial.coeff_map]

/-- The full global normalized test is recovered from finitely many coefficient
equations for one fixed generating family at each chart and smaller open. -/
theorem harrisTaylorCMRationalLieDeterminantCondition_iff_finite_generator_coeff :
    D.HarrisTaylorCMRationalLieDeterminantCondition C p B i ↔
      ∀ (U : S.Opens) (I : Type) [Fintype I]
        (e : SheafOfModules.free (R := S.ringCatSheaf.over U) I ≅ B.Lie.over U)
        (V : Over U)
        (d : Fin (D.harrisHodgePELOrderGeneratorCount C) →₀ ℕ),
        d ∈ HodgeDeterminant.homogeneousEquationIndices
          (Fin (D.harrisHodgePELOrderGeneratorCount C)) (Fintype.card I)
          (Module.finrank ℂ (D.kottwitzHodgeModule C)) →
        (lieRationalSectionDeterminant p B (D.harrisRationalOrderAction C B i) e
          (D.harrisHodgePELOrderGenerators C) V).coeff d =
          (secHom p V.left).hom
            ((D.kottwitzReflexDeterminantBaseChange C hΦ
              (fun k => (D.harrisHodgePELOrderGenerators C k : A))
              (D.harrisTaylorReflexToCM C).toRingHom).coeff d) := by
  rw [← D.harrisTaylorCMGeneratorLieDeterminantCondition_iff C p B i]
  constructor
  · intro h U I _ e V
    exact (D.harrisTaylorCMRationalLieDeterminantConditionAt_iff_finite_coeff C p B i e
      (D.harrisHodgePELOrderGenerators C) V).mp (h U I e V)
  · intro h U I _ e V
    exact (D.harrisTaylorCMRationalLieDeterminantConditionAt_iff_finite_coeff C p B i e
      (D.harrisHodgePELOrderGenerators C) V).mpr (h U I e V)

variable {B}

/-- Equivariant rational isomorphisms preserve the fixed-generator test. -/
theorem harrisTaylorCMGeneratorLieDeterminantCondition_iso
    {B' : AbelianScheme S} (i' : A →ₐ[ℚ] End0 B')
    (e : Langlands.Rationalization.of B ≅ Langlands.Rationalization.of B')
    (he : ∀ a : A, comp0 B B B' (i a) e.hom = comp0 B B' B' e.hom (i' a)) :
    D.HarrisTaylorCMGeneratorLieDeterminantCondition C p B i ↔
      D.HarrisTaylorCMGeneratorLieDeterminantCondition C p B' i' :=
  (D.harrisTaylorCMGeneratorLieDeterminantCondition_iff C p B i).trans
    ((D.harrisTaylorCMRationalLieDeterminantCondition_iso C p i i' e he).trans
      (D.harrisTaylorCMGeneratorLieDeterminantCondition_iff C p B' i').symm)

end Langlands.Shimura.CentralSimpleUnitaryData
