import Langlands.Shimura.PEL.HarrisTaylorCMActionPresheaf
import Langlands.AbelianScheme.LieBaseChangeNaturalityProof

/-! # Open-cover descent of the normalized Harris determinant -/

noncomputable section

open CategoryTheory _root_.AlgebraicGeometry
open Langlands.Scheme.Modules Langlands.AbelianScheme

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.CentralSimpleUnitaryData

open NumberField _root_.Algebra

variable {E F A : Type}
    [Field E] [NumberField E] [IsTotallyReal E]
    [Field F] [NumberField F] [IsTotallyComplex F]
    [Algebra E F] [IsQuadraticExtension E F]
    [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
    [Algebra ℚ A] [IsScalarTower ℚ E A] [IsScalarTower ℚ F A]
    {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
    {S : Scheme.{0}}

section Reflex

variable {Φ : (E →+* ℝ) → (F →+* ℂ)}
    (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)
    (hΦ : IsCMSection E F Φ)
    (s : S ⟶ Spec (.of (D.kottwitzCocharacterReflexField C)))
    (B : AbelianScheme S) (i : A →ₐ[ℚ] End0 B)

/-- Descent uses equality of actual section coefficients on an arbitrary open cover. -/
theorem harrisRationalLieDeterminantCondition_of_openCover (𝒰 : S.OpenCover)
    (h : ∀ k : 𝒰.I₀,
      D.HarrisRationalLieDeterminantCondition C hΦ (𝒰.f k ≫ s)
        ((baseChange (𝒰.f k)).obj B) ((rationalBaseChangeEnd (𝒰.f k) B).comp i)) :
    D.HarrisRationalLieDeterminantCondition C hΦ s B i := by
  intro κ _ a U I _ e V
  apply MvPolynomial.ext
  intro d
  apply 𝒰.ext_elem
  intro k
  let f := 𝒰.f k
  have hk := h k κ a (f ⁻¹ᵁ U) I (lieBaseChangeChart f B e)
    (Over.mk ((TopologicalSpace.Opens.map f.base).map V.hom))
  have hmap :
      MvPolynomial.map (f.app V.left).hom
          (lieRationalSectionDeterminant s B (D.harrisRationalOrderAction C B i) e a V) =
        MvPolynomial.map (f.app V.left).hom
          (D.harrisReflexSectionDeterminant C hΦ s a V.left) := by
    rw [lieRationalSectionDeterminant_baseChange_of_naturality s f B _
      (lieBaseChangeNaturalityStatements S).1 e a V,
      D.harrisReflexSectionDeterminant_pullback C hΦ s f a V.left]
    exact hk
  simpa only [MvPolynomial.coeff_map] using congrArg (fun q => q.coeff d) hmap

end Reflex

variable {L : Type} [Field L] [NumberField L] [IsCMField L]
    [IsQuadraticExtension ℚ L] [Algebra L F]
    {τ₀ : L →+* ℂ}
    (C : HarrisSignatureCharts D.toSecondKindInvolution n
      (harrisCMSection E (algebraMap L F) τ₀))
    (p : S ⟶ Spec (.of F))
    (B : AbelianScheme S) (i : A →ₐ[ℚ] End0 B)

local notation "hΦ" => isCMSection_harrisCMSection E (algebraMap L F) τ₀

/-- The normalized all-family, all-chart determinant condition descends on any open cover. -/
theorem harrisTaylorCMRationalLieDeterminantCondition_of_openCover (𝒰 : S.OpenCover)
    (h : ∀ k : 𝒰.I₀,
      D.HarrisTaylorCMRationalLieDeterminantCondition C (𝒰.f k ≫ p)
        ((baseChange (𝒰.f k)).obj B) ((rationalBaseChangeEnd (𝒰.f k) B).comp i)) :
    D.HarrisTaylorCMRationalLieDeterminantCondition C p B i := by
  apply (D.harrisTaylorCMRationalLieDeterminantCondition_iff C p B i).mpr
  apply D.harrisRationalLieDeterminantCondition_of_openCover C hΦ
    (D.harrisTaylorReflexStructure C p) B i 𝒰
  intro k
  have hk := (D.harrisTaylorCMRationalLieDeterminantCondition_iff C (𝒰.f k ≫ p)
    ((baseChange (𝒰.f k)).obj B) ((rationalBaseChangeEnd (𝒰.f k) B).comp i)).mp (h k)
  rw [D.harrisTaylorReflexStructure_comp C p (𝒰.f k)] at hk
  exact hk

/-- The same descent applies to the actual equivariant rational-action classes. -/
theorem harrisTaylorCMDeterminantClassCondition_of_openCover
    (q : RationalAlgebraAction.IsoClass S A) (𝒰 : S.OpenCover)
    (h : ∀ k : 𝒰.I₀,
      D.HarrisTaylorCMDeterminantClassCondition C (𝒰.f k ≫ p)
        (RationalAlgebraAction.pullbackClass (𝒰.f k) q)) :
    D.HarrisTaylorCMDeterminantClassCondition C p q := by
  obtain ⟨X, rfl⟩ := RationalAlgebraAction.classOf_surjective q
  apply (D.harrisTaylorCMDeterminantClassCondition_classOf C p X).mpr
  apply D.harrisTaylorCMRationalLieDeterminantCondition_of_openCover C p
    X.abelianScheme X.action 𝒰
  intro k
  exact (D.harrisTaylorCMDeterminantClassCondition_classOf C (𝒰.f k ≫ p)
    ((RationalAlgebraAction.pullback (𝒰.f k)).obj X)).mp (h k)

/-- A property of actual test maps, retaining the given family and rational action. -/
def HarrisTaylorCMDeterminantPullbackCondition {T : Scheme.{0}} (g : T ⟶ S) : Prop :=
  D.HarrisTaylorCMDeterminantClassCondition C (g ≫ p)
    (RationalAlgebraAction.pullbackClass g
      (RationalAlgebraAction.classOf (RationalAlgebraAction.of B i)))

/-- The class formulation is exactly the determinant on the actual pulled-back representative. -/
theorem harrisTaylorCMDeterminantPullbackCondition_iff
    {T : Scheme.{0}} (g : T ⟶ S) :
    D.HarrisTaylorCMDeterminantPullbackCondition C p B i g ↔
      D.HarrisTaylorCMRationalLieDeterminantCondition C (g ≫ p)
        ((baseChange g).obj B) ((rationalBaseChangeEnd g B).comp i) :=
  D.harrisTaylorCMDeterminantClassCondition_classOf C (g ≫ p)
    ((RationalAlgebraAction.pullback g).obj (RationalAlgebraAction.of B i))

/-- Stability under precomposition uses the actual pullback comparison on action classes. -/
theorem harrisTaylorCMDeterminantPullbackCondition_comp
    {T T' : Scheme.{0}} (f : T' ⟶ T) (g : T ⟶ S)
    (h : D.HarrisTaylorCMDeterminantPullbackCondition C p B i g) :
    D.HarrisTaylorCMDeterminantPullbackCondition C p B i (f ≫ g) := by
  have h' := D.harrisTaylorCMDeterminantClassCondition_baseChange_of_naturality C (g ≫ p)
    f (lieBaseChangeNaturalityStatements T).1
    (RationalAlgebraAction.pullbackClass g
      (RationalAlgebraAction.classOf (RationalAlgebraAction.of B i))) h
  simpa only [HarrisTaylorCMDeterminantPullbackCondition, Category.assoc,
    RationalAlgebraAction.pullbackClass_comp] using h'

/-- Locality on every open cover of the test scheme, hence on every pulled-back base cover. -/
theorem harrisTaylorCMDeterminantPullbackCondition_of_openCover
    {T : Scheme.{0}} (g : T ⟶ S) (𝒱 : T.OpenCover)
    (h : ∀ k : 𝒱.I₀,
      D.HarrisTaylorCMDeterminantPullbackCondition C p B i (𝒱.f k ≫ g)) :
    D.HarrisTaylorCMDeterminantPullbackCondition C p B i g := by
  apply D.harrisTaylorCMDeterminantClassCondition_of_openCover C (g ≫ p)
    (RationalAlgebraAction.pullbackClass g
      (RationalAlgebraAction.classOf (RationalAlgebraAction.of B i))) 𝒱
  intro k
  simpa only [HarrisTaylorCMDeterminantPullbackCondition, Category.assoc,
    RationalAlgebraAction.pullbackClass_comp] using h k

end Langlands.Shimura.CentralSimpleUnitaryData
