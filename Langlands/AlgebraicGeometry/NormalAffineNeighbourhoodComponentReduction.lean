import Langlands.AlgebraicGeometry.LocalDomainIntegralComponents
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-! # Reduction of normal affine neighbourhoods to integral schemes -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

noncomputable section

namespace Langlands.AlgebraicGeometry

/-- Normal-domain stalks are preserved by passage to an open subscheme. -/
theorem normal_stalks_of_isOpenImmersion
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (hY : ∀ y : Y, IsDomain (Y.presheaf.stalk y) ∧
      IsIntegrallyClosed (Y.presheaf.stalk y)) :
    ∀ x : X, IsDomain (X.presheaf.stalk x) ∧
      IsIntegrallyClosed (X.presheaf.stalk x) := by
  intro x
  have := (hY (f x)).1
  have := (hY (f x)).2
  let e := (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv
  exact ⟨Function.Injective.isDomain e.symm.toRingHom e.symm.injective,
    IsIntegrallyClosed.of_equiv e⟩

/-- Open immersions preserve the dimensions of the corresponding stalks. -/
theorem ringKrullDim_stalk_eq_of_isOpenImmersion
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (x : X) :
    ringKrullDim (X.presheaf.stalk x) = ringKrullDim (Y.presheaf.stalk (f x)) :=
  ((asIso (f.stalkMap x)).commRingCatIsoToRingEquiv.ringKrullDim).symm

/-- Separatedness over an affine base implies separatedness of the scheme. -/
theorem separatedScheme_of_affine_base
    {X S : Scheme.{u}} [IsAffine S] (p : X ⟶ S) [IsSeparated p] :
    X.IsSeparated := by
  constructor
  rw [← terminal.comp_from p]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- The full noetherian-base construction reduces to a constructor for
integral separated locally noetherian schemes locally of finite presentation. -/
def normalAffineNeighbourhoodOfIntegralConstructor
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    (H : ∀ (Y : Scheme.{u}) [IsIntegral Y] [Y.IsSeparated] [IsLocallyNoetherian Y]
      (q : Y ⟶ Spec (CommRingCat.of R)) [LocallyOfFinitePresentation q],
      (∀ y : Y, IsDomain (Y.presheaf.stalk y) ∧
        IsIntegrallyClosed (Y.presheaf.stalk y)) →
      ∀ (F : Set Y), F.Finite →
        (∀ y ∈ F, ringKrullDim (Y.presheaf.stalk y) ≤ 1) →
        {U : Y.Opens // IsAffineOpen U ∧ F ⊆ U})
    {X : Scheme.{u}} (p : X ⟶ Spec (CommRingCat.of R))
    [LocallyOfFiniteType p] [QuasiCompact p] [IsSeparated p]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧
      IsIntegrallyClosed (X.presheaf.stalk x))
    (E : Set X) (hE : E.Finite)
    (hd : ∀ x ∈ E, ringKrullDim (X.presheaf.stalk x) ≤ 1) :
    {U : X.Opens // IsAffineOpen U ∧ E ⊆ U} := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have : IsNoetherian X := ⟨⟩
  have : X.IsSeparated := separatedScheme_of_affine_base p
  let hD := fun x ↦ (hX x).1
  apply affineNeighbourhoodOfIntegralComponentOpens X hD E
  intro C
  let U := integralComponentOpen X hD C
  let Y := U.toScheme
  have : IsIntegral Y := isIntegral_integralComponentOpen X hD C
  have : IsLocallyNoetherian Y := inferInstanceAs (IsLocallyNoetherian U.toScheme)
  have : Y.IsSeparated := by
    constructor
    rw [← terminal.comp_from U.ι]
    infer_instance
  let q := U.ι ≫ p
  have : LocallyOfFinitePresentation q := by dsimp [q]; infer_instance
  let F : Set Y := U.ι ⁻¹' E
  have hF : F.Finite := hE.preimage U.ι.isOpenEmbedding.injective.injOn
  have hY := normal_stalks_of_isOpenImmersion U.ι hX
  have hdY : ∀ y ∈ F, ringKrullDim (Y.presheaf.stalk y) ≤ 1 := by
    intro y hy
    rw [ringKrullDim_stalk_eq_of_isOpenImmersion U.ι y]
    exact hd (U.ι y) hy
  exact H Y q hY F hF hdY

end Langlands.AlgebraicGeometry
