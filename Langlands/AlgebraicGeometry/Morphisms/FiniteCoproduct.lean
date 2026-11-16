import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_isSeparated_sigmaDesc_of_forall_isSeparated

/-! # Properness and smoothness of scheme coproduct morphisms -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.FiniteCoproduct

/-- Closedness of a map can be tested on a finite open cover of its source. -/
theorem isClosedMap_of_finite_openCover {X Y : Scheme.{u}}
    (𝒰 : X.OpenCover) [Finite 𝒰.I₀] (f : X ⟶ Y)
    (hf : ∀ i, IsClosedMap (𝒰.f i ≫ f)) : IsClosedMap f := by
  intro Z hZ
  have heq : f '' Z = ⋃ i, (𝒰.f i ≫ f) '' ((𝒰.f i) ⁻¹' Z) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨i, z, rfl⟩ := 𝒰.exists_eq x
      exact Set.mem_iUnion.mpr ⟨i, z, hx, rfl⟩
    · intro hy
      obtain ⟨i, z, hz, rfl⟩ := Set.mem_iUnion.mp hy
      exact ⟨𝒰.f i z, hz, rfl⟩
  rw [heq]
  exact isClosed_iUnion_of_finite fun i => hf i _ (hZ.preimage (𝒰.f i).continuous)

variable {I : Type v} [Small.{u} I] (X : I → Scheme.{u})
    {Y : Scheme.{u}} (f : ∀ i, X i ⟶ Y)

/-- A finite coproduct of universally closed morphisms to one target is universally closed. -/
theorem universallyClosed_sigmaDesc [Finite I]
    (hf : ∀ i, UniversallyClosed (f i)) : UniversallyClosed (Sigma.desc f) := by
  constructor
  intro X' Y' i₁ i₂ f' H
  let 𝒰 := (sigmaOpenCover X).pullback₁ i₁
  let : Finite 𝒰.I₀ := by
    change Finite I
    infer_instance
  apply isClosedMap_of_finite_openCover 𝒰 f'
  intro i
  change I at i
  have hp := (IsPullback.of_hasPullback i₁ (Sigma.ι X i)).paste_horiz H
  simp only [Sigma.ι_comp_desc] at hp
  let : UniversallyClosed (pullback.fst i₁ (Sigma.ι X i) ≫ f') :=
    MorphismProperty.of_isPullback hp.flip (hf i)
  exact Scheme.Hom.isClosedMap (pullback.fst i₁ (Sigma.ι X i) ≫ f')

/-- A finite coproduct of proper morphisms to one target is proper. -/
theorem isProper_sigmaDesc [Finite I]
    (hf : ∀ i, IsProper (f i)) : IsProper (Sigma.desc f) := by
  let : IsSeparated (Sigma.desc f) :=
    _root_.AlgebraicGeometry.isSeparated_sigmaDesc_of_forall_isSeparated X f
      (fun i => (hf i).toIsSeparated)
  let : UniversallyClosed (Sigma.desc f) :=
    universallyClosed_sigmaDesc X f (fun i => (hf i).toUniversallyClosed)
  let : LocallyOfFiniteType (Sigma.desc f) :=
    IsZariskiLocalAtSource.sigmaDesc (P := @_root_.AlgebraicGeometry.LocallyOfFiniteType)
      (fun i => (hf i).toLocallyOfFiniteType)
  exact {}

/-- A coproduct of smooth morphisms to one target is smooth. -/
theorem smooth_sigmaDesc (hf : ∀ i, Smooth (f i)) : Smooth (Sigma.desc f) :=
  IsZariskiLocalAtSource.sigmaDesc (P := @_root_.AlgebraicGeometry.Smooth) hf

/-- The actual finite coproduct, bundled as a smooth proper scheme over the target. -/
def smoothProperCoproduct [Finite I] (hs : ∀ i, Smooth (f i))
    (hp : ∀ i, IsProper (f i)) :
    {V : Over Y // Smooth V.hom ∧ IsProper V.hom} :=
  ⟨Over.mk (Sigma.desc f), smooth_sigmaDesc X f hs, isProper_sigmaDesc X f hp⟩

/-- The structure morphism of the bundled construction is the coproduct descent map. -/
theorem smoothProperCoproduct_hom [Finite I] (hs : ∀ i, Smooth (f i))
    (hp : ∀ i, IsProper (f i)) :
    (smoothProperCoproduct X f hs hp).val.hom = Sigma.desc f := rfl

end Langlands.AlgebraicGeometry.FiniteCoproduct
