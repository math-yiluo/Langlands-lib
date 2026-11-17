import Langlands.GroupScheme.RelativeIdentityComponent.FieldProductCover
import Langlands.AbelianScheme.SmoothGeometricIntegralityProof

/-! # Finite-type identity components of smooth field groups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open RelativeIdentityComponent

/-- A smooth connected group scheme over a field is quasi-compact, without
any affineness assumption. -/
theorem quasiCompact_of_smooth_connected {k : Type u} [Field k]
    (H : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth H.X.hom] [ConnectedSpace H.X.left] : QuasiCompact H.X.hom := by
  obtain ⟨U, hU, he, -⟩ := exists_isAffineOpen_mem_and_subset
    (U := (⊤ : H.X.left.Opens)) (show IdentityComponent.identityPoint H ∈
      (⊤ : H.X.left.Opens) from trivial)
  let P : Over (Spec (CommRingCat.of k)) := Over.mk (U.ι ≫ H.X.hom)
  let i : P ⟶ H.X := Over.homMk U.ι
  have : IsOpenImmersion i.left := inferInstanceAs (IsOpenImmersion U.ι)
  have : IsAffine P.left := hU
  have : QuasiCompact P.hom := quasiCompact_of_compactSpace _
  have : CompactSpace (P ⊗ P).left :=
    inferInstanceAs (CompactSpace (pullback P.hom P.hom : Scheme.{u}))
  have hunit : IdentityComponent.identityPoint H ∈ Set.range i.left :=
    ⟨⟨IdentityComponent.identityPoint H, he⟩, rfl⟩
  have hsurj : Function.Surjective (fieldOpenProduct H i).left := by
    intro y
    apply identitySet_subset_range_fieldOpenProduct H i hunit
    rw [IdentityComponent.identitySet, PreconnectedSpace.connectedComponent_eq_univ]
    trivial
  have : CompactSpace H.X.left := by
    rw [← isCompact_univ_iff, ← hsurj.range_eq]
    exact isCompact_range (fieldOpenProduct H i).left.continuous
  exact quasiCompact_of_compactSpace _

namespace SmoothFieldComponent

open Langlands.GroupScheme.FiniteEtaleImage (liftOver liftOver_fac)

variable {k : Type u} [Field k]
  (H : GroupScheme (Spec (CommRingCat.of k))) [Smooth H.X.hom]

local instance : Mono (fieldIdentityInclusion H) := Over.mono_of_mono_left _

instance : IsClosedImmersion (fieldIdentityInclusion H).left :=
  IsClosedImmersion.of_isPreimmersion _ (by
    rw [range_fieldIdentityInclusion, IdentityComponent.identitySet]
    exact isClosed_connectedComponent)

@[reassoc (attr := simp)]
theorem one_fac : fieldIdentityOne H ≫ fieldIdentityInclusion H = η[H.X] :=
  liftOver_fac _ _ _

instance : UniversallyOpen (fieldIdentityOver H).hom := UniversallyOpen.of_flat _

instance : ConnectedSpace (fieldIdentityOver H ⊗ fieldIdentityOver H).left :=
  inferInstanceAs (ConnectedSpace
    (pullback (fieldIdentityOver H).hom (fieldIdentityOver H).hom : Scheme.{u}))

/-- Multiplication restricts to the raw identity component. -/
def mul : fieldIdentityOver H ⊗ fieldIdentityOver H ⟶ fieldIdentityOver H :=
  liftOver (fieldIdentityInclusion H)
    ((fieldIdentityInclusion H ⊗ₘ fieldIdentityInclusion H) ≫ μ[H.X]) (by
      rw [range_fieldIdentityInclusion]
      refine IdentityComponent.range_subset_identitySet H _
        (lift (fieldIdentityOne H) (fieldIdentityOne H)) ?_
      rw [lift_map_assoc, one_fac]
      simpa using MonObj.lift_comp_one_left (𝟙 (𝟙_ (Over (Spec (CommRingCat.of k))))) η[H.X])

@[reassoc (attr := simp)]
theorem mul_fac : mul H ≫ fieldIdentityInclusion H =
    (fieldIdentityInclusion H ⊗ₘ fieldIdentityInclusion H) ≫ μ[H.X] :=
  liftOver_fac _ _ _

/-- Inversion restricts to the raw identity component. -/
def inv : fieldIdentityOver H ⟶ fieldIdentityOver H :=
  liftOver (fieldIdentityInclusion H) (fieldIdentityInclusion H ≫ ι[H.X]) (by
    rw [range_fieldIdentityInclusion]
    refine IdentityComponent.range_subset_identitySet H _ (fieldIdentityOne H) ?_
    rw [one_fac_assoc, GrpObj.one_inv])

@[reassoc (attr := simp)]
theorem inv_fac : inv H ≫ fieldIdentityInclusion H = fieldIdentityInclusion H ≫ ι[H.X] :=
  liftOver_fac _ _ _

instance : GrpObj (fieldIdentityOver H) :=
  Langlands.CategoryTheory.GroupObjectDescent.grpObjOfMono
    (fieldIdentityInclusion H) (fieldIdentityOne H) (mul H) (inv H)
    (one_fac H) (mul_fac H) (inv_fac H)

instance : IsMonHom (fieldIdentityInclusion H) :=
  Langlands.CategoryTheory.GroupObjectDescent.isMonHom_grpObjOfMono
    (fieldIdentityInclusion H) (fieldIdentityOne H) (mul H) (inv H)
    (one_fac H) (mul_fac H) (inv_fac H)

/-- The actual identity-component group of a smooth, possibly nonaffine and
non-quasi-compact group scheme over a field. -/
abbrev group : GroupScheme (Spec (CommRingCat.of k)) := { X := fieldIdentityOver H }

/-- The inclusion of the smooth field identity component. -/
def inclusion : group H ⟶ H := Grp.homMk (fieldIdentityInclusion H)

instance : IsOpenImmersion (inclusion H).hom.hom.left :=
  inferInstanceAs (IsOpenImmersion (fieldIdentityInclusion H).left)

instance : IsClosedImmersion (inclusion H).hom.hom.left :=
  inferInstanceAs (IsClosedImmersion (fieldIdentityInclusion H).left)

instance : Smooth (group H).X.hom :=
  inferInstanceAs (Smooth (fieldIdentityOver H).hom)

instance : ConnectedSpace (group H).X.left :=
  inferInstanceAs (ConnectedSpace (fieldIdentityOver H).left)

instance : GeometricallyConnected (group H).X.hom :=
  inferInstanceAs (GeometricallyConnected (fieldIdentityOver H).hom)

instance : QuasiCompact (group H).X.hom := quasiCompact_of_smooth_connected _

instance : GeometricallyIntegral (group H).X.hom :=
  Langlands.AbelianScheme.smoothGeometricIntegrality k (group H).X.left (group H).X.hom
    inferInstance inferInstance

/-- The range of the inclusion is the actual identity connected component. -/
theorem range_inclusion :
    Set.range (inclusion H).hom.hom.left = IdentityComponent.identitySet H :=
  range_fieldIdentityInclusion H

section Factor

variable {C : GroupScheme (Spec (CommRingCat.of k))} [ConnectedSpace C.X.left]
  (f : C ⟶ H)

/-- Every homomorphism from a connected group scheme factors through the
finite-type identity component, without an affine-source premise. -/
def factor : C ⟶ group H :=
  IdentityComponent.liftHom (inclusion H) f (by
    rw [range_inclusion]
    exact IdentityComponent.range_subset_identitySet H f.hom.hom η[C.X]
      (IsMonHom.one_hom _))

@[reassoc (attr := simp)]
theorem factor_inclusion : factor H f ≫ inclusion H = f :=
  IdentityComponent.liftHom_fac _ _ _

end Factor

end SmoothFieldComponent
end Langlands.GroupScheme
