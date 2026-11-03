import Langlands.GroupScheme.CentralIsogeny.Uniqueness
import Langlands.GroupScheme.Torus.Maximal
import Langlands.GroupScheme.Torus.SplitReductiveProof
import Langlands.GroupScheme.Rational.RelativeCentralDirections

/-! # Finite torus restrictions and injectivity on actual cocharacters -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G G' : GroupScheme (Spec (CommRingCat.of k))}
  {T T' : CommGroupScheme (Spec (CommRingCat.of k))}

/-- A finite homomorphism of commutative group schemes over a field is injective on actual
cocharacters. The homomorphism and its kernel may be inseparable or nonsmooth. -/
theorem cocharacterMapInt_injective_of_isFinite (t : T ⟶ T')
    [IsFinite (CommGroupScheme.groupHom t).hom.hom.left] :
    Function.Injective (RealTorusSpace.cocharacterMapInt t) := by
  have hgm : IsSplitTorus (Gm (Spec (CommRingCat.of k))).toGrp := isSplitTorus_gm
  have := hgm.smooth
  have := hgm.isAffineHom
  have := hgm.connectedSpace
  intro ν μ h
  have heq : CommGroupScheme.groupHom ν ≫ CommGroupScheme.groupHom t =
      CommGroupScheme.groupHom μ ≫ CommGroupScheme.groupHom t :=
    congrArg CommGroupScheme.groupHom h
  have hνμ := finiteHom_cancel (CommGroupScheme.groupHom t) heq
  exact congrArg Additive.ofMul hνμ

/-- A finite homomorphism identifies the actual cocharacter lattice of its source with
the image of postcomposition in the target cocharacter lattice. -/
def cocharacterRangeEquivOfFinite (t : T ⟶ T')
    [IsFinite (CommGroupScheme.groupHom t).hom.hom.left] :
    cocharacterLattice T ≃ₗ[ℤ] LinearMap.range (RealTorusSpace.cocharacterMapInt t) :=
  LinearEquiv.ofInjective (RealTorusSpace.cocharacterMapInt t)
    (cocharacterMapInt_injective_of_isFinite t)

@[simp]
theorem cocharacterRangeEquivOfFinite_apply (t : T ⟶ T')
    [IsFinite (CommGroupScheme.groupHom t).hom.hom.left] (ν : cocharacterLattice T) :
    (cocharacterRangeEquivOfFinite t ν : cocharacterLattice T') = ν ≫ t :=
  rfl

/-- A finite ambient homomorphism restricts to a finite map between closed subgroups in a
commuting square. -/
theorem isFinite_torusRestriction {i : T.toGrp ⟶ G} {i' : T'.toGrp ⟶ G'}
    (hi : IsClosedSubgroup i) (hi' : IsClosedSubgroup i')
    (φ : G ⟶ G') [IsFinite φ.hom.hom.left] (t : T ⟶ T')
    (ht : i ≫ φ = CommGroupScheme.groupHom t ≫ i') :
    IsFinite (CommGroupScheme.groupHom t).hom.hom.left := by
  have : IsClosedImmersion i.hom.hom.left := hi
  have : IsClosedImmersion i'.hom.hom.left := hi'
  have hcomp : IsFinite ((CommGroupScheme.groupHom t).hom.hom.left ≫ i'.hom.hom.left) := by
    have h : i.hom.hom.left ≫ φ.hom.hom.left =
        (CommGroupScheme.groupHom t).hom.hom.left ≫ i'.hom.hom.left :=
      congrArg (fun f => f.hom.hom.left) ht
    rw [← h]
    infer_instance
  exact IsFinite.of_comp (CommGroupScheme.groupHom t).hom.hom.left i'.hom.hom.left

/-- In a commuting square over a central isogeny with closed torus embeddings, the actual
pushforward of cocharacters is injective. No splitness or maximality is required. -/
theorem IsCentralIsogeny.cocharacterMapInt_injective_of_square
    {φ : G ⟶ G'} (hφ : IsCentralIsogeny φ)
    {i : T.toGrp ⟶ G} {i' : T'.toGrp ⟶ G'}
    (hi : IsClosedSubgroup i) (hi' : IsClosedSubgroup i') (t : T ⟶ T')
    (ht : i ≫ φ = CommGroupScheme.groupHom t ≫ i') :
    Function.Injective (RealTorusSpace.cocharacterMapInt t) := by
  have := hφ.isFinite
  have := isFinite_torusRestriction hi hi' φ t ht
  exact cocharacterMapInt_injective_of_isFinite t

end Langlands.GroupScheme
