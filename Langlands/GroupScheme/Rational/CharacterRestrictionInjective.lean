import Langlands.GroupScheme.Rational.SplitComponentProof
import Langlands.GroupScheme.Rational.CentralSplitTorusCharacterStatement

/-! # Injectivity of restriction to a split component

Every central split torus of an affine group scheme of finite type over a field factors through
every split component. Hence, if central split tori detect nonzero rational characters, restriction
of rational characters to a split component is injective.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}

/-- Over a field, every central split torus `i'` of an affine group scheme `G` with finite-type
coordinate algebra factors through every split component `i` of `G`. -/
theorem IsSplitComponent.exists_comp_eq [IsAffine G.X.left]
    (hfin : Algebra.FiniteType (CommRingCat.of k) (AffineCoordinates.algebra G))
    {A A' : CommGroupScheme (Spec (CommRingCat.of k))} {i : A.toGrp ⟶ G} {i' : A'.toGrp ⟶ G}
    (hi : IsSplitComponent i) (hi' : IsCentralSplitTorus i') :
    ∃ f : A'.toGrp ⟶ A.toGrp, f ≫ i = i' := by
  obtain ⟨B, j, hj, huniv⟩ := exists_largestCentralSplitTorus G hfin
  obtain ⟨g, hg⟩ := huniv A i hi.1.1.1 hi.1.2
  obtain ⟨g', hg'⟩ := huniv A' i' hi'.1.1 hi'.2
  have : IsIso g := hi.2 B j hj g hg
  exact ⟨g' ≫ inv g, by rw [Category.assoc, ← hg, IsIso.inv_hom_id_assoc, hg']⟩

/-- A chosen factorization `A' ⟶ A` of a central split torus `i'` through a split component `i`,
given by `IsSplitComponent.exists_comp_eq`. -/
noncomputable def IsSplitComponent.lift [IsAffine G.X.left]
    (hfin : Algebra.FiniteType (CommRingCat.of k) (AffineCoordinates.algebra G))
    {A A' : CommGroupScheme (Spec (CommRingCat.of k))} {i : A.toGrp ⟶ G} {i' : A'.toGrp ⟶ G}
    (hi : IsSplitComponent i) (hi' : IsCentralSplitTorus i') : A'.toGrp ⟶ A.toGrp :=
  (hi.exists_comp_eq hfin hi').choose

@[reassoc (attr := simp)]
theorem IsSplitComponent.lift_comp [IsAffine G.X.left]
    (hfin : Algebra.FiniteType (CommRingCat.of k) (AffineCoordinates.algebra G))
    {A A' : CommGroupScheme (Spec (CommRingCat.of k))} {i : A.toGrp ⟶ G} {i' : A'.toGrp ⟶ G}
    (hi : IsSplitComponent i) (hi' : IsCentralSplitTorus i') : hi.lift hfin hi' ≫ i = i' :=
  (hi.exists_comp_eq hfin hi').choose_spec

/-- If central split tori detect nonzero rational characters, restriction of rational characters
to a split component `i` of a connected reductive group `G` is injective. -/
theorem characterRestrict_injective_of_centralSplitTorusCharacter
    (hS : CentralSplitTorusCharacterStatement.{u}) (hG : IsConnectedReductive G)
    {A : CommGroupScheme (Spec (CommRingCat.of k))} {i : A.toGrp ⟶ G}
    (hi : IsSplitComponent i) : Function.Injective (characterRestrict i) := by
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : Smooth G.X.hom := hG.smooth
  rw [injective_iff_map_eq_zero]
  intro χ hχ
  by_contra hne
  obtain ⟨A', i', hi', hχ'⟩ := hS k G hG χ hne
  apply hχ'
  rw [← hi.lift_comp (finiteType_coordinateAlgebra G) hi', characterRestrict_comp,
    AddMonoidHom.comp_apply, hχ, map_zero]

end Langlands.GroupScheme
