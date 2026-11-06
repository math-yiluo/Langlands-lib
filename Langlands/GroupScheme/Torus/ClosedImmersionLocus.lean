import Langlands.GroupScheme.Torus.ClosedImmersionLocusAffine
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Open closed-immersion neighbourhoods for split-torus homomorphisms -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace TorusClosedImmersionLocus

/-- An actual affine open through which a specified field-valued point factors. -/
structure FieldPointAffineChart {S : Scheme.{u}} {K : Type u} [Field K]
    (x : Spec (CommRingCat.of K) ⟶ S) where
  ring : CommRingCat.{u}
  map : Spec ring ⟶ S
  isOpen : IsOpenImmersion map
  lift : Spec (CommRingCat.of K) ⟶ Spec ring
  fac : lift ≫ map = x

/-- Choose an affine open around the image of the unique field point and
factor the supplied actual morphism through it. -/
def fieldPointAffineChart {S : Scheme.{u}} {K : Type u} [Field K]
    (x : Spec (CommRingCat.of K) ⟶ S) : FieldPointAffineChart x := by
  let h := Scheme.exists_affine_mem_range_and_range_subset
    (X := S) (x := x (IsLocalRing.closedPoint K)) (U := ⊤) (by trivial)
  let R := h.choose
  let p : Spec R ⟶ S := h.choose_spec.choose
  have hp : IsOpenImmersion p := h.choose_spec.choose_spec.1
  let := hp
  have hrange : Set.range x ⊆ Set.range p := by
    rintro _ ⟨z, rfl⟩
    rw [Subsingleton.elim z (IsLocalRing.closedPoint K)]
    exact h.choose_spec.choose_spec.2.1
  exact
    { ring := R
      map := p
      isOpen := hp
      lift := IsOpenImmersion.lift p x hrange
      fac := IsOpenImmersion.lift_fac p x hrange }

set_option backward.isDefEq.respectTransparency false in
/-- Closed immersion of an actual homomorphism is unchanged by replacing
one base change along a composite by the corresponding iterated base change. -/
theorem closed_comp_baseChange_iff {S S' S'' : Scheme.{u}}
    (b : S' ⟶ S) (c : S'' ⟶ S') {H G : GroupScheme S} (i : H ⟶ G) :
    IsClosedImmersion ((baseChange (c ≫ b)).map i).hom.hom.left ↔
      IsClosedImmersion ((baseChange c).map ((baseChange b).map i)).hom.hom.left := by
  let e := Over.pullbackComp c b
  let heH : IsIso ((e.app H.X).hom.left) :=
    (Over.forget _).map_isIso (e.app H.X).hom
  let heG : IsIso ((e.app G.X).hom.left) :=
    (Over.forget _).map_isIso (e.app G.X).hom
  have hn := congrArg Over.Hom.left (e.hom.naturality i.hom.hom)
  change ((Over.pullback (c ≫ b)).map i.hom.hom).left ≫ (e.app G.X).hom.left =
    (e.app H.X).hom.left ≫
      ((Over.pullback c).map ((Over.pullback b).map i.hom.hom)).left at hn
  change IsClosedImmersion ((Over.pullback (c ≫ b)).map i.hom.hom).left ↔
    IsClosedImmersion ((Over.pullback c).map ((Over.pullback b).map i.hom.hom)).left
  calc
    _ ↔ IsClosedImmersion
        (((Over.pullback (c ≫ b)).map i.hom.hom).left ≫ (e.app G.X).hom.left) :=
      (MorphismProperty.cancel_right_of_respectsIso (P := @IsClosedImmersion) _ _).symm
    _ ↔ IsClosedImmersion
        ((e.app H.X).hom.left ≫
          ((Over.pullback c).map ((Over.pullback b).map i.hom.hom)).left) := by
      rw [hn]
    _ ↔ _ :=
      MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion) _ _

end TorusClosedImmersionLocus

set_option backward.isDefEq.respectTransparency false in
/-- A homomorphism from an actual split torus into an affine group is a closed
immersion on an open neighbourhood of any field-valued point where it is one.
The given field-valued point factors through that neighbourhood exactly. -/
theorem exists_open_isClosedImmersion_baseChange
    {S : Scheme.{u}} {H G : GroupScheme S}
    (hH : IsSplitTorus H) [IsAffineHom G.X.hom] (i : H ⟶ G)
    (K : Type u) [Field K] (x : Spec (CommRingCat.of K) ⟶ S)
    (hx : IsClosedImmersion ((baseChange x).map i).hom.hom.left) :
    ∃ (V : Scheme.{u}) (q : V ⟶ S), IsOpenImmersion q ∧
      ∃ bx : Spec (CommRingCat.of K) ⟶ V, bx ≫ q = x ∧
        IsClosedImmersion ((baseChange q).map i).hom.hom.left := by
  let C := TorusClosedImmersionLocus.fieldPointAffineChart x
  let hp : IsOpenImmersion C.map := C.isOpen
  let H' := (baseChange C.map).obj H
  let G' := (baseChange C.map).obj G
  let i' : H' ⟶ G' := (baseChange C.map).map i
  let hG' : IsAffineHom G'.X.hom := by
    change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom C.map)
    infer_instance
  let hGa : IsAffine G'.X.left := isAffine_of_isAffineHom G'.X.hom
  have hcx : IsClosedImmersion ((baseChange (C.lift ≫ C.map)).map i).hom.hom.left := by
    rw [C.fac]
    exact hx
  have hxi' : IsClosedImmersion ((baseChange C.lift).map i').hom.hom.left :=
    (TorusClosedImmersionLocus.closed_comp_baseChange_iff C.map C.lift i).mp hcx
  obtain ⟨V, q, hq, bx, hbx, hi⟩ :=
    TorusClosedImmersionLocus.exists_open_affine
      (hH.baseChange C.map) i' K C.lift hxi'
  let := hq
  refine ⟨V, q ≫ C.map, inferInstance, bx, ?_, ?_⟩
  · rw [← Category.assoc, hbx]
    exact C.fac
  · exact (TorusClosedImmersionLocus.closed_comp_baseChange_iff C.map q i).mpr hi

end Langlands.GroupScheme
