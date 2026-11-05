import Langlands.GroupScheme.HopfMorphismBaseChange
import Langlands.GroupScheme.Torus.DiagonalizableHopf
import Mathlib.AlgebraicGeometry.OpenImmersion

/-! # Closed-immersion neighbourhoods for split tori over affine bases -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.TorusClosedImmersionLocus

set_option backward.isDefEq.respectTransparency false in
/-- Replacing a source by an isomorphic group scheme leaves every
base-changed closed-immersion condition unchanged. -/
theorem closed_baseChange_precomp_iso_iff
    {S S' : Scheme.{u}} (b : S' ⟶ S) {H H' G : GroupScheme S}
    (e : H' ≅ H) (i : H ⟶ G) :
    IsClosedImmersion ((baseChange b).map (e.hom ≫ i)).hom.hom.left ↔
      IsClosedImmersion ((baseChange b).map i).hom.hom.left := by
  rw [Functor.map_comp]
  let he : IsIso ((baseChange b).map e.hom).hom.hom.left :=
    (Grp.forget _ ⋙ Over.forget _).map_isIso ((baseChange b).map e.hom)
  change IsClosedImmersion
    (((baseChange b).map e.hom).hom.hom.left ≫ ((baseChange b).map i).hom.hom.left) ↔ _
  exact MorphismProperty.cancel_left_of_respectsIso (P := @IsClosedImmersion) _ _

variable {R : CommRingCat.{u}} {M : Type u} [AddCommGroup M]
  {G : GroupScheme (Spec R)} [IsAffine G.X.left]

/-- The standard diagonal Hopf spectrum used as a source presentation. -/
abbrev diagonalSource (R : CommRingCat.{u}) (M : Type u) [AddCommGroup M] :
    GroupScheme (Spec R) :=
  (hopfSpec R).obj (op (CommHopfAlgCat.of R (AddMonoidAlgebra R M)))

/-- The Hopf coordinate map of a homomorphism from the standard diagonal
source into an actual affine group scheme. -/
def diagonalCoordinateMap (i : diagonalSource R M ⟶ G) :
    AffineCoordinates.hopfAlgebra G →ₐc[R] AddMonoidAlgebra R M :=
  (hopfSpec.fullyFaithful.preimage
    (i ≫ (AffineCoordinates.hopfSpecIso G).inv)).unop.hom

/-- The coordinate map recovers the supplied actual homomorphism. -/
theorem diagonalCoordinateMap_map (i : diagonalSource R M ⟶ G) :
    (hopfSpec R).map (CommHopfAlgCat.ofHom (diagonalCoordinateMap i)).op =
      i ≫ (AffineCoordinates.hopfSpecIso G).inv :=
  hopfSpec.fullyFaithful.map_preimage _

set_option backward.isDefEq.respectTransparency false in
/-- A diagonal source homomorphism is a closed immersion after actual base
change exactly when its diagonal coordinate map becomes surjective. -/
theorem diagonal_closed_iff (i : diagonalSource R M ⟶ G)
    (A : Type u) [CommRing A] [Algebra R A] :
    IsClosedImmersion
      (((baseChange (Spec.map (CommRingCat.ofHom (algebraMap R A)))).map i).hom.hom.left) ↔
      Function.Surjective
        (CommutativeAlgebra.DiagonalCoalgebraLocus.scalarExtension
          (diagonalCoordinateMap i).toAlgHom A) := by
  have h := HopfMorphismBaseChange.isClosedImmersion_hopf_diagonal_baseChange_iff
    (S := A) (diagonalCoordinateMap i)
  rw [diagonalCoordinateMap_map, Functor.map_comp] at h
  let he : IsIso
      (((baseChange (Spec.map (CommRingCat.ofHom (algebraMap R A)))).map
        (AffineCoordinates.hopfSpecIso G).inv).hom.hom.left) :=
    (Grp.forget _ ⋙ Over.forget _).map_isIso
      ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap R A)))).map
        (AffineCoordinates.hopfSpecIso G).inv)
  change IsClosedImmersion
    ((((baseChange (Spec.map (CommRingCat.ofHom (algebraMap R A)))).map i).hom.hom.left ≫
      ((baseChange (Spec.map (CommRingCat.ofHom (algebraMap R A)))).map
        (AffineCoordinates.hopfSpecIso G).inv).hom.hom.left)) ↔ _ at h
  rwa [MorphismProperty.cancel_right_of_respectsIso (P := @IsClosedImmersion)] at h

set_option backward.isDefEq.respectTransparency false in
/-- Over an affine base, a closed field specialization of a finitely generated
diagonal source is a closed immersion on a principal open containing that point. -/
theorem exists_open_diagonal [AddMonoid.FG M] (i : diagonalSource R M ⟶ G)
    (K : Type u) [Field K] [Algebra R K]
    (hx : IsClosedImmersion
      (((baseChange (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map i).hom.hom.left)) :
    ∃ (V : Scheme.{u}) (q : V ⟶ Spec R), IsOpenImmersion q ∧
      ∃ bx : Spec (CommRingCat.of K) ⟶ V,
        bx ≫ q = Spec.map (CommRingCat.ofHom (algebraMap R K)) ∧
          IsClosedImmersion ((baseChange q).map i).hom.hom.left := by
  have hφ := (diagonal_closed_iff i K).mp hx
  obtain ⟨r, hr, hsurj⟩ :=
    CommutativeAlgebra.DiagonalCoalgebraLocus.exists_away_surjective
      (R := R) (M := M) (B := AffineCoordinates.hopfAlgebra G)
      (diagonalCoordinateMap i) K hφ
  let V := Spec (CommRingCat.of (Localization.Away r))
  let q : V ⟶ Spec R :=
    Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r)))
  let kmap : Localization.Away r →+* K :=
    IsLocalization.Away.lift r (g := algebraMap R K) (isUnit_iff_ne_zero.mpr hr)
  let bx : Spec (CommRingCat.of K) ⟶ V := Spec.map (CommRingCat.ofHom kmap)
  refine ⟨V, q, inferInstance, bx, ?_, ?_⟩
  · change Spec.map (CommRingCat.ofHom kmap) ≫
      Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away r))) = _
    rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact IsLocalization.Away.lift_comp r (g := algebraMap R K)
      (isUnit_iff_ne_zero.mpr hr)
  · exact (diagonal_closed_iff i (Localization.Away r)).mpr hsurj

set_option backward.isDefEq.respectTransparency false in
/-- Every split-torus homomorphism into an affine group has an open
closed-immersion neighbourhood at a closed field specialization. -/
theorem exists_open_affine_algebraMap {H : GroupScheme (Spec R)}
    (hH : IsSplitTorus H) (i : H ⟶ G)
    (K : Type u) [Field K] [Algebra R K]
    (hx : IsClosedImmersion
      (((baseChange (Spec.map (CommRingCat.ofHom (algebraMap R K)))).map i).hom.hom.left)) :
    ∃ (V : Scheme.{u}) (q : V ⟶ Spec R), IsOpenImmersion q ∧
      ∃ bx : Spec (CommRingCat.of K) ⟶ V,
        bx ≫ q = Spec.map (CommRingCat.ofHom (algebraMap R K)) ∧
          IsClosedImmersion ((baseChange q).map i).hom.hom.left := by
  classical
  obtain ⟨I, hI, ⟨eH⟩⟩ := hH
  let := Fintype.ofFinite I
  let e : diagonalSource R (I → ℤ) ≅ H :=
    Diagonalizable.hopfSpecIso R (I → ℤ) ≪≫
      Diagonalizable.splitIso R (AddEquiv.refl (I → ℤ)) ≪≫ eH.symm
  have hj := (closed_baseChange_precomp_iso_iff _ e i).mpr hx
  obtain ⟨V, q, hq, bx, hbx, hjq⟩ := exists_open_diagonal (e.hom ≫ i) K hj
  exact ⟨V, q, hq, bx, hbx, (closed_baseChange_precomp_iso_iff q e i).mp hjq⟩

/-- The affine-base neighbourhood statement for an arbitrary supplied
field-valued point, retaining its exact factorization equality. -/
theorem exists_open_affine {H : GroupScheme (Spec R)}
    (hH : IsSplitTorus H) (i : H ⟶ G)
    (K : Type u) [Field K] (x : Spec (CommRingCat.of K) ⟶ Spec R)
    (hx : IsClosedImmersion ((baseChange x).map i).hom.hom.left) :
    ∃ (V : Scheme.{u}) (q : V ⟶ Spec R), IsOpenImmersion q ∧
      ∃ bx : Spec (CommRingCat.of K) ⟶ V, bx ≫ q = x ∧
        IsClosedImmersion ((baseChange q).map i).hom.hom.left := by
  obtain ⟨f, rfl⟩ := Spec.homEquiv.symm.surjective x
  let : Algebra R K := f.hom.toAlgebra
  exact exists_open_affine_algebraMap hH i K hx

end Langlands.GroupScheme.TorusClosedImmersionLocus
