import Langlands.AlgebraicGeometry.AffineProjectiveTensorFactorization
import Mathlib.AlgebraicGeometry.Group.Affine

/-! # Closed factorization loci for actual affine schemes -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  AlgebraicGeometry Opposite
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.AffineClosedFactorizationLocus

/-- The canonical affine coordinate comparison, with the algebra structure
provided by `algΓ`. -/
def coordinateIso (R : CommRingCat.{u}) (X : Over (Spec R)) [IsAffine X.left] :
    X ≅ (algSpec R).obj ((algΓ R).obj X) := by
  let := (algΓAlgSpecAdjunction R).isIso_unit_app_iff_mem_essImage.mpr
    ((essImage_algSpec (R := R) (G := X)).mpr inferInstance)
  exact asIso ((algΓAlgSpecAdjunction R).unit.app X)

theorem over_factorization_iff {S : Scheme.{u}} {T Z Y : Over S}
    (i : Z ⟶ Y) (t : T ⟶ Y) :
    (∃ z : T ⟶ Z, z ≫ i = t) ↔
      ∃ z : T.left ⟶ Z.left, z ≫ i.left = t.left := by
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z.left, congrArg (fun f ↦ f.left) hz⟩
  · rintro ⟨z, hz⟩
    refine ⟨Over.homMk z ?_, ?_⟩
    · rw [← i.w, ← Category.assoc, hz, t.w]
    · ext
      exact hz

section Category

variable {K : Type*} [Category K]

theorem factorization_comp_iso_iff {T D Y Y' : K}
    (d : D ⟶ Y) (t : T ⟶ Y) (e : Y ≅ Y') :
    (∃ q : T ⟶ D, q ≫ d ≫ e.hom = t ≫ e.hom) ↔
      ∃ q : T ⟶ D, q ≫ d = t := by
  simp only [← Category.assoc, cancel_mono]

theorem factorization_precomp_iso_iff {T T' D Y : K}
    (d : D ⟶ Y) (t : T ⟶ Y) (e : T' ≅ T) :
    (∃ q : T' ⟶ D, q ≫ d = e.hom ≫ t) ↔
      ∃ q : T ⟶ D, q ≫ d = t := by
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨e.inv ≫ q, ?_⟩
    simp only [Category.assoc, hq, e.inv_hom_id_assoc]
  · rintro ⟨q, hq⟩
    exact ⟨e.hom ≫ q, by simp only [Category.assoc, hq]⟩

end Category

/-- A closed subscheme of an affine tensor product is represented by its
coefficient quotient on every affine algebra. -/
theorem spec_closed_locus {R A C : Type u} [CommRing R] [CommRing A] [CommRing C]
    [Algebra R A] [Algebra R C] [Module.Projective R C]
    {D : Scheme.{u}}
    (d : D ⟶ pullback (Spec.algebraMap R A) (Spec.algebraMap R C))
    [IsClosedImmersion d] :
    ∃ (Z : Scheme.{u}) (i : Z ⟶ Spec (CommRingCat.of A)), IsClosedImmersion i ∧
      ∀ (B : Type u) [CommRing B] [Algebra R B] (f : A →ₐ[R] B),
        (∃ z : Spec (CommRingCat.of B) ⟶ Z,
          z ≫ i = Spec.map (CommRingCat.ofHom f.toRingHom)) ↔
        ∃ q : pullback (Spec.algebraMap R B) (Spec.algebraMap R C) ⟶ D,
          q ≫ d = affineProductMap (C := C) f := by
  obtain ⟨I, e, he⟩ := IsClosedImmersion.Spec_iff.mp
    (inferInstance : IsClosedImmersion (d ≫ (pullbackSpecIso R A C).hom))
  have hd : d = e.hom ≫ affineTensorQuotientι I := by
    rw [← cancel_mono (pullbackSpecIso R A C).hom]
    simpa [affineTensorQuotientι, Category.assoc] using he
  refine ⟨tensorCoefficientLocus (I : Set (A ⊗[R] C)),
    tensorCoefficientLocusι (I : Set (A ⊗[R] C)), inferInstance, ?_⟩
  intro B _ _ f
  rw [affine_coefficientLocus_iff_productFactorization]
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨q ≫ e.inv, ?_⟩
    simpa only [hd, Category.assoc, e.inv_hom_id_assoc] using hq
  · rintro ⟨q, hq⟩
    refine ⟨q ≫ e.hom, ?_⟩
    simpa only [hd, Category.assoc] using hq

@[simp]
theorem algSpec_map_op_left {R : CommRingCat.{u}} {A B : CommAlgCat.{u} R}
    (f : A ⟶ B) :
    ((algSpec R).map f.op).left =
      Spec.map (CommRingCat.ofHom f.hom.toRingHom) := rfl

set_option maxHeartbeats 800000 in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The affine algebra criterion, expressed intrinsically in the over
category, for every spectrum test. -/
theorem spec_over_closed_locus {R : CommRingCat.{u}} (A C : CommAlgCat.{u} R)
    [Module.Projective R C] {D : Over (Spec R)}
    (d : D ⟶ (algSpec R).obj (op A) ⊗ (algSpec R).obj (op C))
    [hd : IsClosedImmersion d.left] :
    ∃ (Z : Over (Spec R)) (i : Z ⟶ (algSpec R).obj (op A)),
      IsClosedImmersion i.left ∧
      ∀ (B : CommAlgCat.{u} R)
        (t : (algSpec R).obj (op B) ⟶ (algSpec R).obj (op A)),
        (∃ z : (algSpec R).obj (op B) ⟶ Z, z ≫ i = t) ↔
          ∃ q : (algSpec R).obj (op B) ⊗ (algSpec R).obj (op C) ⟶ D,
            q ≫ d = t ▷ (algSpec R).obj (op C) := by
  obtain ⟨Z, i, hi, h⟩ :=
    @spec_closed_locus R A C _ _ _ _ _ _ D.left d.left hd
  refine ⟨Over.mk (i ≫ ((algSpec R).obj (op A)).hom), Over.homMk i, hi, ?_⟩
  intro B t
  let f : A ⟶ B := ((algSpec R).preimage t).unop
  have ht : Spec.map (CommRingCat.ofHom f.hom.toRingHom) = t.left := by
    change ((algSpec R).map ((algSpec R).preimage t)).left = t.left
    rw [Functor.map_preimage]
  have hp : affineProductMap (C := C) f.hom =
      (t ▷ (algSpec R).obj (op C)).left := by
    apply pullback.hom_ext
    · rw [affineProductMap_fst, ht]
      exact (Over.whiskerRight_left_fst (R := (algSpec R).obj (op C)) t).symm
    · rw [affineProductMap_snd]
      exact (Over.whiskerRight_left_snd (R := (algSpec R).obj (op C)) t).symm
  rw [over_factorization_iff, over_factorization_iff]
  change (∃ z, z ≫ i = t.left) ↔
    ∃ q, q ≫ d.left = (t ▷ (algSpec R).obj (op C)).left
  simpa only [ht, hp] using! h B f.hom

/-- The same spectrum-target locus works for every affine test scheme. -/
theorem affine_test_spec_closed_locus {R : CommRingCat.{u}} (A C : CommAlgCat.{u} R)
    [Module.Projective R C] {D : Over (Spec R)}
    (d : D ⟶ (algSpec R).obj (op A) ⊗ (algSpec R).obj (op C))
    [IsClosedImmersion d.left] :
    ∃ (Z : Over (Spec R)) (i : Z ⟶ (algSpec R).obj (op A)),
      IsClosedImmersion i.left ∧
      ∀ (T : Over (Spec R)) [IsAffine T.left]
        (t : T ⟶ (algSpec R).obj (op A)),
        (∃ z : T ⟶ Z, z ≫ i = t) ↔
          ∃ q : T ⊗ (algSpec R).obj (op C) ⟶ D,
            q ≫ d = t ▷ (algSpec R).obj (op C) := by
  obtain ⟨Z, i, hi, h⟩ := spec_over_closed_locus A C d
  refine ⟨Z, i, hi, ?_⟩
  intro T _ t
  let e := coordinateIso R T
  calc
    (∃ z : T ⟶ Z, z ≫ i = t) ↔
        (∃ z : (algSpec R).obj ((algΓ R).obj T) ⟶ Z, z ≫ i = e.inv ≫ t) :=
      (factorization_precomp_iso_iff i t e.symm).symm
    _ ↔ (∃ q : (algSpec R).obj ((algΓ R).obj T) ⊗ (algSpec R).obj (op C) ⟶ D,
        q ≫ d = (e.inv ≫ t) ▷ (algSpec R).obj (op C)) :=
      h ((algΓ R).obj T).unop (e.inv ≫ t)
    _ ↔ _ := by
      rw [comp_whiskerRight]
      exact factorization_precomp_iso_iff d (t ▷ (algSpec R).obj (op C))
        (whiskerRightIso e.symm ((algSpec R).obj (op C)))

/-- An affine closed factorization locus with the coefficient factor first. -/
theorem affine_closed_locus_right {R : CommRingCat.{u}} (X Y : Over (Spec R))
    [IsAffine X.left] [IsAffine Y.left]
    [Module.Projective R ((algΓ R).obj X).unop] {D : Over (Spec R)}
    (d : D ⟶ Y ⊗ X) [hd : IsClosedImmersion d.left] :
    ∃ (Z : Over (Spec R)) (i : Z ⟶ Y), IsClosedImmersion i.left ∧
      ∀ (T : Over (Spec R)) [IsAffine T.left] (t : T ⟶ Y),
        (∃ z : T ⟶ Z, z ≫ i = t) ↔
          ∃ q : T ⊗ X ⟶ D, q ≫ d = t ▷ X := by
  let eX := coordinateIso R X
  let eY := coordinateIso R Y
  let e := eY ⊗ᵢ eX
  let d' := d ≫ e.hom
  let : IsIso e.hom.left := ((Over.forget (Spec R)).mapIso e).isIso_hom
  let : IsIso eY.inv.left := ((Over.forget (Spec R)).mapIso eY).isIso_inv
  have : IsClosedImmersion d'.left := by
    exact @IsClosedImmersion.comp _ _ _ d.left e.hom.left hd inferInstance
  obtain ⟨Z, i, hi, h⟩ := affine_test_spec_closed_locus
    ((algΓ R).obj Y).unop ((algΓ R).obj X).unop d'
  refine ⟨Z, i ≫ eY.inv, ?_, ?_⟩
  · dsimp
    let := hi
    infer_instance
  · intro T _ t
    have hm : (whiskerLeftIso T eX).hom ≫ (t ≫ eY.hom) ▷
          (algSpec R).obj ((algΓ R).obj X) = (t ▷ X) ≫ e.hom := by
      change (T ◁ eX.hom) ≫ ((t ≫ eY.hom) ▷ _) =
        (t ▷ X) ≫ (eY.hom ⊗ₘ eX.hom)
      rw [whiskerRight_comp_tensorHom, tensorHom_def']
    calc
      (∃ z : T ⟶ Z, z ≫ (i ≫ eY.inv) = t) ↔
          (∃ z : T ⟶ Z, z ≫ i = t ≫ eY.hom) := by
        simpa only [Category.assoc, eY.inv_hom_id, Category.comp_id] using
          (factorization_comp_iso_iff (i ≫ eY.inv) t eY).symm
      _ ↔ (∃ q : T ⊗ (algSpec R).obj ((algΓ R).obj X) ⟶ D,
          q ≫ d' = (t ≫ eY.hom) ▷ (algSpec R).obj ((algΓ R).obj X)) :=
        h T (t ≫ eY.hom)
      _ ↔ (∃ q : T ⊗ X ⟶ D, q ≫ d' =
          (whiskerLeftIso T eX).hom ≫
            (t ≫ eY.hom) ▷ (algSpec R).obj ((algΓ R).obj X)) :=
        (factorization_precomp_iso_iff d'
          ((t ≫ eY.hom) ▷ (algSpec R).obj ((algΓ R).obj X))
          (whiskerLeftIso T eX)).symm
      _ ↔ _ := by
        rw [hm]
        exact factorization_comp_iso_iff d (t ▷ X) e

/-- For affine `X` and `Y` and projective coordinate module of `X`, the maps
whose whole product with `X` factors through a closed subscheme form an actual
closed locus, tested on every affine scheme. -/
theorem affine_closed_locus {R : CommRingCat.{u}} (X Y : Over (Spec R))
    [IsAffine X.left] [IsAffine Y.left]
    [Module.Projective R ((algΓ R).obj X).unop] {D : Over (Spec R)}
    (d : D ⟶ X ⊗ Y) [hd : IsClosedImmersion d.left] :
    ∃ (Z : Over (Spec R)) (i : Z ⟶ Y), IsClosedImmersion i.left ∧
      ∀ (T : Over (Spec R)) [IsAffine T.left] (t : T ⟶ Y),
        (∃ z : T ⟶ Z, z ≫ i = t) ↔
          ∃ q : X ⊗ T ⟶ D, q ≫ d = X ◁ t := by
  let e := β_ X Y
  let d' := d ≫ e.hom
  let : IsIso e.hom.left := ((Over.forget (Spec R)).mapIso e).isIso_hom
  have : IsClosedImmersion d'.left :=
    @IsClosedImmersion.comp _ _ _ d.left e.hom.left hd inferInstance
  obtain ⟨Z, i, hi, h⟩ := affine_closed_locus_right X Y d'
  refine ⟨Z, i, hi, ?_⟩
  intro T _ t
  calc
    (∃ z : T ⟶ Z, z ≫ i = t) ↔
        (∃ q : T ⊗ X ⟶ D, q ≫ d' = t ▷ X) := h T t
    _ ↔ (∃ q : X ⊗ T ⟶ D, q ≫ d' = (β_ X T).hom ≫ t ▷ X) :=
      (factorization_precomp_iso_iff d' (t ▷ X) (β_ X T)).symm
    _ ↔ (∃ q : X ⊗ T ⟶ D, q ≫ d ≫ e.hom = (X ◁ t) ≫ e.hom) := by
      rw [← BraidedCategory.braiding_naturality_right]
    _ ↔ _ := factorization_comp_iso_iff d (X ◁ t) e

end Langlands.AlgebraicGeometry.AffineClosedFactorizationLocus
