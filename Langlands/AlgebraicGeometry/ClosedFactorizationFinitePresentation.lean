import Langlands.Algebra.ProjectiveTensorFiniteEquations
import Langlands.AlgebraicGeometry.ClosedFactorizationLocusProof
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected

/-! # Finite presentation of closed factorization loci -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  AlgebraicGeometry Opposite
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.ClosedFactorizationFinitePresentation

open AffineClosedFactorizationLocus
open Langlands.Algebra.ProjectiveTensorCoefficients

set_option backward.isDefEq.respectTransparency false in
private theorem spec_locus_lfp {R : CommRingCat.{u}} (A C : CommAlgCat.{u} R)
    [Module.Projective R C] {D Z : Over (Spec R)}
    (d : D ⟶ (algSpec R).obj (op A) ⊗ (algSpec R).obj (op C))
    [IsClosedImmersion d.left] [LocallyOfFinitePresentation d.left]
    (i : Z ⟶ (algSpec R).obj (op A)) [IsClosedImmersion i.left]
    (h : ∀ (B : CommAlgCat.{u} R) (t : (algSpec R).obj (op B) ⟶ (algSpec R).obj (op A)),
      (∃ z : (algSpec R).obj (op B) ⟶ Z, z ≫ i = t) ↔
        ∃ q : (algSpec R).obj (op B) ⊗ (algSpec R).obj (op C) ⟶ D,
          q ≫ d = t ▷ (algSpec R).obj (op C)) :
    LocallyOfFinitePresentation i.left := by
  let e := pullbackSpecIso R A C
  obtain ⟨I, eD, heD⟩ := IsClosedImmersion.Spec_iff.mp
    (inferInstance : IsClosedImmersion (d.left ≫ e.hom))
  let qI := CommRingCat.ofHom (Ideal.Quotient.mk I)
  have hqI : Spec.map qI = eD.inv ≫ (d.left ≫ e.hom) :=
    (eD.inv_hom_id_assoc (Spec.map qI)).symm.trans (congrArg (eD.inv ≫ ·) heD).symm
  have hquot : LocallyOfFinitePresentation (Spec.map qI) := by
    rw [hqI]
    infer_instance
  let : Algebra.FinitePresentation (A ⊗[R] C) ((A ⊗[R] C) ⧸ I) :=
    RingHom.finitePresentation_algebraMap.mp ((LocallyOfFinitePresentation.SpecMap_iff qI).mp hquot)
  have hI : I.FG := by
    simpa only [Ideal.Quotient.mkₐ_toRingHom, Ideal.mk_ker] using
      Algebra.FinitePresentation.ker_fG_of_surjective
        (Ideal.Quotient.mkₐ (A ⊗[R] C) I) Ideal.Quotient.mk_surjective
  have hJ : (coefficientIdeal (I : Set (A ⊗[R] C))).FG := by
    simpa using coefficientIdeal_image_ideal_fg (AlgHom.id R (A ⊗[R] C)) hI
  let j := tensorCoefficientLocusι (I : Set (A ⊗[R] C))
  let W := Over.mk (j ≫ ((algSpec R).obj (op A)).hom)
  let w : W ⟶ (algSpec R).obj (op A) := Over.homMk j
  have : IsClosedImmersion w.left := tensorCoefficientLocusι_isClosedImmersion _
  have : LocallyOfFinitePresentation w.left :=
    (LocallyOfFinitePresentation.SpecMap_iff _).mpr
      (RingHom.FinitePresentation.of_surjective _ Ideal.Quotient.mk_surjective
        (by
          change (RingHom.ker (Ideal.Quotient.mk (coefficientIdeal (I : Set (A ⊗[R] C))))).FG
          rwa [Ideal.mk_ker]))
  have hd : d.left = eD.hom ≫ affineTensorQuotientι I := by
    rw [← cancel_mono e.hom]
    simpa [e, affineTensorQuotientι, Category.assoc] using heD
  have hw (B : CommAlgCat.{u} R) (t : (algSpec R).obj (op B) ⟶ (algSpec R).obj (op A)) :
      (∃ z : (algSpec R).obj (op B) ⟶ W, z ≫ w = t) ↔
        ∃ q : (algSpec R).obj (op B) ⊗ (algSpec R).obj (op C) ⟶ D,
          q ≫ d = t ▷ (algSpec R).obj (op C) := by
    let f : A ⟶ B := ((algSpec R).preimage t).unop
    have ht : Spec.map (CommRingCat.ofHom f.hom.toRingHom) = t.left := by
      change ((algSpec R).map ((algSpec R).preimage t)).left = t.left
      rw [Functor.map_preimage]
    have hp : affineProductMap (C := C) f.hom = (t ▷ (algSpec R).obj (op C)).left := by
      apply pullback.hom_ext
      · rw [affineProductMap_fst, ht]
        exact (Over.whiskerRight_left_fst (R := (algSpec R).obj (op C)) t).symm
      · rw [affineProductMap_snd]
        exact (Over.whiskerRight_left_snd (R := (algSpec R).obj (op C)) t).symm
    rw [over_factorization_iff, over_factorization_iff]
    change (∃ z : Spec (CommRingCat.of B) ⟶ tensorCoefficientLocus (I : Set (A ⊗[R] C)),
        z ≫ tensorCoefficientLocusι (I : Set (A ⊗[R] C)) = t.left) ↔
      ∃ q : pullback (Spec.algebraMap R B) (Spec.algebraMap R C) ⟶ D.left,
        q ≫ d.left = (t ▷ (algSpec R).obj (op C)).left
    rw [← ht, ← hp]
    refine (affine_coefficientLocus_iff_productFactorization I f.hom).trans ?_
    constructor
    · rintro ⟨q, hq⟩
      exact ⟨q ≫ eD.inv, by simpa only [hd, Category.assoc, eD.inv_hom_id_assoc] using hq⟩
    · rintro ⟨q, hq⟩
      exact ⟨q ≫ eD.hom, by simpa only [hd, Category.assoc] using hq⟩
  have : IsAffine ((algSpec R).obj (op A)).left := inferInstanceAs (IsAffine (Spec _))
  have : IsAffine Z.left := isAffine_of_isAffineHom i.left
  have : IsAffine W.left := inferInstanceAs (IsAffine (Spec _))
  let eZ := coordinateIso R Z
  let eW := coordinateIso R W
  obtain ⟨a, ha⟩ := (hw _ (eZ.inv ≫ i)).mpr ((h _ _).mp ⟨eZ.inv, rfl⟩)
  obtain ⟨b, hb⟩ := (h _ (eW.inv ≫ w)).mpr ((hw _ _).mp ⟨eW.inv, rfl⟩)
  let : Mono i := Over.mono_of_mono_left _
  let : Mono w := Over.mono_of_mono_left w
  let eWZ : Z ≅ W :=
    { hom := eZ.hom ≫ a
      inv := eW.hom ≫ b
      hom_inv_id := by
        rw [← cancel_mono i]
        simp only [Category.assoc, hb, ha, Iso.hom_inv_id_assoc, Category.id_comp]
      inv_hom_id := by
        rw [← cancel_mono w]
        simp only [Category.assoc, ha, hb, Iso.hom_inv_id_assoc, Category.id_comp] }
  have heWZ : eWZ.hom ≫ w = i := by
    simp only [eWZ, Category.assoc, ha, Iso.hom_inv_id_assoc]
  have : IsIso eWZ.hom.left := ((Over.forget _).mapIso eWZ).isIso_hom
  rw [← heWZ, Over.comp_left]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private theorem affine_locus_lfp {R : CommRingCat.{u}} (X Y : Over (Spec R))
    [IsAffine X.left] [IsAffine Y.left] [Module.Projective R ((algΓ R).obj X).unop]
    {D Z : Over (Spec R)} (d : D ⟶ X ⊗ Y)
    [IsClosedImmersion d.left] [LocallyOfFinitePresentation d.left]
    (i : Z ⟶ Y) [IsClosedImmersion i.left]
    (h : ∀ (T : Over (Spec R)) (t : T ⟶ Y),
      (∃ z : T ⟶ Z, z ≫ i = t) ↔ ∃ q : X ⊗ T ⟶ D, q ≫ d = X ◁ t) :
    LocallyOfFinitePresentation i.left := by
  let eX := coordinateIso R X
  let eY := coordinateIso R Y
  let X' := (algSpec R).obj ((algΓ R).obj X)
  let e : X ⊗ Y ≅ (algSpec R).obj ((algΓ R).obj Y) ⊗ X' :=
    β_ X Y ≪≫ (eY ⊗ᵢ eX)
  let d' := d ≫ e.hom
  let i' := i ≫ eY.hom
  let : IsIso e.hom.left := ((Over.forget _).mapIso e).isIso_hom
  let : IsIso eY.hom.left := ((Over.forget _).mapIso eY).isIso_hom
  have : IsClosedImmersion d'.left := inferInstanceAs
    (IsClosedImmersion (d.left ≫ e.hom.left))
  have : LocallyOfFinitePresentation d'.left := inferInstanceAs
    (LocallyOfFinitePresentation (d.left ≫ e.hom.left))
  have : IsClosedImmersion i'.left := inferInstanceAs
    (IsClosedImmersion (i.left ≫ eY.hom.left))
  have hi' := spec_locus_lfp ((algΓ R).obj Y).unop ((algΓ R).obj X).unop d' i' (by
    intro B t
    let T := (algSpec R).obj (op B)
    let s := t ≫ eY.inv
    let eT : X ⊗ T ≅ T ⊗ X' := β_ X T ≪≫ whiskerLeftIso T eX
    have ht : (s ▷ X) ≫ (eY.hom ⊗ₘ eX.hom) = (T ◁ eX.hom) ≫ (t ▷ X') := by
      rw [whiskerRight_comp_tensorHom, show s ≫ eY.hom = t by simp [s], tensorHom_def']
    have hp : eT.hom ≫ (t ▷ X') = (X ◁ s) ≫ e.hom := by
      change ((β_ X T).hom ≫ (T ◁ eX.hom)) ≫ (t ▷ X') =
        (X ◁ s) ≫ (β_ X Y).hom ≫ (eY.hom ⊗ₘ eX.hom)
      rw [Category.assoc, ← ht, ← Category.assoc (β_ X T).hom,
        ← BraidedCategory.braiding_naturality_right, Category.assoc]
    calc
      (∃ z : T ⟶ Z, z ≫ i' = t) ↔ (∃ z : T ⟶ Z, z ≫ i = s) := by
        simpa [i', s, Category.assoc] using factorization_comp_iso_iff i s eY
      _ ↔ (∃ q : X ⊗ T ⟶ D, q ≫ d = X ◁ s) := h T s
      _ ↔ (∃ q : X ⊗ T ⟶ D, q ≫ d' = eT.hom ≫ t ▷ X') := by
        rw [hp]
        exact (factorization_comp_iso_iff d (X ◁ s) e).symm
      _ ↔ _ := factorization_precomp_iso_iff d' (t ▷ X') eT)
  exact (MorphismProperty.cancel_right_of_respectsIso @LocallyOfFinitePresentation
    i.left eY.hom.left).mp hi'

private theorem factors_pullback_snd_iff {S : Scheme.{u}} {D Y V T : Over S}
    (d : D ⟶ Y) (v : V ⟶ Y) (t : T ⟶ V) [HasPullback d v] :
    (∃ q : T ⟶ pullback d v, q ≫ pullback.snd d v = t) ↔
      (∃ q : T ⟶ D, q ≫ d = t ≫ v) := by
  constructor
  · rintro ⟨q, hq⟩
    exact ⟨q ≫ pullback.fst d v, by rw [Category.assoc, pullback.condition,
      ← Category.assoc, hq]⟩
  · rintro ⟨q, hq⟩
    exact ⟨pullback.lift q t hq, pullback.lift_snd _ _ _⟩

/-- A closed locus representing whole-product factorization through a
finitely presented closed immersion is locally finitely presented. -/
theorem locallyOfFinitePresentation_of_represents {R : CommRingCat.{u}}
    (X : Over (Spec R)) [IsAffine X.left] [Module.Projective R ((algΓ R).obj X).unop]
    {Y D Z : Over (Spec R)} (d : D ⟶ X ⊗ Y)
    [IsClosedImmersion d.left] [LocallyOfFinitePresentation d.left]
    (i : Z ⟶ Y) [IsClosedImmersion i.left]
    (h : ∀ (T : Over (Spec R)) (t : T ⟶ Y),
      (∃ z : T ⟶ Z, z ≫ i = t) ↔ ∃ q : X ⊗ T ⟶ D, q ≫ d = X ◁ t) :
    LocallyOfFinitePresentation i.left := by
  let 𝒰 := Y.left.affineCover
  have : IsZariskiLocalAtTarget @LocallyOfFinitePresentation.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtTarget _
  apply IsZariskiLocalAtTarget.of_openCover (P := @LocallyOfFinitePresentation) 𝒰
  intro k
  let V : Over (Spec R) := Over.mk (𝒰.f k ≫ Y.hom)
  let v : V ⟶ Y := Over.homMk (𝒰.f k)
  let d' := pullback.snd d (X ◁ v)
  let i' := pullback.snd i v
  have : IsAffine V.left := inferInstanceAs (IsAffine (Spec _))
  have hd := (IsPullback.of_hasPullback d (X ◁ v)).map (Over.forget _)
  have hi := (IsPullback.of_hasPullback i v).map (Over.forget _)
  have : IsClosedImmersion d'.left := MorphismProperty.of_isPullback hd
    (inferInstance : IsClosedImmersion d.left)
  have : LocallyOfFinitePresentation d'.left := MorphismProperty.of_isPullback hd
    (inferInstance : LocallyOfFinitePresentation d.left)
  have : IsClosedImmersion i'.left := MorphismProperty.of_isPullback hi
    (inferInstance : IsClosedImmersion i.left)
  have : LocallyOfFinitePresentation i'.left := affine_locus_lfp X V d' i' (by
    intro T t
    rw [factors_pullback_snd_iff, factors_pullback_snd_iff, ← whiskerLeft_comp]
    exact h T (t ≫ v))
  change LocallyOfFinitePresentation
    (pullback.snd ((Over.forget (Spec R)).map i) ((Over.forget (Spec R)).map v))
  rw [← hi.isoPullback_inv_snd]
  change LocallyOfFinitePresentation (hi.isoPullback.inv ≫ i'.left)
  infer_instance

/-- A locally finitely presented closed representative of whole-product factorization. -/
structure Model {R : CommRingCat.{u}} {X Y D : Over (Spec R)} (d : D ⟶ X ⊗ Y) where
  source : Over (Spec R)
  ι : source ⟶ Y
  isClosedImmersion : IsClosedImmersion ι.left
  locallyOfFinitePresentation : LocallyOfFinitePresentation ι.left
  represents (T : Over (Spec R)) (t : T ⟶ Y) :
    (∃ z : T ⟶ source, z ≫ ι = t) ↔ ∃ q : X ⊗ T ⟶ D, q ≫ d = X ◁ t

/-- Construct the finite-presentation refinement of the closed factorization locus
when the coordinate module is projective over the given base ring. -/
def model {R : CommRingCat.{u}} (X : Over (Spec R))
    [IsAffineHom X.hom] [Flat X.hom] [Module.Projective R ((algΓ R).obj X).unop]
    {Y D : Over (Spec R)} (d : D ⟶ X ⊗ Y)
    [IsClosedImmersion d.left] [LocallyOfFinitePresentation d.left] : Model d :=
  Classical.choice (by
    have hcoords : HasFpqcProjectiveCoordinateModule X :=
      ⟨CommAlgCat.of R R, inferInstance, inferInstance⟩
    obtain ⟨Z, i, hi, h⟩ :=
      ClosedFactorizationLocusProof.closedFactorizationLocus
        R X inferInstance inferInstance hcoords Y D d inferInstance
    let : IsAffine X.left := isAffine_of_isAffineHom X.hom
    let : IsClosedImmersion i.left := hi
    exact ⟨⟨Z, i, hi, locallyOfFinitePresentation_of_represents X d i h, h⟩⟩)

end Langlands.AlgebraicGeometry.ClosedFactorizationFinitePresentation
