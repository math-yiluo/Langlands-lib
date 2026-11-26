import Langlands.GroupScheme.Dilatation.Algebra
import Langlands.AlgebraicGeometry.AffineClosedFactorizationLocus
import Langlands.AlgebraicGeometry.AffineQuotientPullback
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.Localization.FractionRing

/-! # Affine dilatation along a centre over a principal quotient -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Langlands.GroupScheme.Dilatation

open Langlands.AlgebraicGeometry.AffineClosedFactorizationLocus (coordinateIso)

universe u

variable {R : Type u} [CommRing R]

/-- The spectrum of an algebra as an object over the coefficient spectrum. -/
abbrev algebraSpec (A : Type u) [CommRing A] [Algebra R A] :=
  (algSpec (CommRingCat.of R)).obj (op (CommAlgCat.of R A))

/-- The relative spectrum map of an algebra homomorphism. -/
abbrev algebraSpecMap {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (f : A →ₐ[R] B) : algebraSpec (R := R) B ⟶ algebraSpec (R := R) A :=
  (algSpec (CommRingCat.of R)).map (CommAlgCat.ofHom f).op

@[simp] theorem algebraSpecMap_comp {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C] (f : A →ₐ[R] B) (g : B →ₐ[R] C) :
    algebraSpecMap g ≫ algebraSpecMap f = algebraSpecMap (g.comp f) := by
  rw [← Functor.map_comp]
  rfl

private theorem algebraSpecMap_injective {A B : Type u} [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] :
    Function.Injective (algebraSpecMap : (A →ₐ[R] B) → _) := fun _ _ h =>
  congrArg (fun f : op (CommAlgCat.of R B) ⟶ op (CommAlgCat.of R A) => f.unop.hom)
    (algSpec.fullyFaithful.map_injective h)

/-- The relative coordinate ring given by `algΓ`. -/
abbrev affineAlgebra (X : Over (Spec (CommRingCat.of R))) : CommAlgCat (CommRingCat.of R) :=
  ((algΓ (CommRingCat.of R)).obj X).unop

instance affineAlgebra_algebra (X : Over (Spec (CommRingCat.of R))) :
    Algebra R (affineAlgebra X) := (affineAlgebra X).algebra

/-- Pullback of relative coordinates. -/
abbrev affineAlgebraMap {X Y : Over (Spec (CommRingCat.of R))} (f : X ⟶ Y) :
    affineAlgebra Y →ₐ[R] affineAlgebra X :=
  ((algΓ (CommRingCat.of R)).map f).unop.hom

@[reassoc] theorem coordIso_naturality {X Y : Over (Spec (CommRingCat.of R))}
    [IsAffine X.left] [IsAffine Y.left] (f : X ⟶ Y) :
    (coordinateIso _ X).hom ≫ algebraSpecMap (A := affineAlgebra Y) (B := affineAlgebra X)
      (affineAlgebraMap f) =
      f ≫ (coordinateIso _ Y).hom := by
  exact ((algΓAlgSpecAdjunction (CommRingCat.of R)).unit.naturality f).symm

private theorem coords_surjective {X Y : Over (Spec (CommRingCat.of R))}
    [IsAffine Y.left] (f : X ⟶ Y) [IsClosedImmersion f.left] :
    Function.Surjective (affineAlgebraMap f) :=
  (IsClosedImmersion.isAffine_surjective_of_isAffine f.left).2

/-- On an affine scheme flatness over the base is flatness of its coordinate algebra. -/
theorem affineAlgebra_flat_iff (X : Over (Spec (CommRingCat.of R))) [IsAffine X.left] :
    Module.Flat R (affineAlgebra X) ↔ Flat X.hom := by
  have h := (coordinateIso _ X).hom.w
  have : IsIso (coordinateIso _ X).hom.left :=
    (Over.forget (Spec (CommRingCat.of R))).map_isIso (coordinateIso _ X).hom
  rw [← h, MorphismProperty.cancel_left_of_respectsIso @Flat]
  change _ ↔ Flat (Spec.map (CommRingCat.ofHom (algebraMap R (affineAlgebra X))))
  exact (Flat.SpecMap_iff.trans RingHom.flat_algebraMap_iff).symm

/-- Finite type on an affine scheme is finite type of its coordinate algebra. -/
theorem affineAlgebra_finiteType_iff (X : Over (Spec (CommRingCat.of R))) [IsAffine X.left] :
    Algebra.FiniteType R (affineAlgebra X) ↔ LocallyOfFiniteType X.hom := by
  have h := (coordinateIso _ X).hom.w
  have : IsIso (coordinateIso _ X).hom.left :=
    (Over.forget (Spec (CommRingCat.of R))).map_isIso (coordinateIso _ X).hom
  rw [← h, MorphismProperty.cancel_left_of_respectsIso @LocallyOfFiniteType]
  change _ ↔ LocallyOfFiniteType
    (Spec.map (CommRingCat.ofHom (algebraMap R (affineAlgebra X))))
  exact ((HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).trans
    RingHom.finiteType_algebraMap).symm

/-- The spectrum map of the coefficient quotient. -/
abbrev quotientBase (J : Ideal R) : Spec (CommRingCat.of (R ⧸ J)) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J))

instance (J : Ideal R) : IsClosedImmersion (quotientBase J) :=
  IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective

/-- Projection from the actual pullback, viewed over the original base. -/
abbrev baseProjection {U S : Scheme.{u}} (b : U ⟶ S) (T : Over S) :
    (Over.map b).obj ((Over.pullback b).obj T) ⟶ T :=
  (Over.mapPullbackAdj b).counit.app T

/-- The centre inclusion composed with the projection to the original scheme. -/
abbrev centreInclusion {U S : Scheme.{u}} {b : U ⟶ S} {X : Over S}
    {Y : Over U} (j : Y ⟶ (Over.pullback b).obj X) : (Over.map b).obj Y ⟶ X :=
  (Over.map b).map j ≫ baseProjection b X

instance {U S : Scheme.{u}} {b : U ⟶ S} {X : Over S} {Y : Over U}
    (j : Y ⟶ (Over.pullback b).obj X) [IsClosedImmersion b] [IsClosedImmersion j.left] :
    IsClosedImmersion (centreInclusion j).left := by
  change IsClosedImmersion (j.left ≫ pullback.fst X.hom b)
  infer_instance

/-- The ideal of the closed centre in the original coordinate ring. -/
def centreIdeal {U : Scheme.{u}} {b : U ⟶ Spec (CommRingCat.of R)}
    {X : Over (Spec (CommRingCat.of R))} {Y : Over U} (j : Y ⟶ (Over.pullback b).obj X) :
    Ideal (affineAlgebra X) := RingHom.ker (affineAlgebraMap (centreInclusion j)).toRingHom

/-- The actual affine scheme of the blow-up algebra over the coefficient spectrum. -/
abbrev affineDilatation {U : Scheme.{u}} {b : U ⟶ Spec (CommRingCat.of R)}
    (r : R) {X : Over (Spec (CommRingCat.of R))} {Y : Over U}
    (j : Y ⟶ (Over.pullback b).obj X) : Over (Spec (CommRingCat.of R)) :=
  algebraSpec (blowupAlgebra r (centreIdeal j))

instance {U : Scheme.{u}} {b : U ⟶ Spec (CommRingCat.of R)}
    (r : R) {X : Over (Spec (CommRingCat.of R))} {Y : Over U}
    (j : Y ⟶ (Over.pullback b).obj X) : IsAffine (affineDilatation r j).left := by
  change IsAffine (Spec (CommRingCat.of (blowupAlgebra r (centreIdeal j))))
  infer_instance

/-- The dilatation map to the actual original affine scheme. -/
def affineDilatationHom {U : Scheme.{u}} {b : U ⟶ Spec (CommRingCat.of R)}
    (r : R) {X : Over (Spec (CommRingCat.of R))} [IsAffine X.left] {Y : Over U}
    (j : Y ⟶ (Over.pullback b).obj X) : affineDilatation r j ⟶ X :=
  algebraSpecMap (blowupMap r (centreIdeal j)) ≫ (coordinateIso _ X).inv

instance {U : Scheme.{u}} {b : U ⟶ Spec (CommRingCat.of R)} [IsDedekindDomain R]
    (r : R) {X : Over (Spec (CommRingCat.of R))} [IsAffine X.left] [Flat X.hom]
    {Y : Over U} (j : Y ⟶ (Over.pullback b).obj X) : Flat (affineDilatation r j).hom := by
  let : Module.Flat R (affineAlgebra X) := (affineAlgebra_flat_iff X).mpr inferInstance
  change Flat (Spec.map (CommRingCat.ofHom (algebraMap R (blowupAlgebra r (centreIdeal j)))))
  exact Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)

instance {U : Scheme.{u}} {b : U ⟶ Spec (CommRingCat.of R)} [IsNoetherianRing R]
    (r : R) {X : Over (Spec (CommRingCat.of R))} [IsAffine X.left] [LocallyOfFiniteType X.hom]
    {Y : Over U} (j : Y ⟶ (Over.pullback b).obj X) :
    LocallyOfFiniteType (affineDilatation r j).hom := by
  let : Algebra.FiniteType R (affineAlgebra X) := (affineAlgebra_finiteType_iff X).mpr inferInstance
  change LocallyOfFiniteType
    (Spec.map (CommRingCat.ofHom (algebraMap R (blowupAlgebra r (centreIdeal j)))))
  exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
    (RingHom.finiteType_algebraMap.mpr inferInstance)

section UniversalProperty

variable {T X Y : Over (Spec (CommRingCat.of R))} [IsAffine T.left] [IsAffine X.left]

private def ringPointEquiv {A : Type u} [CommRing A] [Algebra R A] :
    (A →ₐ[R] affineAlgebra T) ≃ (T ⟶ algebraSpec (R := R) A) :=
  (show (A →ₐ[R] affineAlgebra T) ≃ ((algΓ (CommRingCat.of R)).obj T ⟶
    op (CommAlgCat.of R A)) from
    { toFun := fun f => (CommAlgCat.ofHom f).op
      invFun := fun f => f.unop.hom
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }).trans ((algΓAlgSpecAdjunction _).homEquiv _ _)

private theorem ringPointEquiv_apply {A : Type u} [CommRing A] [Algebra R A]
    (f : A →ₐ[R] affineAlgebra T) :
    ringPointEquiv (T := T) f =
      (coordinateIso _ T).hom ≫ algebraSpecMap (A := A) (B := affineAlgebra T) f :=
  Adjunction.homEquiv_unit (algΓAlgSpecAdjunction (CommRingCat.of R)) T
    (op (CommAlgCat.of R A)) (CommAlgCat.ofHom f).op

private theorem ringPointEquiv_comp {A B : Type u} [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) (g : B →ₐ[R] affineAlgebra T) :
    ringPointEquiv (T := T) (g.comp f) = ringPointEquiv g ≫ algebraSpecMap f := by
  simp only [ringPointEquiv_apply, Category.assoc, algebraSpecMap_comp]

private theorem coord_eq_ringPoint (f : T ⟶ X) :
    ringPointEquiv (affineAlgebraMap f) = f ≫ (coordinateIso _ X).hom :=
  (ringPointEquiv_apply _).trans (coordIso_naturality f)

variable [IsDomain R] [Flat T.hom]
variable {U : Scheme.{u}} {b : U ⟶ Spec (CommRingCat.of R)} {Z : Over U}
  (j : Z ⟶ (Over.pullback b).obj X) {r : R} (hr : r ≠ 0)

include hr in
/-- Cancellation of the dilatation map for a flat affine source. -/
theorem affineDilatationHom_injective :
    Function.Injective (fun f : T ⟶ affineDilatation r j => f ≫ affineDilatationHom r j) := by
  let : Module.Flat R (affineAlgebra T) := (affineAlgebra_flat_iff T).mpr inferInstance
  intro f g h
  change f ≫ affineDilatationHom r j = g ≫ affineDilatationHom r j at h
  rw [affineDilatationHom, ← Category.assoc, ← Category.assoc, cancel_mono] at h
  obtain ⟨f, rfl⟩ := (ringPointEquiv (T := T)).surjective f
  obtain ⟨g, rfl⟩ := (ringPointEquiv (T := T)).surjective g
  rw [← ringPointEquiv_comp, ← ringPointEquiv_comp] at h
  exact congrArg _ (blowupMap_ext hr _ (ringPointEquiv.injective h))

include hr in
/-- The affine universal property, stated on the coordinates of the test scheme. -/
theorem affineDilatation_factors_iff (f : T ⟶ X) :
    (∃ g : T ⟶ affineDilatation r j, g ≫ affineDilatationHom r j = f) ↔
      ∀ a ∈ centreIdeal j, affineAlgebraMap f a ∈ Ideal.span {algebraMap R (affineAlgebra T) r} := by
  let : Module.Flat R (affineAlgebra T) := (affineAlgebra_flat_iff T).mpr inferInstance
  constructor
  · rintro ⟨g, hg⟩
    obtain ⟨g, rfl⟩ := (ringPointEquiv (T := T)).surjective g
    have he : g.comp (blowupMap r (centreIdeal j)) = affineAlgebraMap f := by
      apply ringPointEquiv.injective
      rw [ringPointEquiv_comp, coord_eq_ringPoint, ← hg]
      simp [affineDilatationHom]
    rw [← he]
    exact maps_centre_to_span _ g
  · intro hf
    refine ⟨ringPointEquiv (liftBlowup hr _ _ hf), ?_⟩
    rw [affineDilatationHom, ← Category.assoc, ← ringPointEquiv_comp,
      liftBlowup_comp, coord_eq_ringPoint]
    simp

end UniversalProperty

section Quotient

variable {J : Ideal R} {T X : Over (Spec (CommRingCat.of R))} [IsAffine T.left]
  [IsAffine X.left] {Y : Over (Spec (CommRingCat.of (R ⧸ J)))}
  (j : Y ⟶ (Over.pullback (quotientBase J)).obj X) [IsClosedImmersion j.left]

private theorem quotientTestSquare (J : Ideal R) (T : Over (Spec (CommRingCat.of R)))
    [IsAffine T.left] :
    IsPullback
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
        (J.map (algebraMap R (affineAlgebra T))))) ≫ (coordinateIso _ T).inv.left)
      (Spec.map (CommRingCat.ofHom (Ideal.quotientMap _ (algebraMap R (affineAlgebra T))
        Ideal.le_comap_map)))
      T.hom (quotientBase J) := by
  let φ := algebraMap R (affineAlgebra T)
  let e := (Over.forget _).mapIso (coordinateIso (CommRingCat.of R) T).symm
  have h := (isPullback_SpecMap_of_isPushout _ _ _ _
    (Langlands.AlgebraicGeometry.isPushout_quotient_map φ J)).flip
  refine h.of_iso (Iso.refl _) e (Iso.refl _) (Iso.refl _)
    (by rw [Iso.refl_hom, Category.id_comp]; rfl)
    (by simp only [Iso.refl_hom, Category.id_comp, Category.comp_id]; rfl) ?_ (by simp)
  rw [Iso.refl_hom, Category.comp_id]
  exact (coordinateIso (CommRingCat.of R) T).inv.w.symm

/-- The reduction of an affine test is the quotient of its coordinate ring by the extended ideal. -/
def quotientTestIso (J : Ideal R) (T : Over (Spec (CommRingCat.of R))) [IsAffine T.left] :
    algebraSpec (R := R) (affineAlgebra T ⧸ J.map (algebraMap R (affineAlgebra T))) ≅
      (Over.map (quotientBase J)).obj ((Over.pullback (quotientBase J)).obj T) := by
  refine Over.isoMk (quotientTestSquare J T).isoPullback ?_
  change _ ≫ (pullback.snd T.hom (quotientBase J) ≫ quotientBase J) = _
  rw [← pullback.condition, ← Category.assoc, (quotientTestSquare J T).isoPullback_hom_fst,
    Category.assoc]
  rw [(coordinateIso _ T).inv.w]
  rw [algSpec_obj_hom, ← Spec.map_comp]
  rfl

@[reassoc] theorem quotientTestIso_hom_projection (J : Ideal R)
    (T : Over (Spec (CommRingCat.of R))) [IsAffine T.left] :
    (quotientTestIso J T).hom ≫ baseProjection (quotientBase J) T =
      algebraSpecMap (Ideal.Quotient.mkₐ R (J.map (algebraMap R (affineAlgebra T)))) ≫
        (coordinateIso _ T).inv := by
  apply Over.OverMorphism.ext
  change _ ≫ pullback.fst T.hom (quotientBase J) = _
  exact (quotientTestSquare J T).isoPullback_hom_fst

private theorem factors_algSpecMap_iff {A B C : Type u} [CommRing A] [CommRing B]
    [CommRing C] [Algebra R A] [Algebra R B] [Algebra R C]
    (φ : A →ₐ[R] B) (hφ : Function.Surjective φ) (ψ : A →ₐ[R] C) :
    (∃ h : algebraSpec (R := R) C ⟶ algebraSpec (R := R) B,
      h ≫ algebraSpecMap φ = algebraSpecMap ψ) ↔
      RingHom.ker φ.toRingHom ≤ RingHom.ker ψ.toRingHom := by
  constructor
  · rintro ⟨f, hf⟩
    let q := algSpec.fullyFaithful.preimage f
    let g : B →ₐ[R] C := q.unop.hom
    have he : g.comp φ = ψ := algebraSpecMap_injective
      ((algebraSpecMap_comp φ g).symm.trans (by
        change (algSpec _).map q ≫ _ = _
        simpa [q] using hf))
    intro x hx
    change ψ x = 0
    rw [← he, AlgHom.comp_apply, show φ x = 0 from hx, map_zero]
  · intro h
    exact ⟨algebraSpecMap (φ.liftOfSurjective hφ ψ h),
      (algebraSpecMap_comp _ _).trans (congrArg _ (φ.liftOfSurjective_comp hφ ψ h))⟩

/-- Pulling a map back to the quotient base factors through the centre exactly when its
coordinate map sends the centre ideal into the extended base ideal. -/
theorem reduces_into_iff (f : T ⟶ X) :
    (∃ g : (Over.pullback (quotientBase J)).obj T ⟶ Y,
        g ≫ j = (Over.pullback (quotientBase J)).map f) ↔
      ∀ a ∈ centreIdeal j, affineAlgebraMap f a ∈ J.map (algebraMap R (affineAlgebra T)) := by
  let U := (Over.map (quotientBase J)).obj Y
  let i : U ⟶ X := centreInclusion j
  let : IsClosedImmersion i.left := inferInstance
  let : IsAffine U.left := isAffine_of_isAffineHom i.left
  let e := quotientTestIso J T
  let q := Ideal.Quotient.mkₐ R (J.map (algebraMap R (affineAlgebra T)))
  let F := Over.pullback (quotientBase J)
  let L := Over.map (quotientBase J)
  have hx : e.hom ≫ baseProjection (quotientBase J) T ≫ f ≫ (coordinateIso _ X).hom =
      algebraSpecMap (q.comp (affineAlgebraMap f)) := by
    rw [quotientTestIso_hom_projection_assoc, ← coordIso_naturality f,
      Iso.inv_hom_id_assoc]
    exact algebraSpecMap_comp _ _
  calc
    (∃ g : F.obj T ⟶ Y, g ≫ j = F.map f) ↔
        (∃ g : L.obj (F.obj T) ⟶ U, g ≫ i = baseProjection (quotientBase J) T ≫ f) := by
      constructor
      · rintro ⟨g, hg⟩
        refine ⟨L.map g, ?_⟩
        rw [show i = L.map j ≫ baseProjection (quotientBase J) X from rfl,
          ← Category.assoc, ← Functor.map_comp, hg]
        exact (Over.mapPullbackAdj (quotientBase J)).counit.naturality f
      · rintro ⟨g, hg⟩
        have hw : g.left ≫ Y.hom = (F.obj T).hom := by
          apply (cancel_mono (quotientBase J)).mp
          have h := g.w
          change g.left ≫ (Y.hom ≫ quotientBase J) = (F.obj T).hom ≫ quotientBase J at h
          exact (Category.assoc _ _ _).trans h
        let g' : F.obj T ⟶ Y := Over.homMk g.left hw
        refine ⟨g', Over.OverMorphism.ext (pullback.hom_ext ?_ ?_)⟩
        · simpa [i, F, g', baseProjection, Category.assoc] using congrArg (fun k => k.left) hg
        · exact (g' ≫ j).w.trans (F.map f).w.symm
    _ ↔ (∃ g : algebraSpec (R := R) _ ⟶ algebraSpec (R := R) (affineAlgebra U),
        g ≫ algebraSpecMap (affineAlgebraMap i) =
          algebraSpecMap (q.comp (affineAlgebraMap f))) := by
      constructor
      · rintro ⟨g, hg⟩
        refine ⟨e.hom ≫ g ≫ (coordinateIso _ U).hom, ?_⟩
        rw [Category.assoc, Category.assoc, coordIso_naturality, reassoc_of% hg]
        exact hx
      · rintro ⟨g, hg⟩
        refine ⟨e.inv ≫ g ≫ (coordinateIso _ U).inv, ?_⟩
        rw [← cancel_mono (coordinateIso _ X).hom]
        have hi' : (coordinateIso _ U).inv ≫ i ≫ (coordinateIso _ X).hom =
            algebraSpecMap (affineAlgebraMap i) := by
          rw [← cancel_epi (coordinateIso _ U).hom, coordIso_naturality]
          simp
        simp only [Category.assoc, hi', hg, ← hx, Iso.inv_hom_id_assoc]
    _ ↔ _ := by
      rw [factors_algSpecMap_iff _ (coords_surjective i)]
      exact forall_congr' fun a => imp_congr_right fun _ => Ideal.Quotient.eq_zero_iff_mem

variable [IsDomain R] [Flat T.hom] {r : R} (hr : r ≠ 0) (hJ : J = Ideal.span {r})

include hr hJ in
/-- On a flat affine test the dilatation map represents reduction into the actual centre. -/
theorem affineDilatation_lift_iff (f : T ⟶ X) :
    (∃! g : T ⟶ affineDilatation r j, g ≫ affineDilatationHom r j = f) ↔
      ∃ y : (Over.pullback (quotientBase J)).obj T ⟶ Y,
        y ≫ j = (Over.pullback (quotientBase J)).map f := by
  have hmap : J.map (algebraMap R (affineAlgebra T)) =
      Ideal.span {algebraMap R (affineAlgebra T) r} := by
    rw [hJ, Ideal.map_span, Set.image_singleton]
  rw [reduces_into_iff, hmap, ← affineDilatation_factors_iff j hr]
  exact ⟨fun ⟨g, hg, _⟩ => ⟨g, hg⟩,
    fun ⟨g, hg⟩ => ⟨g, hg, fun _ h => affineDilatationHom_injective j hr (h.trans hg.symm)⟩⟩

end Quotient

section Generic

variable {K : Type u} [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  {U : Scheme.{u}} {b : U ⟶ Spec (CommRingCat.of R)} {X : Over (Spec (CommRingCat.of R))}
  [IsAffine X.left] [Flat X.hom] {Y : Over U}
  (j : Y ⟶ (Over.pullback b).obj X) {r : R} (hr : r ≠ 0)

omit [IsDedekindDomain R] in
include hr in
private theorem isUnit_coordinates_of_generic (T : Over (Spec (CommRingCat.of K))) :
    IsUnit (algebraMap R (affineAlgebra ((Over.map (Spec.algebraMap R K)).obj T)) r) := by
  let t : (Over.map (Spec.algebraMap R K)).obj T ⟶ algebraSpec (R := R) K :=
    Over.homMk T.hom rfl
  let k : K →ₐ[R] affineAlgebra (algebraSpec (R := R) K) :=
    ((algΓAlgSpecAdjunction (CommRingCat.of R)).counit.app (op (CommAlgCat.of R K))).unop.hom
  let f := (affineAlgebraMap t).comp k
  rw [← f.commutes r]
  have hn : algebraMap R K r ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective R K).ne hr
  exact (isUnit_iff_ne_zero.mpr hn).map f

set_option maxHeartbeats 600000 in
include hr in
/-- On the actual generic fibre the dilatation map is an isomorphism. -/
theorem isIso_generic_affineDilatationHom :
    IsIso ((Over.pullback (Spec.algebraMap R K)).map (affineDilatationHom r j)) := by
  let a := Spec.algebraMap R K
  let F := Over.pullback a
  let L := Over.map a
  let adj := Over.mapPullbackAdj a
  let D := affineDilatation r j
  let d := affineDilatationHom r j
  have : IsAffineHom a := inferInstance
  have : Flat a :=
    Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat K (nonZeroDivisors R)))
  let : IsAffine (L.obj (F.obj X)).left := by
    change IsAffine (pullback X.hom a)
    infer_instance
  let : IsAffine (L.obj (F.obj D)).left := by
    change IsAffine (pullback D.hom a)
    infer_instance
  let : Flat (L.obj (F.obj X)).hom := by
    change Flat (pullback.snd X.hom a ≫ a)
    infer_instance
  let : Flat (L.obj (F.obj D)).hom := by
    change Flat (pullback.snd D.hom a ≫ a)
    infer_instance
  have htest : ∀ x ∈ centreIdeal j, affineAlgebraMap (baseProjection a X) x ∈
      Ideal.span {algebraMap R (affineAlgebra (L.obj (F.obj X))) r} := by
    rw [Ideal.span_singleton_eq_top.mpr (isUnit_coordinates_of_generic hr (F.obj X))]
    simp
  obtain ⟨v, hv⟩ := (affineDilatation_factors_iff j hr (baseProjection a X)).mpr htest
  let invD : F.obj X ⟶ F.obj D := adj.homEquiv (F.obj X) D v
  have hi : invD ≫ F.map d = 𝟙 (F.obj X) := by
    change adj.homEquiv _ _ v ≫ F.map d = _
    rw [← adj.homEquiv_naturality_right]
    change adj.homEquiv _ _ (v ≫ affineDilatationHom r j) = _
    rw [hv]
    apply (adj.homEquiv (F.obj X) X).symm.injective
    rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
    simp [baseProjection, adj]
  have hcancel : Function.Injective (fun x : F.obj D ⟶ F.obj D => x ≫ F.map d) := by
    intro x y he
    apply (adj.homEquiv _ _).symm.injective
    apply affineDilatationHom_injective j hr
    have h := congrArg (adj.homEquiv (F.obj D) X).symm he
    rw [adj.homEquiv_naturality_right_symm x d, adj.homEquiv_naturality_right_symm y d] at h
    exact h
  refine ⟨⟨invD, hcancel ?_, hi⟩⟩
  change (F.map d ≫ invD) ≫ F.map d = (𝟙 _) ≫ F.map d
  simp [Category.assoc, hi]

end Generic

end Langlands.GroupScheme.Dilatation
