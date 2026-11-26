import Langlands.GroupScheme.Dilatation.CongruenceModel
import Langlands.GroupScheme.IntegralModel.Iso

/-! # Addition of congruence levels on the actual models -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

open CategoryTheory CategoryTheory.CartesianMonoidalCategory
  CategoryTheory.MonoidalCategory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dilatation

section Coefficients

variable {R A B : Type*} [CommRing R] [IsDomain R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Module.Flat R B]

private theorem quotient_eq_iff {B : Type*} [CommRing B] (N : Ideal B) (x y : B) :
    Ideal.Quotient.mk N x = Ideal.Quotient.mk N y ↔ x - y ∈ N := by
  rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]

/-- Relative agreement modulo a scalar on the blow-up algebra is equivalent to agreement
modulo the product of the scalars on the original augmented algebra. -/
theorem blowup_congruence_iff (e : A →ₐ[R] R) {I : Ideal A}
    (hI : RingHom.ker e.toRingHom ≤ I) {r : R} (hr : r ≠ 0) (s : R)
    (f g : blowupAlgebra r I →ₐ[R] B) :
    (∀ b, f b - g b ∈ Ideal.span {algebraMap R B s}) ↔
      ∀ a, f (blowupMap r I a) - g (blowupMap r I a) ∈ Ideal.span {algebraMap R B (r * s)} := by
  have hd (a : I) :
      algebraMap R B r * (f (dividedElement (algebraMap R A r) I a) -
          g (dividedElement (algebraMap R A r) I a)) =
        f (blowupMap r I a) - g (blowupMap r I a) := by
    have hf' := congrArg f (mul_dividedElement (algebraMap R A r) I a)
    have hg' := congrArg g (mul_dividedElement (algebraMap R A r) I a)
    simp only [map_mul, ← IsScalarTower.algebraMap_apply, AlgHom.commutes] at hf' hg'
    rw [mul_sub]
    exact congrArg₂ Sub.sub hf' hg'
  constructor
  · intro h a
    let a₀ : A := a - algebraMap R A (e a)
    have ha₀ : a₀ ∈ I := hI (show e a₀ = 0 by simp [a₀])
    have key : f (blowupMap r I a₀) - g (blowupMap r I a₀) =
        f (blowupMap r I a) - g (blowupMap r I a) := by
      simp only [a₀, map_sub, AlgHom.commutes]
      abel
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.mp
      (h (dividedElement (algebraMap R A r) I ⟨a₀, ha₀⟩))
    apply Ideal.mem_span_singleton.mpr
    refine ⟨z, ?_⟩
    rw [← key, ← hd ⟨a₀, ha₀⟩, hz, map_mul, mul_assoc]
  · intro h b
    let N : Ideal B := Ideal.span {algebraMap R B s}
    let q := Ideal.Quotient.mk N
    apply (quotient_eq_iff N _ _).mp
    obtain ⟨b, hb⟩ := b
    induction hb using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      change q (f (dividedElement (algebraMap R A r) I ⟨a, ha⟩)) =
        q (g (dividedElement (algebraMap R A r) I ⟨a, ha⟩))
      apply (quotient_eq_iff N _ _).mpr
      obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.mp (h a)
      apply Ideal.mem_span_singleton.mpr
      refine ⟨z, smul_right_injective B hr ?_⟩
      change r • (_ - _) = r • (algebraMap R B s * z)
      rw [Algebra.smul_def, Algebra.smul_def, hd ⟨a, ha⟩, hz, map_mul, mul_assoc]
    | algebraMap a =>
      change q (f (blowupMap r I a)) = q (g (blowupMap r I a))
      apply (quotient_eq_iff N _ _).mpr
      obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.mp (h a)
      exact Ideal.mem_span_singleton.mpr ⟨algebraMap R B r * z, by
        rw [hz, map_mul, mul_comm (algebraMap R B r), mul_assoc]⟩
    | add x y hx hy ihx ihy =>
      change q (f (⟨x, hx⟩ + ⟨y, hy⟩)) = q (g (⟨x, hx⟩ + ⟨y, hy⟩))
      rw [map_add, map_add, map_add, map_add, ihx, ihy]
    | mul x y hx hy ihx ihy =>
      change q (f (⟨x, hx⟩ * ⟨y, hy⟩)) = q (g (⟨x, hx⟩ * ⟨y, hy⟩))
      rw [map_mul, map_mul, map_mul, map_mul, ihx, ihy]

end Coefficients

section Coordinates

open Langlands.AlgebraicGeometry.AffineClosedFactorizationLocus (coordinateIso)

universe u

variable {R : Type u} [CommRing R]

@[simp] theorem affineAlgebraMap_comp {X Y Z : Over (Spec (CommRingCat.of R))}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    affineAlgebraMap (f ≫ g) = (affineAlgebraMap f).comp (affineAlgebraMap g) := by
  exact congrArg (fun h => h.unop.hom) ((algΓ (CommRingCat.of R)).map_comp f g)

/-- The coordinate isomorphism for the relative spectrum of a supplied algebra. -/
private def specCoordinates (A : Type u) [CommRing A] [Algebra R A] :
    A ≃ₐ[R] affineAlgebra (algebraSpec (R := R) A) := by
  let f := (algΓAlgSpecAdjunction (CommRingCat.of R)).counit.app (op (CommAlgCat.of R A))
  let : (algSpec (CommRingCat.of R)).Full := algSpec.fullyFaithful.full
  let : (algSpec (CommRingCat.of R)).Faithful := algSpec.fullyFaithful.faithful
  have : IsIso f := by
    exact isIso_of_epi_of_isSplitMono f
  exact AlgEquiv.ofBijective f.unop.hom (ConcreteCategory.bijective_of_isIso f.unop)

/-- Evaluation of coordinates of a spectrum at an actual test point. -/
private def specPoint {T : Over (Spec (CommRingCat.of R))}
    {A : Type u} [CommRing A] [Algebra R A] (x : T ⟶ algebraSpec (R := R) A) :
    A →ₐ[R] affineAlgebra T :=
  (((algΓAlgSpecAdjunction (CommRingCat.of R)).homEquiv T (op (CommAlgCat.of R A))).symm x).unop.hom

private theorem specPoint_comp {T : Over (Spec (CommRingCat.of R))}
    {A B : Type u} [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (x : T ⟶ algebraSpec (R := R) B) (f : A →ₐ[R] B) :
    specPoint (x ≫ algebraSpecMap f) = (specPoint x).comp f := by
  unfold specPoint
  rw [Adjunction.homEquiv_naturality_right_symm]
  rfl

private theorem specPoint_eq {T : Over (Spec (CommRingCat.of R))}
    {A : Type u} [CommRing A] [Algebra R A] (x : T ⟶ algebraSpec (R := R) A) :
    specPoint x = (affineAlgebraMap x).comp (specCoordinates A).toAlgHom := by
  unfold specPoint
  rw [Adjunction.homEquiv_counit]
  rfl

private theorem specPoint_comp_coordIso {T X : Over (Spec (CommRingCat.of R))} [IsAffine X.left]
    (x : T ⟶ X) :
    specPoint (A := affineAlgebra X) (x ≫ (coordinateIso _ X).hom) = affineAlgebraMap x := by
  let adj := algΓAlgSpecAdjunction (CommRingCat.of R)
  have hu : adj.unit.app X = (adj.homEquiv X ((algΓ _).obj X)) (𝟙 _) := by
    rw [Adjunction.homEquiv_unit, (algSpec (CommRingCat.of R)).map_id]
    exact (Category.comp_id (adj.unit.app X)).symm
  change (((adj.homEquiv T ((algΓ _).obj X)).symm (x ≫ adj.unit.app X))).unop.hom = _
  rw [hu, adj.homEquiv_naturality_left_symm, Equiv.symm_apply_apply, Category.comp_id]

private theorem algSpecMaps_equal_iff {A B : Type u} [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (f g : A →ₐ[R] B) :
    algebraSpecMap f = algebraSpecMap g ↔ f = g := by
  constructor
  · intro h
    exact congrArg (fun h : op (CommAlgCat.of R B) ⟶ op (CommAlgCat.of R A) => h.unop.hom)
      (algSpec.fullyFaithful.map_injective h)
  · rintro rfl
    rfl

/-- Quotient-base pullback identifies two affine test points exactly when their coordinate
maps agree modulo the extended coefficient ideal. -/
theorem quotient_points_equal_iff (J : Ideal R) {T X : Over (Spec (CommRingCat.of R))}
    [IsAffine T.left] [IsAffine X.left] (x y : T ⟶ X) :
    (Over.pullback (quotientBase J)).map x = (Over.pullback (quotientBase J)).map y ↔
      ∀ a, affineAlgebraMap x a - affineAlgebraMap y a ∈
        J.map (algebraMap R (affineAlgebra T)) := by
  let b := quotientBase J
  let F := Over.pullback b
  let e := quotientTestIso J T
  let c := coordinateIso (CommRingCat.of R) X
  let q := Ideal.Quotient.mkₐ R (J.map (algebraMap R (affineAlgebra T)))
  have h (z : T ⟶ X) : e.hom ≫ baseProjection b T ≫ z ≫ c.hom =
      algebraSpecMap (q.comp (affineAlgebraMap z)) := by
    rw [quotientTestIso_hom_projection_assoc, ← coordIso_naturality z, Iso.inv_hom_id_assoc]
    exact algebraSpecMap_comp _ _
  calc
    F.map x = F.map y ↔ baseProjection b T ≫ x = baseProjection b T ≫ y := by
      have he (z : T ⟶ X) : ((Over.mapPullbackAdj b).homEquiv (F.obj T) X).symm (F.map z) =
          baseProjection b T ≫ z := by
        rw [Adjunction.homEquiv_counit]
        exact (Over.mapPullbackAdj b).counit.naturality z
      rw [← he x, ← he y, Equiv.apply_eq_iff_eq]
    _ ↔ e.hom ≫ baseProjection b T ≫ x ≫ c.hom =
        e.hom ≫ baseProjection b T ≫ y ≫ c.hom := by
      constructor
      · intro hxy
        simpa only [Category.assoc] using congrArg (fun f => e.hom ≫ f ≫ c.hom) hxy
      · intro hxy
        apply (cancel_epi e.hom).mp
        apply (cancel_mono c.hom).mp
        simpa only [Category.assoc] using hxy
    _ ↔ _ := by
      rw [h, h, algSpecMaps_equal_iff]
      constructor
      · intro h a
        exact (quotient_eq_iff _ _ _).mp (DFunLike.congr_fun h a)
      · intro h
        ext a
        exact (quotient_eq_iff _ _ _).mpr (h a)

private theorem quotient_spec_points_equal_iff (J : Ideal R) {T : Over (Spec (CommRingCat.of R))}
    [IsAffine T.left] {A : Type u} [CommRing A] [Algebra R A]
    (x y : T ⟶ algebraSpec (R := R) A) :
    (Over.pullback (quotientBase J)).map x = (Over.pullback (quotientBase J)).map y ↔
      ∀ a, specPoint x a - specPoint y a ∈ J.map (algebraMap R (affineAlgebra T)) := by
  let : IsAffine (algebraSpec (R := R) A).left := inferInstanceAs (IsAffine (Spec (CommRingCat.of A)))
  rw [quotient_points_equal_iff J]
  simp only [specPoint_eq, AlgHom.comp_apply, AlgEquiv.coe_toAlgHom]
  exact (specCoordinates (R := R) A).surjective.forall

end Coordinates

section Augmentation

variable {R : Type u} [CommRing R] (X : GroupScheme (Spec (CommRingCat.of R)))

private def baseCoordinates : R ≃ₐ[R] affineAlgebra (𝟙_ (Over (Spec (CommRingCat.of R)))) := by
  let i : algebraSpec (R := R) R ≅ 𝟙_ (Over (Spec (CommRingCat.of R))) := by
    refine Over.isoMk (Iso.refl _) ?_
    change 𝟙 _ ≫ 𝟙 _ = Spec.map (CommRingCat.ofHom (algebraMap R R))
    rw [Category.id_comp]
    change 𝟙 _ = Spec.map (𝟙 (CommRingCat.of R))
    exact (Spec.map_id _).symm
  let e := ((algΓ (CommRingCat.of R)).mapIso i.symm).unop
  exact (specCoordinates R).trans
    (AlgEquiv.ofBijective e.hom.hom (ConcreteCategory.bijective_of_isIso e.hom))

/-- The augmentation in the actual global coordinates, induced by the unit section. -/
def augmentation : affineAlgebra X.X →ₐ[R] R :=
  (baseCoordinates (R := R)).symm.toAlgHom.comp (affineAlgebraMap (η[X.X]))

private theorem unitCentreInclusion {J : Ideal R} :
    centreInclusion (kernelUnit ((baseChange (quotientBase J)).obj X)).hom.hom =
      toUnit _ ≫ η[X.X] := by
  let b := quotientBase J
  let H := (baseChange b).obj X
  have hu : baseChangeSectionHom b X η[X.X] = η[H.X] := by
    simpa only [MonObj.one_eq_one] using (baseChangeSectionHom b X).map_one
  have h := baseChangeSectionHom_fst b X η[X.X]
  rw [hu] at h
  apply Over.OverMorphism.ext
  change η[H.X].left ≫ Limits.pullback.fst X.X.hom b = _
  rw [h, Over.comp_left]
  congr 1

/-- The centre ideal of a congruence model contains the full augmentation ideal. -/
theorem ker_augmentation_le_centreIdeal {J : Ideal R} :
    RingHom.ker (augmentation X).toRingHom ≤
      centreIdeal (kernelUnit ((baseChange (quotientBase J)).obj X)).hom.hom := by
  intro a ha
  have he : affineAlgebraMap η[X.X] a = 0 := by
    apply (baseCoordinates (R := R)).symm.injective
    rw [map_zero]
    exact ha
  change affineAlgebraMap (centreInclusion
    (kernelUnit ((baseChange (quotientBase J)).obj X)).hom.hom) a = 0
  rw [unitCentreInclusion, affineAlgebraMap_comp, AlgHom.comp_apply, he, map_zero]

end Augmentation

section UnitFactor

variable {S U : Scheme.{u}} (b : U ⟶ S) (X : GroupScheme S) {T : Over S}

theorem unit_factor_iff (x : T ⟶ X.X) :
    (∃ z : (Over.pullback b).obj T ⟶ (Grp.trivial (Over U)).X,
      z ≫ (kernelUnit ((baseChange b).obj X)).hom.hom = (Over.pullback b).map x) ↔
      (Over.pullback b).map x = (Over.pullback b).map (1 : T ⟶ X.X) := by
  have h1 := (Over.pullback b).map_one (X := T) (M := X.X)
  rw [h1]
  constructor
  · rintro ⟨y, hy⟩
    rw [← hy]
    change y ≫ η[((baseChange b).obj X).X] = 1
    rw [toUnit_unique y (toUnit _)]
    rfl
  · intro h
    exact ⟨toUnit _, h.symm⟩

end UnitFactor

end Langlands.GroupScheme.Dilatation

namespace Langlands.GroupScheme.IntegralModel

open Dilatation
open Langlands.AlgebraicGeometry.AffineClosedFactorizationLocus (coordinateIso)

universe u

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  (M : IntegralModel R K G) {ϖ : R} (hϖ : Irreducible ϖ)

set_option maxHeartbeats 800000 in
/-- Reduction at level `n` on the level `m` model is trivial exactly when its image
in the original group is trivial at level `m + n`. -/
theorem congruenceTestReduction_add (m n : ℕ+) {T : Over (Spec (CommRingCat.of R))}
    [IsAffine T.left] [Flat T.hom]
    (x : T ⟶ (M.positiveCongruenceModel hϖ m).group.X) :
    (M.positiveCongruenceModel hϖ m).congruenceTestReduction n T x = 1 ↔
      M.congruenceTestReduction (m + n) T
        (x ≫ (M.positiveCongruenceModelHom hϖ m).hom.hom.hom) = 1 := by
  let P := M.positiveCongruenceModel hϖ m
  let p := (M.positiveCongruenceModelHom hϖ m).hom.hom.hom
  let j := (kernelUnit (M.congruenceFibre m)).hom.hom
  let B := blowupAlgebra (ϖ ^ (m : ℕ)) (centreIdeal j)
  let : IsAffine M.group.X.left := isAffine_of_isAffineHom M.group.X.hom
  let : Module.Flat R (affineAlgebra T) := (affineAlgebra_flat_iff T).mpr inferInstance
  have hcoord (z : T ⟶ P.group.X) : affineAlgebraMap (z ≫ p) =
      (specPoint (A := B) z).comp (blowupMap _ (centreIdeal j)) := by
    rw [← specPoint_comp]
    rw [← specPoint_comp_coordIso (z ≫ p)]
    congr 1
    change (z ≫ (algebraSpecMap (blowupMap (ϖ ^ (m : ℕ)) (centreIdeal j)) ≫
      (coordinateIso _ M.group.X).inv)) ≫ (coordinateIso _ M.group.X).hom = _
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  let y : T ⟶ P.group.X := 1
  have hy : y ≫ p = (1 : T ⟶ M.group.X) := MonObj.one_comp _
  rw [← map_one (P.congruenceTestReduction n T), ← map_one (M.congruenceTestReduction (m + n) T)]
  change (Over.pullback (quotientBase (IsLocalRing.maximalIdeal R ^ (n : ℕ)))).map x =
      (Over.pullback (quotientBase (IsLocalRing.maximalIdeal R ^ (n : ℕ)))).map y ↔
    (Over.pullback (quotientBase (IsLocalRing.maximalIdeal R ^ ((m + n : ℕ+) : ℕ)))).map (x ≫ p) =
      (Over.pullback (quotientBase (IsLocalRing.maximalIdeal R ^ ((m + n : ℕ+) : ℕ)))).map
        (1 : T ⟶ M.group.X)
  rw [← hy, quotient_spec_points_equal_iff (A := B), quotient_points_equal_iff,
    hcoord x, hcoord y]
  rw [maximalIdeal_pow_eq_span hϖ ((m + n : ℕ+) : ℕ),
    maximalIdeal_pow_eq_span hϖ (n : ℕ), Ideal.map_span, Ideal.map_span,
    Set.image_singleton, Set.image_singleton]
  change _ ↔ ∀ a, _ ∈ Ideal.span {algebraMap R (affineAlgebra T) (ϖ ^ ((m : ℕ) + (n : ℕ)))}
  rw [pow_add]
  exact blowup_congruence_iff (augmentation M.group) (ker_augmentation_le_centreIdeal _)
    (pow_ne_zero _ hϖ.ne_zero) (ϖ ^ (n : ℕ)) (specPoint x) (specPoint y)

/-- Reduction on an affine test is trivial at shallower levels whenever it is trivial
at a deeper level. -/
theorem congruenceTestReduction_one_of_le {m n : ℕ+} (h : m ≤ n)
    {T : Over (Spec (CommRingCat.of R))} [IsAffine T.left] {x : T ⟶ M.group.X}
    (hx : M.congruenceTestReduction n T x = 1) : M.congruenceTestReduction m T x = 1 := by
  let : IsAffine M.group.X.left := isAffine_of_isAffineHom M.group.X.hom
  rw [← map_one (M.congruenceTestReduction n T)] at hx
  rw [← map_one (M.congruenceTestReduction m T)]
  have he := (quotient_points_equal_iff (IsLocalRing.maximalIdeal R ^ (n : ℕ)) x 1).mp hx
  apply (quotient_points_equal_iff (IsLocalRing.maximalIdeal R ^ (m : ℕ)) x 1).mpr
  intro a
  exact Ideal.map_mono (Ideal.pow_le_pow_right (show (m : ℕ) ≤ (n : ℕ) from h)) (he a)

private theorem positiveHom_injective (n : ℕ+)
    {T : Over (Spec (CommRingCat.of R))} [IsAffine T.left] [Flat T.hom] :
    Function.Injective (fun x : T ⟶ (M.positiveCongruenceModel hϖ n).group.X =>
      x ≫ (M.positiveCongruenceModelHom hϖ n).hom.hom.hom) := by
  let : IsAffine M.group.X.left := isAffine_of_isAffineHom M.group.X.hom
  exact affineDilatationHom_injective _ (pow_ne_zero (n : ℕ) hϖ.ne_zero)

set_option maxHeartbeats 700000 in
private theorem positiveComposite_lift_iff (m n : ℕ+)
    {T : Over (Spec (CommRingCat.of R))} [IsAffine T.left] [Flat T.hom]
    (x : T ⟶ M.group.X) :
    (∃! y : T ⟶ ((M.positiveCongruenceModel hϖ m).positiveCongruenceModel hϖ n).group.X,
      y ≫ ((M.positiveCongruenceModel hϖ m).positiveCongruenceModelHom hϖ n).hom.hom.hom ≫
        (M.positiveCongruenceModelHom hϖ m).hom.hom.hom = x) ↔
      M.congruenceTestReduction (m + n) T x = 1 := by
  let P := M.positiveCongruenceModel hϖ m
  let p := (M.positiveCongruenceModelHom hϖ m).hom.hom.hom
  let q := (P.positiveCongruenceModelHom hϖ n).hom.hom.hom
  constructor
  · rintro ⟨y, hy, -⟩
    have he := (P.positiveCongruenceModel_lift_iff hϖ n (y ≫ q)).mp
      ⟨y, rfl, fun _ hz => positiveHom_injective P hϖ n hz⟩
    exact (congrArg (M.congruenceTestReduction (m + n) T)
      ((Category.assoc y q p).trans hy)).symm.trans
        ((M.congruenceTestReduction_add hϖ m n (y ≫ q)).mp he)
  · intro hx
    have hm : m ≤ m + n := by
      change (m : ℕ) ≤ (m : ℕ) + (n : ℕ)
      exact Nat.le_add_right _ _
    obtain ⟨y, hy, hyuniq⟩ := (M.positiveCongruenceModel_lift_iff hϖ m x).mpr
      (M.congruenceTestReduction_one_of_le hm hx)
    have hyn : P.congruenceTestReduction n T y = 1 := by
      apply (M.congruenceTestReduction_add hϖ m n y).mpr
      change y ≫ _ = x at hy
      simpa only [hy] using hx
    obtain ⟨z, hz, hzuniq⟩ := (P.positiveCongruenceModel_lift_iff hϖ n y).mpr hyn
    refine ⟨z, ?_, fun w hw => hzuniq w (hyuniq _ ?_)⟩
    · change z ≫ q ≫ p = x
      rw [← Category.assoc, hz, hy]
    · change (w ≫ q) ≫ p = x
      rw [Category.assoc]
      exact hw

set_option maxHeartbeats 900000 in
/-- Taking a positive congruence model of a positive congruence model adds the levels.
The isomorphism is compatible with the identification of the original generic group. -/
def positiveCongruenceModelAddIso (m n : ℕ+) :
    ((M.positiveCongruenceModel hϖ m).positiveCongruenceModel hϖ n).Iso
      (M.positiveCongruenceModel hϖ (m + n)) (CategoryTheory.Iso.refl G) := by
  let P := M.positiveCongruenceModel hϖ m
  let Q := P.positiveCongruenceModel hϖ n
  let p := M.positiveCongruenceModelHom hϖ m
  let q := P.positiveCongruenceModelHom hϖ n
  let r := M.positiveCongruenceModelHom hϖ (m + n)
  let j := kernelUnit (M.congruenceFibre (m + n))
  letI : IsAffine M.group.X.left := isAffine_of_isAffineHom M.group.X.hom
  letI : IsAffine Q.group.X.left := isAffine_of_isAffineHom Q.group.X.hom
  letI : IsAffineHom (M.congruenceFibre (m + n)).X.hom := inferInstanceAs
    (IsAffineHom (pullback.snd M.group.X.hom (congruenceBaseMap R (m + n))))
  letI : IsSeparated (M.congruenceFibre (m + n)).X.hom := IsSeparated.of_isAffineHom _
  letI : IsClosedImmersion j.hom.hom.left := kernelUnit_isClosedSubgroup _
  let σ := ϖ ^ ((m + n : ℕ+) : ℕ)
  have hσ : σ ≠ 0 := pow_ne_zero _ hϖ.ne_zero
  have hJ := maximalIdeal_pow_eq_span hϖ ((m + n : ℕ+) : ℕ)
  have hlift (T : Over (Spec (CommRingCat.of R))) [IsAffine T.left] [Flat T.hom]
      (x : T ⟶ M.group.X) :
      (∃! y : T ⟶ Q.group.X, y ≫ (q.hom ≫ p.hom).hom.hom = x) ↔
        ∃ z : (Over.pullback (congruenceBaseMap R (m + n))).obj T ⟶ (Grp.trivial _).X,
          z ≫ j.hom.hom = (Over.pullback (congruenceBaseMap R (m + n))).map x := by
    refine (M.positiveComposite_lift_iff hϖ m n x).trans ?_
    rw [← map_one (M.congruenceTestReduction (m + n) T)]
    exact (unit_factor_iff (congruenceBaseMap R (m + n)) M.group x).symm
  have hinj : Function.Injective (fun x : Q.group.X ⟶ Q.group.X =>
      x ≫ (q.hom ≫ p.hom).hom.hom) := by
    intro x y he
    apply positiveHom_injective P hϖ n
    apply positiveHom_injective M hϖ m
    change x ≫ q.hom.hom.hom ≫ p.hom.hom.hom = y ≫ q.hom.hom.hom ≫ p.hom.hom.hom at he
    simpa only [Category.assoc] using he
  let e := (existsUnique_dilatationGroupIso hσ hJ j (q.hom ≫ p.hom) hlift hinj).exists.choose
  have he : e.hom ≫ r.hom = q.hom ≫ p.hom :=
    (existsUnique_dilatationGroupIso hσ hJ j (q.hom ≫ p.hom) hlift hinj).exists.choose_spec
  refine ⟨e, ?_⟩
  let F := baseChange (Spec.algebraMap R K)
  have hf (A B : IntegralModel R K G) (φ : A.Hom B (𝟙 G)) :
      F.map φ.hom ≫ B.genericIso.hom = A.genericIso.hom := by
    simpa only [Category.comp_id] using φ.generic_comm
  change F.map e.hom ≫ (M.positiveCongruenceModel hϖ (m + n)).genericIso.hom =
    Q.genericIso.hom ≫ 𝟙 G
  rw [Category.comp_id, ← hf _ _ r, ← Category.assoc, ← F.map_comp, he, F.map_comp,
    Category.assoc, hf _ _ p, hf _ _ q]

/-- The first congruence model is the ordinary special-fibre dilatation at the unit. -/
theorem positiveCongruenceModel_one
    [IsClosedImmersion (kernelUnit M.specialFibre).hom.hom.left] :
    M.positiveCongruenceModel hϖ 1 = M.dilatation hϖ (kernelUnit M.specialFibre) := by
  let mk (J : Ideal R) (r : R) (hr : r ≠ 0) (hJ : J = Ideal.span {r}) : IntegralModel R K G :=
    let H := (baseChange (quotientBase J)).obj M.group
    letI : IsAffineHom H.X.hom :=
      inferInstanceAs (IsAffineHom (pullback.snd M.group.X.hom (quotientBase J)))
    letI : IsSeparated H.X.hom := IsSeparated.of_isAffineHom _
    letI : IsClosedImmersion (kernelUnit H).hom.hom.left := kernelUnit_isClosedSubgroup _
    M.dilatationAtQuotient hr hJ (kernelUnit H)
  have cmp (J J' : Ideal R) (r r' : R) (hr : r ≠ 0) (hr' : r' ≠ 0)
      (hJ : J = Ideal.span {r}) (hJ' : J' = Ideal.span {r'})
      (h : J = J') (h' : r = r') : mk J r hr hJ = mk J' r' hr' hJ' := by
    cases h
    cases h'
    rfl
  exact cmp _ _ _ _ _ _ _ _ (pow_one (IsLocalRing.maximalIdeal R)) (pow_one ϖ)

/-- Positive-level addition stated directly with the existing congruence subgroups. -/
theorem congruenceSubgroupAt_positiveCongruenceModel (m n : ℕ+) :
    (M.positiveCongruenceModel hϖ m).congruenceSubgroupAt n =
      M.congruenceSubgroupAt (m + n) := by
  rw [← integralPoints_positiveCongruenceModel _ hϖ n,
    ← M.integralPoints_positiveCongruenceModel hϖ (m + n)]
  exact (M.positiveCongruenceModelAddIso hϖ m n).integralPoints_eq

/-- The addition-of-levels identity for integral congruence points in the original
generic group, including level zero. -/
theorem integralPoints_congruenceModel_add (m n : ℕ) :
    ((M.congruenceModel hϖ m).congruenceModel hϖ n).integralPoints =
      (M.congruenceModel hϖ (m + n)).integralPoints := by
  cases m with
  | zero => simp
  | succ m =>
    cases n with
    | zero => simp
    | succ n =>
      exact (M.positiveCongruenceModelAddIso hϖ ⟨m + 1, Nat.succ_pos m⟩
        ⟨n + 1, Nat.succ_pos n⟩).integralPoints_eq

end Langlands.GroupScheme.IntegralModel
