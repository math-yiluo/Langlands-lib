import Langlands.GroupScheme.Dynamic.InvariantOpen
import Langlands.GroupScheme.NormalizedSubgroup

/-! # Orbit extensions inside cocharacter-stable open subschemes -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}} {G : GroupScheme S}

namespace AffineLine

/-- Scaling a point multiplies its affine coordinate by its multiplicative coordinate. -/
@[reassoc]
theorem lift_comp_scale {T Q : Over S} (b : Q ⟶ T) (a : Q ⟶ (Gm S).X)
    (x : Γ(Q.left, ⊤)) :
    lift (lift b a) ((homEquiv Q).symm x) ≫ scale T =
      lift b ((homEquiv Q).symm ((Gm.pointsEquiv S Q a : Γ(Q.left, ⊤)) * x)) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [scale]
  · apply hom_ext
    simp only [Category.assoc, scale, lift_snd]
    rw [homEquiv_comp, Equiv.apply_symm_apply, map_mul,
      ← homEquiv_comp, ← homEquiv_comp]
    simp only [lift_fst_assoc, lift_snd_assoc, lift_snd, homEquiv_comp_unitInclusion,
      Equiv.apply_symm_apply]

section Field

variable {k K : Type u} [Field k] [Field K]

/-- A field extension as a test scheme over the base field. -/
abbrev fieldTest (f : k →+* K) : Over (Spec (CommRingCat.of k)) :=
  Over.mk (Spec.map (CommRingCat.ofHom f))

/-- The structure map to the base field, viewed as the identity test scheme. -/
def fieldBase (f : k →+* K) :
    fieldTest f ⟶ Over.mk (𝟙 (Spec (CommRingCat.of k))) :=
  Over.homMk (Spec.map (CommRingCat.ofHom f)) (by simp)

/-- Evaluation of the polynomial affine line at an element of a field extension. -/
def fieldEvaluation (f : k →+* K) (x : K) :
    fieldTest f ⟶ polynomialScheme (𝟙 (Spec (CommRingCat.of k))) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom f x))) (by
    change Spec.map _ ≫ Spec.map (polynomialC (CommRingCat.of k)) ≫ 𝟙 _ = _
    rw [Category.comp_id, ← Spec.map_comp]
    congr 1
    ext r
    simp)

theorem fieldEvaluation_apply (f : k →+* K) (x : K) :
    (fieldEvaluation f x).left (⊥ : PrimeSpectrum K) = fieldPoint f x :=
  rfl

/-- Polynomial evaluation has its expected affine coordinate after the product comparison. -/
@[reassoc]
theorem fieldEvaluation_comp_polynomialPoint (f : k →+* K) (x : K) :
    fieldEvaluation f x ≫ polynomialPoint (𝟙 (Spec (CommRingCat.of k))) =
      lift (fieldBase f)
        ((homEquiv (fieldTest f)).symm ((Scheme.ΓSpecIso (CommRingCat.of K)).inv x)) := by
  rw [polynomialPoint, comp_lift]
  congr 1
  · apply Over.OverMorphism.ext
    change Spec.map _ ≫ Spec.map (polynomialC (CommRingCat.of k)) =
      Spec.map (CommRingCat.ofHom f)
    rw [← Spec.map_comp]
    congr 1
    ext r
    simp
  · apply hom_ext
    rw [homEquiv_comp, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    change (Spec.map (CommRingCat.ofHom (Polynomial.eval₂RingHom f x))).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial k))).inv Polynomial.X) = _
    rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
    simp

/-- A nonzero scalar as a multiplicative-group point of the field test scheme. -/
def fieldUnit (f : k →+* K) (a : Kˣ) :
    fieldTest f ⟶ (Gm (Spec (CommRingCat.of k))).X :=
  (Gm.pointsEquiv _ _).symm
    (Units.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom.toMonoidHom a)

theorem pointsEquiv_fieldUnit (f : k →+* K) (a : Kˣ) :
    (Gm.pointsEquiv _ _ (fieldUnit f a) : Γ((fieldTest f).left, ⊤)) =
      (Scheme.ΓSpecIso (CommRingCat.of K)).inv (a : K) := by
  rw [fieldUnit, MulEquiv.apply_symm_apply]
  rfl

/-- A field-valued point lies in an open subscheme exactly when it factors through it. -/
theorem fieldTest_mem_opensRange_iff (f : k →+* K)
    {U X : Over (Spec (CommRingCat.of k))} (j : U ⟶ X)
    [IsOpenImmersion j.left] (y : fieldTest f ⟶ X) :
    y.left (⊥ : PrimeSpectrum K) ∈ j.left.opensRange ↔
      ∃ z : fieldTest f ⟶ U, z ≫ j = y := by
  constructor
  · intro hy
    have hr : Set.range y.left ⊆ Set.range j.left := by
      rintro _ ⟨p, rfl⟩
      have hp : p = (⊥ : PrimeSpectrum K) :=
        @Subsingleton.elim (PrimeSpectrum K) _ p ⊥
      change y.left p ∈ j.left.opensRange
      rw [hp]
      exact hy
    refine ⟨Over.homMk (IsOpenImmersion.lift j.left y.left hr) ?_, ?_⟩
    · rw [← Over.w j, ← Category.assoc, IsOpenImmersion.lift_fac, Over.w]
    · exact Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)
  · rintro ⟨z, rfl⟩
    exact ⟨z.left (⊥ : PrimeSpectrum K), rfl⟩

/-- Polynomial evaluation at the zero point is the actual zero value of the extension. -/
theorem polynomialPoint_eval_zero {Y : Over (Spec (CommRingCat.of k))}
    (e : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⊗
      scheme (Spec (CommRingCat.of k)) ⟶ Y) :
    (polynomialPoint (𝟙 (Spec (CommRingCat.of k))) ≫ e).left
        (fieldPoint (RingHom.id k) 0) =
      (Dynamic.evalZero e).left (⊥ : PrimeSpectrum k) := by
  have h : polynomialZero (𝟙 (Spec (CommRingCat.of k))) ≫
      polynomialPoint (𝟙 (Spec (CommRingCat.of k))) ≫ e = Dynamic.evalZero e := by
    rw [← Category.assoc, polynomialZero_comp_polynomialPoint]
    rfl
  exact congrArg (fun y => y.left (⊥ : PrimeSpectrum k)) h

end Field

end AffineLine

namespace Dynamic

variable (χ : (Gm S).toGrp ⟶ G)

/-- Stability under conjugation by the cocharacter, on every scheme over the base. -/
def IsCocharacterStable {U : Over S} (j : U ⟶ G.X) : Prop :=
  ∀ (Q : Over S) (a : Q ⟶ (Gm S).X) (z : Q ⟶ U),
    ∃ z' : Q ⟶ U,
      z' ≫ j = (a ≫ χ.hom.hom) * (z ≫ j) * (a ≫ χ.hom.hom)⁻¹

/-- Stability in both scalar directions preserves factorization through the subscheme. -/
theorem IsCocharacterStable.factors_iff {U Q : Over S} {j : U ⟶ G.X}
    (hj : IsCocharacterStable χ j) (a : Q ⟶ (Gm S).X) (y : Q ⟶ G.X) :
    (∃ z : Q ⟶ U, z ≫ j = (a ≫ χ.hom.hom) * y * (a ≫ χ.hom.hom)⁻¹) ↔
      ∃ z : Q ⟶ U, z ≫ j = y := by
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨z', hz'⟩ := hj Q a⁻¹ z
    refine ⟨z', ?_⟩
    rw [hz, GrpObj.inv_comp] at hz'
    calc
      z' ≫ j = _ := hz'
      _ = y := by group
  · rintro ⟨z, hz⟩
    obtain ⟨z', hz'⟩ := hj Q a z
    exact ⟨z', hz ▸ hz'⟩

/-- A product of two subgroup presentations normalized by the cocharacter is stable. -/
theorem isCocharacterStable_product {H K : GroupScheme S} (iH : H ⟶ G) (iK : K ⟶ G)
    (hH : (SubgroupFunctor.range iH).IsNormalizedBy (SubgroupFunctor.range χ))
    (hK : (SubgroupFunctor.range iK).IsNormalizedBy (SubgroupFunctor.range χ)) :
    IsCocharacterStable χ
      ((fst H.X K.X ≫ iH.hom.hom) * (snd H.X K.X ≫ iK.hom.hom)) := by
  intro Q a z
  let zH := lift a (z ≫ fst H.X K.X) ≫
    SubgroupFunctor.normalizedConjugation iH χ hH
  let zK := lift a (z ≫ snd H.X K.X) ≫
    SubgroupFunctor.normalizedConjugation iK χ hK
  refine ⟨lift zH zK, ?_⟩
  simp only [MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc]
  rw [SubgroupFunctor.lift_comp_normalizedConjugation_comp,
    SubgroupFunctor.lift_comp_normalizedConjugation_comp]
  simp only [Category.assoc]
  group

variable [IsSeparated G.X.hom]

/-- Uniqueness of extensions makes an actual orbit extension equivariant for scaling. -/
theorem IsOrbitExtension.scale {T : Over S} {g : T ⟶ G.X}
    {e : T ⊗ AffineLine.scheme S ⟶ G.X} (he : IsOrbitExtension χ g e) :
    let s : (T ⊗ (Gm S).X) ⊗ AffineLine.scheme S ⟶ G.X :=
      fst _ _ ≫ snd _ _ ≫ χ.hom.hom
    s * (fst T (Gm S).X ▷ AffineLine.scheme S ≫ e) * s⁻¹ =
      AffineLine.scale T ≫ e := by
  dsimp only
  apply AffineLine.hom_ext_of_unitInclusion
  rw [AffineLine.whiskerLeft_unitInclusion_scale_assoc, he, MonObj.comp_mul, MonObj.comp_mul,
    GrpObj.comp_inv, whisker_exchange_assoc, he, whiskerRight_orbit]
  simp only [orbit, MonObj.comp_mul, GrpObj.comp_inv, whiskerLeft_fst_assoc, lift_fst_assoc,
    lift_snd_assoc, MonObj.mul_comp, mul_inv_rev, mul_assoc, Category.assoc]

/-- Scaling equivariance evaluated on arbitrary test-scheme points. -/
theorem IsOrbitExtension.eval_scale {T Q : Over S} {g : T ⟶ G.X}
    {e : T ⊗ AffineLine.scheme S ⟶ G.X} (he : IsOrbitExtension χ g e)
    (b : Q ⟶ T) (a : Q ⟶ (Gm S).X) (x : Γ(Q.left, ⊤)) :
    (a ≫ χ.hom.hom) * (lift b ((AffineLine.homEquiv Q).symm x) ≫ e) *
      (a ≫ χ.hom.hom)⁻¹ =
    lift b ((AffineLine.homEquiv Q).symm
      ((Gm.pointsEquiv S Q a : Γ(Q.left, ⊤)) * x)) ≫ e := by
  have h := congrArg
    (fun v => lift (lift b a) ((AffineLine.homEquiv Q).symm x) ≫ v) (he.scale χ)
  simpa only [Category.assoc, MonObj.comp_mul, GrpObj.comp_inv, lift_fst_assoc, lift_snd_assoc,
    lift_whiskerRight_assoc, lift_fst, AffineLine.lift_comp_scale_assoc] using h

section Field

variable {k K : Type u} [Field k] [Field K]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
  [IsSeparated G.X.hom]

/-- At field-valued coordinates, scaling the parameter conjugates the orbit extension. -/
theorem IsOrbitExtension.fieldEvaluation_scale
    {g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X}
    {e : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⊗
      AffineLine.scheme (Spec (CommRingCat.of k)) ⟶ G.X}
    (he : IsOrbitExtension χ g e) (f : k →+* K) (x : K) (a : Kˣ) :
    (AffineLine.fieldUnit f a ≫ χ.hom.hom) *
        (AffineLine.fieldEvaluation f x ≫
          AffineLine.polynomialPoint (𝟙 (Spec (CommRingCat.of k))) ≫ e) *
        (AffineLine.fieldUnit f a ≫ χ.hom.hom)⁻¹ =
      AffineLine.fieldEvaluation f ((a : K) * x) ≫
        AffineLine.polynomialPoint (𝟙 (Spec (CommRingCat.of k))) ≫ e := by
  simpa only [AffineLine.fieldEvaluation_comp_polynomialPoint_assoc,
    AffineLine.pointsEquiv_fieldUnit, map_mul] using
    he.eval_scale χ (AffineLine.fieldBase f) (AffineLine.fieldUnit f a)
      ((Scheme.ΓSpecIso (CommRingCat.of K)).inv x)

/-- Pulling back a stable open along an orbit extension gives an all-field
scalar-invariant open subset of the polynomial affine line. -/
theorem IsOrbitExtension.isScalarInvariantOpen
    {g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X}
    {e : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⊗
      AffineLine.scheme (Spec (CommRingCat.of k)) ⟶ G.X}
    (he : IsOrbitExtension χ g e)
    {U : Over (Spec (CommRingCat.of k))} (j : U ⟶ G.X)
    [IsOpenImmersion j.left] (hj : IsCocharacterStable χ j) :
    AffineLine.IsScalarInvariantOpen
      ((AffineLine.polynomialPoint (𝟙 (Spec (CommRingCat.of k))) ≫ e).left ⁻¹ᵁ
        j.left.opensRange) := by
  intro K _ f x a
  change (AffineLine.fieldEvaluation f ((a : K) * x) ≫
      AffineLine.polynomialPoint (𝟙 (Spec (CommRingCat.of k))) ≫ e).left
        (⊥ : PrimeSpectrum K) ∈ j.left.opensRange ↔
    (AffineLine.fieldEvaluation f x ≫
      AffineLine.polynomialPoint (𝟙 (Spec (CommRingCat.of k))) ≫ e).left
        (⊥ : PrimeSpectrum K) ∈ j.left.opensRange
  rw [AffineLine.fieldTest_mem_opensRange_iff, AffineLine.fieldTest_mem_opensRange_iff,
    ← he.fieldEvaluation_scale χ f x a]
  exact hj.factors_iff χ _ _

variable {g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X}
  {e : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⊗
    AffineLine.scheme (Spec (CommRingCat.of k)) ⟶ G.X}
  {U : Over (Spec (CommRingCat.of k))} (j : U ⟶ G.X)
  [IsOpenImmersion j.left] (hj : IsCocharacterStable χ j)
  (he : IsOrbitExtension χ g e)
  (h0 : (evalZero e).left (⊥ : PrimeSpectrum k) ∈ j.left.opensRange)

/-- Lift the polynomial presentation of an orbit extension into its stable open. -/
def polynomialOrbitOpenLift :
    AffineLine.polynomialScheme (𝟙 (Spec (CommRingCat.of k))) ⟶ U :=
  Over.homMk
    (AffineLine.invariantOpenLift j.left
      (AffineLine.polynomialPoint (𝟙 (Spec (CommRingCat.of k))) ≫ e).left
      (he.isScalarInvariantOpen χ j hj)
      (by rw [AffineLine.polynomialPoint_eval_zero]; exact h0))
    (by
      rw [← Over.w j, ← Category.assoc, AffineLine.invariantOpenLift_fac, Over.w])

@[reassoc]
theorem polynomialOrbitOpenLift_fac :
    polynomialOrbitOpenLift χ j hj he h0 ≫ j =
      AffineLine.polynomialPoint (𝟙 (Spec (CommRingCat.of k))) ≫ e :=
  Over.OverMorphism.ext (AffineLine.invariantOpenLift_fac _ _
    (he.isScalarInvariantOpen χ j hj)
    (by rw [AffineLine.polynomialPoint_eval_zero]; exact h0))

/-- An orbit extension whose zero value lies in a stable open lifts into that open. -/
def orbitOpenLift :
    Over.mk (𝟙 (Spec (CommRingCat.of k))) ⊗
      AffineLine.scheme (Spec (CommRingCat.of k)) ⟶ U :=
  AffineLine.polynomialPointInv (𝟙 (Spec (CommRingCat.of k))) ≫
    polynomialOrbitOpenLift χ j hj he h0

@[reassoc]
theorem orbitOpenLift_fac :
    orbitOpenLift χ j hj he h0 ≫ j = e := by
  rw [orbitOpenLift, Category.assoc, polynomialOrbitOpenLift_fac,
    ← Category.assoc, AffineLine.polynomialPointInv_comp_polynomialPoint,
    Category.id_comp]

end Field

end Dynamic

end Langlands.GroupScheme
