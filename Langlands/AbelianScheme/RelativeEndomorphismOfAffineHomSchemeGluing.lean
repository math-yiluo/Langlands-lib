import Langlands.GroupScheme.Cartier.Restriction
import Langlands.AbelianScheme.GroupSchemeSubalgebraDescentProof

/-! # Zariski locality and gluing of relative homomorphisms -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonObj
open AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj CategoryTheory.Obj
attribute [local instance] CategoryTheory.Over.cartesianMonoidalCategory
  CategoryTheory.Over.braidedCategory

namespace Langlands.GroupScheme.Cartier

universe v u
variable {S : Scheme.{u}}

/-! ### Canonical projections along open immersions -/

section OpenImmersion

variable (G : CommGroupScheme S) {T W : Over S} (a : W ⟶ T)

/-- The canonical projection `G_W ⟶ G_T` is the base change of `a`. -/
lemma isPullback_baseChangeProj :
    IsPullback (baseChangeProj G a) (pullback.snd G.X.hom W.hom)
      (pullback.snd G.X.hom T.hom) a.left := by
  refine IsPullback.of_right ?_ (baseChangeProj_snd G a)
    (IsPullback.of_hasPullback G.X.hom T.hom)
  rw [baseChangeProj_fst, Over.w a]
  exact IsPullback.of_hasPullback G.X.hom W.hom

instance [IsOpenImmersion a.left] : IsOpenImmersion (baseChangeProj G a) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsOpenImmersion)
    (isPullback_baseChangeProj G a).flip ‹_›

/-- The canonical projection `G_W ⟶ G_T` has image the preimage of the image of `a`. -/
lemma range_baseChangeProj :
    Set.range (baseChangeProj G a) =
      pullback.snd G.X.hom T.hom ⁻¹' Set.range a.left := by
  have h := isPullback_baseChangeProj G a
  rw [← Scheme.Pullback.range_fst]
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨h.isoPullback.hom z, ?_⟩
    rw [← Scheme.Hom.comp_apply, h.isoPullback_hom_fst]
    rfl
  · rintro ⟨z, rfl⟩
    refine ⟨h.isoPullback.inv z, ?_⟩
    rw [← Scheme.Hom.comp_apply, h.isoPullback_inv_fst]
    rfl

end OpenImmersion

/-! ### Locality -/

/-- Relative homomorphisms agreeing on the members of an open cover of the test scheme are
equal. -/
theorem relativeHom_eq_of_locally {G H : CommGroupScheme S} {T : Over S}
    (χ χ' : RelativeHom G H T)
    (h : ∀ x : T.left, ∃ (W : Over S) (a : W ⟶ T), IsOpenImmersion a.left ∧
      x ∈ Set.range a.left ∧ restrict G H a χ = restrict G H a χ') :
    χ = χ' := by
  apply relativeHom_ext
  apply Scheme.hom_ext_of_forall
  intro y
  obtain ⟨W, a, ha, hx, hres⟩ := h (pullback.snd G.X.hom T.hom y)
  have hy : y ∈ Set.range (baseChangeProj G a) := by
    rw [range_baseChangeProj]
    exact hx
  refine ⟨(baseChangeProj G a).opensRange, hy, ?_⟩
  rw [← Scheme.Hom.isoOpensRange_inv_comp]
  simp only [Category.assoc]
  rw [← restrict_fst G H a χ, hres, restrict_fst]

/-- Relative homomorphisms agreeing on all affine open subschemes of the test scheme are
equal. -/
theorem relativeHom_eq_of_forall_isAffine {G H : CommGroupScheme S} {T : Over S}
    (χ χ' : RelativeHom G H T)
    (h : ∀ (W : Over S) (a : W ⟶ T), IsAffine W.left → IsOpenImmersion a.left →
      restrict G H a χ = restrict G H a χ') :
    χ = χ' := by
  refine relativeHom_eq_of_locally χ χ' fun x => ?_
  obtain ⟨i, y, hy⟩ := T.left.affineCover.exists_eq x
  let a : Over.mk (T.left.affineCover.f i ≫ T.hom) ⟶ T := Over.homMk (T.left.affineCover.f i)
  refine ⟨_, a, inferInstanceAs (IsOpenImmersion (T.left.affineCover.f i)), ⟨y, hy⟩,
    h _ a (inferInstanceAs (IsAffine (Spec _)))
    (inferInstanceAs (IsOpenImmersion (T.left.affineCover.f i)))⟩

/-! ### Relative homomorphisms through their first projections -/

section Points

variable {G H : CommGroupScheme S} {T : Over S}

/-- The point of `G_T` lying over `x₀ : Z ⟶ T` with first projection `P`. -/
abbrev ptLift {Z : Scheme.{u}} (x₀ : Z ⟶ T.left) (P : Over.mk (x₀ ≫ T.hom) ⟶ G.X) :
    Z ⟶ pullback G.X.hom T.hom :=
  pullback.lift P.left x₀ (Over.w P)

/-- The map on points lying over `T` induced by a morphism `m : G_T ⟶ H` over `S`. -/
def ptMap (m : pullback G.X.hom T.hom ⟶ H.X.left)
    (hm : m ≫ H.X.hom = pullback.snd G.X.hom T.hom ≫ T.hom) {Z : Scheme.{u}}
    (x₀ : Z ⟶ T.left) (P : Over.mk (x₀ ≫ T.hom) ⟶ G.X) : Over.mk (x₀ ≫ T.hom) ⟶ H.X :=
  Over.homMk (ptLift x₀ P ≫ m) (by simp [hm])

@[simp]
lemma ptMap_left (m : pullback G.X.hom T.hom ⟶ H.X.left)
    (hm : m ≫ H.X.hom = pullback.snd G.X.hom T.hom ≫ T.hom) {Z : Scheme.{u}}
    (x₀ : Z ⟶ T.left) (P : Over.mk (x₀ ≫ T.hom) ⟶ G.X) :
    (ptMap m hm x₀ P).left = ptLift x₀ P ≫ m :=
  rfl

/-- A morphism `m : G_T ⟶ H` over `S` is multiplicative on all points lying over `T`. -/
def IsPtMul (m : pullback G.X.hom T.hom ⟶ H.X.left)
    (hm : m ≫ H.X.hom = pullback.snd G.X.hom T.hom ≫ T.hom) : Prop :=
  ∀ ⦃Z : Scheme.{u}⦄ (x₀ : Z ⟶ T.left) (P Q : Over.mk (x₀ ≫ T.hom) ⟶ G.X),
    ptMap m hm x₀ (P * Q) = ptMap m hm x₀ P * ptMap m hm x₀ Q

/-- Points transported along a map of test schemes are mapped compatibly. -/
lemma comp_ptMap {T' : Over S} (b : T' ⟶ T) (m : pullback G.X.hom T.hom ⟶ H.X.left)
    (hm : m ≫ H.X.hom = pullback.snd G.X.hom T.hom ≫ T.hom)
    (m' : pullback G.X.hom T'.hom ⟶ H.X.left)
    (hm' : m' ≫ H.X.hom = pullback.snd G.X.hom T'.hom ≫ T'.hom)
    (hb : baseChangeProj G b ≫ m = m') {Z Z' : Scheme.{u}} (x₀ : Z ⟶ T.left)
    (y₀ : Z' ⟶ T'.left) (e : Over.mk (y₀ ≫ T'.hom) ⟶ Over.mk (x₀ ≫ T.hom))
    (he : e.left ≫ x₀ = y₀ ≫ b.left) (R : Over.mk (x₀ ≫ T.hom) ⟶ G.X) :
    e ≫ ptMap m hm x₀ R = ptMap m' hm' y₀ (e ≫ R) := by
  apply Over.OverMorphism.ext
  rw [Over.comp_left, ptMap_left, ptMap_left, ← hb]
  have : e.left ≫ ptLift x₀ R = ptLift y₀ (e ≫ R) ≫ baseChangeProj G b := by
    apply pullback.hom_ext
    · simp
    · simp [he]
  rw [reassoc_of% this]

/-- The first projection `G_T ⟶ H` of a relative homomorphism. -/
abbrev fstMap (χ : RelativeHom G H T) : pullback G.X.hom T.hom ⟶ H.X.left :=
  CommGroupScheme.hom χ ≫ pullback.fst H.X.hom T.hom

lemma fstMap_hom (χ : RelativeHom G H T) :
    fstMap χ ≫ H.X.hom = pullback.snd G.X.hom T.hom ≫ T.hom := by
  have hχ : CommGroupScheme.hom χ ≫ pullback.snd H.X.hom T.hom =
      pullback.snd G.X.hom T.hom :=
    Over.w (CommGroupScheme.groupHom χ).hom.hom
  rw [Category.assoc, pullback.condition, reassoc_of% hχ]

lemma fstMap_restrict {T' : Over S} (a : T' ⟶ T) (χ : RelativeHom G H T) :
    fstMap (restrict G H a χ) = baseChangeProj G a ≫ fstMap χ :=
  restrict_fst G H a χ

lemma basePoint_mul {S' : Scheme.{u}} (ψ : S' ⟶ S) {Y : Over S} [GrpObj Y] {U : Over S'}
    (z₁ z₂ : U ⟶ (Over.pullback ψ).obj Y) :
    basePoint ψ (z₁ * z₂) = basePoint ψ z₁ * basePoint ψ z₂ := by
  apply ((Over.mapPullbackAdj ψ).homEquiv U Y).injective
  rw [mapPullbackAdj_homEquiv_mul]
  simp only [basePoint, Equiv.apply_symm_apply]

lemma homEquiv_left {Z : Scheme.{u}} (x₀ : Z ⟶ T.left) (P : Over.mk (x₀ ≫ T.hom) ⟶ G.X) :
    ((Over.mapPullbackAdj T.hom).homEquiv (Over.mk x₀) G.X P).left = ptLift x₀ P := by
  apply pullback.hom_ext
  · rw [pullback.lift_fst]
    exact homEquiv_left_fst (U := Over.mk x₀) T.hom P
  · rw [pullback.lift_snd]
    exact Over.w ((Over.mapPullbackAdj T.hom).homEquiv (Over.mk x₀) G.X P)

lemma ptMap_fstMap (χ : RelativeHom G H T) {Z : Scheme.{u}} (x₀ : Z ⟶ T.left)
    (P : Over.mk (x₀ ≫ T.hom) ⟶ G.X) :
    ptMap (fstMap χ) (fstMap_hom χ) x₀ P =
      basePoint T.hom ((Over.mapPullbackAdj T.hom).homEquiv (Over.mk x₀) G.X P ≫
        (CommGroupScheme.groupHom χ).hom.hom) := by
  apply Over.OverMorphism.ext
  rw [ptMap_left, basePoint_left, Over.comp_left, homEquiv_left, Category.assoc]

/-- The first projection of a relative homomorphism is multiplicative on points. -/
lemma isPtMul_fstMap (χ : RelativeHom G H T) : IsPtMul (fstMap χ) (fstMap_hom χ) := by
  intro Z x₀ P Q
  rw [ptMap_fstMap, ptMap_fstMap, ptMap_fstMap, mapPullbackAdj_homEquiv_mul, MonObj.mul_comp,
    basePoint_mul]

section OfFstMap

variable (m : pullback G.X.hom T.hom ⟶ H.X.left)
    (hm : m ≫ H.X.hom = pullback.snd G.X.hom T.hom ≫ T.hom)

/-- The morphism `G_T ⟶ H_T` over `T` whose first projection is `m`. -/
def liftMap : (testBaseChange T G).X ⟶ (testBaseChange T H).X :=
  Over.homMk (pullback.lift m (pullback.snd G.X.hom T.hom) hm) (pullback.lift_snd _ _ _)

lemma ptLift_basePoint {X : Over T.left} (z : X ⟶ (testBaseChange T G).X) :
    ptLift X.hom (basePoint T.hom z) = z.left := by
  apply pullback.hom_ext
  · rw [pullback.lift_fst, basePoint_left]
  · rw [pullback.lift_snd]
    exact (Over.w z).symm

lemma basePoint_comp_liftMap {X : Over T.left} (z : X ⟶ (testBaseChange T G).X) :
    basePoint T.hom (z ≫ liftMap m hm) = ptMap m hm X.hom (basePoint T.hom z) := by
  apply Over.OverMorphism.ext
  rw [basePoint_left, ptMap_left, ptLift_basePoint, Over.comp_left, Category.assoc]
  congr 1
  exact pullback.lift_fst _ _ _

lemma isMonHom_liftMap (hmul : IsPtMul m hm) : IsMonHom (liftMap m hm) := by
  refine isMonHom_of_mul_comp _ fun {X} x y => ?_
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · calc ((x * y) ≫ liftMap m hm).left ≫ pullback.fst H.X.hom T.hom
        = (basePoint T.hom ((x * y) ≫ liftMap m hm)).left := (basePoint_left _ _).symm
      _ = (basePoint T.hom (x ≫ liftMap m hm) * basePoint T.hom (y ≫ liftMap m hm)).left := by
        rw [basePoint_comp_liftMap, basePoint_mul, hmul, basePoint_comp_liftMap,
          basePoint_comp_liftMap]
      _ = ((x ≫ liftMap m hm) * (y ≫ liftMap m hm)).left ≫ pullback.fst H.X.hom T.hom :=
        (mul_left_fst _ _ _).symm
  · exact (Over.w _).trans (Over.w _).symm

/-- The relative homomorphism whose first projection is a given multiplicative morphism. -/
def ofFstMap (hmul : IsPtMul m hm) : RelativeHom G H T :=
  haveI := isMonHom_liftMap m hm hmul
  Additive.ofMul (Grp.homMk (liftMap m hm))

lemma fstMap_ofFstMap (hmul : IsPtMul m hm) : fstMap (ofFstMap m hm hmul) = m :=
  pullback.lift_fst _ _ _

end OfFstMap

end Points

/-! ### Gluing -/

section Gluing

variable {G H : CommGroupScheme S} {T : Over S} {J : Type*} (W : J → Over S)
  (a : ∀ i, W i ⟶ T)

/-- Compatible relative homomorphisms have compatible first projections on the overlaps of the
canonical projections. -/
lemma fstMap_overlap (χ : ∀ i, RelativeHom G H (W i))
    (hχ : ∀ i j (Z : Over S) (p : Z ⟶ W i) (q : Z ⟶ W j), p ≫ a i = q ≫ a j →
      restrict G H p (χ i) = restrict G H q (χ j)) (i j : J) :
    pullback.fst (baseChangeProj G (a i)) (baseChangeProj G (a j)) ≫ fstMap (χ i) =
      pullback.snd (baseChangeProj G (a i)) (baseChangeProj G (a j)) ≫ fstMap (χ j) := by
  set fV := pullback.fst (baseChangeProj G (a i)) (baseChangeProj G (a j))
  set sV := pullback.snd (baseChangeProj G (a i)) (baseChangeProj G (a j))
  have hV : fV ≫ baseChangeProj G (a i) = sV ≫ baseChangeProj G (a j) := pullback.condition
  have h1 : (fV ≫ pullback.snd G.X.hom (W i).hom) ≫ (a i).left =
      (sV ≫ pullback.snd G.X.hom (W j).hom) ≫ (a j).left := by
    rw [Category.assoc, Category.assoc, ← baseChangeProj_snd, ← baseChangeProj_snd,
      reassoc_of% hV]
  have h2 : fV ≫ pullback.fst G.X.hom (W i).hom = sV ≫ pullback.fst G.X.hom (W j).hom := by
    rw [← baseChangeProj_fst G (a i), ← baseChangeProj_fst G (a j), reassoc_of% hV]
  let Z : Over S := Over.mk (pullback.fst (a i).left (a j).left ≫ (W i).hom)
  let p : Z ⟶ W i := Over.homMk (pullback.fst (a i).left (a j).left)
  let q : Z ⟶ W j := Over.homMk (pullback.snd (a i).left (a j).left) (by
    simp only [Z, Over.mk_hom]
    rw [← Over.w (a j), ← pullback.condition_assoc, Over.w (a i)])
  have hpq : p ≫ a i = q ≫ a j := Over.OverMorphism.ext pullback.condition
  let lam : pullback (baseChangeProj G (a i)) (baseChangeProj G (a j)) ⟶
      pullback G.X.hom Z.hom :=
    pullback.lift (fV ≫ pullback.fst G.X.hom (W i).hom)
      (pullback.lift (fV ≫ pullback.snd G.X.hom (W i).hom)
        (sV ≫ pullback.snd G.X.hom (W j).hom) h1)
      (by simp [Z, pullback.condition])
  have hlp : lam ≫ baseChangeProj G p = fV := by
    apply pullback.hom_ext
    · simp [lam]
    · simp [lam, p]
  have hlq : lam ≫ baseChangeProj G q = sV := by
    apply pullback.hom_ext
    · simp [lam, h2]
    · simp [lam, q]
  calc fV ≫ fstMap (χ i) = lam ≫ baseChangeProj G p ≫ fstMap (χ i) := by
        rw [reassoc_of% hlp]
    _ = lam ≫ fstMap (restrict G H p (χ i)) := by rw [fstMap_restrict]
    _ = lam ≫ fstMap (restrict G H q (χ j)) := by rw [hχ i j Z p q hpq]
    _ = lam ≫ baseChangeProj G q ≫ fstMap (χ j) := by rw [fstMap_restrict]
    _ = sV ≫ fstMap (χ j) := by rw [reassoc_of% hlq]

/-- Relative homomorphisms on the members of an open cover of the test scheme that agree on all
common refinements glue to a relative homomorphism on the test scheme. -/
theorem relativeHom_exists_glue [∀ i, IsOpenImmersion (a i).left]
    (hcov : ∀ x : T.left, ∃ i, x ∈ Set.range (a i).left)
    (χ : ∀ i, RelativeHom G H (W i))
    (hχ : ∀ i j (Z : Over S) (p : Z ⟶ W i) (q : Z ⟶ W j), p ≫ a i = q ≫ a j →
      restrict G H p (χ i) = restrict G H q (χ j)) :
    ∃ χ' : RelativeHom G H T, ∀ i, restrict G H (a i) χ' = χ i := by
  let 𝒱 : (pullback G.X.hom T.hom).OpenCover :=
    Scheme.Cover.mkOfCovers J (fun i => pullback G.X.hom (W i).hom)
      (fun i => baseChangeProj G (a i)) (fun y => by
        obtain ⟨i, hi⟩ := hcov (pullback.snd G.X.hom T.hom y)
        have hy : y ∈ Set.range (baseChangeProj G (a i)) := by
          rw [range_baseChangeProj]
          exact hi
        obtain ⟨z, hz⟩ := hy
        exact ⟨i, z, hz⟩)
  have hcompat : ∀ i j, pullback.fst (𝒱.f i) (𝒱.f j) ≫ fstMap (χ i) =
      pullback.snd (𝒱.f i) (𝒱.f j) ≫ fstMap (χ j) :=
    fstMap_overlap W a χ hχ
  let m := 𝒱.glueMorphisms (fun i => fstMap (χ i)) hcompat
  have hmi : ∀ i, baseChangeProj G (a i) ≫ m = fstMap (χ i) :=
    fun i => 𝒱.ι_glueMorphisms _ hcompat i
  have hm : m ≫ H.X.hom = pullback.snd G.X.hom T.hom ≫ T.hom := by
    refine 𝒱.hom_ext _ _ fun (i : J) => ?_
    change baseChangeProj G (a i) ≫ m ≫ H.X.hom =
      baseChangeProj G (a i) ≫ pullback.snd G.X.hom T.hom ≫ T.hom
    rw [← Category.assoc, hmi i, fstMap_hom (χ i), baseChangeProj_snd_assoc, Over.w (a i)]
  have hmul : IsPtMul m hm := by
    intro Z x₀ P Q
    apply Over.OverMorphism.ext
    let 𝒵 : Z.OpenCover :=
      Scheme.Cover.mkOfCovers J (fun i => pullback x₀ (a i).left)
        (fun i => pullback.fst x₀ (a i).left) (fun z => by
          obtain ⟨i, hi⟩ := hcov (x₀ z)
          have hz : z ∈ Set.range (pullback.fst x₀ (a i).left) := by
            rw [Scheme.Pullback.range_fst]
            exact hi
          obtain ⟨w, hw⟩ := hz
          exact ⟨i, w, hw⟩)
    refine 𝒵.hom_ext _ _ fun i => ?_
    let e : Over.mk (pullback.snd x₀ (a i).left ≫ (W i).hom) ⟶ Over.mk (x₀ ≫ T.hom) :=
      Over.homMk (pullback.fst x₀ (a i).left) (by
        simp only [Over.mk_hom]
        rw [pullback.condition_assoc, Over.w (a i)])
    have he : e.left ≫ x₀ = pullback.snd x₀ (a i).left ≫ (a i).left := pullback.condition
    have key : e ≫ ptMap m hm x₀ (P * Q) = e ≫ (ptMap m hm x₀ P * ptMap m hm x₀ Q) := by
      rw [comp_ptMap (a i) m hm _ (fstMap_hom (χ i)) (hmi i) x₀ _ e he, MonObj.comp_mul,
        isPtMul_fstMap, MonObj.comp_mul, comp_ptMap (a i) m hm _ (fstMap_hom (χ i)) (hmi i) x₀ _
        e he, comp_ptMap (a i) m hm _ (fstMap_hom (χ i)) (hmi i) x₀ _ e he]
    exact congrArg (fun g => g.left) key
  refine ⟨ofFstMap m hm hmul, fun i => relativeHom_ext _ _ ?_⟩
  change fstMap _ = fstMap _
  rw [fstMap_restrict, fstMap_ofFstMap, hmi]

end Gluing

end Langlands.GroupScheme.Cartier
