import Langlands.GroupScheme.Torus.EtalePermutationWeilCharts
import Langlands.GroupScheme.Torus.EtalePermutationAtlasRefinement
import Langlands.GroupScheme.Torus.AffineWeilPoints

/-! # Compatibility of invariant coefficients and Weil charts -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

namespace Langlands.GroupScheme.LocalCoefficientReindexing.Datum

variable {S : Scheme.{u}} {I J : Type u}

/-- If all local data describe one globally constant unit permutation, the
glued coefficient equivalence is that same reindexing map. -/
theorem equiv_eq_constant (A : LocalCoefficientReindexing.Datum S I J) (σ : J ≃ I)
    (F : ∀ T : Over S, (I → (Γ(T.left, ⊤))ˣ) → (J → (Γ(T.left, ⊤))ˣ))
    (hA : ∀ a (T : Over S), Set.range T.hom ⊆ A.opens a →
      ∀ (z : I → (Γ(T.left, ⊤))ˣ) (j : J), F T z j = z (A.permutation a j))
    (hσ : ∀ (T : Over S) (z : I → (Γ(T.left, ⊤))ˣ) (j : J), F T z j = z (σ j)) :
    A.equiv = splitTorus.coefficientReindex S σ := by
  let B : LocalCoefficientReindexing.Datum S I J :=
    { Index := PUnit
      opens := fun _ => ⊤
      covers := by simp
      permutation := fun _ => σ
      agree := fun _ _ _ => rfl }
  have hB : B.equiv = splitTorus.coefficientReindex S σ := by
    ext z j
    simpa [B, restrict, splitTorus.coefficientReindex] using B.equiv_restrict z j PUnit.unit
  rw [← hB]
  exact A.equiv_eq_of_unitTransform B F hA (fun _ T _ z j => hσ T z j)

end Langlands.GroupScheme.LocalCoefficientReindexing.Datum

namespace Langlands.GroupScheme.EtalePermutationAtlas

variable {S U U' V : Scheme.{u}} {D : GroupScheme S}
  {I J : Type u} [Finite I] [Finite J]

/-- Global normalized agreement gives the formula for the original chart unit
transition on every relative test. -/
theorem transitionUnits_eq_of_agreeBy (f : U ⟶ S) (g : U' ⟶ S)
    (e : (GroupScheme.baseChange f).obj D ≅ splitTorus U I)
    (e' : (GroupScheme.baseChange g).obj D ≅ splitTorus U' J)
    (q : V ⟶ U) (q' : V ⟶ U') (r : V ⟶ S)
    (h : q ≫ f = r) (h' : q' ≫ g = r) (σ : J ≃ I)
    (H : AgreeBy f g e e' q q' r h h' σ)
    (T : Over V) (z : I → (Γ(T.left, ⊤))ˣ) (j : J) :
    transitionUnits f g e e' q q' (h.trans h'.symm) T z j = z (σ j) := by
  let x := (chartPointsEquiv f e (T.hom ≫ q)).symm z
  have hx : x.left ≫ D.X.hom = T.hom ≫ r :=
    (Over.w x).trans (by change (T.hom ≫ q) ≫ f = T.hom ≫ r; rw [Category.assoc, h])
  have hc := H.coordinates f g e e' q q' r h h' σ T x.left hx j
  change coordinates g e' (T.hom ≫ q') x.left _ j = _
  exact hc.trans (congrFun ((chartPointsEquiv f e (T.hom ≫ q)).apply_symm_apply z) (σ j))

/-- On a base where the original charts agree by one permutation, their actual
coefficient equivalence is exactly that permutation's reindexing. -/
theorem coefficientEquivAlong_eq_reindex (f : U ⟶ S) (g : U' ⟶ S)
    (e : (GroupScheme.baseChange f).obj D ≅ splitTorus U I)
    (e' : (GroupScheme.baseChange g).obj D ≅ splitTorus U' J)
    (H : LocallyPermutes f g e e')
    (q : V ⟶ U) (q' : V ⟶ U') (r : V ⟶ S)
    (h : q ≫ f = r) (h' : q' ≫ g = r) (σ : J ≃ I)
    (Hσ : AgreeBy f g e e' q q' r h h' σ) :
    (H.coefficientDatumAlong f g e e' q q' (h.trans h'.symm)).equiv =
      splitTorus.coefficientReindex V σ := by
  apply LocalCoefficientReindexing.Datum.equiv_eq_constant _ σ
    (transitionUnits f g e e' q q' (h.trans h'.symm))
  · exact H.coefficientDatumAlong_formula f g e e' q q' (h.trans h'.symm)
  · exact transitionUnits_eq_of_agreeBy f g e e' q q' r h h' σ Hσ

end Langlands.GroupScheme.EtalePermutationAtlas

namespace Langlands.GroupScheme.FiniteAffinePermutationCoefficients

open EtalePermutationAtlas
open Langlands.AlgebraicGeometry

variable {S : Scheme.{u}} [IsAffine S] {D : GroupScheme S}
  {α : Type u} [Finite α] (U : α → Scheme.{u}) [∀ a, IsAffine (U a)]
  (f : ∀ a, U a ⟶ S) (I : α → Type u) [∀ a, Finite (I a)]
  (e : ∀ a, (GroupScheme.baseChange (f a)).obj D ≅ splitTorus (U a) (I a))
  (H : ∀ a b, LocallyPermutes (f a) (f b) (e a) (e b))

/-- Every original local chart permutation also permutes the values of every
invariant coefficient on that open. -/
theorem invariant_local_permutation (a b : α) (O : (pullback (f a) (f b)).Opens)
    (σ : I b ≃ I a)
    (Hσ : AgreeBy (f a) (f b) (e a) (e b)
      (O.ι ≫ pullback.fst (f a) (f b)) (O.ι ≫ pullback.snd (f a) (f b))
      (O.ι ≫ pullback.fst (f a) (f b) ≫ f a)
      (by simp only [Category.assoc])
      (by simp only [Category.assoc, pullback.condition]) σ)
    (c : (coaction U f I e H).invariants) (j : I b) :
    (O.ι ≫ pullback.snd (f a) (f b)).appTop.hom (c.val b j) =
      (O.ι ≫ pullback.fst (f a) (f b)).appTop.hom (c.val a (σ j)) := by
  have he := coefficientEquivAlong_eq_reindex (f a) (f b) (e a) (e b) (H a b)
    (O.ι ≫ pullback.fst (f a) (f b)) (O.ι ≫ pullback.snd (f a) (f b))
    (O.ι ≫ pullback.fst (f a) (f b) ≫ f a) _ _ σ Hσ
  have hn := (H a b).coefficientEquivAlong_naturality (f a) (f b) (e a) (e b)
    (pullback.fst (f a) (f b)) (pullback.snd (f a) (f b)) pullback.condition O.ι
    (fun i => (pullback.fst (f a) (f b)).appTop.hom (c.val a i)) j
  rw [he] at hn
  change O.ι.appTop.hom ((pullback.fst (f a) (f b)).appTop.hom (c.val a (σ j))) =
    O.ι.appTop.hom (overlapEquiv U f I e H a b
      (fun i => (pullback.fst (f a) (f b)).appTop.hom (c.val a i)) j) at hn
  rw [invariant_overlap] at hn
  simpa only [appTop_comp_apply] using hn.symm

section PointCharts

variable [∀ a, Flat (f a)] [Surjective (Sigma.desc f)]

/-- The local invariant decomposition on a relative test, with the actual
structure map's action on global sections. -/
def chartTensorEquiv (a : α) (T : Over (U a)) :
    (coaction U f I e H).invariants ⊗[Γ(S, ⊤)]
        AffineWeilPoints.sections S ((Over.map (f a)).obj T) ≃+*
      (I a → Γ(T.left, ⊤)) := by
  letI (a : α) := (f a).appTop.hom.toAlgebra
  letI : Algebra Γ(U a, ⊤) (AffineWeilPoints.sections S ((Over.map (f a)).obj T)) :=
    T.hom.appTop.hom.toAlgebra
  haveI : IsScalarTower Γ(S, ⊤) Γ(U a, ⊤)
      (AffineWeilPoints.sections S ((Over.map (f a)).obj T)) := by
    apply IsScalarTower.of_algebraMap_eq'
    ext r
    change (T.hom ≫ f a).appTop.hom r = T.hom.appTop.hom ((f a).appTop.hom r)
    rw [Scheme.Hom.comp_appTop]
    rfl
  exact WeilCoefficientTensor.equiv Γ(S, ⊤) Γ(U a, ⊤) (coaction U f I e H).invariants
    (AffineWeilPoints.sections S ((Over.map (f a)).obj T)) (I a) (localDescentEquiv U f I e H a)

@[simp] theorem chartTensorEquiv_tmul (a : α) (T : Over (U a))
    (c : (coaction U f I e H).invariants)
    (t : AffineWeilPoints.sections S ((Over.map (f a)).obj T)) (i : I a) :
    chartTensorEquiv U f I e H a T (c ⊗ₜ[Γ(S, ⊤)] t) i =
      T.hom.appTop.hom (c.val a i) * (show Γ(T.left, ⊤) from t) := by
  letI (a : α) := (f a).appTop.hom.toAlgebra
  letI : Algebra Γ(U a, ⊤) (AffineWeilPoints.sections S ((Over.map (f a)).obj T)) :=
    T.hom.appTop.hom.toAlgebra
  haveI : IsScalarTower Γ(S, ⊤) Γ(U a, ⊤)
      (AffineWeilPoints.sections S ((Over.map (f a)).obj T)) := by
    apply IsScalarTower.of_algebraMap_eq'
    ext r
    change (T.hom ≫ f a).appTop.hom r = T.hom.appTop.hom ((f a).appTop.hom r)
    rw [Scheme.Hom.comp_appTop]
    rfl
  change WeilCoefficientTensor.equiv Γ(S, ⊤) Γ(U a, ⊤) (coaction U f I e H).invariants
    (AffineWeilPoints.sections S ((Over.map (f a)).obj T)) (I a)
      (localDescentEquiv U f I e H a) (c ⊗ₜ[Γ(S, ⊤)] t) i = _
  rw [WeilCoefficientTensor.equiv_tmul Γ(S, ⊤) Γ(U a, ⊤) (coaction U f I e H).invariants
    (AffineWeilPoints.sections S ((Over.map (f a)).obj T)) (I a)
      (localDescentEquiv U f I e H a) c t]
  change T.hom.appTop.hom ((1 : Γ(U a, ⊤)) * c.val a i) * (show Γ(T.left, ⊤) from t) = _
  rw [one_mul]

set_option maxHeartbeats 800000 in
/-- The chart tensor model is natural for every relative test morphism. -/
theorem chartTensorEquiv_naturality (a : α) {T T' : Over (U a)} (m : T' ⟶ T)
    (z : (coaction U f I e H).invariants ⊗[Γ(S, ⊤)]
      AffineWeilPoints.sections S ((Over.map (f a)).obj T)) :
    chartTensorEquiv U f I e H a T'
        (Algebra.TensorProduct.lTensor (S := (coaction U f I e H).invariants)
          (coaction U f I e H).invariants (AffineWeilPoints.sectionsMap S ((Over.map (f a)).map m)) z) =
      fun i => m.left.appTop.hom (chartTensorEquiv U f I e H a T z i) := by
  induction z using TensorProduct.inductionOn with
  | tmul c t =>
    funext i
    simp only [Algebra.TensorProduct.map_tmul, chartTensorEquiv_tmul]
    change T'.hom.appTop.hom (c.val a i) * m.left.appTop.hom t =
      m.left.appTop.hom (T.hom.appTop.hom (c.val a i) * (show Γ(T.left, ⊤) from t))
    rw [map_mul]
    congr 1
    have hw := congrArg (fun k : T'.left ⟶ U a => k.appTop.hom (c.val a i)) (Over.w m)
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp,
      Function.comp_apply] using hw.symm
  | add x y hx hy =>
    funext i
    simp only [map_add, Pi.add_apply, hx, hy]

/-- The actual Weil points in chart coordinates using the raw section scalars. -/
def weilCoordinatePoints (a : α) (T : Over (U a)) :
    (T ⟶ ((GroupScheme.baseChange (f a)).obj (weilGroup U f I e H)).X) ≃*
      (I a → (Γ(T.left, ⊤))ˣ) :=
  (GroupScheme.baseChangePointsEquiv (f a) (weilGroup U f I e H) T).trans
    ((AffineWeilPoints.pointsEquiv S (coaction U f I e H).invariants ((Over.map (f a)).obj T)).trans
      ((Units.mapEquiv (chartTensorEquiv U f I e H a T).toMulEquiv).trans MulEquiv.piUnits))

set_option maxHeartbeats 800000 in
theorem weilCoordinatePoints_naturality (a : α) {T T' : Over (U a)} (m : T' ⟶ T)
    (x : T ⟶ ((GroupScheme.baseChange (f a)).obj (weilGroup U f I e H)).X) :
    weilCoordinatePoints U f I e H a T' (m ≫ x) =
      splitTorus.unitsRestrict (I a) m (weilCoordinatePoints U f I e H a T x) := by
  simp only [weilCoordinatePoints, MulEquiv.trans_apply,
    GroupScheme.baseChangePointsEquiv_naturality]
  let y : (Over.map (f a)).obj T ⟶
      (AffineWeilPoints.group S (coaction U f I e H).invariants).X :=
    GroupScheme.baseChangePointsEquiv (f a) (weilGroup U f I e H) T x
  let u := AffineWeilPoints.pointsEquiv S (coaction U f I e H).invariants
    ((Over.map (f a)).obj T) y
  change MulEquiv.piUnits ((Units.mapEquiv (chartTensorEquiv U f I e H a T').toMulEquiv)
      (AffineWeilPoints.pointsEquiv S (coaction U f I e H).invariants ((Over.map (f a)).obj T')
        ((Over.map (f a)).map m ≫ y))) =
    splitTorus.unitsRestrict (I a) m
      (MulEquiv.piUnits ((Units.mapEquiv (chartTensorEquiv U f I e H a T).toMulEquiv) u))
  have hn := AffineWeilPoints.pointsEquiv_naturality S (coaction U f I e H).invariants
    ((Over.map (f a)).map m) y
  rw [hn]
  funext i
  apply Units.ext
  exact congrFun (chartTensorEquiv_naturality U f I e H a m u) i

/-- The actual split Weil chart with explicit raw section coordinate formulas. -/
def coordinateWeilChart (a : α) :
    (GroupScheme.baseChange (f a)).obj (weilGroup U f I e H) ≅ splitTorus (U a) (I a) :=
  isoOfPointModels (fun T : Over (U a) => I a → (Γ(T.left, ⊤))ˣ)
    (fun m => splitTorus.unitsRestrict (I a) m)
    (weilCoordinatePoints U f I e H a) (splitTorus.pointsEquiv (I a))
    (fun m x => weilCoordinatePoints_naturality U f I e H a m x)
    (fun m x => splitTorus.pointsEquiv_naturality (I a) m x)

theorem coordinateWeilChart_hom_points (a : α) (T : Over (U a))
    (x : T ⟶ ((GroupScheme.baseChange (f a)).obj (weilGroup U f I e H)).X) :
    splitTorus.pointsEquiv (I a) T (x ≫ (coordinateWeilChart U f I e H a).hom.hom.hom) =
      weilCoordinatePoints U f I e H a T x :=
  isoOfPointModels_hom (fun T : Over (U a) => I a → (Γ(T.left, ⊤))ˣ)
    (fun m => splitTorus.unitsRestrict (I a) m)
    (weilCoordinatePoints U f I e H a) (splitTorus.pointsEquiv (I a))
    (fun m x => weilCoordinatePoints_naturality U f I e H a m x)
    (fun m x => splitTorus.pointsEquiv_naturality (I a) m x) T x

/-- Evaluate a chart tensor model after specifying an equal common test base. -/
def chartTensorAlong (a : α) {T : Scheme.{u}} (t : T ⟶ U a) (s : T ⟶ S)
    (h : t ≫ f a = s) :
    (coaction U f I e H).invariants ⊗[Γ(S, ⊤)] AffineWeilPoints.sections S (Over.mk s) ≃+*
      (I a → Γ(T, ⊤)) := by
  subst s
  exact chartTensorEquiv U f I e H a (Over.mk t)

@[simp] theorem chartTensorAlong_tmul (a : α) {T : Scheme.{u}}
    (t : T ⟶ U a) (s : T ⟶ S) (h : t ≫ f a = s)
    (c : (coaction U f I e H).invariants) (v : AffineWeilPoints.sections S (Over.mk s))
    (i : I a) :
    chartTensorAlong U f I e H a t s h (c ⊗ₜ[Γ(S, ⊤)] v) i =
      t.appTop.hom (c.val a i) * (show Γ(T, ⊤) from v) := by
  subst s
  exact chartTensorEquiv_tmul U f I e H a (Over.mk t) c v i

set_option maxHeartbeats 800000 in
/-- The original Weil-group point over a common test base is evaluated by the
explicit chart tensor model. -/
theorem coordinateWeilChart_coordinates (a : α) {T : Scheme.{u}}
    (t : T ⟶ U a) (s : T ⟶ S) (h : t ≫ f a = s)
    (x : Over.mk s ⟶ (weilGroup U f I e H).X) :
    coordinates (f a) (coordinateWeilChart U f I e H a) t x.left
        ((Over.w x).trans h.symm) =
      MulEquiv.piUnits (Units.map (chartTensorAlong U f I e H a t s h).toMonoidHom
        (AffineWeilPoints.pointsEquiv S (coaction U f I e H).invariants (Over.mk s) x)) := by
  subst s
  change splitTorus.pointsEquiv (I a) (Over.mk t)
      (((GroupScheme.baseChangePointsEquiv (f a) (weilGroup U f I e H) (Over.mk t)).symm x) ≫
        (coordinateWeilChart U f I e H a).hom.hom.hom) = _
  rw [coordinateWeilChart_hom_points]
  simp only [weilCoordinatePoints, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  rfl

set_option maxHeartbeats 800000 in
/-- The original local permutation also permutes the invariant tensor
coordinates on every relative test of that overlap open. -/
theorem chartTensorAlong_local_permutation
    (a b : α) (O : (pullback (f a) (f b)).Opens) (σ : I b ≃ I a)
    (Hσ : AgreeBy (f a) (f b) (e a) (e b)
      (O.ι ≫ pullback.fst (f a) (f b)) (O.ι ≫ pullback.snd (f a) (f b))
      (O.ι ≫ pullback.fst (f a) (f b) ≫ f a)
      (by simp only [Category.assoc])
      (by simp only [Category.assoc, pullback.condition]) σ)
    (T : Over (O : Scheme.{u}))
    (z : (coaction U f I e H).invariants ⊗[Γ(S, ⊤)]
      AffineWeilPoints.sections S (Over.mk (T.hom ≫ O.ι ≫ pullback.fst (f a) (f b) ≫ f a)))
    (j : I b) :
    chartTensorAlong U f I e H b (T.hom ≫ (O.ι ≫ pullback.snd (f a) (f b)))
        (T.hom ≫ O.ι ≫ pullback.fst (f a) (f b) ≫ f a)
        (by simp only [Category.assoc, pullback.condition]) z j =
      chartTensorAlong U f I e H a (T.hom ≫ (O.ι ≫ pullback.fst (f a) (f b)))
        (T.hom ≫ O.ι ≫ pullback.fst (f a) (f b) ≫ f a)
        (by simp only [Category.assoc]) z (σ j) := by
  induction z using TensorProduct.inductionOn with
  | tmul c v =>
    rw [chartTensorAlong_tmul, chartTensorAlong_tmul]
    congr 1
    have hc := congrArg T.hom.appTop.hom (invariant_local_permutation U f I e H a b O σ Hσ c j)
    simpa only [appTop_comp_apply, Category.assoc] using hc
  | add x y hx hy =>
    simp only [map_add, Pi.add_apply, hx, hy]

set_option maxHeartbeats 800000 in
/-- Each original local coordinate permutation holds for the actual Weil
charts on the same open and every relative test. -/
theorem weil_agreeBy_of_original
    (a b : α) (O : (pullback (f a) (f b)).Opens) (σ : I b ≃ I a)
    (Hσ : AgreeBy (f a) (f b) (e a) (e b)
      (O.ι ≫ pullback.fst (f a) (f b)) (O.ι ≫ pullback.snd (f a) (f b))
      (O.ι ≫ pullback.fst (f a) (f b) ≫ f a)
      (by simp only [Category.assoc])
      (by simp only [Category.assoc, pullback.condition]) σ) :
    AgreeBy (f a) (f b) (coordinateWeilChart U f I e H a) (coordinateWeilChart U f I e H b)
      (O.ι ≫ pullback.fst (f a) (f b)) (O.ι ≫ pullback.snd (f a) (f b))
      (O.ι ≫ pullback.fst (f a) (f b) ≫ f a)
      (by simp only [Category.assoc])
      (by simp only [Category.assoc, pullback.condition]) σ := by
  apply AgreeBy.of_coordinates
  intro T x hx j
  let s := T.hom ≫ O.ι ≫ pullback.fst (f a) (f b) ≫ f a
  let p : Over.mk s ⟶ (weilGroup U f I e H).X := Over.homMk x hx
  have ha : (T.hom ≫ (O.ι ≫ pullback.fst (f a) (f b))) ≫ f a = s := by
    simp only [s, Category.assoc]
  have hb : (T.hom ≫ (O.ι ≫ pullback.snd (f a) (f b))) ≫ f b = s := by
    simp only [s, Category.assoc, pullback.condition]
  change coordinates (f b) (coordinateWeilChart U f I e H b)
      (T.hom ≫ (O.ι ≫ pullback.snd (f a) (f b))) p.left _ j =
    coordinates (f a) (coordinateWeilChart U f I e H a)
      (T.hom ≫ (O.ι ≫ pullback.fst (f a) (f b))) p.left _ (σ j)
  rw [coordinateWeilChart_coordinates U f I e H b _ s hb p,
    coordinateWeilChart_coordinates U f I e H a _ s ha p]
  apply Units.ext
  exact chartTensorAlong_local_permutation U f I e H a b O σ Hσ T
    (AffineWeilPoints.pointsEquiv S (coaction U f I e H).invariants (Over.mk s) p) j

end PointCharts
end Langlands.GroupScheme.FiniteAffinePermutationCoefficients
