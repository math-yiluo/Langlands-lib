import Langlands.AlgebraicGeometry.AlgebraicSpace.UniformFieldPointChartsStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.FieldPointEtaleLift
import Langlands.AlgebraicGeometry.AlgebraicSpace.AffineIntersections
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceProductPointsSurjective
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationPresentation
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationTupleFieldPoints
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationTupleBound

/-!
# Finitely many affine étale charts carrying all field-valued points

Let `X` be a separated, quasi-compact algebraic space over `Spec C`. Choose an étale surjective
atlas `a : U → X` with `U` affine and let `E` be its kernel pair `R = U ×_X U`, an étale
equivalence relation whose relation scheme is affine because `X` is separated. For every `n`,
the free action of the symmetric group on the scheme of distinct related `(n + 1)`-tuples has
an affine quotient `V_n` (Stacks Tag 0BBN), and the map to `X` given by the first coordinate
descends to an étale map `V_n → X`.

A `k`-point `x` of `X` lifts as follows (compare `FieldPointEtaleLift`). The fibre of the atlas
over `x` has a point with values in a finite separable extension `L/k`, and for a finite
Galois extension `K/k` the `k`-embeddings `e : L → K` give pairwise distinct related `K`-points
of `U` over `x`. In some order they form a `K`-point of the distinct tuples of length
`n + 1 = [L : k]`, whose image in `V_n` is invariant under `Gal(K/k)`, because the Galois group
permutes the embeddings. It descends to a `k`-point of `V_n` over `x`. The length is bounded by
the uniform bound `tupleLengthBound` of the relation, so finitely many `V_n` suffice.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology (ringTest RingPoint ringTestMap ringTestMap_comp
  ringTestMap_left)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace UniformFieldPointCharts

open FieldPointEtaleLift

-- The relation `ofKernelPair` is a plain definition, so its fields `U`, `R`, `t`, `s` are
-- `U.left`, `R.left`, `t.left`, `s.left` only up to unfolding it.
set_option backward.isDefEq.respectTransparency false

variable {C : Type u} [CommRing C] {X : AlgebraicSpace (Spec (CommRingCat.of C))}
  {U R : Over (Spec (CommRingCat.of C))} {t s : R ⟶ U}
  {a : (schemeYoneda _).obj U ⟶ X.presheaf}
  (h : IsPullback ((schemeYoneda _).map t) ((schemeYoneda _).map s) a a)
  (ht : Etale t.left) (hs : Etale s.left)

/-- The étale equivalence relation `U ×_X U ⇉ U` of the atlas. -/
abbrev rel : EtaleEquivalenceRelation.{u} :=
  EtaleEquivalenceRelation.ofKernelPair t s a h ht hs

/-- Every coordinate of a related tuple has the same image in the base. -/
theorem tupleProjection_hom (n : ℕ) (i : Fin (n + 1)) :
    (rel h ht hs).tupleProjection n i ≫ U.hom = (rel h ht hs).tupleProjection n 0 ≫ U.hom := by
  obtain ⟨r, hrt, hrs⟩ := (rel h ht hs).tupleProjection_related n i 0
  have e1 : t.left ≫ U.hom = R.hom := Over.w t
  have e2 : s.left ≫ U.hom = R.hom := Over.w s
  rw [← hrt, ← hrs, Category.assoc, Category.assoc]
  exact (congrArg (r ≫ ·) e1).trans (congrArg (r ≫ ·) e2).symm

section Tuples

variable [IsAffine R.left]

instance : IsAffine (rel h ht hs).R := ‹IsAffine R.left›

instance : _root_.AlgebraicGeometry.IsSeparated (rel h ht hs).s := by
  change _root_.AlgebraicGeometry.IsSeparated s.left
  infer_instance

theorem tupleDistinctProjection_hom (n : ℕ) (i : Fin (n + 1)) :
    (rel h ht hs).tupleDistinctProjection n i ≫ U.hom =
      (rel h ht hs).tupleDistinctProjection n 0 ≫ U.hom := by
  change (_ ≫ _) ≫ U.hom = (_ ≫ _) ≫ U.hom
  rw [Category.assoc, Category.assoc, tupleProjection_hom]

/-- The distinct related tuples, over the base through their first coordinate. -/
abbrev tupleOver (n : ℕ) : Over (Spec (CommRingCat.of C)) :=
  Over.mk ((rel h ht hs).tupleDistinctProjection n 0 ≫ U.hom)

/-- A coordinate of the distinct related tuples, as a morphism over the base. -/
def projOver (n : ℕ) (i : Fin (n + 1)) : tupleOver h ht hs n ⟶ U :=
  Over.homMk ((rel h ht hs).tupleDistinctProjection n i) (tupleDistinctProjection_hom h ht hs n i)

@[simp] theorem projOver_left (n : ℕ) (i : Fin (n + 1)) :
    (projOver h ht hs n i).left = (rel h ht hs).tupleDistinctProjection n i := rfl

/-- All coordinates of the distinct related tuples have the same image in `X`. -/
theorem map_projOver (n : ℕ) (i j : Fin (n + 1)) :
    (schemeYoneda _).map (projOver h ht hs n i) ≫ a =
      (schemeYoneda _).map (projOver h ht hs n j) ≫ a := by
  obtain ⟨r, hrt, hrs⟩ := (rel h ht hs).tupleProjection_related n i j
  let r' : tupleOver h ht hs n ⟶ R :=
    Over.homMk (((rel h ht hs).tupleDistinctOpen n).ι ≫ r) (by
      change (_ ≫ r) ≫ R.hom = (_ ≫ _) ≫ U.hom
      rw [← Over.w s, Category.assoc, Category.assoc]
      change _ ≫ r ≫ (rel h ht hs).s ≫ U.hom = _
      rw [← Category.assoc r, hrs, tupleProjection_hom])
  have h1 : projOver h ht hs n i = r' ≫ t := Over.OverMorphism.ext (by
    change _ ≫ _ = (_ ≫ r) ≫ t.left
    rw [Category.assoc]
    exact congrArg (_ ≫ ·) hrt.symm)
  have h2 : projOver h ht hs n j = r' ≫ s := Over.OverMorphism.ext (by
    change _ ≫ _ = (_ ≫ r) ≫ s.left
    rw [Category.assoc]
    exact congrArg (_ ≫ ·) hrs.symm)
  rw [h1, h2, Functor.map_comp_assoc, Functor.map_comp_assoc, h.w]

/-- The permutation action on distinct tuples is an action over the base. -/
theorem act_hom (n : ℕ) (g : EtaleEquivalenceRelation.TuplePermutationGroup.{u} n) :
    (((rel h ht hs).tuplePermutationAction n).act g).hom ≫ (tupleOver h ht hs n).hom =
      (tupleOver h ht hs n).hom := by
  change _ ≫ (rel h ht hs).tupleDistinctProjection n 0 ≫ U.hom = _
  rw [← Category.assoc, (rel h ht hs).tuplePermutationAction_projection n g 0,
    tupleDistinctProjection_hom]
  rfl

theorem actOver_projOver (n : ℕ) (g : EtaleEquivalenceRelation.TuplePermutationGroup.{u} n)
    (i : Fin (n + 1)) :
    FiniteActionChart.actOver (A := tupleOver h ht hs n) _ (act_hom h ht hs n) g ≫
      projOver h ht hs n i = projOver h ht hs n (g.down i) :=
  Over.OverMorphism.ext ((rel h ht hs).tuplePermutationAction_projection n g i)

variable [IsAffine U.left]

instance : IsAffine (rel h ht hs).U := ‹IsAffine U.left›

/-- The affine quotient `V_n` of the distinct tuples by the symmetric group, over the base. -/
abbrev quot (n : ℕ) : Over (Spec (CommRingCat.of C)) :=
  FiniteActionChart.quotientOver (A := tupleOver h ht hs n) _ (act_hom h ht hs n)
    ((rel h ht hs).tupleSymmetricQuotient n)

/-- The quotient map from the distinct tuples to `V_n`, over the base. -/
abbrev quotMap (n : ℕ) : tupleOver h ht hs n ⟶ quot h ht hs n :=
  FiniteActionChart.quotientMapOver (A := tupleOver h ht hs n) _ (act_hom h ht hs n)
    ((rel h ht hs).tupleSymmetricQuotient n)

theorem actOver_quotMap (n : ℕ) (g : EtaleEquivalenceRelation.TuplePermutationGroup.{u} n) :
    FiniteActionChart.actOver (A := tupleOver h ht hs n) _ (act_hom h ht hs n) g ≫
      quotMap h ht hs n = quotMap h ht hs n :=
  Over.OverMorphism.ext (((rel h ht hs).tupleSymmetricQuotient n).invariant g)

/-- The first coordinate descends to an étale map `V_n → X`. -/
theorem exists_chart (ha : IsEtale a) (n : ℕ) :
    ∃ tM : (schemeYoneda _).obj (quot h ht hs n) ⟶ X.presheaf, IsEtale tM ∧
      (schemeYoneda _).map (quotMap h ht hs n) ≫ tM =
        (schemeYoneda _).map (projOver h ht hs n 0) ≫ a := by
  obtain ⟨tM, htM⟩ := FiniteActionChart.exists_desc (A := tupleOver h ht hs n) _
    (act_hom h ht hs n) ((rel h ht hs).tupleSymmetricQuotient n) X.toSheaf
    ((schemeYoneda _).map (projOver h ht hs n 0) ≫ a)
    (fun g => by rw [← Functor.map_comp_assoc, actOver_projOver, map_projOver])
  refine ⟨tM, ?_, htM⟩
  apply isEtale_of_finiteEtale_comp X.hasRepresentableDiagonal (quotMap h ht hs n)
  rw [htM]
  exact IsEtale.comp (isEtale_map _
    (inferInstanceAs (Etale ((rel h ht hs).tupleDistinctProjection n 0)))) ha

/-- Every field-valued point of `X` lifts to a field-valued point of some `V_n`, with
`n` below the uniform tuple bound. -/
theorem exists_point (ha : IsEtale a) (has : IsSurjective a)
    (tM : ∀ n, (schemeYoneda _).obj (quot h ht hs n) ⟶ X.presheaf)
    (hcomp : ∀ n, (schemeYoneda _).map (quotMap h ht hs n) ≫ tM n =
      (schemeYoneda _).map (projOver h ht hs n 0) ≫ a)
    {k : Type u} [Field k] [Algebra C k] (x : RingPoints C X k) :
    ∃ n, n < (rel h ht hs).tupleLengthBound ∧ ∃ u : RingPoint C (quot h ht hs n) k,
      RingPoints.map (AlgebraicSpace.homMk (tM n) : (schemeToSpace _).obj (quot h ht hs n) ⟶ X)
        ((schemeRingPointsEquiv C _ k).symm u) = x := by
  -- the fibre of the atlas over `x`, a nonempty scheme étale over `Spec k`
  let hr := ha.representable
  let xh : (schemeYoneda (Spec (CommRingCat.of C))).obj (ringTest C k) ⟶ X.presheaf :=
    uliftYonedaEquiv.symm x
  let P := hr.pullback xh
  let p : P ⟶ ringTest C k := hr.snd xh
  let q : P ⟶ U := Functor.relativelyRepresentable.fst' hr xh
  have hsq : IsPullback ((schemeYoneda _).map q) ((schemeYoneda _).map p) a xh :=
    Functor.relativelyRepresentable.isPullback' hr xh
  have hpe : Etale p.left := ha.projection xh _ p hsq
  have hps : Surjective p.left := has.projection xh _ p hsq
  let T : Over (Spec (CommRingCat.of k)) := Over.mk p.left
  have : Etale T.hom := hpe
  have : Nonempty T.left := by
    obtain ⟨y⟩ : Nonempty (Spec (CommRingCat.of k)) := inferInstance
    obtain ⟨z, -⟩ := hps.surj y
    exact ⟨z⟩
  -- a point of the fibre with values in a finite separable `L`, and a Galois extension `K`
  obtain ⟨L, _, _, hL, hLs, w₀, hw₀⟩ := exists_separable_point_mono T
  have := hL
  have := hLs
  have := hw₀
  obtain ⟨K, _, _, hK, hKg, hEfin, hEne, -⟩ := exists_faithful_galois (k := k) (L := L)
  have := hK
  have := hKg
  have := hEfin
  have := hEne
  let _ : Algebra C L := ((algebraMap k L).comp (algebraMap C k)).toAlgebra
  have : IsScalarTower C k L := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let _ : Algebra C K := ((algebraMap k K).comp (algebraMap C k)).toAlgebra
  have : IsScalarTower C k K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let w₀l : (ringTest C L).left ⟶ P.left := w₀.left
  have hw₀p : w₀l ≫ p.left = (fieldTestMap (C := C) (k := k) (K := L)).left := Over.w w₀
  have : Mono w₀l := hw₀
  let w₁ : ringTest C L ⟶ P := Over.homMk w₀l (by
    rw [← Over.w p, ← Category.assoc, hw₀p]
    exact Over.w (fieldTestMap (C := C) (k := k) (K := L)))
  have hw₁p : w₁ ≫ p = fieldTestMap (C := C) (k := k) (K := L) := Over.OverMorphism.ext hw₀p
  -- the `K`-points of `U` given by the embeddings `L → K`
  let vE : (L →ₐ[k] K) → (ringTest C K ⟶ U) :=
    fun e => (ringTestMap C (e.restrictScalars C) ≫ w₁) ≫ q
  have hwp : ∀ e : L →ₐ[k] K, (ringTestMap C (e.restrictScalars C) ≫ w₁) ≫ p =
      fieldTestMap (C := C) (k := k) (K := K) := by
    intro e
    rw [Category.assoc, hw₁p, ← ringTestMap_comp]
    congr 1
    ext c
    exact e.commutes c
  have hvE : ∀ e, (schemeYoneda _).map (vE e) ≫ a =
      (schemeYoneda _).map (fieldTestMap (C := C) (k := k) (K := K)) ≫ xh := fun e => by
    change (schemeYoneda _).map ((ringTestMap C (e.restrictScalars C) ≫ w₁) ≫ q) ≫ a = _
    rw [Functor.map_comp_assoc, hsq.w, ← Functor.map_comp_assoc, hwp]
  have hvinj : Function.Injective vE := by
    intro e e' hee
    have hw : ringTestMap C (e.restrictScalars C) ≫ w₁ =
        ringTestMap C (e'.restrictScalars C) ≫ w₁ :=
      Functor.relativelyRepresentable.hom_ext' hr hee (by rw [hwp, hwp])
    have h1 : (ringTestMap C (e.restrictScalars C)).left ≫ w₀l =
        (ringTestMap C (e'.restrictScalars C)).left ≫ w₀l := congrArg CommaMorphism.left hw
    rw [cancel_mono, ringTestMap_left, ringTestMap_left] at h1
    have h2 := Spec.map_injective h1
    ext y
    exact congrArg (fun φ => φ.hom y) h2
  have hγv : ∀ (γ : K ≃ₐ[k] K) (e : L →ₐ[k] K),
      (galoisAction (C := C) (k := k)).act γ ≫ vE e = vE ((γ : K →ₐ[k] K).comp e) := by
    intro γ e
    have hcomp' : ringTestMap C ((γ : K →ₐ[k] K).restrictScalars C) ≫
        ringTestMap C (e.restrictScalars C) =
          ringTestMap C (((γ : K →ₐ[k] K).comp e).restrictScalars C) := by
      rw [← ringTestMap_comp]
      exact congrArg (ringTestMap C) (AlgHom.ext fun _ => rfl)
    change ringTestMap C ((γ : K →ₐ[k] K).restrictScalars C) ≫
        (ringTestMap C (e.restrictScalars C) ≫ w₁) ≫ q =
      (ringTestMap C (((γ : K →ₐ[k] K).comp e).restrictScalars C) ≫ w₁) ≫ q
    rw [← hcomp', Category.assoc, Category.assoc, Category.assoc]
  -- an enumeration of the embeddings, and the distinct related tuple they form
  obtain ⟨m, hm⟩ : ∃ m, Nat.card (L →ₐ[k] K) = m + 1 :=
    Nat.exists_eq_succ_of_ne_zero (Nat.card_pos (α := L →ₐ[k] K)).ne'
  let e₀ : Fin (m + 1) ≃ (L →ₐ[k] K) := (Finite.equivFinOfCardEq hm).symm
  let E := rel h ht hs
  let c : Fin (m + 1) → (Spec (.of K) ⟶ E.U) := fun i => (vE (e₀ i)).left
  have hrelc : ∀ i j, ∃ r : Spec (.of K) ⟶ E.R, r ≫ E.t = c i ∧ r ≫ E.s = c j := by
    intro i j
    obtain ⟨r, hrt, hrs⟩ := EtaleEquivalenceRelation.exists_lift_of_isPullback h
      (vE (e₀ i)) (vE (e₀ j)) (by rw [hvE, hvE])
    exact ⟨r.left, congrArg CommaMorphism.left hrt, congrArg CommaMorphism.left hrs⟩
  have hcinj : Function.Injective c := by
    intro i j hij
    exact e₀.injective (hvinj (Over.OverMorphism.ext hij))
  let z := E.tupleDistinctFieldLift m K c hrelc hcinj
  have hmN : m < E.tupleLengthBound := E.tupleDistinct_fieldPoint_length_le m K z
  have hz : ∀ i, z ≫ E.tupleDistinctProjection m i = c i :=
    E.tupleDistinctFieldLift_projection m K c hrelc hcinj
  let zO : ringTest C K ⟶ tupleOver h ht hs m := Over.homMk z (by
    change z ≫ E.tupleDistinctProjection m 0 ≫ U.hom = (ringTest C K).hom
    rw [← Category.assoc, hz]
    exact Over.w (vE (e₀ 0)))
  have hzO : ∀ i, zO ≫ projOver h ht hs m i = vE (e₀ i) := fun i =>
    Over.OverMorphism.ext (hz i)
  -- the Galois group permutes the coordinates
  let permE : (K ≃ₐ[k] K) → Equiv.Perm (L →ₐ[k] K) := fun γ =>
    { toFun := fun e => (γ : K →ₐ[k] K).comp e
      invFun := fun e => (γ.symm : K →ₐ[k] K).comp e
      left_inv := fun e => by ext y; simp
      right_inv := fun e => by ext y; simp }
  let π : (K ≃ₐ[k] K) → Equiv.Perm (Fin (m + 1)) := fun γ =>
    (e₀.trans (permE γ)).trans e₀.symm
  have hπ : ∀ γ i, e₀ (π γ i) = (γ : K →ₐ[k] K).comp (e₀ i) := fun γ i => by
    simp [π, permE]
  have hzγ : ∀ γ : K ≃ₐ[k] K, (galoisAction (C := C) (k := k)).act γ ≫ zO =
      zO ≫ FiniteActionChart.actOver (A := tupleOver h ht hs m) _ (act_hom h ht hs m)
        (ULift.up (π γ)) := by
    intro γ
    have key : ∀ i, ((galoisAction (C := C) (k := k)).act γ ≫ zO) ≫ projOver h ht hs m i =
        (zO ≫ FiniteActionChart.actOver (A := tupleOver h ht hs m) _ (act_hom h ht hs m)
          (ULift.up (π γ))) ≫ projOver h ht hs m i := by
      intro i
      rw [Category.assoc, hzO, hγv, Category.assoc, actOver_projOver, hzO, hπ]
    apply Over.OverMorphism.ext
    apply E.tupleDistinct_hom_ext m
    intro i
    exact congrArg CommaMorphism.left (key i)
  -- the invariant point of `V_m`, its descent to `k`, and its image in `X`
  let w : ringTest C K ⟶ quot h ht hs m := zO ≫ quotMap h ht hs m
  have hw : ∀ γ : K ≃ₐ[k] K, (galoisAction (C := C) (k := k)).act γ ≫ w = w := by
    intro γ
    change (galoisAction (C := C) (k := k)).act γ ≫ zO ≫ quotMap h ht hs m = zO ≫ quotMap h ht hs m
    rw [← Category.assoc, hzγ, Category.assoc, actOver_quotMap]
  obtain ⟨u, hu⟩ := exists_desc_of_galois_invariant w hw
  have hfinal : (schemeYoneda _).map w ≫ tM m =
      (schemeYoneda _).map (fieldTestMap (C := C) (k := k) (K := K)) ≫ xh := by
    change (schemeYoneda _).map (zO ≫ quotMap h ht hs m) ≫ tM m = _
    rw [Functor.map_comp_assoc, hcomp, ← Functor.map_comp_assoc, hzO, hvE]
  refine ⟨m, hmN, u, ?_⟩
  apply changeRing_injective (K := K) X
  have e₁ : RingPoints.map (AlgebraicSpace.homMk (tM m) : (schemeToSpace _).obj (quot h ht hs m) ⟶ X)
      ((schemeRingPointsEquiv C (quot h ht hs m) k).symm u) =
        uliftYonedaEquiv ((schemeYoneda _).map u ≫ tM m) := by
    rw [uliftYonedaEquiv_comp, uliftYonedaEquiv_uliftYoneda_map]
    rfl
  have e₂ : x = uliftYonedaEquiv
      (uliftYonedaEquiv.symm x : (schemeYoneda _).obj (ringTest C k) ⟶ X.presheaf) :=
    (Equiv.apply_symm_apply _ _).symm
  rw [e₁, e₂]
  change X.presheaf.map (fieldTestMap (C := C) (k := k) (K := K)).op _ =
    X.presheaf.map (fieldTestMap (C := C) (k := k) (K := K)).op _
  rw [uliftYonedaEquiv_naturality, uliftYonedaEquiv_naturality]
  congr 1
  rw [Quiver.Hom.unop_op, ← Functor.map_comp_assoc, hu]
  exact hfinal

end Tuples

end UniformFieldPointCharts

open UniformFieldPointCharts in
/-- **Uniform affine étale charts for field-valued points.** A separated, quasi-compact
algebraic space over `Spec C` has finitely many affine schemes with étale maps to it through
which every field-valued point lifts. -/
theorem uniformFieldPointCharts : UniformFieldPointChartsStatement.{u} := by
  intro C _ X hXsep hXqc
  -- an affine atlas: a finite disjoint union of affine opens of a quasi-compact atlas
  obtain ⟨W, aW, haW, hsW, hW⟩ := hXqc.exists_atlas
  let 𝒰 := W.left.affineCover.finiteSubcover
  let J : ∐ 𝒰.X ⟶ W.left := Sigma.desc 𝒰.f
  have : IsZariskiLocalAtSource @Etale.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale.{u})
  have hJ : Etale J := IsZariskiLocalAtSource.sigmaDesc fun _ => inferInstance
  have hJs : Surjective J := by
    constructor
    intro y
    obtain ⟨i, y', rfl⟩ := 𝒰.exists_eq y
    exact ⟨Sigma.ι 𝒰.X i y', by rw [← Scheme.Hom.comp_apply, Sigma.ι_comp_desc]⟩
  let U : Over (Spec (CommRingCat.of C)) := Over.mk (J ≫ W.hom)
  let j : U ⟶ W := Over.homMk J
  have : ∀ i, IsAffine (𝒰.X i) := fun _ => inferInstance
  have : IsAffine U.left := inferInstanceAs (IsAffine (∐ 𝒰.X))
  let a : (schemeYoneda _).obj U ⟶ X.presheaf := (schemeYoneda _).map j ≫ aW
  have ha : IsEtale a := (isEtale_map j hJ).comp haW
  have has : IsSurjective a :=
    SpaceProductPoints.IsSurjective.comp (SpaceProductPoints.isSurjective_map j hJs) hsW
  -- its kernel pair, with affine relation scheme because `X` is separated
  obtain ⟨R, t, s, hpb, ht, hs⟩ := exists_kernelPair ha
  have : IsAffine R.left := isAffine_of_isPullback_of_closedDiagonal hXsep a a t s hpb
  choose tM htM hcomp using exists_chart hpb ht hs ha
  refine ⟨(rel hpb ht hs).tupleLengthBound, fun i => quot hpb ht hs i.val,
    fun i => AlgebraicSpace.homMk (tM i.val), fun i => ⟨inferInstance, htM i.val⟩, ?_⟩
  intro k _ _ x
  obtain ⟨n, hn, u, hu⟩ := exists_point hpb ht hs ha has tM hcomp x
  exact ⟨⟨n, hn⟩, u, hu⟩

end Langlands.AlgebraicGeometry.AlgebraicSpace
