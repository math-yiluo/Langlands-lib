import Langlands.AlgebraicGeometry.PointTopology.ProductRingPoints
import Mathlib.AlgebraicGeometry.AlgClosed.Basic
import Mathlib.FieldTheory.Finite.Basic

/-! # Points of schemes over finite fields and their algebraic closures -/

noncomputable section

universe u

open CategoryTheory Limits
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.GroupScheme.FiniteFieldTorsorPoint

section Fixed

variable {k : Type*} [Field k] [Fintype k]

/-- In a field extension of a finite field `k` with `q` elements, every solution of
`z ^ q = z` lies in the image of `k`. -/
theorem mem_range_algebraMap_of_pow_card_eq {K : Type*} [Field K] [Algebra k K] {z : K}
    (hz : z ^ Fintype.card k = z) : z ∈ Set.range (algebraMap k K) := by
  classical
  by_contra hnot
  have hq : 1 < Fintype.card k := Fintype.one_lt_card
  have hP : (Polynomial.X ^ Fintype.card k - Polynomial.X : Polynomial K) ≠ 0 :=
    FiniteField.X_pow_card_sub_X_ne_zero K hq
  have hroot : ∀ w : K, w ^ Fintype.card k = w →
      w ∈ (Polynomial.X ^ Fintype.card k - Polynomial.X : Polynomial K).roots.toFinset := by
    intro w hw
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP]
    simp [hw]
  have hsub : insert z (Finset.univ.image (algebraMap k K)) ⊆
      (Polynomial.X ^ Fintype.card k - Polynomial.X : Polynomial K).roots.toFinset := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact hroot _ hz
    · obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hw
      exact hroot _ (by rw [← map_pow, FiniteField.pow_card])
  have hnot' : z ∉ Finset.univ.image (algebraMap k K) := by
    simpa using hnot
  have hcard := (Finset.card_le_card hsub).trans
    ((Multiset.toFinset_card_le _).trans (Polynomial.card_roots' _))
  rw [Finset.card_insert_of_notMem hnot',
    Finset.card_image_of_injective _ (algebraMap k K).injective, Finset.card_univ,
    FiniteField.X_pow_card_sub_X_natDegree_eq K hq] at hcard
  omega

end Fixed

variable {k : Type u} [Field k]

/-- A point over a field extension `K` of a finite field `k` that is fixed by the
`q`-power Frobenius of `K` comes from a `k`-point. -/
theorem nonempty_ringPoint_of_frobenius_fixed [Fintype k]
    {X : Over (Spec (CommRingCat.of k))} {K : Type u} [Field K] [Algebra k K]
    (p : RingPoint k X K)
    (hp : ringTestMap k (FiniteField.frobeniusAlgHom k K) ≫ p = p) :
    Nonempty (RingPoint k X k) := by
  classical
  set σ := CommRingCat.ofHom (FiniteField.frobeniusAlgHom k K).toRingHom
  obtain ⟨⟨x, ι⟩, hxι⟩ := (Scheme.SpecToEquivOfField K X.left).symm.surjective p.left
  simp only [Scheme.SpecToEquivOfField_symm_apply] at hxι
  have hfix : ι ≫ σ = ι := by
    have h : Spec.map σ ≫ p.left = p.left := congrArg CommaMorphism.left hp
    have h2 : (Scheme.SpecToEquivOfField K X.left).symm ⟨x, ι ≫ σ⟩ =
        (Scheme.SpecToEquivOfField K X.left).symm ⟨x, ι⟩ := by
      simp only [Scheme.SpecToEquivOfField_symm_apply, Spec.map_comp, Category.assoc, hxι, h]
      rfl
    have h3 := (Scheme.SpecToEquivOfField K X.left).symm.injective h2
    exact eq_of_heq (Sigma.mk.inj_iff.mp h3).2
  have hmem : ∀ y, ι y ∈ (algebraMap k K).range := by
    intro y
    obtain ⟨c, hc⟩ := mem_range_algebraMap_of_pow_card_eq (k := k) (z := ι y) (by
      have := congrArg (fun f => f y) hfix
      simpa [σ, FiniteField.coe_frobeniusAlgHom] using this)
    exact ⟨c, hc⟩
  let e : k ≃+* (algebraMap k K).range :=
    RingEquiv.ofBijective (algebraMap k K).rangeRestrict
      ⟨fun a b h => (algebraMap k K).injective (congrArg Subtype.val h),
        (algebraMap k K).rangeRestrict_surjective⟩
  let τ : X.left.residueField x →+* k :=
    e.symm.toRingHom.comp (ι.hom.codRestrict _ hmem)
  have hτ : CommRingCat.ofHom τ ≫ CommRingCat.ofHom (algebraMap k K) = ι := by
    ext y
    change algebraMap k K (e.symm _) = ι y
    have := congrArg Subtype.val (e.apply_symm_apply ⟨ι y, hmem y⟩)
    exact this
  let q : Spec (CommRingCat.of k) ⟶ X.left :=
    Spec.map (CommRingCat.ofHom τ) ≫ X.left.fromSpecResidueField x
  have hq : q ≫ X.hom = Spec.algebraMap k k := by
    set f := q ≫ X.hom
    have hpK : Spec.algebraMap k K ≫ f = Spec.algebraMap k K := by
      have hw : p.left ≫ X.hom = Spec.algebraMap k K := Over.w p
      refine Eq.trans ?_ hw
      rw [← hxι, ← hτ, Spec.map_comp]
      simp only [f, q, Spec.algebraMap, Category.assoc]
      rfl
    rw [← Spec.map_preimage f] at hpK ⊢
    rw [Spec.algebraMap, ← Spec.map_comp, Spec.map_inj] at hpK
    rw [Spec.algebraMap, Spec.map_inj]
    ext c
    apply (algebraMap k K).injective
    have := congrArg (fun g => g c) (congrArg CommRingCat.Hom.hom hpK)
    simpa using this
  exact ⟨Over.homMk q hq⟩

/-- A nonempty scheme locally of finite type over a field `k` has a point over every
algebraically closed field extension of `k`. -/
theorem nonempty_ringPoint_of_locallyOfFiniteType {X : Over (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType X.hom] [Nonempty X.left]
    (K : Type u) [Field K] [IsAlgClosed K] [Algebra k K] :
    Nonempty (RingPoint k X K) := by
  set t := Spec.algebraMap k K
  have : Surjective t := ⟨fun _ => ⟨Classical.arbitrary _, Subsingleton.elim _ _⟩⟩
  obtain ⟨x⟩ := ‹Nonempty X.left›
  obtain ⟨y, -⟩ := (pullback.fst X.hom t).surjective x
  have : JacobsonSpace ↥(pullback X.hom t) :=
    LocallyOfFiniteType.jacobsonSpace (pullback.snd X.hom t)
  obtain ⟨z, -, hz⟩ := nonempty_inter_closedPoints (X := ↥(pullback X.hom t))
    ⟨y, Set.mem_univ _⟩ isClosed_univ.isLocallyClosed
  replace hz : IsClosed {z} := hz
  refine ⟨Over.homMk (pointOfClosedPoint (pullback.snd X.hom t) z hz ≫
    pullback.fst X.hom t) ?_⟩
  change (_ ≫ _) ≫ _ = t
  rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc]

end Langlands.GroupScheme.FiniteFieldTorsorPoint
