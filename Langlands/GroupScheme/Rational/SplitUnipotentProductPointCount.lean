import Langlands.GroupScheme.Rational.SplitSeriesPointCount
import Langlands.GroupScheme.SubgroupIntersection

/-! # Counting products of split unipotent subgroups over finite fields -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

private def mulFiberEquivPullback
    {A : Type u} {B : Type v} {P : Type w} [Group A] [Group B] [Group P]
    (f : A →* P) (g : B →* P) (a₀ : A) (b₀ : B) :
    {p : A × B // f p.1 * g p.2 = f a₀ * g b₀} ≃
      {p : A × B // f p.1 = g p.2} where
  toFun p := ⟨(a₀⁻¹ * p.val.1, b₀ * p.val.2⁻¹), by
    simp only [map_mul, map_inv]
    apply (eq_mul_inv_iff_mul_eq).2
    rw [mul_assoc, p.property, inv_mul_cancel_left]⟩
  invFun p := ⟨(a₀ * p.val.1, p.val.2⁻¹ * b₀), by
    simp only [map_mul, map_inv]
    rw [p.property]
    group⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext <;> simp
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext <;> simp

/-- If multiplication of two group images is onto, the common-image pullback
measures the cardinality of every multiplication fiber. -/
theorem card_mul_pullback_of_mul_surjective
    {A : Type u} {B : Type v} {P : Type w} [Group A] [Group B] [Group P]
    (f : A →* P) (g : B →* P)
    (hsurj : ∀ p, ∃ a b, f a * g b = p) :
    Nat.card A * Nat.card B =
      Nat.card P * Nat.card {p : A × B // f p.1 = g p.2} := by
  classical
  let m : A × B → P := fun p => f p.1 * g p.2
  have hs : Function.Surjective m := by
    intro p
    obtain ⟨a, b, h⟩ := hsurj p
    exact ⟨(a, b), h⟩
  let s : P → A × B := Function.surjInv hs
  have he (p : P) : m (s p) = p := Function.surjInv_eq hs p
  let e (p : P) : {x : A × B // m x = p} ≃
      {x : A × B // f x.1 = g x.2} := by
    rw [← he p]
    exact mulFiberEquivPullback f g (s p).1 (s p).2
  calc
    Nat.card A * Nat.card B = Nat.card (A × B) := (Nat.card_prod A B).symm
    _ = Nat.card (Σ p : P, {x : A × B // m x = p}) :=
      Nat.card_congr (Equiv.sigmaFiberEquiv m).symm
    _ = Nat.card (Σ _p : P, {x : A × B // f x.1 = g x.2}) :=
      Nat.card_congr (Equiv.sigmaCongrRight e)
    _ = Nat.card P * Nat.card {x : A × B // f x.1 = g x.2} := by
      rw [Nat.card_congr (Equiv.sigmaEquivProd P _), Nat.card_prod]

section SchemePoints

variable {S : Scheme.{u}} {V C U : GroupScheme S}

/-- Points of the scheme-theoretic intersection are exactly pairs with the
same ambient image, on an arbitrary scheme test. -/
def subgroupIntersectionPointsEquiv (j : V ⟶ U) (c : C ⟶ U) (T : Over S) :
    (T ⟶ (subgroupIntersection j c).X) ≃
      {p : (T ⟶ V.X) × (T ⟶ C.X) // p.1 ≫ j.hom.hom = p.2 ≫ c.hom.hom} where
  toFun x := ⟨(x ≫ (subgroupIntersectionFst j c).hom.hom,
    x ≫ (subgroupIntersectionSnd j c).hom.hom), by
      rw [Category.assoc, Category.assoc, (subgroupIntersection_isPullback j c).w]⟩
  invFun p := (subgroupIntersection_isPullback j c).lift p.val.1 p.val.2 p.property
  left_inv x := by
    apply (subgroupIntersection_isPullback j c).hom_ext <;>
      simp only [IsPullback.lift_fst, IsPullback.lift_snd]
  right_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact (subgroupIntersection_isPullback j c).lift_fst _ _ _
    · exact (subgroupIntersection_isPullback j c).lift_snd _ _ _

/-- Rationally surjective subgroup multiplication gives the exact
intersection-corrected rational point count. -/
theorem card_points_mul_card_intersection
    (j : V ⟶ U) (c : C ⟶ U) (T : Over S)
    (hsurj : ∀ u : T ⟶ U.X, ∃ v : T ⟶ V.X, ∃ x : T ⟶ C.X,
      (v ≫ j.hom.hom) * (x ≫ c.hom.hom) = u) :
    Nat.card (T ⟶ V.X) * Nat.card (T ⟶ C.X) =
      Nat.card (T ⟶ U.X) * Nat.card (T ⟶ (subgroupIntersection j c).X) := by
  let f := ((yonedaGrp.map j).app (Opposite.op T)).hom
  let g := ((yonedaGrp.map c).app (Opposite.op T)).hom
  have h := card_mul_pullback_of_mul_surjective f g hsurj
  rw [Nat.card_congr (subgroupIntersectionPointsEquiv j c T)]
  exact h

end SchemePoints

namespace RelativeRoot

variable {k : Type u} [Field k] [Finite k]
    {V C U : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom V.X.hom] [IsAffineHom C.X.hom] [IsAffineHom U.X.hom]
    [Smooth V.X.hom] [Smooth C.X.hom] [Smooth U.X.hom]

/-- Over a finite field, rationally surjective multiplication of split
unipotent subgroups forces the expected Lie-dimension equality whenever
the scheme-theoretic intersection is smooth and split as well. -/
theorem lieDimension_add_intersection_of_rationalPoints_mul_surjective
    (j : V ⟶ U) (c : C ⟶ U)
    [IsAffineHom (subgroupIntersection j c).X.hom]
    [Smooth (subgroupIntersection j c).X.hom]
    (hV : IsSplitUnipotent V) (hC : IsSplitUnipotent C) (hU : IsSplitUnipotent U)
    (hE : IsSplitUnipotent (subgroupIntersection j c))
    (hsurj : ∀ u : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ U.X,
      ∃ v : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ V.X,
      ∃ x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ C.X,
        (v ≫ j.hom.hom) * (x ≫ c.hom.hom) = u) :
    Lie.dimension V + Lie.dimension C =
      Lie.dimension U + Lie.dimension (subgroupIntersection j c) := by
  obtain ⟨nV, hsV⟩ := hV
  obtain ⟨nC, hsC⟩ := hC
  obtain ⟨nU, hsU⟩ := hU
  obtain ⟨nE, hsE⟩ := hE
  have h := card_points_mul_card_intersection j c
    (Over.mk (𝟙 (Spec (CommRingCat.of k)))) hsurj
  rw [hsV.card_rationalPoints, hsC.card_rationalPoints,
    hsU.card_rationalPoints, hsE.card_rationalPoints, ← pow_add, ← pow_add] at h
  have hn := Nat.pow_right_injective (show 2 ≤ Nat.card k from Finite.one_lt_card) h
  simpa only [hsV.lieDimension_eq, hsC.lieDimension_eq,
    hsU.lieDimension_eq, hsE.lieDimension_eq] using hn

end RelativeRoot

end Langlands.GroupScheme
