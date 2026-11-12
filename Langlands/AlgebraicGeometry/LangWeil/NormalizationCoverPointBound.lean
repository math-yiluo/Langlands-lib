import Langlands.AlgebraicGeometry.LangWeil.FiniteMorphismPointBound
import Langlands.AlgebraicGeometry.LangWeil.FiniteNormalizationCoverStatement
import Langlands.AlgebraicGeometry.LangWeil.FamilyPointUpperBoundStatement

/-! # Counting points from a finite relative normalization cover -/

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.LangWeil

/-- Decompose points of a normalization above a base point according to their
image in relative affine space. -/
noncomputable def affineNormalizationPointEquiv {T U : Scheme.{u}} (d : ℕ)
    (ν : U ⟶ AffineSpace (ULift.{u} (Fin d)) T)
    (K : Type u) [Field K] (s : Spec (.of K) ⟶ T) :
    {z : Spec (.of K) ⟶ U //
      z ≫ ν ≫ (AffineSpace (ULift.{u} (Fin d)) T ↘ T) = s} ≃
    Σ a : {a : Spec (.of K) ⟶ AffineSpace (ULift.{u} (Fin d)) T //
      a ≫ (AffineSpace (ULift.{u} (Fin d)) T ↘ T) = s},
      {z : Spec (.of K) ⟶ U // z ≫ ν = a.1} where
  toFun z := ⟨⟨z.1 ≫ ν, by simpa only [Category.assoc] using z.2⟩, ⟨z.1, rfl⟩⟩
  invFun a := ⟨a.2.1, by rw [← Category.assoc, a.2.2]; exact a.1.2⟩
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨a, ha⟩, ⟨z, hz⟩⟩
    change z ≫ ν = a at hz
    subst a
    rfl

/-- A finite morphism to relative affine `d`-space over an affine base has
at most `N q^d` points above every finite-field base point, for one `N`. -/
theorem exists_uniform_card_affineNormalization_le {T U : Scheme.{u}} [IsAffine T]
    (d : ℕ) (ν : U ⟶ AffineSpace (ULift.{u} (Fin d)) T) [IsFinite ν] :
    ∃ N : ℕ, ∀ (K : Type u) [Field K] [Finite K] (s : Spec (.of K) ⟶ T),
      Finite {z : Spec (.of K) ⟶ U //
        z ≫ ν ≫ (AffineSpace (ULift.{u} (Fin d)) T ↘ T) = s} ∧
      Nat.card {z : Spec (.of K) ⟶ U //
        z ≫ ν ≫ (AffineSpace (ULift.{u} (Fin d)) T ↘ T) = s} ≤
          N * Nat.card K ^ d := by
  classical
  obtain ⟨N, hN⟩ := exists_uniform_card_finiteMorphism_le ν
  refine ⟨N, ?_⟩
  intro K _ _ s
  let A := {a : Spec (.of K) ⟶ AffineSpace (ULift.{u} (Fin d)) T //
    a ≫ (AffineSpace (ULift.{u} (Fin d)) T ↘ T) = s}
  obtain ⟨hAfin, hAcard⟩ := card_affineSpace_fibrePoints T d K s
  let : Finite A := hAfin
  let : Fintype A := Fintype.ofFinite A
  let : ∀ a : A, Finite {z : Spec (.of K) ⟶ U // z ≫ ν = a.1} :=
    fun a => (hN K a.1).1
  let E := affineNormalizationPointEquiv d ν K s
  refine ⟨Finite.of_equiv _ E.symm, ?_⟩
  rw [Nat.card_congr E, Nat.card_sigma]
  calc
    ∑ a : A, Nat.card {z : Spec (.of K) ⟶ U // z ≫ ν = a.1} ≤ ∑ _a : A, N :=
      Finset.sum_le_sum fun a _ => (hN K a.1).2
    _ = Nat.card A * N := by simp [Nat.card_eq_fintype_card]
    _ = N * Nat.card K ^ d := by rw [show Nat.card A = Nat.card K ^ d from hAcard, mul_comm]

/-- An actual finite normalization cover supplies a positive uniform point bound,
with the exponent chosen from an upper bound for the original fibre dimension. -/
theorem FiniteNormalizationCover.exists_uniform_nat_card_fibrePoints_le
    {S X : Scheme.{u}} {f : X ⟶ S} (c : FiniteNormalizationCover f) :
    ∃ N : ℕ, 0 < N ∧ ∀ (K : Type u) [Field K] [Finite K]
      (s : Spec (.of K) ⟶ S) (e : ℕ),
      topologicalKrullDim (f.fiber (s (IsLocalRing.closedPoint K))) ≤ (e : WithBot ℕ∞) →
      Finite {x : Spec (.of K) ⟶ X // x ≫ f = s} ∧
      Nat.card {x : Spec (.of K) ⟶ X // x ≫ f = s} ≤ N * Nat.card K ^ e := by
  classical
  have hbound (i : Fin c.count) :
      ∃ N : ℕ, ∀ (K : Type u) [Field K] [Finite K] (t : Spec (.of K) ⟶ c.base i),
        Finite {z : Spec (.of K) ⟶ c.source i //
          z ≫ c.normalization i ≫
            (AffineSpace (ULift.{u} (Fin (c.dimension i))) (c.base i) ↘ c.base i) = t} ∧
        Nat.card {z : Spec (.of K) ⟶ c.source i //
          z ≫ c.normalization i ≫
            (AffineSpace (ULift.{u} (Fin (c.dimension i))) (c.base i) ↘ c.base i) = t} ≤
              N * Nat.card K ^ c.dimension i := by
    let := c.baseAffine i
    let := c.normalizationFinite i
    exact exists_uniform_card_affineNormalization_le (c.dimension i) (c.normalization i)
  choose N hN using hbound
  refine ⟨(∑ i, N i) + 1, Nat.succ_pos _, ?_⟩
  intro K _ _ s e hdim
  let P (i : Fin c.count) := {z : Spec (.of K) ⟶ c.source i //
    z ≫ c.sourceMap i ≫ f = s}
  have hP (i : Fin c.count) : Finite (P i) ∧ Nat.card (P i) ≤ N i * Nat.card K ^ e := by
    by_cases hne : Nonempty (P i)
    · obtain ⟨z₀⟩ := hne
      let p := (AffineSpace (ULift.{u} (Fin (c.dimension i))) (c.base i) ↘ c.base i)
      have hover (z : Spec (.of K) ⟶ c.source i) :
          (z ≫ c.normalization i ≫ p) ≫ c.baseMap i = z ≫ c.sourceMap i ≫ f := by
        simpa only [Category.assoc] using
          congrArg (fun a => z ≫ a) (c.over i)
      let t : Spec (.of K) ⟶ c.base i := z₀.1 ≫ c.normalization i ≫ p
      have ht : t ≫ c.baseMap i = s := (hover z₀.1).trans z₀.2
      have hzt (z : P i) : z.1 ≫ c.normalization i ≫ p = t := by
        let := c.baseImmersion i
        apply (cancel_mono (c.baseMap i)).mp
        exact (hover z.1).trans (z.2.trans ht.symm)
      let ev : P i → {z : Spec (.of K) ⟶ c.source i //
        z ≫ c.normalization i ≫ p = t} := fun z => ⟨z.1, hzt z⟩
      have hev : Function.Injective ev := by
        intro z w h
        have hval := congrArg Subtype.val h
        exact Subtype.ext hval
      obtain ⟨hfin, hcard⟩ := hN i K t
      let := hfin
      have hd : c.dimension i ≤ e := by
        have hpoint : c.baseMap i (t (IsLocalRing.closedPoint K)) =
            s (IsLocalRing.closedPoint K) := by
          change (t ≫ c.baseMap i) (IsLocalRing.closedPoint K) = _
          rw [ht]
        have hle := c.dimension_le i (t (IsLocalRing.closedPoint K))
        rw [hpoint] at hle
        exact ENat.natCast_le_natCast.mp (WithBot.coe_le_coe.mp (hle.trans hdim))
      refine ⟨Finite.of_injective ev hev, ?_⟩
      exact ((Nat.card_le_card_of_injective ev hev).trans hcard).trans
        (Nat.mul_le_mul_left (N i) (pow_le_pow_right' Nat.card_pos hd))
    · let : IsEmpty (P i) := not_nonempty_iff.mp hne
      exact ⟨inferInstance, by simp⟩
  let : ∀ i, Finite (P i) := fun i => (hP i).1
  let toPoint : (Σ i, P i) → {x : Spec (.of K) ⟶ X // x ≫ f = s} :=
    fun z => ⟨z.2.1 ≫ c.sourceMap z.1, by simpa only [Category.assoc] using z.2.2⟩
  have hsurj : Function.Surjective toPoint := by
    intro x
    obtain ⟨i, z, hzx⟩ := c.covers K x.1
    refine ⟨⟨i, ⟨z, ?_⟩⟩, ?_⟩
    · rw [← Category.assoc, hzx]
      exact x.2
    · exact Subtype.ext hzx
  refine ⟨Finite.of_surjective toPoint hsurj, ?_⟩
  calc
    Nat.card {x : Spec (.of K) ⟶ X // x ≫ f = s} ≤ Nat.card (Σ i, P i) :=
      Nat.card_le_card_of_surjective toPoint hsurj
    _ = ∑ i, Nat.card (P i) := Nat.card_sigma
    _ ≤ ∑ i, N i * Nat.card K ^ e := Finset.sum_le_sum fun i _ => (hP i).2
    _ = (∑ i, N i) * Nat.card K ^ e := (Finset.sum_mul ..).symm
    _ ≤ ((∑ i, N i) + 1) * Nat.card K ^ e :=
      Nat.mul_le_mul_right _ (Nat.le_add_right _ _)

/-- The geometric existence theorem for normalization covers implies the exact
uniform upper bound for families over the integers. -/
theorem familyPointUpperBound_of_finiteNormalizationCover
    (hnorm : FiniteNormalizationCoverStatement.{u}) : FamilyPointUpperBoundStatement.{u} := by
  intro S X f hSZ hS hft hqc
  let := hSZ
  let := hS
  let : IsNoetherianRing (ULift.{u} ℤ) :=
    isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  let : IsLocallyNoetherian S :=
    LocallyOfFiniteType.isLocallyNoetherian (specULiftZIsTerminal.{u}.from S)
  have hnoeth : IsNoetherian S := ⟨⟩
  obtain ⟨c⟩ := hnorm S X f hnoeth hft hqc
  obtain ⟨N, hpos, hN⟩ := c.exists_uniform_nat_card_fibrePoints_le
  refine ⟨(N : ℝ), Nat.cast_pos.mpr hpos, ?_⟩
  intro K _ _ s e hdim
  have hcard := (hN K s e hdim).2
  exact_mod_cast hcard

end Langlands.AlgebraicGeometry.LangWeil
