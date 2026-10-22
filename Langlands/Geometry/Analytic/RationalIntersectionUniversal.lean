import Langlands.Geometry.Analytic.RationalIntersection
import Langlands.Geometry.Analytic.RationalIntersectionUniversal.Statement

/-! # Bounded maps out of the actual rational intersection quotient -/

noncomputable section

universe u v

namespace Langlands.Analytic.RationalIntersection

open StrictTateAlgebra PresentedStrictAffinoidAlgebra

section Tuples

variable (B : Type v) [NormedCommRing B] (m n : ℕ)

/-- Adjoining a unit coordinate preserves bounded monomials, including in
an unnormalized or trivial target ring. -/
theorem bounded_cons_one (b : Fin m → B) (hb : HasBoundedMonomials (Fin m) B b) :
    HasBoundedMonomials (Fin (m + 1)) B (Fin.cons 1 b) := by
  apply (hasBoundedMonomials_iff_pow_bound _ _ _).mpr
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · refine ⟨max 1 ‖(1 : B)‖, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
    intro r
    simpa only [Fin.cons_zero, one_pow] using le_max_right (1 : ℝ) ‖(1 : B)‖
  · simpa only [Fin.cons_succ] using hb.pow_bound (Fin m) B j

/-- The products of the two extended fraction tuples. -/
def fractionProducts (b : Fin m → B) (c : Fin n → B) :
    Fin ((m + 1) * (n + 1)) → B := fun a =>
  (Fin.cons 1 b : Fin (m + 1) → B) (finProdFinEquiv.symm a).1 *
    (Fin.cons 1 c : Fin (n + 1) → B) (finProdFinEquiv.symm a).2

theorem fractionProducts_bounded (b : Fin m → B) (c : Fin n → B)
    (hb : HasBoundedMonomials (Fin m) B b)
    (hc : HasBoundedMonomials (Fin n) B c) :
    HasBoundedMonomials (Fin ((m + 1) * (n + 1))) B (fractionProducts B m n b c) := by
  apply (hasBoundedMonomials_iff_pow_bound _ _ _).mpr
  intro a
  obtain ⟨C, hC, hCb⟩ := (bounded_cons_one B m b hb).pow_bound _ _
    (finProdFinEquiv.symm a).1
  obtain ⟨D, hD, hDc⟩ := (bounded_cons_one B n c hc).pow_bound _ _
    (finProdFinEquiv.symm a).2
  refine ⟨C * D, mul_pos hC hD, fun r => ?_⟩
  change ‖((Fin.cons 1 b : Fin (m + 1) → B) (finProdFinEquiv.symm a).1 *
    (Fin.cons 1 c : Fin (n + 1) → B) (finProdFinEquiv.symm a).2) ^ r‖ ≤ _
  rw [mul_pow]
  exact (norm_mul_le _ _).trans (mul_le_mul (hCb r) (hDc r) (norm_nonneg _) hC.le)

end Tuples

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (P : PresentedStrictAffinoidAlgebra K)
  (m n : ℕ) (g h : P) (f : Fin m → P) (k : Fin n → P)
  (B : Type v) [NormedCommRing B] [NormedAlgebra K B]
  [IsUltrametricDist B] [CompleteSpace B]

omit [CompleteSpace K] [IsUltrametricDist B] [CompleteSpace B] in
theorem fractionProducts_equations (φ : BoundedAlgHom K P B)
    (b : Fin m → B) (c : Fin n → B)
    (hb : ∀ i, φ g * b i = φ (f i)) (hc : ∀ j, φ h * c j = φ (k j))
    (a : Fin ((m + 1) * (n + 1))) :
    φ (g * h) * fractionProducts B m n b c a = φ (numerators K P m n g h f k a) := by
  have hb' : ∀ i, φ g * (Fin.cons 1 b : Fin (m + 1) → B) i =
      φ ((Fin.cons g f : Fin (m + 1) → P) i) :=
    Fin.cases (by simp) hb
  have hc' : ∀ j, φ h * (Fin.cons 1 c : Fin (n + 1) → B) j =
      φ ((Fin.cons h k : Fin (n + 1) → P) j) :=
    Fin.cases (by simp) hc
  change φ (g * h) *
    ((Fin.cons 1 b : Fin (m + 1) → B) (finProdFinEquiv.symm a).1 *
      (Fin.cons 1 c : Fin (n + 1) → B) (finProdFinEquiv.symm a).2) =
    φ ((Fin.cons g f : Fin (m + 1) → P) (finProdFinEquiv.symm a).1 *
      (Fin.cons h k : Fin (n + 1) → P) (finProdFinEquiv.symm a).2)
  rw [map_mul, map_mul, ← hb', ← hc']
  ring

/-- Construct the bounded map from actual bounded solutions of both sets
of denominator equations. -/
def liftFromSolutions (φ : BoundedAlgHom K P B)
    (b : Fin m → B) (c : Fin n → B)
    (hb : HasBoundedMonomials (Fin m) B b)
    (hc : HasBoundedMonomials (Fin n) B c)
    (heqf : ∀ i, φ g * b i = φ (f i)) (heqk : ∀ j, φ h * c j = φ (k j)) :
    BoundedAlgHom K (algebra K P m n g h f k) B :=
  RationalLocalization.liftFromBase _ _ _ _ _ B φ (fractionProducts B m n b c)
    (fractionProducts_bounded B m n b c hb hc)
    (fractionProducts_equations K P m n g h f k B φ b c heqf heqk)

theorem liftFromSolutions_comp_baseMap (φ : BoundedAlgHom K P B)
    (b : Fin m → B) (c : Fin n → B)
    (hb : HasBoundedMonomials (Fin m) B b)
    (hc : HasBoundedMonomials (Fin n) B c)
    (heqf : ∀ i, φ g * b i = φ (f i)) (heqk : ∀ j, φ h * c j = φ (k j)) :
    (liftFromSolutions K P m n g h f k B φ b c hb hc heqf heqk).comp
      (baseMap K P m n g h f k) = φ :=
  RationalLocalization.liftFromBase_comp_baseMap _ _ _ _ _ _ _ _ _ _

omit [IsUltrametricDist B] [CompleteSpace B] in
/-- A bounded map out of a rational quotient sends its fraction coordinates
to an actually bounded tuple, by composition with the Tate quotient map. -/
theorem mappedFractions_bounded
    (φ : BoundedAlgHom K (RationalLocalization.algebra K P m g f) B) :
    HasBoundedMonomials (Fin m) B
      (fun i => φ (RationalLocalization.fractionCoordinate K P m g f i)) := by
  apply (hasBoundedMonomials_iff_pow_bound _ _ _).mpr
  intro i
  exact (hasBoundedMonomials_map_X
    (Fin (RationalLocalization.algebra K P m g f).arity) K B
    (φ.comp (presentationMap K (RationalLocalization.algebra K P m g f)))).pow_bound _ _
      (Fin.natAdd P.arity i)

variable (α : BoundedAlgHom K (RationalLocalization.algebra K P m g f) B)
  (β : BoundedAlgHom K (RationalLocalization.algebra K P n h k) B)
  (hcompat : α.comp (RationalLocalization.baseMap K P m g f) =
    β.comp (RationalLocalization.baseMap K P n h k))

/-- A pair of bounded morphisms agreeing on the base determines a bounded
morphism out of the constructed intersection quotient. -/
def lift : BoundedAlgHom K (algebra K P m n g h f k) B :=
  liftFromSolutions K P m n g h f k B
    (α.comp (RationalLocalization.baseMap K P m g f))
    (fun i => α (RationalLocalization.fractionCoordinate K P m g f i))
    (fun j => β (RationalLocalization.fractionCoordinate K P n h k j))
    (mappedFractions_bounded K P m g f B α) (mappedFractions_bounded K P n h k B β)
    (fun i => (map_mul α.toAlgHom _ _).symm.trans
      (congrArg α (RationalLocalization.coordinate_equation K P m g f i)))
    (fun j => by
      have hh := congrArg (fun χ => χ h) hcompat
      have hk := congrArg (fun χ => χ (k j)) hcompat
      change α (RationalLocalization.baseMap K P m g f h) *
        β (RationalLocalization.fractionCoordinate K P n h k j) =
          α (RationalLocalization.baseMap K P m g f (k j))
      change α (RationalLocalization.baseMap K P m g f h) =
        β (RationalLocalization.baseMap K P n h k h) at hh
      change α (RationalLocalization.baseMap K P m g f (k j)) =
        β (RationalLocalization.baseMap K P n h k (k j)) at hk
      rw [hh, hk, ← map_mul]
      exact congrArg β (RationalLocalization.coordinate_equation K P n h k j))

theorem lift_comp_baseMap :
    (lift K P m n g h f k B α β hcompat).comp (baseMap K P m n g h f k) =
      α.comp (RationalLocalization.baseMap K P m g f) :=
  liftFromSolutions_comp_baseMap _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

variable (hf : RationalLocalization.GeneratesUnitIdeal K P m g f)
  (hk : RationalLocalization.GeneratesUnitIdeal K P n h k)

theorem lift_comp_leftMap :
    (lift K P m n g h f k B α β hcompat).comp (leftMap K P m n g h f k hf hk) = α := by
  apply RationalLocalization.hom_ext_base K P m g f B hf
  apply BoundedAlgHom.ext
  intro a
  change lift K P m n g h f k B α β hcompat
    (leftMap K P m n g h f k hf hk (RationalLocalization.baseMap K P m g f a)) =
      α (RationalLocalization.baseMap K P m g f a)
  have hleft := congrArg (fun χ => χ a) (leftMap_comp_baseMap K P m n g h f k hf hk)
  change leftMap K P m n g h f k hf hk (RationalLocalization.baseMap K P m g f a) =
    baseMap K P m n g h f k a at hleft
  rw [hleft]
  exact congrArg (fun χ => χ a) (lift_comp_baseMap K P m n g h f k B α β hcompat)

theorem lift_comp_rightMap :
    (lift K P m n g h f k B α β hcompat).comp (rightMap K P m n g h f k hf hk) = β := by
  apply RationalLocalization.hom_ext_base K P n h k B hk
  apply BoundedAlgHom.ext
  intro a
  change lift K P m n g h f k B α β hcompat
    (rightMap K P m n g h f k hf hk (RationalLocalization.baseMap K P n h k a)) =
      β (RationalLocalization.baseMap K P n h k a)
  have hright := congrArg (fun χ => χ a) (rightMap_comp_baseMap K P m n g h f k hf hk)
  change rightMap K P m n g h f k hf hk (RationalLocalization.baseMap K P n h k a) =
    baseMap K P m n g h f k a at hright
  rw [hright]
  exact (congrArg (fun χ => χ a) (lift_comp_baseMap K P m n g h f k B α β hcompat)).trans
    (congrArg (fun χ => χ a) hcompat)

include hcompat in
/-- The constructed intersection quotient has the bounded pushout universal
property for complete ultrametric target algebras. No spectral implication is
needed: the two supplied bounded maps give the fraction bounds. -/
theorem existsUnique_lift :
    ∃! ψ : BoundedAlgHom K (algebra K P m n g h f k) B,
      ψ.comp (leftMap K P m n g h f k hf hk) = α ∧
        ψ.comp (rightMap K P m n g h f k hf hk) = β := by
  refine ⟨lift K P m n g h f k B α β hcompat,
    ⟨lift_comp_leftMap K P m n g h f k B α β hcompat hf hk,
      lift_comp_rightMap K P m n g h f k B α β hcompat hf hk⟩, ?_⟩
  intro ψ hψ
  apply RationalLocalization.hom_ext_base K P ((m + 1) * (n + 1)) (g * h)
    (numerators K P m n g h f k) B (generatesUnitIdeal K P m n g h f k hf hk)
  apply BoundedAlgHom.ext
  intro a
  change ψ (baseMap K P m n g h f k a) =
    lift K P m n g h f k B α β hcompat (baseMap K P m n g h f k a)
  calc
    _ = ψ (leftMap K P m n g h f k hf hk
        (RationalLocalization.baseMap K P m g f a)) :=
      congrArg ψ (congrArg (fun χ => χ a)
        (leftMap_comp_baseMap K P m n g h f k hf hk)).symm
    _ = α (RationalLocalization.baseMap K P m g f a) :=
      congrArg (fun χ => χ (RationalLocalization.baseMap K P m g f a)) hψ.1
    _ = _ := (congrArg (fun χ => χ a)
      (lift_comp_baseMap K P m n g h f k B α β hcompat)).symm

/-- The constructed restriction maps have the stated bounded pushout
property, with an independent universe for the common target. -/
theorem boundedPushout : BoundedPushoutStatement.{u, v} := by
  intro K _ _ _ P m n g h f k hf hk
  refine ⟨leftMap K P m n g h f k hf hk, rightMap K P m n g h f k hf hk,
    leftMap_comp_baseMap K P m n g h f k hf hk,
    rightMap_comp_baseMap K P m n g h f k hf hk, ?_⟩
  intro B _ _ _ _ α β hcompat
  exact existsUnique_lift K P m n g h f k B α β hcompat hf hk

end Langlands.Analytic.RationalIntersection
