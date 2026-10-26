import Langlands.Representation.Exponents.DualJacquetStatement
import Langlands.Representation.Classification.RelativeJacquetMultiplicityStatement
import Mathlib.LinearAlgebra.AffineSpace.AffineMap

/-!
# Actual real-twist families and opposite Jacquet occurrence loci

Internal packaging of the existing induction, determinant twist, Weyl transport,
and class-exponent predicate. No continuation property is part of these data.
-/

noncomputable section

namespace Langlands.RealTwistFamilies

open GeneralLinear Geometric
open scoped NNReal

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B D C : BlockShape n)

/-- The real determinant-twist family of actual upper normalized inductions. -/
def induced (σ : Rep.{uV} ℂ (B.Levi F.Carrier)) :
    (Fin B.length → ℝ) → Rep.{max uF uV} ℂ (GeneralLinear n F.Carrier) :=
  fun t => CuspidalJacquetMultiplicity.induced T B
    (Rep.of (T.leviRealPowerTwist B t σ.ρ))

theorem induced_apply (σ : Rep.{uV} ℂ (B.Levi F.Carrier))
    (t : Fin B.length → ℝ) :
    induced T B σ t = CuspidalJacquetMultiplicity.induced T B
      (Rep.of (T.leviRealPowerTwist B t σ.ρ)) := rfl

/-- The bundled action is the existing normalized induction action. -/
theorem induced_representation (σ : Rep.{uV} ℂ (B.Levi F.Carrier))
    (t : Fin B.length → ℝ) :
    letI := T.topology
    (induced T B σ t).ρ =
      T.normalizedParabolicInduced B (T.leviRealPowerTwist B t σ.ρ) := rfl

@[simp]
theorem induced_zero (σ : Rep.{uV} ℂ (B.Levi F.Carrier)) :
    induced T B σ 0 = CuspidalJacquetMultiplicity.induced T B σ := by
  simp [induced]

/-- Evaluate the existing smooth induced function; no new carrier is introduced. -/
def inducedEval (σ : Rep.{uV} ℂ (B.Levi F.Carrier))
    (t : Fin B.length → ℝ) (f : induced T B σ t)
    (g : GeneralLinear n F.Carrier) : σ :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  Induction.eval (B.parabolic F.Carrier)
    (twist (T.parabolicHalfModulus B)
      ((T.leviRealPowerTwist B t σ.ρ).comp (B.leviProjection F.Carrier))) f g

/-- The induced family acts by the same right translations at every parameter. -/
@[simp]
theorem inducedEval_action (σ : Rep.{uV} ℂ (B.Levi F.Carrier))
    (t : Fin B.length → ℝ) (f : induced T B σ t)
    (g x : GeneralLinear n F.Carrier) :
    inducedEval T B σ t ((induced T B σ t).ρ g f) x =
      inducedEval T B σ t f (x * g) := rfl

/-- Covariance retains the upper positive half modulus and determinant twist. -/
theorem inducedEval_covariant (σ : Rep.{uV} ℂ (B.Levi F.Carrier))
    (t : Fin B.length → ℝ) (f : induced T B σ t)
    (g : B.parabolic F.Carrier) (x : GeneralLinear n F.Carrier) :
    inducedEval T B σ t f ((g : GeneralLinear n F.Carrier) * x) =
      ((NNReal.sqrt (T.leviModulus B (B.leviProjection F.Carrier g) : ℝ≥0) : ℝ) : ℂ) •
        ((T.leviRealPowerCharacter B t (B.leviProjection F.Carrier g) : ℂ) •
          σ.ρ (B.leviProjection F.Carrier g) (inducedEval T B σ t f x)) :=
  T.normalizedParabolicInduced_covariant B (T.leviRealPowerTwist B t σ.ρ) f g x

/-- An affine map on real vector spaces is its offset plus its real linear part. -/
theorem affine_apply (a : (Fin B.length → ℝ) →ᵃ[ℝ] (Fin D.length → ℝ))
    (t : Fin B.length → ℝ) :
    a t = a 0 + a.linear t := by
  simpa only [vadd_eq_add, add_zero, add_comm] using a.map_vadd 0 t

/-- Twist a fixed actual source-Levi representation, then use the existing
inverse-conjugation transport along the supplied actual permutation. -/
def transported (w : Equiv.Perm (Fin n))
    (hw : CuspidalSupport.ConjugatesLevi (F := F.Carrier) D C w)
    (ω : Rep.{uW} ℂ (D.Levi F.Carrier))
    (a : (Fin B.length → ℝ) →ᵃ[ℝ] (Fin D.length → ℝ)) :
    (Fin B.length → ℝ) → Rep.{uW} ℂ (C.Levi F.Carrier) :=
  fun t => Rep.of (CuspidalSupport.transport D C w hw
    (T.leviRealPowerTwist D (a t) ω.ρ))

theorem transported_apply (w : Equiv.Perm (Fin n))
    (hw : CuspidalSupport.ConjugatesLevi (F := F.Carrier) D C w)
    (ω : Rep.{uW} ℂ (D.Levi F.Carrier))
    (a : (Fin B.length → ℝ) →ᵃ[ℝ] (Fin D.length → ℝ))
    (t : Fin B.length → ℝ) :
    transported T B D C w hw ω a t =
      Rep.of (CuspidalSupport.transport D C w hw
        (T.leviRealPowerTwist D (a t) ω.ρ)) := rfl

@[simp]
theorem transported_action (w : Equiv.Perm (Fin n))
    (hw : CuspidalSupport.ConjugatesLevi (F := F.Carrier) D C w)
    (ω : Rep.{uW} ℂ (D.Levi F.Carrier))
    (a : (Fin B.length → ℝ) →ᵃ[ℝ] (Fin D.length → ℝ))
    (t : Fin B.length → ℝ) (m : C.Levi F.Carrier) (v : ω) :
    (transported T B D C w hw ω a t).ρ m v =
      (T.leviRealPowerCharacter D (a t)
        ((CuspidalSupport.leviConjugation D C w hw).symm m) : ℂ) •
      ω.ρ ((CuspidalSupport.leviConjugation D C w hw).symm m) v := rfl

@[simp]
theorem transported_zero (w : Equiv.Perm (Fin n))
    (hw : CuspidalSupport.ConjugatesLevi (F := F.Carrier) D C w)
    (ω : Rep.{uW} ℂ (D.Levi F.Carrier)) (t : Fin B.length → ℝ) :
    transported T B D C w hw ω 0 t =
      Rep.of (CuspidalSupport.transport D C w hw ω.ρ) := by
  simp [transported]

/-- The identity permutation really conjugates the embedded Levi to itself. -/
theorem conjugatesLevi_one :
    CuspidalSupport.ConjugatesLevi (F := F.Carrier) D D 1 := by
  simp only [CuspidalSupport.ConjugatesLevi, map_one]
  exact Subgroup.map_id _

/-- For the identity permutation the candidate is the untransported twist. -/
theorem transported_one
    (hw : CuspidalSupport.ConjugatesLevi (F := F.Carrier) D D 1)
    (ω : Rep.{uW} ℂ (D.Levi F.Carrier))
    (a : (Fin B.length → ℝ) →ᵃ[ℝ] (Fin D.length → ℝ))
    (t : Fin B.length → ℝ) :
    transported T B D D 1 hw ω a t =
      Rep.of (T.leviRealPowerTwist D (a t) ω.ρ) := by
  have h (m : D.Levi F.Carrier) :
      (CuspidalSupport.leviConjugation D D 1 hw).symm m = m := by
    apply D.leviEmbedding_injective F.Carrier
    simpa using CuspidalSupport.leviConjugation_symm_embedding D D 1 hw m
  have hr : CuspidalSupport.transport D D 1 hw (T.leviRealPowerTwist D (a t) ω.ρ) =
      T.leviRealPowerTwist D (a t) ω.ρ := by
    ext m v
    change (T.leviRealPowerTwist D (a t) ω.ρ)
      ((CuspidalSupport.leviConjugation D D 1 hw).symm m) v = _
    rw [h]
  exact congrArg Rep.of hr

theorem transported_id
    (ω : Rep.{uW} ℂ (B.Levi F.Carrier)) (t : Fin B.length → ℝ) :
    transported T B B B 1 (conjugatesLevi_one (F := F) B) ω
      (AffineMap.id ℝ (Fin B.length → ℝ)) t =
      Rep.of (T.leviRealPowerTwist B t ω.ρ) :=
  transported_one T B B _ ω _ t

/-- Pointwise occurrence in the actual opposite Jacquet module of the entire
induced representation, with independent source and candidate carriers. -/
def Occurs (σ : Rep.{uV} ℂ (B.Levi F.Carrier))
    (w : Equiv.Perm (Fin n))
    (hw : CuspidalSupport.ConjugatesLevi (F := F.Carrier) D C w)
    (ω : Rep.{uW} ℂ (D.Levi F.Carrier))
    (a : (Fin B.length → ℝ) →ᵃ[ℝ] (Fin D.length → ℝ))
    (t : Fin B.length → ℝ) : Prop :=
  T.IsOppositeJacquetClassExponent C (induced T B σ t)
    (transported T B D C w hw ω a t)

/-- Exactly the parameters at which the specified actual candidate occurs. -/
def occurrenceLocus (σ : Rep.{uV} ℂ (B.Levi F.Carrier))
    (w : Equiv.Perm (Fin n))
    (hw : CuspidalSupport.ConjugatesLevi (F := F.Carrier) D C w)
    (ω : Rep.{uW} ℂ (D.Levi F.Carrier))
    (a : (Fin B.length → ℝ) →ᵃ[ℝ] (Fin D.length → ℝ)) :
    Set (Fin B.length → ℝ) :=
  {t | Occurs T B D C σ w hw ω a t}

@[simp]
theorem mem_occurrenceLocus (σ : Rep.{uV} ℂ (B.Levi F.Carrier))
    (w : Equiv.Perm (Fin n))
    (hw : CuspidalSupport.ConjugatesLevi (F := F.Carrier) D C w)
    (ω : Rep.{uW} ℂ (D.Levi F.Carrier))
    (a : (Fin B.length → ℝ) →ᵃ[ℝ] (Fin D.length → ℝ))
    (t : Fin B.length → ℝ) :
    t ∈ occurrenceLocus T B D C σ w hw ω a ↔
      Occurs T B D C σ w hw ω a t := Iff.rfl

/-- Unfolding exposes only irreducibility, admissibility and an actual
subrepresentation followed by a surjective intertwiner. -/
theorem occurs_iff (σ : Rep.{uV} ℂ (B.Levi F.Carrier))
    (w : Equiv.Perm (Fin n))
    (hw : CuspidalSupport.ConjugatesLevi (F := F.Carrier) D C w)
    (ω : Rep.{uW} ℂ (D.Levi F.Carrier))
    (a : (Fin B.length → ℝ) →ᵃ[ℝ] (Fin D.length → ℝ))
    (t : Fin B.length → ℝ) :
    letI := T.topology
    Occurs T B D C σ w hw ω a t ↔
      Representation.IsIrreducible (transported T B D C w hw ω a t).ρ ∧
      IsAdmissible (transported T B D C w hw ω a t).ρ ∧
      ∃ U : Subrepresentation
          (CuspidalJacquetMultiplicity.oppositeJacquet T C (induced T B σ t)).ρ,
        ∃ q : U.toRepresentation.IntertwiningMap (transported T B D C w hw ω a t).ρ,
          Function.Surjective q := Iff.rfl

/-- Restrict coarse determinant parameters to the actual flattened block indices. -/
def restrictParameter (S : BlockRefinement B) :
    (Fin B.length → ℝ) →ₗ[ℝ] (Fin (B.flatten S).length → ℝ) where
  toFun t k := t ((B.flattenBlockEquiv S).symm k).1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The existing nested fine parameter, as a Mathlib affine map with offset `-v₀`. -/
def nestedParameter (S : BlockRefinement B) (v₀ : Fin (B.flatten S).length → ℝ) :
    (Fin B.length → ℝ) →ᵃ[ℝ] (Fin (B.flatten S).length → ℝ) :=
  AffineMap.const ℝ (Fin B.length → ℝ) (-v₀) + (restrictParameter B S).toAffineMap

@[simp]
theorem nestedParameter_apply (S : BlockRefinement B)
    (v₀ : Fin (B.flatten S).length → ℝ) (t : Fin B.length → ℝ)
    (k : Fin (B.flatten S).length) :
    nestedParameter B S v₀ t k = -v₀ k + t ((B.flattenBlockEquiv S).symm k).1 := rfl

@[simp]
theorem nestedParameter_zero (S : BlockRefinement B)
    (v₀ : Fin (B.flatten S).length → ℝ) :
    nestedParameter B S v₀ 0 = -v₀ := by
  ext k
  simp

/-- The affine specialization uses exactly the published refined-Levi pullback. -/
theorem fineTwist_eq_nestedParameter (S : BlockRefinement B)
    (ω : Rep.{uW} ℂ ((B.flatten S).Levi F.Carrier))
    (v₀ : Fin (B.flatten S).length → ℝ) (t : Fin B.length → ℝ) :
    RelativeJacquetMultiplicity.fineTwist T B S ω v₀ t =
      Rep.of ((T.leviRealPowerTwist (B.flatten S) (nestedParameter B S v₀ t) ω.ρ).comp
        (flattenedLeviEquiv F.Carrier B S).symm.toMonoidHom) := rfl

end Langlands.RealTwistFamilies
