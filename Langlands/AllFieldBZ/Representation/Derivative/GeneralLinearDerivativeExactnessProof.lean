import Langlands.AllFieldBZ.Representation.Derivative.GeneralLinearDerivativeExactnessStatement
import Langlands.AllFieldBZ.Representation.Derivative.MirabolicMinusExactnessProof
import Langlands.Representation.Derivative.GeneralLinearDerivativeExactnessProof

/-!
# All-field port of `Langlands.Representation.Derivative.GeneralLinearDerivativeExactnessProof`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Derivative.GeneralLinearDerivativeExactnessProof` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
namespace Langlands.AllFieldBZ.Derivative
open Langlands.Derivative hiding GeneralLinearDerivativeExactnessStatement generalLinearDerivative generalLinearDerivativeExactness generalLinearDerivativePositive generalLinearDerivativePositive_eq generalLinearDerivativePositive_mapsShortExact generalLinearDerivativePositive_obj generalLinearDerivative_of_pos generalLinearDerivative_succ generalLinearDerivative_succ_obj generalLinearDerivative_top_succ generalLinearDerivative_zero generalLinearRankCast generalLinearRankCast_mapsShortExact generalLinearRankCast_refl generalLinearRankCast_symm_comp generalLinearRankCast_trans generalLinearRestriction generalLinearRestriction_map_apply generalLinearRestriction_map_toLinearMap generalLinearRestriction_mapsShortExact mirabolicDerivative mirabolicDerivative_eq mirabolicDerivative_mapsShortExact mirabolicDerivative_succ mirabolicDerivative_zero phiMinusIterate phiMinusIterate_mapsShortExact phiMinusIterate_succ phiMinusIterate_zero
open CategoryTheory
open Langlands.GeneralLinear
open Langlands.HarmonicAnalysis
universe uF uV

open _root_.Langlands.Derivative.LevelCalculus (mapsShortExact_id mapsShortExact_comp)
variable (F : LocalFieldPackage.{uF}) (T : F.TopologicalData)

/-- Restriction from `GL_(n+1)` to the mirabolic subgroup `P_(n+1)` preserves short
exact sequences, because it keeps the underlying map of every intertwiner. -/
theorem generalLinearRestriction_mapsShortExact (n : ℕ) :
    letI := T.topology
    Mirabolic.MapsShortExactIntertwiners (generalLinearRestriction.{uF, uV} T n) := by
  let _ := T.topology
  intro A B C i q hi hq hex
  have hmap : ∀ {X Y : SmoothRep.{0, uF, uV} ℂ (GeneralLinear (n + 1) F.Carrier)}
      (f : X ⟶ Y), (SmoothRep.hom ((generalLinearRestriction T n).map f)).toLinearMap =
        (SmoothRep.hom f).toLinearMap :=
    generalLinearRestriction_map_toLinearMap T n
  refine ⟨?_, ?_, ?_⟩
  · intro x y hxy
    rw [generalLinearRestriction_map_apply T n i x,
      generalLinearRestriction_map_apply T n i y] at hxy
    exact hi hxy
  · rw [hmap i, hmap q]
    exact hex
  · intro z
    obtain ⟨y, rfl⟩ := hq z
    exact ⟨y, generalLinearRestriction_map_apply T n q y⟩

/-- The rank transport along an equality of ranks preserves short exact sequences: after
eliminating the equality it is the identity functor. -/
theorem generalLinearRankCast_mapsShortExact {a b : ℕ} (h : a = b) :
    letI := T.topology
    Mirabolic.MapsShortExactIntertwiners (generalLinearRankCast.{uF, uV} T h) := by
  let _ := T.topology
  subst h
  rw [generalLinearRankCast_refl T a rfl]
  exact mapsShortExact_id

/-- The iterated normalized `Φ⁻`, `(Φ⁻)^k : P_(n+k+1) → P_(n+1)`, preserves short exact
sequences, by induction on `k` from the exactness of each normalized `Φ⁻`. -/
theorem phiMinusIterate_mapsShortExact
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n : ℕ) :
    ∀ k : ℕ, letI := T.topology
      Mirabolic.MapsShortExactIntertwiners (phiMinusIterate.{uF, uV} T ψ n k) := by
  let _ := T.topology
  intro k
  induction k with
  | zero =>
    rw [phiMinusIterate_zero]
    exact mapsShortExact_id
  | succ k ih =>
    rw [phiMinusIterate_succ]
    exact mapsShortExact_comp ((Mirabolic.minusExactness.{uF, uV} F T).2.2.2 (n + k) ψ) ih

/-- The mirabolic derivative `Ψ⁻ ∘ (Φ⁻)^k : P_(n+k+1) → GL_n` preserves short exact
sequences. -/
theorem mirabolicDerivative_mapsShortExact
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n k : ℕ) :
    letI := T.topology
    Mirabolic.MapsShortExactIntertwiners (mirabolicDerivative.{uF, uV} T ψ n k) := by
  let _ := T.topology
  rw [mirabolicDerivative_eq]
  exact mapsShortExact_comp (phiMinusIterate_mapsShortExact F T ψ n k)
    ((Mirabolic.minusExactness.{uF, uV} F T).2.2.1 n)

/-- The positive-order derivative `Ψ⁻ ∘ (Φ⁻)^k ∘ Res : GL_(n+k+1) → GL_n` preserves short
exact sequences. -/
theorem generalLinearDerivativePositive_mapsShortExact
    (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (n k : ℕ) :
    letI := T.topology
    Mirabolic.MapsShortExactIntertwiners (generalLinearDerivativePositive.{uF, uV} T ψ n k) := by
  let _ := T.topology
  rw [generalLinearDerivativePositive_eq]
  exact mapsShortExact_comp (generalLinearRestriction_mapsShortExact F T (n + k))
    (mirabolicDerivative_mapsShortExact F T ψ n k)

/-- Every actual derivative `generalLinearDerivative T ψ N k hk : GL_N → GL_(N-k)`,
for every rank `N` and every order `k ≤ N`, preserves short exact sequences of
intertwiners. -/
theorem generalLinearDerivativeExactness :
    GeneralLinearDerivativeExactnessStatement.{uF, uV} F T := by
  let _ := T.topology
  intro ψ N k hk
  cases k with
  | zero =>
    rw [generalLinearDerivative_zero]
    exact mapsShortExact_id
  | succ k =>
    rw [generalLinearDerivative_succ]
    exact mapsShortExact_comp (generalLinearRankCast_mapsShortExact F T _)
      (generalLinearDerivativePositive_mapsShortExact F T ψ (N - (k + 1)) k)

end Langlands.AllFieldBZ.Derivative
