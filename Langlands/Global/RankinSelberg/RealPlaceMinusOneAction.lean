import Langlands.Global.RankinSelberg.ArchimedeanPlaces
import Langlands.Global.ArchimedeanPlaceAdjoint

/-! # Scalar action of minus one at a real place -/

noncomputable section
universe u

open scoped Classical TensorProduct Matrix.Norms.Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000

namespace Langlands.Global

variable (F : Type u) [Field F] (n : ℕ)

local notation "RP" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsReal v}

/-- Minus one at a single real place is central in the full infinite compact. -/
theorem realPlaceCompactMinusOne_commute (v : RP) (k : standardInfiniteCompact F n) :
    Commute (realPlaceCompactInclusion F n v (-1)) k := by
  obtain ⟨p, rfl⟩ := ArchimedeanCompactFactors.toStandardCompact_surjective F n k
  change ArchimedeanCompactFactors.toStandardCompact F n
      (ArchimedeanCompactFactors.realPlaceFactor F n v (-1)) * _ =
    _ * ArchimedeanCompactFactors.toStandardCompact F n
      (ArchimedeanCompactFactors.realPlaceFactor F n v (-1))
  rw [← map_mul, ← map_mul]
  congr 1
  apply Prod.ext
  · funext w
    change (Pi.mulSingle v (-1) : RP → Matrix.unitaryGroup (Fin n) ℝ) w * p.1 w =
      p.1 w * (Pi.mulSingle v (-1) : RP → Matrix.unitaryGroup (Fin n) ℝ) w
    by_cases hw : w = v
    · subst w
      simp
    · simp [hw]
  · funext w
    change 1 * p.2 w = p.2 w * 1
    simp

namespace ArchimedeanGL

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The actual full real Lie adjoint of this central matrix is the identity. -/
theorem realLieConjugation_realPlaceMinusOne (v : RP) (X : RealLieAlgebra F n) :
    realLieConjugation F n (realPlaceCompactInclusion F n v (-1)).val X = X := by
  apply (realLiePlaceCoordinates F n).injective
  apply Prod.ext
  · funext w
    change realPlaceLieProjection F n w _ = realPlaceLieProjection F n w X
    rw [realProjection_realLieConjugation, ← Subgroup.coe_inv, ← map_inv,
      inv_neg_one, realMatrix_realPlaceCompactInclusion]
    by_cases hw : w = v
    · subst w
      simp only [Pi.mulSingle_eq_same]
      change (-1 : Matrix (Fin n) (Fin n) ℝ) * _ * (-1) = _
      simp
    · simp [hw]
  · funext w
    change complexPlaceLieProjection F n w _ = complexPlaceLieProjection F n w X
    rw [complexProjection_realLieConjugation, ← Subgroup.coe_inv, ← map_inv,
      inv_neg_one, complexMatrix_realPlaceCompactInclusion]
    simp

theorem complexLieConjugation_realPlaceMinusOne (v : RP) (X : ComplexLieAlgebra F n) :
    complexLieConjugation F n (realPlaceCompactInclusion F n v (-1)).val X = X := by
  induction X using TensorProduct.inductionOn with
  | tmul z X =>
    rw [complexLieConjugation_tmul, realLieConjugation_realPlaceMinusOne]
  | add X Y hX hY => simp only [map_add, hX, hY]

/-- Centrality extends from the Lie generators to the whole enveloping algebra. -/
theorem envelopingConjugation_realPlaceMinusOne (v : RP) (a : EnvelopingAlgebra F n) :
    envelopingConjugation F n (realPlaceCompactInclusion F n v (-1)).val a = a := by
  have he : (envelopingConjugation F n
      (realPlaceCompactInclusion F n v (-1)).val).toAlgHom =
      AlgHom.id ℂ (EnvelopingAlgebra F n) := by
    apply UniversalEnvelopingAlgebra.hom_ext
    apply LieHom.ext
    intro X
    change envelopingConjugation F n (realPlaceCompactInclusion F n v (-1)).val
      (envelopingGenerator F n X) = envelopingGenerator F n X
    rw [envelopingConjugation_generator, complexLieConjugation_realPlaceMinusOne]
  exact AlgHom.congr_fun he a

end ArchimedeanGL
end Langlands.Global

namespace Langlands.Global.RankinSelbergGlobal

open Langlands.Automorphic

variable {F : Type u} [Field F] [NumberField F]

local instance (n : ℕ) : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance {n : ℕ} (S : OperatorRealization F n) : AddCommGroup S.Space :=
  Submodule.addCommGroup _

set_option maxHeartbeats 1000000 in
/-- The real-place central involution intertwines the full operator algebra. -/
def realPlaceMinusOneIntertwiner {n : ℕ} (S : OperatorRealization F n)
    (v : {v : NumberField.InfinitePlace F // v.IsReal}) : S.Intertwiner S :=
  OperatorRealization.Intertwiner.ofGenerators
    (S.realPlaceCompactRepresentation v (-1))
    (fun d x => (S.finiteRepresentation_realPlaceCompactRepresentation d v (-1) x).symm)
    (fun k x => by
      change S.compactRepresentation (realPlaceCompactInclusion F n v (-1))
          (S.compactRepresentation k x) =
        S.compactRepresentation k
          (S.compactRepresentation (realPlaceCompactInclusion F n v (-1)) x)
      exact congrArg (fun A : Module.End ℂ S.Space => A x)
        ((realPlaceCompactMinusOne_commute F n v k).map S.compactRepresentation).eq)
    (fun a x => by
      change S.compactRepresentation (realPlaceCompactInclusion F n v (-1))
          (S.envelopingAction a x) =
        S.envelopingAction a
          (S.compactRepresentation (realPlaceCompactInclusion F n v (-1)) x)
      simpa only [ArchimedeanGL.envelopingConjugation_realPlaceMinusOne] using
        S.compactRepresentation_envelopingAction
          (realPlaceCompactInclusion F n v (-1)) a x)

/-- A central involution on an irreducible representation is either plus or minus identity. -/
theorem intertwiner_involution_eq_one_or_neg_one
    {G V : Type*} [Monoid G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) [ρ.IsIrreducible]
    (A : ρ.IntertwiningMap ρ) (hA : ∀ x, A (A x) = x) :
    (∀ x, A x = x) ∨ (∀ x, A x = -x) := by
  let B : ρ.IntertwiningMap ρ := A - 1
  rcases Representation.IsIrreducible.injective_or_eq_zero B with hB | hB
  · right
    intro x
    have hz : B (A x + x) = B 0 := by
      change A (A x + x) - (A x + x) = A 0 - 0
      rw [map_add, hA, map_zero]
      abel
    exact eq_neg_of_add_eq_zero_left (hB hz)
  · left
    intro x
    have hx := congrArg (fun C : ρ.IntertwiningMap ρ => C x) hB
    change A x - x = 0 at hx
    exact sub_eq_zero.mp hx

variable [CompactSpace (AdeleQuotient F)]

set_option maxHeartbeats 1000000 in
/-- Scalar action is unconditional for the actual irreducible cuspidal realization. -/
theorem exists_realPlaceMinusOneScalar {r : ℕ} (T : CuspidalOperatorRealization F r)
    (v : {v : NumberField.InfinitePlace F // v.IsReal}) :
    ∃ c : ℂ, ∀ x : T.Space,
      T.realization.realPlaceCompactRepresentation v (-1) x = c • x := by
  let : T.realization.representation.IsIrreducible := T.irreducible
  have hinv : ∀ x : T.Space,
      realPlaceMinusOneIntertwiner T.realization v
        (realPlaceMinusOneIntertwiner T.realization v x) = x := by
    intro x
    change T.realization.realPlaceCompactRepresentation v (-1)
      (T.realization.realPlaceCompactRepresentation v (-1) x) = x
    have hρ := congrArg (fun A : Module.End ℂ T.Space => A x)
      ((T.realization.realPlaceCompactRepresentation v).map_mul
        (-1 : Matrix.unitaryGroup (Fin (r + 1)) ℝ) (-1))
    simpa only [neg_mul_neg, one_mul, map_one, Module.End.one_apply,
      Module.End.mul_apply] using hρ.symm
  rcases intertwiner_involution_eq_one_or_neg_one T.realization.representation
      (realPlaceMinusOneIntertwiner T.realization v) hinv with h | h
  · exact ⟨1, fun x => (h x).trans (one_smul ℂ x).symm⟩
  · exact ⟨-1, fun x => (h x).trans (neg_one_smul ℂ x).symm⟩

/-- The Library's chosen scalar always gives the actual action. -/
theorem realMinusOneScalar_action {r : ℕ} (T : CuspidalOperatorRealization F r)
    (v : {v : NumberField.InfinitePlace F // v.IsReal}) (x : T.Space) :
    T.realization.realPlaceCompactRepresentation v (-1) x = realMinusOneScalar T v • x :=
  realMinusOneScalar_spec T v (exists_realPlaceMinusOneScalar T v) x

end Langlands.Global.RankinSelbergGlobal
