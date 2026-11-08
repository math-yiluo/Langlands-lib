import Mathlib.GroupTheory.DoubleCoset
import Mathlib.RingTheory.Length
import Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints
import Langlands.Representation.Exponents.LeviSupercuspidalInductionSupport
import Langlands.Representation.Plancherel.UnramifiedCharacters
import Langlands.Representation.Plancherel.RationalCharacterValuation
import Langlands.Representation.Category.Twist
import Langlands.GroupScheme.Rational.ParabolicPointConjugation
import Langlands.GroupScheme.Reductive.Basic

/-! # The length of an induced supercuspidal representation (Renard VI.10.3, Corollary)

For a parabolic `P = MN` of `G` and an irreducible supercuspidal representation `ρ` of
`M(F)` with inertial class `D = [M, ρ]_M`, the length of `i_P^G(ρ)` is at most `|W(D)|`, the
number of elements of `N_G(M)/M` whose conjugation preserves `D`. In particular `i_P^G(ρ)`
is irreducible when `W(D)` is trivial.
-/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- Renard VI.10.3, Corollary, in derived form: let `P = MN` be an actual rational parabolic
of `G` and `ρ` an irreducible supercuspidal smooth representation of `M(F)`. Let `W` be the
set of double cosets `P(F) w P(F)` containing an element `w` that normalizes `M`, through
an automorphism `φ` of `M` with `w · ι(m) · w⁻¹ = ι(φ m)` for the embedding `ι = l ≫ p`, such
that the conjugate `ρ ∘ φ` is isomorphic to an unramified twist `ρ ⊗ χ`. Then the length of
`i_P^G(ρ)` (as a module over the group algebra of `G(F)`) is at most the cardinality of `W`,
and `i_P^G(ρ)` is irreducible if `W` has at most one element. The set `W` is in bijection
with Renard's `W(D) = {w ∈ W(M, M) | w · D = D} / W_M`. -/
def SupercuspidalInductionLengthStatement : Prop :=
  ∀ (k : Type u) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [T2Space k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    letI : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
    ∀ [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]
      (P M N : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (l : M ⟶ P) (r : N ⟶ P)
      (hp : IsParabolicSubgroup p) (hl : IsRationalLeviSubgroup l)
      (hr : LeviSubgroup.IsGeometricUnipotentRadical r)
      (hmul : IsIso (subgroupMultiplication l r)),
      haveI := hl.isConnectedReductive.isAffineHom
      letI : TopologicalSpace (rationalPoints M) := leviPointTopology l hl
      haveI : LocallyCompactSpace (rationalPoints M) := leviPoints_locallyCompactSpace p l hp hl
      haveI : NonarchimedeanGroup (rationalPoints M) := leviPoints_nonarchimedeanGroup p l hp hl
      ∀ ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M), ρ.IsIrreducible → IsSupercuspidal ρ →
        let W : Set (DoubleCoset.Quotient (pointImage p : Set (rationalPoints G))
            (pointImage p : Set (rationalPoints G))) :=
          {x | ∃ (w : rationalPoints G) (φ : M ≅ M) (e : rationalPoints M ≃ₜ* rationalPoints M)
              (χ : Plancherel.unramifiedCharacters
                (fun χ : rationalCharacters M => (Plancherel.rationalNormCharacters M χ).toMul)),
            DoubleCoset.mk (pointImage p) (pointImage p) w = x ∧
              φ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso w).hom ∧
              (∀ m, e m = rationalPoints.map φ.hom m) ∧
              Nonempty (SmoothRep.pullback e ρ ≅
                ρ.twist χ.val.toMonoidHom (Plancherel.unramifiedCharacter_isOpen_ker _ χ))}
        let π := (leviInductionFunctor p l r hp hr hl hmul).obj ρ
        Module.length (MonoidAlgebra ℂ (rationalPoints G)) π.representation.asModule ≤
            W.encard ∧
          (W.encard ≤ 1 → π.IsIrreducible)

end Langlands.Aubert.General.RepresentedParabolic
