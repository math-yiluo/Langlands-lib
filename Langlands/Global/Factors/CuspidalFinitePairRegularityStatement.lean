import Langlands.Global.Factors.CuspidalPairPoleStatement

/-!
# Regularity of the finite pair L-factors of unitary cuspidal realizations on `Re s ≥ 1`

The non-Archimedean half of Getz–Hahn, Theorem 11.5.2, for the local components of two actual
cuspidal realizations with unitary central characters, in the normalization of the finite pair
L-data `CuspidalPairPoles.FinitePairLChoice` used by the pole statement
`Langlands.Global.CuspidalPairPoleStatement`: the pair L-polynomial `P_v` of the local
components at every finite place satisfies `P_v(q_v^(-s)) ≠ 0` whenever `1 ≤ Re s`, so that
`L(s, Π_v × Π'_v) = P_v(q_v^(-s))⁻¹` is finite there. It is the finite-place counterpart of
`Langlands.Automorphic.CuspidalArchimedeanPairRegularityStatement`. This is a statement, not a
proof.
-/

noncomputable section

set_option autoImplicit false

open Polynomial

universe u uQ

namespace Langlands.Global

open NumberField
open Automorphic (CuspidalOperatorRealization CuspidalSpectralPresentation)
open CuspidalPairFunctionalEquation (HasIrreducibleAdmissibleComponents residueCardinality)
open Langlands.ClassFieldTheory.Global.RelativeWeilGroup (HasUnitaryCentralCharacter)

/-- **Getz–Hahn (2024), Theorem 11.5.2, non-Archimedean case, for cuspidal pairs.** For actual
cuspidal realizations `T`, `T'` of `GL_(r+1)`, `GL_(t+1)` with unitary central characters,
spectral presentations of both with irreducible admissible finite components, and finite pair
L-data `c` for them, the pair L-polynomial at every finite place `v` does not vanish at
`q_v^(-s)` when `1 ≤ Re s`. -/
def CuspidalFinitePairRegularityStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r t : ℕ) (T : CuspidalOperatorRealization F r) (T' : CuspidalOperatorRealization F t),
    HasUnitaryCentralCharacter T → HasUnitaryCentralCharacter T' →
  ∀ (P : CuspidalSpectralPresentation.{u, uQ} T)
    (P' : CuspidalSpectralPresentation.{u, uQ} T')
    (h : HasIrreducibleAdmissibleComponents P) (h' : HasIrreducibleAdmissibleComponents P')
    (c : CuspidalPairPoles.FinitePairLChoice P P' h h') (v : FinitePlace F) (s : ℂ),
    1 ≤ s.re →
      (c.lPolynomial v).eval (RankinSelberg.spectralPoint (residueCardinality v) s) ≠ 0

end Langlands.Global
