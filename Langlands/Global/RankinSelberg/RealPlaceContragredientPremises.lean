import Langlands.Global.RankinSelberg.RealLocalTheoryReduction
import Langlands.Automorphic.CuspidalArchimedeanComponentStatement

/-! # Premises for the real-place contragredient pair-factor reduction

`RealPlaceContragredientPairLStatement` says: if `Td`, `Td'` are contragredient to the actual
cuspidal realizations `T`, `T'`, and `ds`, `es`, `dds`, `ees` are parameters of `T`, `T'`, `Td`,
`Td'` at the real place `v`, then the pair `L`-factors of `(dds, ees)` and of the dualized
blocks `(ds.map dualBlock, es.map dualBlock)` have the same denominator. This module states one
new local premise and the reduction statement; neither is proved here:

* `RealStandardPairingPairLStatement` (local): if the `O(n)`-finite real standard modules of
  `ds` and `dds` are irreducible `(𝔤, K)`-modules and carry a nonzero invariant bilinear
  pairing, then `dds` and `ds.map dualBlock` have pair `L`-factors with the same denominator
  against every list of real blocks, in either slot;
* `RealPlaceContragredientPairLReductionStatement`: the published global irreducibility
  statement `Automorphic.CuspidalArchimedeanStandardIrreducibleStatement` and the local premise
  imply `RealPlaceContragredientPairLStatement`. It is proved in
  `Langlands.Global.RankinSelberg.RealPlaceContragredientReduction`.

See the paired Markdown.
-/

noncomputable section
universe u
open scoped TensorProduct
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.Automorphic Langlands.LocalFactor.Archimedean Langlands.Archimedean

/-- `P` is a `(𝔤, K)`-invariant bilinear pairing of the `O(n)`-finite real standard modules of
`ds` and `dds`: `P(k f, k f') = P(f, f')` for `k ∈ O(n)` acting by right translation, and
`P(X f, f') + P(f, X f') = 0` for the right derivatives along `X ∈ 𝔤𝔩_n(ℝ)`. -/
def IsRealStandardInvariantPairing (n : ℕ) (ds dds : List RealBlock)
    (P : realStandardKFinite n ds →ₗ[ℂ] realStandardKFinite n dds →ₗ[ℂ] ℂ) : Prop :=
  (∀ (k : Matrix.unitaryGroup (Fin n) ℝ) (f : realStandardKFinite n ds)
      (f' : realStandardKFinite n dds),
      P (realStandardRep n ds k f) (realStandardRep n dds k f') = P f f') ∧
    ∀ (X : Matrix (Fin n) (Fin n) ℝ) (f : realStandardKFinite n ds)
      (f' : realStandardKFinite n dds),
      P (realStandardLie n ds (1 ⊗ₜ X) f) f' + P f (realStandardLie n dds (1 ⊗ₜ X) f') = 0

/-- **Local pairing premise.** Let `ds` and `dds` be lists of real blocks of total rank `n`
whose `O(n)`-finite real standard modules are irreducible `(𝔤𝔩_n(ℝ), O(n))`-modules and carry
a nonzero invariant bilinear pairing. Then, for every list `xs` of real blocks, the pair
`L`-factors of `dds` and of the dualized blocks `ds.map dualBlock` against `xs` have the same
denominator, with `xs` in the second slot and with `xs` in the first slot. -/
def RealStandardPairingPairLStatement : Prop :=
  ∀ (n : ℕ) (ds dds : List RealBlock), realRank ds = n → realRank dds = n →
    IsIrreducibleGKModule (realStandardRep n ds) (realStandardLie n ds) →
    IsIrreducibleGKModule (realStandardRep n dds) (realStandardLie n dds) →
    ∀ P : realStandardKFinite n ds →ₗ[ℂ] realStandardKFinite n dds →ₗ[ℂ] ℂ,
      IsRealStandardInvariantPairing n ds dds P → P ≠ 0 →
      ∀ xs : List RealBlock,
        (realPairLFactor dds xs).denominator =
            (realPairLFactor (ds.map RealLocalJacquet.dualBlock) xs).denominator ∧
          (realPairLFactor xs dds).denominator =
            (realPairLFactor xs (ds.map RealLocalJacquet.dualBlock)).denominator

/-- **The reduction.** The published irreducibility of the archimedean standard-module
components of actual cuspidal realizations and the local pairing premise imply the
real-place contragredient pair-factor statement. -/
def RealPlaceContragredientPairLReductionStatement : Prop :=
  Automorphic.CuspidalArchimedeanStandardIrreducibleStatement.{u} →
    RealStandardPairingPairLStatement → RealPlaceContragredientPairLStatement.{u}

end Langlands.Global.RankinSelbergGlobal
