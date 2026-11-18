import Langlands.Global.RankinSelberg.RealLocalWhittakerModel
import Langlands.Representation.Archimedean.RealStandardModuleGKModule
import Langlands.LocalFactor.ArchimedeanPairFactor

/-! # Duality and factor invariance for real standard modules

Two local statements about the `O(n)`-finite real standard modules `I(ds)` of `GL_n(ℝ)`:

* `RealStandardDualPairingStatement` (duality): if `I(ds)` is irreducible, there is an
  invariant bilinear pairing of `I(ds)` with `I(ds.map dualBlock)` under which every nonzero
  vector of `I(ds.map dualBlock)` pairs nontrivially with some vector of `I(ds)`;
* `RealStandardIntertwinerPairLStatement` (factor invariance): if `I(es)` and `I(es')` are
  irreducible and there is a nonzero `(𝔤, K)`-intertwiner `I(es) → I(es')`, then `es` and
  `es'` have pair `L`-factors with the same denominator against every list of real blocks, in
  either slot.

Neither is proved here. See the paired Markdown.
-/

noncomputable section
open scoped TensorProduct
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.Automorphic Langlands.LocalFactor.Archimedean Langlands.Archimedean

/-- **Duality.** Let `ds` be a list of real blocks of total rank `n` whose `O(n)`-finite real
standard module `I(ds)` is an irreducible `(𝔤𝔩_n(ℝ), O(n))`-module. Then there is a bilinear
pairing `Q` of `I(ds)` with the `O(n)`-finite real standard module of the dualized blocks
`ds.map dualBlock` that is invariant under right translation by `O(n)`, satisfies
`Q(X f, h) + Q(f, X h) = 0` for the right derivatives along real matrices `X`, and is such that
every nonzero `h` of the second module has some `f` of `I(ds)` with `Q f h ≠ 0`. -/
def RealStandardDualPairingStatement : Prop :=
  ∀ (n : ℕ) (ds : List RealBlock), realRank ds = n →
    IsIrreducibleGKModule (realStandardRep n ds) (realStandardLie n ds) →
    ∃ Q : realStandardKFinite n ds →ₗ[ℂ]
        realStandardKFinite n (ds.map RealLocalJacquet.dualBlock) →ₗ[ℂ] ℂ,
      ((∀ (k : Matrix.unitaryGroup (Fin n) ℝ) (f : realStandardKFinite n ds)
          (h : realStandardKFinite n (ds.map RealLocalJacquet.dualBlock)),
          Q (realStandardRep n ds k f)
              (realStandardRep n (ds.map RealLocalJacquet.dualBlock) k h) = Q f h) ∧
        ∀ (X : Matrix (Fin n) (Fin n) ℝ) (f : realStandardKFinite n ds)
          (h : realStandardKFinite n (ds.map RealLocalJacquet.dualBlock)),
          Q (realStandardLie n ds (1 ⊗ₜ X) f) h +
              Q f (realStandardLie n (ds.map RealLocalJacquet.dualBlock) (1 ⊗ₜ X) h) = 0) ∧
        ∀ h : realStandardKFinite n (ds.map RealLocalJacquet.dualBlock), h ≠ 0 →
          ∃ f : realStandardKFinite n ds, Q f h ≠ 0

/-- **Factor invariance.** Let `es` and `es'` be lists of real blocks of total rank `n` whose
`O(n)`-finite real standard modules are irreducible `(𝔤𝔩_n(ℝ), O(n))`-modules. If some
nonzero linear map from the first to the second intertwines the actions of `O(n)` and of
`𝔤𝔩_n(ℝ)`, then for every list `xs` of real blocks the pair `L`-factors of `es` and of `es'`
against `xs` have the same denominator, with `xs` in the second slot and with `xs` in the first
slot. -/
def RealStandardIntertwinerPairLStatement : Prop :=
  ∀ (n : ℕ) (es es' : List RealBlock), realRank es = n → realRank es' = n →
    IsIrreducibleGKModule (realStandardRep n es) (realStandardLie n es) →
    IsIrreducibleGKModule (realStandardRep n es') (realStandardLie n es') →
    ∀ T : realStandardKFinite n es →ₗ[ℂ] realStandardKFinite n es',
      IsRealStandardIntertwiner n (realStandardRep n es') (realStandardLie n es') es T →
        T ≠ 0 →
        ∀ xs : List RealBlock,
          (realPairLFactor es xs).denominator = (realPairLFactor es' xs).denominator ∧
            (realPairLFactor xs es).denominator = (realPairLFactor xs es').denominator

end Langlands.Global.RankinSelbergGlobal
