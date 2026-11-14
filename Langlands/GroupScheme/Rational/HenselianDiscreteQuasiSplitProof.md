# Quasi-splitness over Henselian discretely valued fields: the proof

Author: Worker 4699.

Lean module: `Langlands.GroupScheme.Rational.HenselianDiscreteQuasiSplitProof`,
namespace `Langlands.GroupScheme`.

`henselianDiscreteQuasiSplit : HenselianDiscreteQuasiSplitStatement.{u}` proves the
published statement unchanged, for an arbitrary universe `u`: for a field `K : Type u`, a
surjective valuation `v : Valuation K (WithZero (Multiplicative ℤ))` whose valuation subring
is Henselian and whose residue field is algebraically closed, every connected reductive
group scheme over `Spec K` is `IsQuasiSplit`.

## Proof

The Lean proof is the single application

`henselianDiscreteQuasiSplit_of_dimensionLEOne dimensionLEOneQuasiSplit`,

which combines two published results:

- `dimensionLEOneQuasiSplit : DimensionLEOneQuasiSplitStatement.{u}` (module
  `Langlands.GroupScheme.Rational.DimensionLEOneQuasiSplitProof`) is Steinberg's theorem
  (Kaletha–Prasad Thm. 2.3.3(2)): over every field satisfying the finite-separable
  norm criterion `Langlands.FieldTheory.HasDimensionLEOne`, every connected reductive group
  scheme is quasi-split.
- `henselianDiscreteQuasiSplit_of_dimensionLEOne` (module
  `Langlands.GroupScheme.Rational.HenselianDiscreteQuasiSplitReduction`) takes Steinberg's
  theorem to the target. Given `K`, `v` and the Henselian and residue hypotheses, it
  obtains `HasDimensionLEOne K` from `Langlands.FieldTheory.henselianDiscreteDimensionLEOne`
  (Kaletha–Prasad Cor. 2.3.7) and then applies Steinberg's theorem to the group scheme.

No hypothesis is added and the statement is not modified.

## Provenance

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), Corollary 2.3.8, printed p.81
(PDF p.112), source `kaletha-prasad-2023-bruhat-tits-new-approach`. The proof follows the
book's route: Corollary 2.3.7 (the field has dimension at most one) and Theorem 2.3.3(2)
(Steinberg's theorem), printed pp.79–81 (PDF pp.110–112).
