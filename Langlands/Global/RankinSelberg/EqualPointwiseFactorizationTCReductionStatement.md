# Equal-rank pointwise factorization from complex place tests and the TC slice comparison

Module `Langlands.Global.RankinSelberg.EqualPointwiseFactorizationTCReductionStatement`,
namespace `Langlands.Global.RankinSelbergGlobal`. The field universe `u` and the spectral
presentation universe `uQ` are independent.

`EqualPointwiseFactorizationTCReductionStatement` is the implication from two premises:

1. [`InfiniteWhittakerSliceModelTCStatement`](InfiniteWhittakerSliceModelTCStatement.md)
   gives the normalized local model maps and actual one-place slice equalities for a
   single cuspidal realization and its spectral presentation at each totally complex
   field. The comparison can be applied separately to each member of the pair.
2. `ComplexEqualPlaceTestsStatement` in
   [`EqualInfinitePlaceTests`](EqualInfinitePlaceTests.md) supplies the actual local
   Whittaker restrictions for opposite characters, a Schwartz function and quotient
   measure data at a complex place. For the chosen data, the ordinary and dual test
   integrals are each holomorphic on a right half-plane and nonzero at a point of their
   respective half-planes. This is the existing proposition at all complex places of
   number fields with its original hypotheses, not a functional equation.

The conclusion is `EqualPointwiseFactorizationTCStatement` in
[`EqualFactorizationAtStatement`](EqualFactorizationAtStatement.md), with no change to
its data. It gives the ordinary and dual pointwise product formulas on the integral
quotient classes for two cuspidal realizations of the same positive rank, including
rank one. It uses one common nonzero scalar for the two Whittaker integrand formulas,
retains the local test integrals and their nonvanishing clauses (and those of the
archimedean products), and retains the exact, scalar-free product formulas for the
Schwartz–Bruhat function and its Fourier transform. The index for real places is empty
at the fields of the conclusion. There is no real-place test premise.

## Provenance and proof boundary

The intended proof uses the published `equalInfiniteWhittakerTest_of_local` argument
from [`EqualInfiniteWhittakerSliceReduction`](EqualInfiniteWhittakerSliceReduction.md)
at a fixed totally complex field `F`. In that argument the comparison for the character
and for its inverse is needed only at `F`, and the real tests are requested only at real
places of `F`, of which there are none. The complex tests supply the remaining data.
The resulting joint infinite test feeds the argument of `equalPointwiseOfInfiniteTests`
from [`EqualInfiniteWhittakerReduction`](EqualInfiniteWhittakerReduction.md), which
likewise uses its infinite input only at `F`. The published unrestricted reductions
cannot be applied directly to the restricted hypotheses. No step here changes their
types or `ArchimedeanFactorizationStatement`.

This is a proof target, not a proof of the implication or of either premise. It does
not integrate the pointwise formulas or prove a local or global functional equation.
The separate same-field integration target can consume its conclusion at each
totally complex field.

**Source.** J. W. Cogdell, *Analytic theory of L-functions for GL_n*, in J. Bernstein
and S. Gelbart (eds.), *An Introduction to the Langlands Program*, Birkhäuser, 2004,
pp. 197–228, `cogdell-2004-analytic-theory-gln`, §1.2, printed pp. 201–202 (PDF pp.
204–205), for the factorization of pure-tensor Whittaker functions, and §2.3, printed
pp. 210–211 (PDF pp. 213–214), for the two equal-rank products with factorizable
Schwartz data. The Lean division into pointwise and integrated statements, the
actual comparison and test hypotheses, and the restriction by field signature
are derived Library interfaces, not separate assertions of Cogdell.
