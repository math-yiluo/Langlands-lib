# Reduction to one actual compatible apartment

This module proves that constructing one compatible quasi-split apartment
with full indivisible derivative lifts is equivalent to the published
`QuasiSplitIndivisibleDerivativeLiftsStatement`. The actual construction
remains open here.

`QuasiSplitIndivisibleApartmentExistenceStatement` retains every field,
valuation, henselianity, group, quasi-splitness, prescribed maximal split
torus, and universe parameter of the published target. Its conclusion
constructs an actual `KPApartmentData D` and actual `CentralizerDatum C`
with full integer-valued V6 compatibility and
`HasIndivisibleDerivativeLifts D.affineRoots`. It imposes no new premise on
the target and makes no reduced-subsystem substitution. Every full
derivative, including multipliable ones, is retained.

The implemented transport first changes the centralizer representative
using `IntegerValuation.IsOmegaCompatible.changeCentralizer`. It then uses
`IntegerValuation.IsOmegaCompatible.eq_of_isMaximalSplitTorus` to identify
the compatible apartment data. Substitution transfers the entire derivative
lift assertion, including its dependent apartment and affine functional
types. Thus any existential witness supplies the published universal
target, for every compatible apartment and every centralizer
representative. Conversely, the already published
`quasiSplitIntegerApartmentExistence` supplies a compatible apartment to
which the universal target can be applied.

This is an internal logical reduction derived from the named Library
theorems and definitions. Its source motivation is Kaletha–Prasad,
*Bruhat–Tits Theory: A New Approach* (2023), Proposition 6.2.6, printed
p.216, PDF p.247, identifying compatible valuation classes, together with
the quasi-split construction underlying Proposition 6.4.8. The registered
source is `kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The 2024 corrections, `kaletha-prasad-2024-corrections`, SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
PDF p.32, require the adjoint-group reduction for general reductive groups.
This module does not perform that construction or assert the exceptional
integer-constant description for an actual apartment.

There are no perfect-residue-field, completeness, characteristic,
classification, or Kneser–Tits assumptions. The equivalence and transfer
lemmas do not prove either of the equivalent full construction assertions
without a further input.
