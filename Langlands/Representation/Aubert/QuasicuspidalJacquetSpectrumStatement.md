# Conditional quasicuspidal Jacquet spectrum comparison

Author: Worker 320.

`Langlands.Aubert.QuasicuspidalJacquetSpectrumStatement` is an internal
conditional interface for a supplied actual signed Aubert image. The module
defines a proposition and supplies no proof.

Fix an arbitrary prime `p`, a field `F : PadicField.{uF} p`, and supplied
compatible topological data `T`. The field universe `uF` and carrier universe
`uV` are independent; actual smooth complex representations have carriers in
`Type (max uF uV)`. All Jacquet modules use the Library's normalized upper
block convention.

For every rank `n`, block shape `B`, and actual finite-length smooth
representations `π, τ` of `GL_n(F)`, assume both representations are
admissible. Let `ε : ℤ` be either `1` or `-1`, and assume the equality

`D[π] = ε[τ]`

in the actual exact finite-length Grothendieck group. Assume also that the
actual normalized Jacquet module `J_(B.reverse)(π)` is quasicuspidal on its
product Levi and has a nontrivial carrier.

The proposition concludes that `ε = (-1)^(n - B.length)` and, for every
character `χ : (Fˣ)^B.length →* ℂˣ`, the following are equivalent:

- `χ` is a generalized eigencharacter of `J_B(τ)` restricted to the block
  scalar center of `B`;
- `χ` is a generalized eigencharacter of the actual transported
  `J_(B.reverse)(π)`, restricted to that same block scalar center.

Here transport is exactly `CuspidalSupport.transport B.reverse B` along
`B.reversePermutation` and its published whole-Levi conjugation
certificate. Its action uses inverse conjugation and retains the actual
Jacquet carrier. The second action is written literally in Lean, so the
statement requires no implicit identification of block coordinates.
Generalized occurrence means a nonzero vector killed by one common power
of every scalar-defect operator. The equivalence preserves the character;
it need not preserve a chosen vector or nilpotence exponent.

The character is arbitrary as an algebraic homomorphism. No open-kernel
assumption is imposed here. For a character with open kernel, adjoining that
same condition to both sides gives the corresponding Jacquet-exponent
comparison. This proposition itself asserts only generalized occurrence.

## Provenance and intended derivation

This is a derived internal interface. It combines the conclusions of the
published `Aubert.quasicuspidalJacquetClass` and
`Langlands.exactClassCentralSpectrum`, rather than transcribing a new
original-literature assertion.

The intended proof first obtains the sign and equal actual Jacquet classes
from the former theorem. Normalized Jacquet functors preserve finite
length and admissibility, and actual whole-Levi transport preserves both.
On the target product Levi, compact open subgroups are cofinal and the
block-scalar map into its center is continuous. The latter theorem then
transfers generalized occurrence between the two actual objects with equal
exact classes. These are proof obligations, not extra assumptions in this
proposition.

The interface does not construct an Aubert image, assume its general
irreducibility theorem, or identify whole representations from equal
Grothendieck classes. It asserts no square-integrability criterion or
single-segment classification. Quasicuspidality and nonzero reversed
Jacquet data are essential stated hypotheses. No multisegment exhaustion,
ordered strong-head coverage, or downstream Langlands classification is
part of the proposed derivation.
