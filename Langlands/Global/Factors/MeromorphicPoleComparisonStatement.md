# Removing regular factors before comparing poles

This module defines the conditional local analytic step used by the H1
comparison engine. Its target is
`Langlands.Global.PoleComparison.MeromorphicPoleComparisonStatement`.
It is a proposition definition, not a proof of that proposition.

The data are actual functions from `ℂ` to `ℂ`. `omittedProduct S f` is the
finite product over the supplied finite set `S`; `completedProduct` multiplies
the distinguished local function by that product and a separate boundary
function. The two sides may have different index types, in independent
universes, and different finite sets. No product over all places is formed.
An empty omitted set is allowed and contributes the multiplicative identity.

`HolomorphicUnitAt f z` means precisely that `f` is complex analytic at `z`
and that `f z` is nonzero. `OmittedUnitsAt` requires this for every member of
the specified finite set. Boundary regularity is an additional hypothesis,
with the same two explicit conditions, on each boundary function. It does not
follow from the regularity of the omitted local functions.

The first two conjuncts assert that multiplication by these regular nonzero
functions preserves `meromorphicOrderAt`. They do not require the
distinguished function to have a nonzero value. The last conjunct assumes the
two distinguished functions are meromorphic at the comparison point and that
the completed functions agree on a punctured neighborhood of that point.
It concludes that the two distinguished meromorphic orders agree. Orders
use Mathlib's convention: poles have negative order and zeros positive order.
No pole multiplicity is discarded by taking a natural-number part.

This is a derived analytic prerequisite, motivated by Henniart, *Une preuve
simple des conjectures de Langlands pour GL(n) sur un corps p-adique* (2000),
§§2.5–2.8, printed pp.445–448. Those passages compare local pair factors and
then use their pole orders to identify the pairings on virtual
representations. The finite-product formulation here is internal to H1,
not a separately numbered theorem of that article.

The H1 finite-set functional-equation engine supplies completed germ
identities separately. Applications must also supply the original local
meromorphic factors, the omitted factors, and the boundary functions. The
global boundary nonvanishing input, including the relevant use of Shahidi
(1981), Theorem 5.2, remains an unresolved input owned by the parent program
`34b81620-20d7-4059-9b08-6bedd1c1c029` and its common library track.
This target neither proves that theorem nor identifies local regularity with
global nonvanishing. Factor existence, functional equations, and highly
ramified twist stability are not asserted by this module.
