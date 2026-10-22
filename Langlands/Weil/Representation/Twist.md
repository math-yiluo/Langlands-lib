# Character twists of finite-dimensional representations

Worker 17 authored this finite-dimensional packaging of the published
character-twist interface. `twist chi A` retains the actual vector space
and acts by `chi(g)` times the original action. Its finite-dimensional
certificate is the original one.

`twistFunctor` uses `Langlands.twistIntertwining`, retaining the linear
map on each morphism. Identity and composition follow from equality of
those maps. `twistFullyFaithful` uses `untwistIntertwining` to cancel the
common unit-valued character and proves both inverse equations.
`twistEquiv` retains an actual linear representation equivalence, and
certifies `twistClass` on the genuine quotient. Coefficient, group and
carrier universes remain independent; zero-dimensional objects are allowed.

The character is an algebraic homomorphism into units. No continuity or
unitarity is included. This construction does not assert preservation
of a separately imposed inertia or continuity predicate.

Exact imported dependency: Worker 4's
`Langlands.Representation.Twist.Definitions`, present at Library commit
`843c574c920aa9926ab56adf662c74b3cd4ed0e1`, effective Lean SHA-256
`9e193a22784cba92e727402aac5117056433e796e37e1c76f8710e2ddd11d8cf`.
The source is imported, not copied. The finite-representation foundation
`Langlands.Weil.Representation.Basic` is published in that same Library tree.

Source correspondence: Henniart, *Une preuve simple des conjectures de
Langlands pour GL(n) sur un corps p-adique* (2000), §1.2(2), printed
page 440, specifies the Weil-side scalar tensor twist. The distinction
between quasicharacters and unitary characters is in §1.1, footnote 1,
page 439. Literature ID `henniart-2000-simple-proof`, PDF SHA-256
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
The category and quotient packaging is intrinsic implementation work.
