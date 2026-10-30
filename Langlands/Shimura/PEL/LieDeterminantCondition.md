# The Harris Lie determinant condition on actual scheme sections

This derived characteristic-zero specialization uses the constructed Harris
integer order, the constructed reflex determinant and an actual abelian scheme
over an actual scheme mapping to the spectrum of the cocharacter reflex field.
It defines an additional determinant condition on its order action and proves
that the condition is independent of finite bases and local charts.

The inputs retain the actual totally real field, its CM quadratic extension,
central simple algebra, Harris signature charts and CM-section hypothesis. The
acting ring is `D.harrisHodgePELIntegralOrder C`, constructed using the positive
auxiliary left involution. The base is an actual scheme `S` with an actual
morphism `s` to `Spec` of `D.kottwitzCocharacterReflexField C`. An actual abelian
scheme `B` over `S` carries a unital ring action of that integer order in
`End B`. This unit does not impose injectivity on the action.

For a finite order family `a` and an open `W`, the construction
`harrisReflexSectionDeterminant` maps the coefficients of
`kottwitzReflexDeterminant` for the underlying algebra elements into the actual
ring `Γ(S,W)`. It reuses `secHom s W` from
`SmoothProperConnectedGlobalFunctionsProof`. That helper is defined for any
morphism to an affine spectrum, without smoothness, properness or connectedness
hypotheses. Its compatibility with restriction proves the new polynomial
restriction identity by composition of coefficient maps. The coefficient and
evaluation identities are the corresponding multivariate-polynomial map laws.

On a finite free-sheaf trivialization `e` of `B.Lie` over `U` and an object `V`
of `Over U`, `HarrisLieDeterminantConditionAt` equates the actual
`lieSectionDeterminant B α e a V` to that reflex polynomial on `V.left`.
The Lie polynomial uses the constructed differential action evaluated on the
actual Lie sections and a genuine basis of this section module, supplied by
the sheaf trivialization. The condition is polynomial equality, so its
coefficientwise characterization applies to all monomials, including over
section rings with nilpotents.

The arbitrary finite-basis characterization uses the previously proved
`lieSectionDeterminant_eq_basis`. The overlap equivalence compares two possibly
different finite trivializations on different opens, after passing to any open
contained in both. It uses the existing Lie polynomial overlap identity; the
reflex sides are already the identical polynomial on that common open.
Restriction of the condition follows by applying the actual structure-sheaf
coefficient map to the equality and using both polynomial restriction laws.
Evaluation then gives the intrinsic `LinearMap.det` of every scalar linear
combination of the actual section endomorphisms, equal to evaluation of the
reflex polynomial through `secHom`. This is a consequence of polynomial
equality; the file does not assert an evaluation-only converse.

`HarrisLieDeterminantCondition` is a proposition quantifying all finite order
families, all finite Lie trivializations and every smaller open in each chart.
The local-cover lemma proves descent of this equality on any open covering of
the smaller open: polynomial extensionality reduces to one coefficient at a
time, and the structure sheaf's uniqueness of gluing proves equality from its
restrictions. The final cover equivalence uses the Lie covering constructed in
`LieDeterminant`, whose existence follows from smooth relative differentials,
identity pullback and internal duality. A global condition restricts to its
whole chart opens. Conversely, the proof intersects any proposed chart open
with the members of that covering, restricts the equality, changes charts on
each intersection and uses the local-cover lemma. Thus checking that actual
cover suffices. The number of covering opens is not asserted to be finite;
each trivialization has a finite basis.

The original source is Robert E. Kottwitz, *Points on Some Shimura Varieties over
Finite Fields*, Journal of the American Mathematical Society 5 (1992), 373–444,
section 5, printed pp.389–391 (PDF pp.17–19), source ID
`kottwitz-1992-points-shimura-finite-fields`, SHA-256
`c7cede3d0a5e201068e6100acbb3832adb67767d69248ec65458e7cc74ee46f1`.
These pages were reread for this construction. The source's p.389 defines the
Hodge polynomial for a basis of a prime-local order and states its reflex and
integral coefficient properties; p.390 requires equality with the polynomial
on Lie sections; p.391 addresses representability for sufficiently small levels.

This unit is a derived reflex-field condition using the constructed integer
order and requiring every finite family. It makes no assertion that arbitrary
abelian schemes satisfy the condition. It does not identify this predicate
with the entire original prime-local moduli problem: the prime-local order and
integral coefficient model, projectivity and isogeny category, polarization,
levels and moduli representability remain separate obligations. No output
scheme or desired Hodge comparison theorem is supplied as construction data.

Worker 57 authored this unit. All arithmetic types, the polynomial variable and
finite chart-basis types, and the base scheme have universe-zero scope, matching
the existing reflex polynomial. The index of an auxiliary covering in the
local-cover lemma may have any universe. The proofs impose no affine-open,
reducedness, domain, local noetherianity or nontrivial-section-ring assumption.
