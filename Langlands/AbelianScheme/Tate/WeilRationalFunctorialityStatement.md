# Rational dual-homomorphism compatibility of the actual Weil pairing

Worker 142. `Langlands.AbelianScheme.RationalWeilFunctorialityStatement`
is the precise rational functoriality obligation for the constructed Weil
pairing. For actual abelian schemes `A` and `B` over a quasi-separated base,
an actual rational homomorphism `f : Hom0 A B`, a test scheme `T/S`, and a
selection `P` of positive torsion orders, the asserted identity is

\[
 E_B(V(f)x,y)=E_A(x,V(f^\vee)y)
 \quad\text{in }\mathbb Q\otimes_{\mathbb Z}
       \varprojlim_{n\in P}\mu_n(\Gamma(T,\mathcal O_T)).
\]

Here `x` belongs to the actual rational Tate module of `A`, and `y` belongs
to that of the constructed dual abelian scheme of `B`. The maps `V(f)`
and `V(f^vee)` are exactly `Tate.rationalHomMap`. The dual `f^vee` is
`dualHom0`, the rational-linear extension of the actual dual map classifying
pullback of Picard-zero line bundles. The two forms are the published
`rationalWeilBilinearMap`, with normalization `beta(y)(x)`. The equation
neither changes the twist nor inverts the pairing.

The quantifiers retain the seven named dual-constructor and coherence
propositions, the finite Weil transition proposition, both `HasDualScheme`
witnesses and `DualSchemeGeometry` inputs, the actual inverse Poincare
line bundles and their evaluation isomorphisms, and the named
`DualSchemeMapAdditivity` proposition for `A` and `B`. The last proposition
is required by the existing rational dual constructor; it concerns additivity
of the actual integral dual map and does not assume this pairing equation.
Every endpoint uses the same coherence and transition inputs.

No finite-étaleness, torsion-order invertibility, field, nondegeneracy or
isogeny hypothesis is required for this equation of rationalized section
pairings. `P` is any predicate on natural numbers; the inverse-system
indices themselves impose positivity. Specializing `P` to all orders or
to orders prime to a modulus gives the full or away identity. The existing
adelic bundles have precisely these values, using their coupled scalar
comparisons, so no replacement adelic module or pairing is introduced.
This statement does not itself assert an equation between those bundled
linear maps.

The original source is Edixhoven, van der Geer and Moonen, *Abelian
Varieties*, preliminary draft built 2012-02-08, registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
Chapter XI, Proposition (11.21)(i), printed p.167 / PDF p.171, gives
`e_n(f(x),y)=e_n(x,f^vee(y))` for actual integral homomorphisms over a
field, on points valued in every test scheme. Paragraph (11.23), printed
p.168 / PDF p.172, constructs the inverse-limit pairing into the actual
Tate twist. No source-specific errata note was found in the consulted
project notes.

The relative rational extension here is derived provenance, not a literal
additional assertion of that field-level passage. A proof can evaluate the
published relative finite-functoriality theorem on actual kernel lifts,
pass coordinatewise to the inverse limit, then use tensor induction in
both Tate arguments and in `f`. The pure-tensor formula for `dualHom0`
fixes the dual map in this reduction. This route has not been proved in
this unit: the file defines a proposition, with no proof or new axiom,
and a separate proof task must establish this exact declaration after
publication.

This unit does not construct a polarization, prove rational
nondegeneracy or alternation, introduce a chosen twist trivialization,
or transport PEL frames or their invariant orbits. It supplies the
explicit geometric theorem target needed before those constructions.
