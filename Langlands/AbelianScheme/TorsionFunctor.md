# Functoriality of actual integer torsion group schemes

This is an internal deduction from `Langlands.AbelianScheme.Torsion`,
`Multiplication`, `TorsionBaseChange`, and Mathlib's pullback universal
property. It constructs bundled homomorphisms on the actual kernel schemes;
there is no additional geometric existence assertion or external source claim.

Fix an arbitrary base scheme `S : Scheme.{u}` and commutative group schemes
`G`, `H`, and `J` over `S`. For every signed integer `n` and actual
homomorphism `f : G ⟶ H`, `GroupScheme.torsionMap f n` is a homomorphism
`G[n] ⟶ H[n]`. Here `G[n]` means the previously constructed
`GroupScheme.torsion G n`, the pullback of multiplication by `n` against
the unit section. The construction applies `pullback.map` in the category
`Grp (Over S)` to the maps `f`, the identity of the trivial group scheme,
and `f` at the three vertices. Integer multiplication is natural in `f`,
and a group homomorphism preserves the unit, so both required squares
commute.

`torsionMap_ι` proves the defining inclusion equation

\[
 f[n]\ ;\ \iota_{H,n}=\iota_{G,n}\ ;\ f.
\]

`torsion_hom_ext` tests equality of any two homomorphisms into `H[n]`
after this inclusion. Its source can be an arbitrary group scheme, with
no commutativity requirement. The proof uses monicity of the underlying
kernel inclusion in `Over S`, followed by extensionality for bundled
group homomorphisms.

The inclusion equation and this extensionality prove `torsionMap_id` and
`torsionMap_comp`, so restriction preserves identity and composition.
They also prove `torsionMap_one` and `torsionMap_mul`, using distribution
of composition over the pointwise group law. `torsionMapHom n` bundles
the latter two identities as a monoid homomorphism between the Hom
groups. The multiplication and numeral `1` here denote the pointwise
group law and the trivial homomorphism, respectively; they do not
denote composition and the identity morphism.

`torsionι_multiplication` states that the inclusion of `G[n]` followed
by multiplication by `n` on `G` is trivial. This is the kernel
pullback equation. Naturality of multiplication and monicity of the
inclusion then prove `multiplication_torsion`: multiplication by `n`
on `G[n]` itself is trivial.

For every test scheme `T : Over S`, `torsionPointsEquiv_map` identifies
the underlying torsion point of `x ; f[n]` with the torsion point of
`x` followed by `f`. It uses the existing equivalence between actual
scheme points and the subgroup of points killed by `n`. This is an
all-test-scheme identity, with no restriction to field-valued points.

For every scheme morphism `b : S' ⟶ S`, `torsionMap_baseChange` proves
that the restriction map commutes with pullback, using the existing
canonical isomorphisms between the pullback of `G[n]` and the torsion
of the pullback of `G`. Compose the two proposed morphisms with the
target torsion inclusion; the inclusion equations for restriction and
base change reduce their equality to functoriality of pullback.
The extensionality theorem then gives equality of the bundled maps.

In the Library's additive category of commutative group schemes,
`CommGroupScheme.torsionFunctor n` bundles this construction as an
endofunctor. Its `Functor.Additive` instance follows from
`torsionMap_mul`: the same pointwise Hom group law is written
additively in this category. `torsionInclusion n` is the natural
transformation from this functor to the identity, with components the
actual torsion inclusions and naturality given by `torsionMap_ι`.

All assertions include zero and negative integers and arbitrary base
schemes, including bases with nilpotents. No finiteness, étaleness,
smoothness, separatedness, connectedness, or characteristic hypothesis
is imposed. This unit supplies the restriction step for constructing
a sum of torsion images; it does not construct that sum, an abelian
quotient, an integral model for a rational action, or a CM
representing scheme.
