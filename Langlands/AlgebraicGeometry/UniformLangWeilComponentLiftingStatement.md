# Uniform lifting with component-dependent dimensions

`Langlands.AlgebraicGeometry.UniformLangWeilComponentLiftingStatement.{u}` is
a derived, conditional consequence of the uniform Lang–Weil estimate used in
Brian Conrad, *Weil and Grothendieck approaches to adelic points*
(December 31, 2011), printed pp.12–13, Lemma 4.6 and the proof of Theorem 4.5.
The registered source is `conrad-2011-weil-grothendieck-adelic-points`,
SHA-256 `fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

Each of its three clauses assumes `UniformLangWeilStatement.{u}`. For an actual
scheme morphism `f : Y ⟶ B`, the hypotheses require `B` to be of finite type
over the actual lifted integer spectrum: its canonical structure map is
locally of finite type and its underlying space is compact. The morphism `f`
is smooth, separated, quasi-compact and geometrically connected. Smoothness
implies local finite type, so `f` is of finite type. Mathlib's geometric
connectedness includes nonempty geometric fibres and implies surjectivity.
No dimension, affine presentation, reduction or nonempty target is supplied.
There is no separatedness assumption on `B` over the integers.

The first clause supplies a real constant `C > 0`, chosen before the finite
field and the point. For every finite field `K` in the same arbitrary universe
`u`, if `C² < #K`, every actual point `p : Spec K ⟶ B` lifts to an actual point
`q : Spec K ⟶ Y` with `q ≫ f = p`. The cardinality is that of the entire
finite field of values, rather than the image point's residue field.

The second clause supplies such a constant uniformly over all Henselian local
commutative rings `R` in universe `u`, all finite fields `K`, and all surjective
coefficient maps `R → K` expressed as an algebra structure. If `C² < #K`,
every `Spec R` point of `B` lifts to a `Spec R` point of `Y`. The named
class is `HenselianLocalRing`, as in the imported smooth lifting result.

The third clause retains an arbitrary original commutative coefficient ring
`A`, actual schemes `B` and `Y` over `Spec A`, and a morphism in that
over-category. For every `A`-algebra `R` which is Henselian local and every
surjective `A`-algebra homomorphism `φ : R → K` to a sufficiently large finite
field, every relative `RingPoint A B R` lifts to a relative `RingPoint A Y R`.
The equality is in the actual over-category, so it preserves the original
coefficient structure. All objects and fields share arbitrary universe `u`.

This formulation removes the fixed fibre dimension required by the existing
`uniformLangWeilLargeFiniteFieldPointLifts` and Henselian helpers. The
derivation uses the finite actual connected components of the noetherian
target. Each restriction has its own constant smooth relative dimension and
full pure fibre geometry. A finite upper bound on their individual constants
works for the whole morphism. A field-valued point factors through its image
component, independently of the component chosen by any other point. This
does not require a whole adelic point to lie in a single component.

The original paper first reduces to connected target components and then uses
Lemma 4.6, finite-field largeness and Hensel's lemma. The present interface
packages the corresponding finite-component argument for a supplied
arithmetic family. It retains the absolute finite-type hypothesis over the
integers; establishing that hypothesis for actual arithmetic models remains
a separate obligation. This statement supplies neither a proof of
Lang–Weil, compatible arithmetic model existence, geometric-connectedness
spreading, nor adelic openness. Its proof is a separate unit.
