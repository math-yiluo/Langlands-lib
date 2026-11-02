# Actual abelian sheaves: injective restrictions and flasque cohomology

This internal construction supplies the free-representable section
equivalence for actual abelian presheaves, its restriction compatibility,
and the resulting flasque cohomology adapter. It works with Mathlib's
actual sheaves and Ext-defined `CategoryTheory.Sheaf.H`.

The generic site part uses a category `C : Type u` with morphisms in
`Type v` and abelian groups in universe `v`. The topological part has an
arbitrary `X : TopCat.{u}` and abelian groups in universe `u`. It assumes
no separation, compactness, noetherianity or scheme structure on `X`.

## Free representables and injective restrictions

`freeYonedaEquiv F U` identifies maps from the sectionwise free abelian
presheaf on `yoneda.obj U` to an abelian presheaf `F` with the actual
section group of `F` at `U`, as an equivalence of types. It composes the
whiskered free/forgetful adjunction with the Yoneda equivalence.
`freeYonedaEquiv_naturality` proves compatibility with restriction along
every map `U ⟶ V`.

For a Grothendieck topology `J` with
`HasSheafify J AddCommGrpCat.{v}`, `surjective_map_of_injective` proves
that the restriction of an injective abelian sheaf along any monomorphism
of the site is surjective. A section is first viewed as a map from the
free representable. A monomorphism of representables stays monic under
the free abelian presheaf functor, because the free abelian group
functor preserves monomorphisms. Mathlib's finite-limit-preserving
sheafification carries it to a monomorphism of sheaves. Injectivity
extends the corresponding map across this monomorphism. The
sheafification adjunction and the proved restriction compatibility
identify this extension with a section restricting to the original one.

For opens of a topological space, every inclusion is monic, so
`isFlasque_of_injective` proves that every injective abelian sheaf is
flasque. Here flasque means that every restriction map is an
epimorphism of abelian groups, equivalently a surjective homomorphism.

## Injective cokernels and actual cohomology

`injectiveSc F` is the actual short complex

`F ⟶ Injective.under F ⟶ cokernel (Injective.ι F)`,

using the chosen injective embedding and its categorical cokernel.
`injectiveSc_shortExact` proves short exactness from the cokernel
universal property and the monicity of the embedding.

If `F` is flasque, `isFlasque_cokernel` shows that this cokernel is
flasque. It applies Mathlib's theorem that the third sheaf in a short
exact sequence is flasque when the first two are flasque, with the
middle sheaf flasque by injectivity. Mathlib also proves surjectivity
on sections for a short exact sequence with flasque first term.
`surjective_H_zero_map` applies this at the whole space and transports
it through the natural equivalence between `Sheaf.H F 0` and actual
global sections.

`H_eq_zero_of_isFlasque n F x` proves `x = 0` for every
`x : Sheaf.H.{u} F (n + 1)`. The proof uses induction on `n`. In the
short exact sequence above, the middle injective has zero cohomology
in positive degrees, so the long exact sequence expresses every
positive-degree class of `F` as a connecting image from its cokernel.
In degree one, surjectivity on degree-zero cohomology and the
zero-composite property of the long exact sequence make this
connecting image zero. In higher degrees, the inductive hypothesis
annihilates the class of the flasque cokernel.

`isZero_H_succ_of_isFlasque` packages the conclusion as

`IsZero (AddCommGrpCat.of (Sheaf.H.{u} F (n + 1)))`

for every natural `n` and every flasque abelian sheaf `F` on `X`.
This is the actual Ext-defined cohomology in universe `u`, including
degree one and all higher degrees.

## Provenance and scope

The free-representable lifting construction adapts the published
`Langlands.AlgebraicGeometry.Modules.PushforwardInjectiveAcyclic`
module argument to Mathlib's free abelian group adjunction. Its
ingredients are the whiskered adjunction, Yoneda, preservation of
monomorphisms, exact sheafification and `Injective.factorThru`.
The cokernel and vanishing arguments use Mathlib's flasque exact
sequence lemmas, its natural degree-zero cohomology equivalence, and
its Ext long exact sequence. This is an internal derivation from
those actual constructions, with no external literature theorem
assumed as an input.

This contribution does not identify module cohomology with
abelian-sheaf cohomology, identify Picard groups with degree-one
cohomology, classify deformations, or prove Picard representability.
In particular it does not assume that forgetting a module structure
preserves injective objects. Its flasque vanishing conclusion is an
input to a subsequent acyclic-resolution comparison.
