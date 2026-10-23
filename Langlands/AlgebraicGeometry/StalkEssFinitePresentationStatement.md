# Essential finite presentation of scheme stalk maps

The module and proposition declaration are both named
`Langlands.AlgebraicGeometry.StalkEssFinitePresentationStatement`.
This file states a derived local consequence of local finite presentation.
It supplies no proof and introduces no axiom.

## Statement and stalk algebra

For arbitrary schemes `X Y : Scheme.{u}`, a morphism `f : X ⟶ Y`, and any
point `x : X`, assume `LocallyOfFinitePresentation f`. Then the actual map
of local rings

\[
\mathcal O_{Y,f(x)} \longrightarrow \mathcal O_{X,x}
\]

makes the target an essentially finitely presented algebra over the source,
in the sense of Stacks Definition 10.54.1 (tag 00QM).

In Lean these rings are `Y.presheaf.stalk (f x)` and `X.presheaf.stalk x`.
The homomorphism is `(f.stalkMap x).hom`. The expression
`letI := (f.stalkMap x).hom.toAlgebra` installs precisely the algebra structure
induced by this homomorphism before applying the published predicate
`Langlands.Algebra.EssFinitePresentation`. There is no independently chosen
algebra structure and no additional algebra hypothesis.

The proposition quantifies over all points and all schemes in the indicated
universe. Its only hypothesis is local finite presentation of `f`. In
particular, it requires no Noetherian, affine, quasi-compact, quasi-separated,
or flatness hypothesis, and does not assume finite type or finite presentation
of the stalk map.

## Source correspondence and derived provenance

The registered source is `stacks-algebra-flatness-criteria-2026-10-22`,
folder SHA256
`4bc1f2db6141508f6dad2132d4abc7963380cd71497ad20620c0e511b972a949`.
The relevant original files are:

- `07DR.html`, Section 10.54, Definition 10.54.1 (tag 00QM):
  essential finite presentation means localization of a finitely presented
  algebra. Lemmas 10.54.2 and 10.54.3 give preservation under composition
  and base change, respectively. Comment #2262 clarifies that localization
  permits an arbitrary multiplicatively closed subset.
- `039C.html`, Theorem 37.16.2, first proof paragraph: the arbitrary-base
  fibrewise flatness argument applies the algebraic criterion to the actual
  local ring maps
  \(\mathcal O_{S,s}\to\mathcal O_{Y,y}\to\mathcal O_{X,x}\).
  The present proposition supplies the essential finite presentation input
  when applied to the structure map \(X\to S\).

This scheme-stalk assertion is **derived**, rather than a verbatim named
theorem in those pages. Mathlib's `LocallyOfFinitePresentation` expresses
finite presentation of the ring map on every pair of compatible affine
opens. Choose affine neighborhoods of `f x` and `x`, with coordinate rings
`R` and `A`; their map `R → A` is finitely presented. If `q` represents `x`
and `p` is its inverse image in `R`, the stalk map is identified with
`R_p → A_q`. Base change gives a finitely presented `R_p`-algebra
`R_p ⊗[R] A`, and `A_q` is a further localization of it. Thus the stalk map
has the form required by Definition 10.54.1. This paragraph explains the
mathematical provenance; these localization and base-change arguments are
not proved in this statement file.

The imported predicate uses a finite-variable polynomial quotient by a
finitely generated ideal, an arbitrary submonoid of that quotient, and
an algebra isomorphism from its localization to the target. That published
definition is imported unchanged.

## Finite presentation versus essential finite presentation

The affine coordinate-ring map is finitely presented. Passing to stalks
can invert an arbitrary multiplicative subset, so the conclusion here is
essential finite presentation, not finite presentation. In particular,
the proposition makes no claim that the stalk algebra has finitely many
algebra generators over the base stalk.

Mathlib already supplies the finite-type analogue,
`AlgebraicGeometry.LocallyOfFiniteType.stalkMap`, in
`Mathlib.AlgebraicGeometry.Morphisms.FiniteType`. It is not restated here.
The general reduction
`AlgebraicGeometry.HasRingHomProperty.stalkMap_of_respectsIso` in
`Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties` is a possible route
for a later proof, once the corresponding essential-finite-presentation
localization and isomorphism properties have been proved.

## Status

The Lean file contains one `Prop`-valued definition with the quantifiers,
hypothesis, and conclusion above. A separate proof must establish this
published proposition in its entirety; this statement file asserts no such
proof.
