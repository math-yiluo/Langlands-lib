# Essential finite presentation: localization and isomorphism transport

This proof module imports the published predicate and transport statement without
changing either pair or any of their imports. Its closing theorem is
`Langlands.Algebra.essFinitePresentationTransport.{u, v, w}`, whose complete type
is `Langlands.Algebra.EssFinitePresentationTransportStatement.{u, v, w}`.
The theorem has no additional outer hypotheses or parameters. The final
unapplied-constant example checks this complete type directly.

## Reusable interface

- `Langlands.Algebra.essFinitePresentation_of_isLocalization` takes
  `R : Type u`, `A : Type v`, and `B : Type w`, commutative-ring structures,
  compatible algebras `R → A → B` and `R → B`, finite presentation of `A` over
  `R`, an arbitrary `M : Submonoid A`, and `IsLocalization M B`. It concludes
  `EssFinitePresentation R B` for the given `R`-algebra structure.
- `Langlands.Algebra.essFinitePresentation_of_algEquiv` transports
  `EssFinitePresentation R S` along `S ≃ₐ[R] T`, with independent universes
  for `R`, `S`, and `T`.
- `Langlands.Algebra.essFinitePresentation_respectsIso.{u}` proves the actual
  Mathlib `RingHom.RespectsIso` for the inline property
  `fun {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) =>
  @Langlands.Algebra.EssFinitePresentation R S _ _ f.toAlgebra`.

No new ring-hom property definition is introduced.

## Implemented proof

The constructor `essFinitePresentation_of_isLocalization` chooses a standard
finite polynomial quotient `Q = R[X₀, …, Xₙ₋₁]/I` using
`Algebra.FinitePresentation.iff`, obtaining `e : Q ≃ₐ[R] A` and `I.FG`.
It pulls the given submonoid back to `N = M.comap e`. Surjectivity identifies
`N.map e` with `M` by `Submonoid.map_comap_eq_of_surjective`, so
`IsLocalization.algEquivOfAlgEquiv` gives the required algebra equivalence from
`Localization N` to `B`. This argument permits three independent universes
and an arbitrary submonoid, including one containing zero or zero divisors.
It does not assume that the localization map is injective.

The helper `essFinitePresentation_of_algEquiv` composes the witnessing algebra
equivalence with an algebra equivalence of the target. For the target half of
`essFinitePresentation_respectsIso`, the target ring equivalence becomes an
algebra equivalence for the algebra structures induced by the original map and
its composition with that equivalence: for `f : R →+* S` and `e : S ≃+* T`,
these are `f.toAlgebra` and `(e.toRingHom.comp f).toAlgebra`.

For source transport, write the original map as `f : S →+* T`, the source
equivalence as `e : R ≃+* S`, and a witnessing presentation as
`a : Localization M ≃ₐ[S] T`, where `M` belongs to a standard quotient `A`
over `S`. The proof gives `A` the `R`-algebra map
`(algebraMap S A).comp e.toRingHom`.
`Algebra.FinitePresentation.quotient` and
`RingHom.finitePresentation_respectsIso` make `A` finitely presented over `R`.
The `A`-algebra map on `T` is the composite of the canonical localization map
with `a`. Thus `a` is also an `A`-algebra equivalence, and
`IsLocalization.isLocalization_of_algEquiv` supplies `IsLocalization M T`.
The `R`-algebra on `T` is exactly `(f.comp e.toRingHom).toAlgebra`.
The scalar-tower equation follows from the canonical `S → A → Localization M`
tower and `a.commutes`. Applying the three-universe constructor to `R`, `A`,
and `T` concludes the source half.

The closing theorem combines these helpers. There are no Noetherian, domain,
nonzero, local-ring, or extra finiteness assumptions on a localization.
The module proves neither general composition or base-change closure nor a
scheme-stalk theorem.

## Derived provenance

These are derived transport facts for the definition in the Stacks Project,
Section 10.54, Definition 10.54.1 (tag 00QM), and Comment 2262 on arbitrary
multiplicatively closed subsets. The registered source is
`stacks-algebra-flatness-criteria-2026-10-22`, file `07DR.html`, folder SHA-256
`4bc1f2db6141508f6dad2132d4abc7963380cd71497ad20620c0e511b972a949`.
Both relevant passages were read in the registered snapshot; no source-specific
errata file was present. The proof route uses the pinned Mathlib implementation
rather than a verbatim source proof. The Mathlib modules are
`Mathlib.RingTheory.FinitePresentation`, `Mathlib.RingTheory.Localization.Basic`,
and `Mathlib.RingTheory.RingHom.FinitePresentation`, at commit
`5ed2965256430c3649e86755f9576b54eca72435`.

Worker 405 implemented the Lean proof and this explanation. Worker 136 supplied
the presentation-and-localization transport strategy and the source-isomorphism
finite-presentation strategy in the task context.
