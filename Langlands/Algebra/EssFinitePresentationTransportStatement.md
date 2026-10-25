# Essential finite presentation: localization construction and isomorphism transport

The module `Langlands.Algebra.EssFinitePresentationTransportStatement` defines
`Langlands.Algebra.EssFinitePresentationTransportStatement.{u, v, w} : Prop`.
It is a conjunction of two transport assertions and proves neither assertion.
It imports the published `Langlands.Algebra.EssFinitePresentation` unchanged.

## Localization constructor

The first conjunct quantifies over three independent universes:
`R : Type u`, `A : Type v`, and `B : Type w`. Its hypotheses are exactly:

- `CommRing R`, `CommRing A`, and `CommRing B`;
- `Algebra R A`, `Algebra R B`, and `Algebra A B`;
- `IsScalarTower R A B`, expressing compatibility of these algebra structures;
- `Algebra.FinitePresentation R A`;
- an arbitrary `M : Submonoid A` and `IsLocalization M B`.

Its conclusion is `Langlands.Algebra.EssFinitePresentation R B`, with the
given `R`-algebra structure on `B`. Thus every localization of a finitely
presented `R`-algebra is essentially of finite presentation over `R`, even
when the three rings live in different universes.

The submonoid is arbitrary: it need not be finitely generated or the
complement of a prime, and it may contain zero or zero divisors. The map
`A → B` need not be injective. There are no Noetherian, nonzero, domain,
local-ring, or finite-type hypotheses on the localization.

## Isomorphism invariance

The second conjunct is the actual Mathlib predicate `RingHom.RespectsIso`
applied to the inline ring-hom property

```lean
fun {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) =>
  @Langlands.Algebra.EssFinitePresentation R S _ _ f.toAlgebra
```

Here all rings lie in the arbitrary universe `u`, as required by Mathlib's
`RespectsIso` interface. In particular, the algebra structure is induced
by the ring homomorphism being tested, including after composition.
No separate ring-hom wrapper is defined.

Writing this inline property as `Q` only in prose, `RespectsIso Q` asserts:

- For arbitrary commutative rings `R`, `S`, `T : Type u`, a ring homomorphism
  `f : R →+* S`, and a ring isomorphism `e : S ≃+* T`,
  `Q f` implies `Q (e.toRingHom.comp f)`.
- For arbitrary commutative rings `R`, `S`, `T : Type u`, a ring homomorphism
  `f : S →+* T`, and a ring isomorphism `e : R ≃+* S`,
  `Q f` implies `Q (f.comp e.toRingHom)`.

These are target and source isomorphism transport, respectively. Applying
them also to inverse isomorphisms yields invariance in both directions.

## Derived provenance

These are derived formalization statements, not named theorems reproduced
verbatim from the literature. Their source meaning is the Stacks Project,
Section 10.54, Definition 10.54.1 (tag 00QM): essentially finite presentation
means being a localization of a finitely presented algebra. Comment #2262
on that section specifies localization at an arbitrary multiplicatively
closed subset. Both passages were checked in the registered source
`stacks-algebra-flatness-criteria-2026-10-22`, file `07DR.html`, folder
SHA256 `4bc1f2db6141508f6dad2132d4abc7963380cd71497ad20620c0e511b972a949`.

The existing predicate expresses finite presentation using a finite
polynomial quotient by a finitely generated ideal and an algebra
isomorphism from a localization of that quotient. The constructor is the
transport from an arbitrary finitely presented algebra to this standard
presentation. Isomorphism invariance expresses preservation of the same
presentation-and-localization description under changing source or target
by a ring isomorphism. These explanations justify the derived statements;
their formal proofs are reserved for a separate proof task.

The statement does not assert general composition or base-change closure,
or any theorem about scheme stalks or `Localization.localRingHom`.
