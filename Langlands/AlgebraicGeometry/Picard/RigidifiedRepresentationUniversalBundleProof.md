# Universal rigidified bundles from representations of the class presheaf: proof

`Langlands.AlgebraicGeometry.Picard.RigidifiedLineBundle.representationUniversalBundle`
proves exactly the published proposition `RepresentationUniversalBundleStatement`,
imported from
`Langlands.AlgebraicGeometry.Picard.RigidifiedRepresentationUniversalBundleStatement`.
The theorem's type is that proposition in every universe `u`. The proof keeps the
schemes `S` and `X`, the map `f`, the section `ε`, the `S`-scheme `P` and the
representation `r` arbitrary. It uses the explicit `coherence` proof only where the
target uses it: as the argument that forms `classPresheaf`.

## The implemented proof

This is the Yoneda argument.

1. **Choice of the bundle.** The value `r.homEquiv (𝟙 P)` is an element of
   `Classes f ε section_eq P`, the actual quotient of rigidified line bundles on
   `P ×_S X` by isomorphism. `Quotient.exists_rep` gives an actual
   `L : relative f ε section_eq P` whose quotient class is `r.homEquiv (𝟙 P)`
   (the equation `hL`). The proof takes this `L` as the witness.

2. **The classifying map is the representation.** Fix `T : Over S` and
   `h : T ⟶ P`. Mathlib's naturality field `r.homEquiv_comp h (𝟙 P)` says that
   `r.homEquiv (h ≫ 𝟙 P)` is the presheaf map of `h.op` applied to
   `r.homEquiv (𝟙 P)`. `simpa` removes `h ≫ 𝟙 P = h`. The proof then rewrites
   `r.homEquiv (𝟙 P)` as the class of `L`, using `hL` backwards. What remains is
   `classifyingMap f ε section_eq L T h = (classPresheaf coherence f ε section_eq).map h.op (classOf L)`.
   This holds by `rfl`. By definition, `classifyingMap L T h` is
   `classesPullback h (classOf L)`. The presheaf map of `h.op` is, by the
   definition of `classPresheaf`, `classesPullback` along `h.op.unop = h`,
   wrapped by `TypeCat.ofHom`. This proves the second clause of the target for every `T`
   and `h` (the statement `key`).

3. **Universality.** For each `T`, `key` and function extensionality give
   `classifyingMap f ε section_eq L T = r.homEquiv`, as functions
   `(T ⟶ P) → Classes f ε section_eq T`. The right side is the function of an
   equivalence, so it is bijective by `Equiv.bijective`. This is the unchanged
   Library predicate `IsUniversal f ε section_eq L`.

The witness `L` together with these two facts proves the existential.

## Scope

The proof uses no geometric property of `f`, `S`, `X`, `P` or the test schemes.
It does not assert that `L` is unique, that its rigidified isomorphisms are
unique, or that any representation exists. Those remain outside the statement.
Through the Library lemmas `isUniversal_iff` and `classifyingMap_eq_iff` in
`RigidifiedUniversalBundle`, the two clauses can be read as statements about
actual rigidified bundle isomorphisms. This proof uses neither lemma.

`lean_check` reports that the theorem depends only on the standard axioms
`propext`, `Classical.choice` and `Quot.sound`.

## Provenance

The mathematical source is Edixhoven–van der Geer–Moonen, *Abelian Varieties*,
Chapter VI §1, (6.2), printed p.88, as recorded in the statement's Markdown. The
source states the passage from representability to a universal rigidified bundle
without proof. This proof is the standard categorical (Yoneda) argument, not a
reproduction of a printed proof. Worker 361 proposed the route. Worker 270
checked the Lean implementation against the statement before this task was
published. This file uses that implementation without change.
