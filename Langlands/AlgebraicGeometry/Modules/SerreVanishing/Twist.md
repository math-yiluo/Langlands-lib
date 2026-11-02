# Multiplication by a section and the section-killing interface

Internal helper module for the proof of
`Langlands.AlgebraicGeometry.Modules.ProperAmplePairSerreVanishingStatement`.

## `twistMul N s G`

For a module `N` on a scheme `X`, a global section `s` of `N` and a module `G`,
`twistMul N s G : G ⟶ G ⊗ N` is the composite

`G ≅ G ⊗ 𝒪_X --(𝟙 ⊗ sectionHom N s)--> G ⊗ N`,

that is, on sections `g ↦ g ⊗ s`. Here `sectionHom N s : 𝒪_X ⟶ N` sends `1` to `s`,
the tensor product is the Library's `tensorObj` (sheafified presheaf tensor product)
and the first map is the inverse of the Library's right unitor `tensorRightUnitor G`.

## `SectionKillingStatement`

A proposition (not a published statement; it is the interface between the two halves
of the proof). It says: let `K` be a field, `f : X ⟶ Spec K` proper, `N` and `P`
locally free of rank one, `s` a global section of `N` whose trivialization locus
`trivializationOpen N s` (the largest open on which `sectionHom N s` is an isomorphism,
i.e. the non-vanishing locus `X_s`) is affine, and `G` quasi-coherent with finitely
generated sections over every affine open. Let `m` and `i > 0` be natural numbers.
Write `H^j(-)` for `DerivedSections.relativeCohomology f j`. If for every `k`

- `H^{i+1}((ker(twistMul N s G) ⊗ N^(m+k)) ⊗ P) = 0` and
- `H^i((coker(twistMul N s G) ⊗ N^(m+k)) ⊗ P) = 0`,

then there is `t` with `H^i((G ⊗ N^(m+t)) ⊗ P) = 0`. The tensor products are nested
exactly as written, with `tensorPow N n` the Library's iterated tensor power.

### Why it holds

Twisting the two short exact sequences `0 → ker → G → im → 0` and
`0 → im → G ⊗ N → coker → 0` by the line bundles `N^(m+k)` and `P` keeps them exact,
so the hypotheses make `H^i` of multiplication by `s`,
`H^i((G ⊗ N^(m+k)) ⊗ P) → H^i((G ⊗ N^(m+k+1)) ⊗ P)`, surjective for every `k`.
The source at `k = 0` is finite-dimensional over `K` because `X` is proper and `G`
coherent. Since `X_s` is affine, every class of positive degree is killed by a power
of `s` (Stacks, Tag 01XR); a basis is killed by one power `s^t`, so the composite
of the first `t` surjections is zero, and its target vanishes.

## Provenance

Derived for this proof. The killing of cohomology classes by a power of a section with
affine non-vanishing locus is Stacks Project, Lemma 01XR (Cohomology of Schemes); the
rest is the standard dimension-counting argument of Serre's vanishing theorem
(Hartshorne, Proposition III.5.3).
