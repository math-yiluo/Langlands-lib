# Actual Hecke corner elements isolating a compact-coefficient irreducible

The module `Langlands.Representation.Hecke.CornerIsolationStatement` defines one
proposition, `Langlands.Hecke.CompactCoefficientCornerIsolationStatement.{uG,uV,uW}`.
It is a statement, not a proof: the module asserts nothing to be true. It states
the existence clause of Bernstein–Zelevinsky (1976), Theorem 2.42(a), restricted to
fixed vectors and expressed through the Library's actual compact-open Hecke corner.

## The proposition

Let `G : Type uG` be a topological group that is Hausdorff, locally compact,
totally disconnected and sigma-compact, with its Borel measurable structure. Let
`μ` be a left Haar measure on `G` (`μ.IsHaarMeasure`) that is regular and right
invariant. Let `A : SmoothRep.{0, uG, uV} ℂ G` be an irreducible smooth complex
representation with `HasCompactSmoothDualCoefficients A.representation`. Let `K`
be an open subgroup of `G` with compact underlying set (`hK`).

The proposition asserts that there is `e : HeckeAlgebra.Corner μ K hK` such that:

- `cornerAction μ A.representation A.isSmooth K hK e = 1`, the identity
  endomorphism of the `K`-fixed vectors of `A`;
- for every irreducible `B : SmoothRep.{0, uG, uW} ℂ G` with
  `¬ Nonempty (A.representation.Equiv B.representation)`,
  `cornerAction μ B.representation B.isSmooth K hK e = 0` on the `K`-fixed
  vectors of `B`.

One element `e` works for all such `B` at once. The `B` need not have compact
smooth-dual coefficients, need not be admissible, and may have their carriers in a
universe `uW` independent of the universe `uV` of `A`. Inequivalence means that no
actual `Representation.Equiv` exists, that is, no `G`-equivariant complex linear
isomorphism; Mathlib's `Representation.Equiv` allows different carrier universes.
The group universe `uG` is a third independent universe.

## The objects used

- `HeckeAlgebra.Corner μ K hK` (module `Langlands.Representation.Hecke.Corner`) is
  the actual subalgebra of bi-`K`-invariant test functions (locally constant,
  compactly supported complex functions) on `G`. Its product is the convolution
  `(f₁ * f₂)(x) = ∫ f₁(y) f₂(y⁻¹x) dμ(y)`. Its unit is the normalized indicator
  `μ(K)⁻¹ 1_K`.
- `cornerAction` (module `Langlands.Representation.Hecke.CornerAction`) is the
  unital complex algebra homomorphism from that corner to the endomorphisms of the
  existing fixed-vector space `fixedVectors ρ K.toSubgroup`. It restricts the
  integrated action `v ↦ ∫ f(g) • ρ(g) v dμ(g)`, with the positive `ρ(g)`
  convention and the supplied left Haar measure.
- `HasCompactSmoothDualCoefficients` (module
  `Langlands.Representation.CompactCoefficient.Classes`) requires that every
  coefficient `g ↦ ℓ(ρ(g) v)` has compact support, for every vector `v` and every
  smooth vector `ℓ` of the algebraic dual action. This is the source's condition
  "finite" of 2.39–2.40, not finite dimension.
- `SmoothRep.IsIrreducible` is Mathlib's `Representation.IsIrreducible` of the
  underlying action: the subrepresentation lattice is a simple order. In
  particular an irreducible representation is nonzero.

## Hypotheses compared with the source

The source assumes a unimodular l-group that is countable at infinity.

- Hausdorff, locally compact and totally disconnected together give the source's
  l-group (1.1): the topological group is an l-space.
- Sigma-compactness is the source's "countable at infinity" (1.5): `G` is a
  countable union of compact sets.
- A left Haar measure that is also right invariant expresses unimodularity (1.19):
  the modulus is trivial.
- Regularity of `μ` has no counterpart in the source, whose Haar measure is an
  invariant positive functional on locally constant compactly supported functions
  (1.18). It only restricts which Lean measures the statement quantifies over.
- Neither admissibility nor finite dimension of `A` is assumed. In the source,
  admissibility of irreducible finite representations is a consequence (2.41).

## Provenance (derived)

Source: Bernstein–Zelevinsky (1976), Theorem 2.42 and its proof, printed pages
26–28 (PDF page indices 26–28), together with 1.26 and 1.29–1.30 (printed pages
13–14) and 2.3–2.4 (printed pages 15–16). The source is registered as
`bernstein-zelevinsky-1976-representations-gln`, SHA256
`72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`. The retained
original is `/home/taskhub/central-library/Bernstein-Zelevinsky--Representations of
the group GL(n,F) where F is a non-archimedean local field (survey)--1976.pdf`.

Theorem 2.42(a) states: for each open compact subgroup `N` there exists a
distribution `ε_N^ω ∈ ℋ(G)` such that `ω(ε_N^ω) = ω(ε_N)` and `π(ε_N^ω) = 0` for
any irreducible representation `π` not isomorphic to `ω`. Here `ω` is the
irreducible finite representation, `ℋ(G)` the algebra of locally constant
compactly supported distributions, and `ε_N` the normalized Haar measure of `N`
(1.26). The proposition is derived from this clause in three steps.

1. **Test functions instead of distributions.** By 1.29–1.30, `f ↦ f μ_G`
   identifies the test functions with `ℋ(G)` for a fixed left Haar measure
   `μ_G`, and turns convolution of distributions into the convolution displayed
   above. Taking `μ_G = μ`, the distribution `ε_N^ω` is `f μ` for a unique test
   function `f`. The normalized Haar measure `ε_K` corresponds to `μ(K)⁻¹ 1_K`,
   the unit of the corner. The source's operator `π(f μ)` (2.3) is
   `ξ ↦ ∫ f(g) π(g) ξ dμ(g)`, the integrated action used by `cornerAction`.
   Because the statement is existential, the choice of Haar measure only
   rescales the test function.
2. **The element lies in the corner.** Theorem 2.42(b) with `N' = N` gives
   `ε_N * ε_N^ω = ε_N^ω * ε_N = ε_N^ω`. For `N = K`, the corresponding test
   function is therefore bi-`K`-invariant, so it is an element `e` of
   `HeckeAlgebra.Corner μ K hK`.
3. **Restriction to fixed vectors.** The operator `ω(ε_K)` is the projection
   onto the `K`-fixed vectors (2.4), hence the identity on them. Restricting
   `ω(ε_K^ω) = ω(ε_K)` to them gives `cornerAction … e = 1` for `A`.
   Restricting `π(ε_K^ω) = 0` gives `cornerAction … e = 0` for `B`.

Only these restrictions to `K`-fixed vectors are stated. The statement does not
include the uniqueness of `ε_N^ω` (2.42(a)), its compatibility with smaller
subgroups or its conjugation law (2.42(b)), the limit projector `π(ε^ω)` (2.43),
or the splitting of a representation into its `ω`-part and a complement (2.44).
It says nothing about the action of `e` outside the fixed vectors.

## The source's proof

This section records the source's argument as guidance for a proof. None of it is
formalized in this module.

The source first notes that `ω` is admissible (2.41). It lets `L` be the smooth
part of `End V` under `G × G`, acting by `A ↦ ω(g₁) A ω(g₂⁻¹)`. The map
`ξ ⊗ ξ̃ ↦ (η ↦ ⟨ξ̃, η⟩ ξ)` from `V ⊗ Ṽ` to `L` is an isomorphism, by a
dimension count on fixed vectors. So `L` is irreducible under `G × G` and, under
`G × {e}`, a direct sum of copies of `V`. The map `φ(A)(g) = tr(ω(g⁻¹) A)`
sends `L` into the test functions, because the coefficients of `ω` have compact
support; identifying test functions with distributions through the Haar
measure, `φ` and the integrated action `ω̂ : h ↦ ω(h)` are `G × G`-equivariant.
For any representation `π` and vector `ξ`, the image of `φ(L)` under
`h ↦ π(h) ξ` is a sum of copies of `V`, so every irreducible `π` not isomorphic
to `ω` satisfies `π(φ(L)) = 0`. By Schur's lemma (2.11), `ω̂ ∘ φ` is a scalar `c`
on `L`; the completeness of irreducible representations (2.12) together with the
previous observation gives `c ≠ 0`. The distribution `ε_N^ω = c⁻¹ φ(ω(ε_N))` then
has the required properties. Schur's lemma and the completeness result are stated
in the source for groups countable at infinity.

## Intended use

The statement is a prerequisite of the proof task
`6884361c-0ab2-41b3-8098-9c070c4a1b3e`: fixed-level finiteness of compact-coefficient
classes for product-Levi determinant-unit groups (BZ76 Theorem 4.14 via 4.16). That
argument needs actual corner elements separating inequivalent classes.
