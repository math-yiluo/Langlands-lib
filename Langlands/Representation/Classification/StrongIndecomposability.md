# Strong indecomposability

Authors: Worker 864 (initial definition-only draft) and Worker 713.

This module defines Zelevinsky's intersection condition for an arbitrary
representation of a group over a field. It records one short consequence of
the definition, for representations on a zero space. It states and proves
nothing else.

## Declarations

Both declarations are in the namespace `Langlands.Classification`. The
coefficient field `k : Type uK`, the group `G : Type uG` and the carrier
`V : Type uV` have independent universes. `V` is an additive commutative group
with `[Module k V]`, and `ρ : Representation k G V`.

- `IsStronglyIndecomposable ρ : Prop` is defined as

  ```lean
  ∀ S T : Subrepresentation ρ, S ≠ ⊥ → T ≠ ⊥ → S ⊓ T ≠ ⊥
  ```

  Every two nonbottom subrepresentations of `ρ` have a nonbottom intersection.
- `IsStronglyIndecomposable.of_subsingleton`: if `[Subsingleton V]`, then
  `IsStronglyIndecomposable ρ`. Over a zero space the only subrepresentation
  is `⊥`, so the hypothesis `S ≠ ⊥` cannot hold. The proof applies
  `Subrepresentation.toSubmodule_injective` to Mathlib's `Unique` instance on
  the submodules of a subsingleton module.

## The lattice used

`Subrepresentation ρ` is Mathlib's actual type of `G`-invariant `k`-submodules
of `V` (`Mathlib/RepresentationTheory/Subrepresentation.lean`). In the
elaborated definition, `⊥` is Mathlib's `Subrepresentation.instBoundedOrder`
bottom, whose underlying submodule is the zero submodule `⊥ : Submodule k V`.
The meet `⊓` is Mathlib's `Subrepresentation.instMin`, whose underlying set is
the intersection of the two underlying sets (`Subrepresentation.coe_inf`, which
holds by `rfl`). So `S ≠ ⊥` says that `S` contains a nonzero vector, and
`S ⊓ T ≠ ⊥` says that some nonzero vector lies in both `S` and `T`.

The module imports the published `Langlands.Representation.SubrepresentationLattice`.
Its complete lattice reuses these same `Min` and `BoundedOrder` instances
definitionally. Downstream modules can therefore use complete-lattice
suprema and infima with this predicate without an instance mismatch. A private
development check confirmed that the meet and bottom of
`Langlands.Subrepresentation.instCompleteLattice` equal Mathlib's at
reducible-and-instances transparency. That check is not part of this module.

## Source and provenance

A. V. Zelevinsky, *Induced representations of reductive p-adic groups II. On
irreducible representations of GL(n)*, Ann. Sci. ENS (4) 13 (1980), 165–210,
§5.4, printed p. 188 / PDF p. 25 (literature ID `zelevinsky-1980-induced-ii`,
SHA256 `663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`):

> 5.4. Let G be an l-group (see [1], 1.1). Call π ∈ Alg G strongly
> indecomposable if each two non-zero submodules of π have non-zero
> intersection. Clearly if π has finite length then it is strongly
> indecomposable iff it has a unique non-zero irreducible submodule.

Here [1] is I. N. Bernstein and A. V. Zelevinsky, *Induced representations of
reductive p-adic groups I*, Ann. Sci. ENS (4) 10 (1977), 441–472 (literature
ID `bernstein-zelevinsky-1977-induced-i`, SHA256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`). In 1.1
(printed p. 442 / PDF p. 3) an l-group is a Hausdorff topological group in which
every neighbourhood of the identity contains an open compact subgroup. In 1.2
(printed p. 443 / PDF p. 4), a representation `(π, G, E)` acts on a complex
vector space `E`, called a `G`-module, with no topology on `E`. It is algebraic
when every vector has an open stabilizer, and `Alg G` is the category of
algebraic representations. The submodules of `π` are its `G`-invariant
complex subspaces.

The general field and group interface is a derived extension of this smooth
formulation. Take an l-group `G`, a representation `π ∈ Alg G` on `E`, and
`k = ℂ`, `V = E`, `ρ = π` with the topology of `G` forgotten. Then the
`G`-submodules of `π` are exactly the elements of `Subrepresentation ρ`. Every
invariant subspace of an algebraic representation is itself algebraic, so the
smoothness condition removes no subspace. Hence `IsStronglyIndecomposable ρ`
is exactly the source's condition on `π`. The Lean definition only drops
hypotheses: `k` is any field, `G` is any group with no topology, and `ρ` need
not be smooth. On the same page Zelevinsky applies the notion to
representations of the mirabolic subgroups `P_n` (the Proposition of §5.4) and
to restrictions to `P_n` of representations of `G_n` (the derivation of
Theorem 6.1(a) after Theorem 6.2). The generic interface covers each of these
by the choice of `G`.

## The zero representation and nonzero hypotheses

The zero representation satisfies the intersection condition vacuously. It has
no nonzero submodule, so there is no pair `S`, `T` to test.
`IsStronglyIndecomposable.of_subsingleton` proves this for every
representation on a zero space.

Consequently, strong indecomposability alone does not give an irreducible
subrepresentation. Extracting a socle, or a unique irreducible
subrepresentation, needs a separate hypothesis that `ρ` is nonzero, together
with whatever hypothesis (such as finite length) supplies irreducible
subrepresentations. The same applies to the
source's remark after the definition. The zero representation has finite
length `0` and is strongly indecomposable, but it has no irreducible
submodule. So the remark's forward direction needs `π ≠ 0`. This is a reading
observation by the authors of this module, not an erratum issued by the
author.

## Scope

The definition does not include a nonzero carrier, finite length,
Artinianity, homogeneity (§5.1), derivative data or a socle. Neither the
finite-length remark nor the Proposition of §5.4 (strong indecomposability
of `τ ∈ Alg P_n` versus homogeneity and strong indecomposability of its
highest derivative) is stated or proved here. Their uses in §6, such as the
uniqueness of the irreducible submodule in Theorem 6.1(a), are not stated or
proved here either. These belong to separate statement and proof units.
