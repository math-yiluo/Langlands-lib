# The plus-minus multiplication homeomorphism of the upper unipotent group

Author: Worker 778.

`Langlands.GeneralLinear.UpperUnipotentFactorizationStatement.{u}` is a closed,
transparent `Prop`-valued definition in
`Langlands.Group.GL.UpperUnipotentFactorizationStatement`. This module only
states the proposition. It provides no proof, and no Library declaration is
claimed to prove it. Consumers must not assume it until a separate proof is
independently accepted and published.

## The proposition

```lean
def UpperUnipotentFactorizationStatement : Prop :=
  ∀ (K : Type u) [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K]
    [T2Space K] (n : ℕ) (w : Equiv.Perm (Fin n)),
    ∃ e : (permutationUnipotentPlus n K w × permutationUnipotentMinus n K w) ≃ₜ
        upperUnipotent n K,
      ∀ x : permutationUnipotentPlus n K w × permutationUnipotentMinus n K w,
        (e x).val = x.1.val * x.2.val
```

### Quantifiers

All quantifiers are inside the proposition. The caller supplies nothing.

- `K : Type u` ranges over every field in the universe `u` of the definition.
- `TopologicalSpace K` ranges over every topology on `K`.
- `IsTopologicalDivisionRing K` asks that addition, negation and multiplication
  be continuous and that inversion be continuous at every nonzero element.
- `T2Space K` asks that the topology be Hausdorff.
- `n : ℕ` ranges over every natural rank, including `n = 0`. No positivity or
  nontriviality hypothesis appears.
- `w : Equiv.Perm (Fin n)` ranges over every permutation of the coordinates.

No local compactness, completeness, countability, metrizability, valuation,
characteristic, or algebraic closure hypothesis appears. In particular there is
no geometric premise, and no premise of surjectivity, inverse continuity, or
algebraic factorization. Those properties are what the conclusion asserts.

### The actual groups and the permutation convention

Every object is imported unchanged from the published
`Langlands.Group.GL.UpperBruhatCells` and its imports. Write
`p = Langlands.GeneralLinear.permutation n K w`, `U = upperUnipotent n K`, and
`Ubar = lowerUnipotent n K`.

- `Langlands.GeneralLinear n K` is `Matrix.GeneralLinearGroup (Fin n) K`, the
  units of the matrix ring.
- `U` is the subgroup of invertible upper triangular matrices whose diagonal
  entries are all one.
- `p` has entry `(i,j)` equal to `if w j = i then 1 else 0`. It sends `e_j` to
  `e_(w j)`, and `(p * g * p⁻¹) i j = g (w⁻¹ i) (w⁻¹ j)`.
- `permutationUnipotentPlus n K w` is `U ⊓ U.comap (MulAut.conj p)`, that is,
  the `g ∈ U` with `p * g * p⁻¹ ∈ U`. This is Shalika's `U_w⁺ = U ∩ w⁻¹Uw`.
  The published lemma `mem_permutationUnipotentPlus_iff_entries` shows that it
  consists of the `g ∈ U` with `g i j = 0` whenever `w j < w i`.
- `permutationUnipotentMinus n K w` is `U ⊓ Ubar.comap (MulAut.conj p)`, that
  is, the `g ∈ U` with `p * g * p⁻¹ ∈ Ubar`. This is Shalika's
  `U_w⁻ = U ∩ w⁻¹ Ubar w`. The published lemma
  `mem_permutationUnipotentMinus_iff_entries` shows that it consists of the
  `g ∈ U` with `g i j = 0` whenever `w i < w j`.

The permutation `w` is not reversed or inverted anywhere in the statement.

### Topologies

All topologies are the inherited ones found by instance search. The matrix
space carries the product topology from `K`. The unit group
`Langlands.GeneralLinear n K` carries Mathlib's topology on units, induced by
`g ↦ (g, g⁻¹)`, so both a matrix and its inverse vary continuously. The three
subgroups carry their subtype topologies, and the domain `U_w⁺ × U_w⁻` carries
the product topology. No alternative topology is introduced.

### The conclusion and the map

The conclusion asks for a homeomorphism
`e : (U_w⁺ × U_w⁻) ≃ₜ U` whose value at every pair `x = (u⁺, u⁻)` has
underlying invertible matrix `u⁺ * u⁻`. The product is taken in
`Langlands.GeneralLinear n K`, with the plus factor on the left and the minus
factor on the right. No other order of multiplication is asserted.

The equation determines the forward map of `e`: it is the multiplication map
`(u⁺, u⁻) ↦ u⁺ * u⁻`, corestricted to `U`. Hence the proposition is not merely
the existence of some abstract homeomorphism between the carriers. Its
existence says exactly the following.

- Every `u ∈ U` factors as `u = u⁺ * u⁻` with `u⁺ ∈ U_w⁺` and `u⁻ ∈ U_w⁻`
  (surjectivity of `e`).
- The factors are unique (injectivity of `e`).
- The multiplication map is continuous.
- The coordinates `u ↦ u⁺` and `u ↦ u⁻`, the two components of `e.symm`,
  are continuous for the inherited topologies.

The statement does not assert that `e` is a group homomorphism, which is false
in general. It says nothing about the reverse order `U_w⁻ × U_w⁺ → U`, the map
`U × H × U_w⁻ → C_w`, Bruhat cells, local closedness, dimension, Haar measures,
distributions, or integration.

In rank zero the three groups are trivial and the conclusion is the statement
for one-point spaces. The proposition still quantifies over this case.

## Source and provenance

The registered original is `shalika-1974-multiplicity-one`, J. A. Shalika,
*The multiplicity one theorem for GLn*, Ann. of Math. (2) 100 (1974), 171–193.
The file
`/home/taskhub/central-library/Shalika--The multiplicity one theorem for GLn--1974.pdf`
has SHA256
`788c5d124024c768aa47c4e8b179475fbcf5b0882a518ae60b19cdc88089f087`.
Printed pages 173–176 are one-based PDF pages 4–7. All four were read by text
extraction. Printed pp.174 and 176 were also checked visually on fresh renders
of PDF pages 5 and 7. The bibliography on printed p.193 identifies [25]. No
errata file for this source was found in the public notes.

- Printed p.173 sets the notation. `G = GL_n`, `H` is the diagonal subgroup,
  `U` the upper triangular unipotent ("super triangular") group and `Ubar` the
  opposite group. When `k` is a local field these are regarded as locally
  compact groups, and Weyl elements are represented by permutation matrices.
- Printed p.174 defines `U_w⁺ = U ∩ w⁻¹Uw` and `U_w⁻ = U ∩ w⁻¹ Ubar w`.
- Printed p.176, proof of Lemma 1.9: "Write `U = U_w⁺ · U_w⁻` (with uniqueness
  of expression [25]) and accordingly `u = u⁺ · u⁻`". Here [25] is
  R. Steinberg, *Lectures on Chevalley Groups*, Yale University, 1967. The same
  page then uses this decomposition to write an integral over `U` as an iterated
  integral over `U_w⁺` and `U_w⁻`. That step treats the multiplication map as
  an identification of `U_w⁺ × U_w⁻` with `U` for integration, not only as a
  bijection of sets.

The local-field content is therefore the source content: the plus-minus order,
existence, uniqueness, and the identification used for the integration. Shalika
does not state the homeomorphism as a separate lemma. The explicit
homeomorphism, with its forward map fixed by the matrix equation, is the
project's precise formulation of that identification.

The quantification over every Hausdorff topological field is an internal
generalization of the actual matrix formulas. It is not a claim about the
hypotheses of the original, which works over a local field.

### Why the generalization is appropriate

This section gives the expected justification. It is not proved in this module.

Take `u ∈ U`. Write `u⁺` and `u⁻` for upper unipotent matrices supported off the
diagonal on the pairs `i < j` with `w i < w j` and with `w j < w i`
respectively. For `i < j`,

```text
(u⁺ * u⁻) i j = u⁺ i j + u⁻ i j + Σ_{i < k < j} u⁺ i k * u⁻ k j.
```

Since `w` is injective, exactly one of `u⁺ i j` and `u⁻ i j` may be nonzero.
Solving by induction on `j - i` therefore determines both factors uniquely.
Their entries are integer polynomials in the entries of `u`. The inverses
`(u⁺)⁻¹ = u⁻ * u⁻¹` and `(u⁻)⁻¹ = u⁻¹ * u⁺` are then continuous as well,
because the unit topology makes `u⁻¹` continuous.

So the factorization and its continuity use only continuity of the ring
operations. No completeness, local compactness, or Arens–Pontryagin argument
(the device used for printed p.175, Lemma 1.7) is needed. Local fields, both
p-adic and archimedean, are Hausdorff topological fields, so the original
setting is covered. The Hausdorff hypothesis and the continuity of inversion
are retained as the specified scope of this statement. As extra hypotheses they
only make the proposition weaker.

### Direct specializations

A private compilation check, not part of this module, instantiated the
proposition with the pinned environment:

- at `F.Carrier` for every `F : Langlands.PadicField.{u} p` and every
  `T : F.TopologicalData`, after installing `T.topology`, `T.valuativeRel`,
  `T.localField` and the published certificate `T.fieldT2`; Mathlib's
  `IsNonarchimedeanLocalField` instance supplies `IsTopologicalDivisionRing`;
- in particular at the canonical realization `F.canonicalTopologicalData`, for
  positive rank;
- at Mathlib's `Padic p` with its global instances, at rank `n + 1`;
- at rank zero for an arbitrary field satisfying the hypotheses.

In each case the instantiated topologies are the same instance-search
topologies used by `TopologicalData.generalLinearTopology` and
`TopologicalData.upperUnipotentTopology`.

## Imports

The module imports `Langlands.Group.GL.UpperBruhatCells` unchanged.
It also imports `Mathlib.Topology.Algebra.Field` for
`IsTopologicalDivisionRing` and `Mathlib.Topology.Homeomorph.Defs` for `≃ₜ`.
It adds no axioms, no theorem, and no other declaration.
