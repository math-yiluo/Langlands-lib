# Proof of the Kneser–Tits property of quaternionic symplectic groups of Witt index one

Module `Langlands.GroupScheme.Quaternionic.LocalSymplecticKneserTitsProof`.

## Statement

`localSymplecticKneserTits : LocalSymplecticKneserTitsStatement.{u}`. This is the published
statement of module `Langlands.GroupScheme.Quaternionic.LocalSymplecticKneserTitsStatement`, at
an arbitrary universe `u` and with unchanged hypotheses. Let `K` be a nonarchimedean local field,
`D` a central division `K`-algebra with `dim_K D = 4`, and `σ` an involution of the first kind of
`D` with `dim_K D^σ = 3`. Let `m = 2` or `3` and `H ∈ M_m(D)` with `σ.IsAntihermitian H`,
`IsUnit H` and `σ.wittIndex H = 1`. Then
`parabolicElementarySubgroup (σ.symplecticGroup H) = ⊤`.

## Proof

The proof is one application of
`localSymplecticKneserTits_of_isConnectedReductive` (module `Quaternionic.SymplecticGeneration`).
That theorem derives the statement from connected reductivity of the groups
`σ.symplecticGroup H`. Reductivity is supplied by
`FirstKindInvolution.isConnectedReductive_symplecticGroup hD σ hσ H hH hu` (module
`Quaternionic.SymplecticReductive`), which needs only `dim_K D = 4`, `dim_K D^σ = 3`, `H`
antihermitian and `H` invertible. The local-field structure of `K` is not used, so the argument
works over every field, in every characteristic.

The proof of `localSymplecticKneserTits_of_isConnectedReductive`, through the modules it
imports, runs as follows.

1. **Standard form** (`HyperbolicBasis`). `exists_gramTwo` and `exists_gramThree` give an invertible
   `P` with `P H ᵗP^σ = gramTwo D = !![0, 1; -1, 0]` (for `m = 2`) or
   `P H ᵗP^σ = gramThree c = !![0, 1, 0; -1, 0, 0; 0, 0, c]` with `c ∈ {a - σ a}`, `c ≠ 0`
   (for `m = 3`). The rows of `P` are an isotropic vector, a hyperbolic partner and an orthogonal
   anisotropic vector.
2. **Transport** (`SymplecticPoints`). `symplecticGroupCongr P H` is an isomorphism
   `σ.symplecticGroup H ≅ σ.symplecticGroup (P H ᵗP^σ)`, induced by conjugation with `P` in the
   unit group scheme of `M_m(D)`. The published `parabolicElementarySubgroup_eq_top_iff_iso` and
   `IsConnectedReductive.of_iso` transfer the conclusion and the hypothesis.
3. **Matrix generation** (`StandardGenerationTwo/Three`). Every isometry of the standard Gram
   matrix is a product of isometries of contracting shape for the weights `(1, -1[, 0])` or their
   negatives (`unitaryMatrixGroup_gramTwo_le`, `unitaryMatrixGroup_gramThree_le`). This step uses
   `dim_K D = 4` and `dim_K D^σ = 3`: every quaternion is a product of two symmetric elements.
4. **Cocharacters** (`WeightedDynamic`, `SymplecticCocharacter`). The cocharacter
   `t ↦ diag(t, t⁻¹[, 1])` and its inverse factor through the symplectic group: they preserve
   the standard form, and their reduced norm is trivial because they are commutators.
5. **Contracting points** (`WeightedDynamic`, `SymplecticRationalPoints`). Every isometry of
   contracting shape is the matrix of a rational point of the symplectic group in the dynamic
   unipotent subgroup of the corresponding cocharacter (`exists_rationalMatrix_eq_of_contracting`).
   This uses an explicit polynomial contraction curve, closedness of the unitary and symplectic
   subgroups, and the triviality of the dynamic unipotent subgroup of the trivial cocharacter of
   `𝔾_m` for the reduced norm.
6. **Radicals** (`SymplecticGeneration`). The published
   `dynamicUnipotent_le_parabolicElementarySubgroup` (module
   `Rational.DynamicElementarySubgroup`, needs `IsConnectedReductive`) puts these rational
   points in `parabolicElementarySubgroup`. The injective rational matrix map
   `rationalMatrix` and step 3 then show that every rational point lies there
   (`parabolicElementarySubgroup_eq_top_of_le_contracting`).

## Library results used

`localSymplecticKneserTits_of_isConnectedReductive`,
`FirstKindInvolution.isConnectedReductive_symplecticGroup`, and through them
`dynamicUnipotent_le_parabolicElementarySubgroup`,
`parabolicElementarySubgroup_eq_top_iff_iso`, `IsConnectedReductive.of_iso`,
`Dynamic.unipotent_eq_comap_of_isClosedSubgroup`, `Dynamic.unipotent_le_comap`,
`Dynamic.unipotent_trivialCocharacter`, `SubgroupFunctor.IsRepresentedBy.isoOfComap` and
`IsRepresentedBy.liftOfLE`, `homOfPoints`/`isoOfPoints`,
`FiniteAlgebraUnits.MatrixPoints.tensorMatrixEquiv`, `FiniteAlgebraUnits.rationalPointsEquiv`,
`mem_range_unitaryGroupι_iff` and `mem_range_kernelι_iff`.
