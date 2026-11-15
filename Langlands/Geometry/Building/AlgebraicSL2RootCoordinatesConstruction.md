# Construction of algebraic SL2 rank-one coordinates at non-multipliable roots

Module `Langlands.Geometry.Building.AlgebraicSL2RootCoordinatesConstruction`, namespaces
`Langlands.GroupScheme.SimpleRootFiber` and `Langlands.Geometry.Building`.

Worker 163, for Task 6836 (8c04a3ed-3fa6-4680-a59f-856738cb578b).

## Purpose

`AlgebraicRankOneCoordinatesExistenceStatement` (the target of Task 6836) has two clauses
for an indivisible relative root `b`:

- an SL2 clause when `2 • b` is not a relative root;
- an SU3 clause when it is, which is the published statement
  `AlgebraicSU3RootCoordinatesExistenceStatement`.

This module proves the SL2 clause from one explicit hypothesis, the published proposition
`SplitRelativeRootGroupProductStatement`, whose proof is Task 7010. It then reduces the whole
target to that proposition and the SU3 statement. Neither proposition is assumed outside the
hypotheses of the theorems below.

## Contents

- `SimpleRootFiber.fiberSL2Coordinates : AlgebraicSL2RootCoordinates (groupHom f ≫ j) j
  (groupHom f) a`, in the setting of `SimpleRootFiberPinning`: the fiber pinning for a generic
  `ν` making `a` simple, `2 • a` not a relative root, `K/k` Galois, `j` closed. The fields are:
  - `extension`: the fiber field `fiberField`;
  - `positive`, `negative`: `positiveCoordinates` / `negativeCoordinates` (module
    `SimpleRootFiberCoordinates`). Their product hypotheses are discharged by
    `fiber_hprodp`, `fiber_huniqp`, `fiber_hprodm`, `fiber_huniqm` (module
    `SimpleRootFiberProducts`) from `hProd`;
  - `rho`: the descended `SplitPinning.fieldSL2` (module `OrthogonalOrbitSpecialLinear`);
  - `rho_upper`, `rho_lower`: by definition (`rfl`);
  - `coroot` and `coroot_points`: `fiberCoroot` and `fiberCoroot_points` (module
    `SimpleRootFiberCoroot`).
- `SimpleRootFiber.fiberSL2Coordinates_weyl`: `rho weylMatrix ∈ normalizerPoints
  (groupHom f ≫ j)`. `SplitPinning.fieldSL2_weylMatrix_mem` (module
  `OrthogonalOrbitWeylNormalizer`) places it in the normalizer of `j`. Then
  `IsMaximalSplitTorus.mem_normalizerPoints_of_mem_normalizerPoints` passes to the maximal
  split torus.
- `Geometry.Building.exists_algebraicSL2RootCoordinates_of_product hProd`: the SL2 clause,
  with exactly the binders of the target (`G` connected reductive, `i` maximal split, `Z` a
  torus, `j` representing `torusCentralizer i`, `s ≫ j = i`, `b` indivisible, `2 • b` not a
  relative root). The proof follows the Library proof of
  `quasiSplitR1RootFieldCoordinates_of_structuralStatements`:
  - `j` is closed (`IsSplitTorus.isClosedSubgroup_torusCentralizer`) and `Z` is its own
    centralizer, so `j_K` is a maximal torus (`isMaximalTorus_baseChange_of_torusCentralizer_eq`);
  - `torusFiniteGaloisSplitting` gives a finite Galois `K` splitting `Z`;
  - `rootDatumExistence` gives a reduced root datum `P` of `j_K`;
  - `relativeRootSystem` gives `HasRelativeRootSystem i`;
  - `RelativeRoot.exists_isGenericCocharacter_mem_simpleRelativeRoots` (module
    `SimpleRootFiberPinning`) gives a generic `ν` for which `b` is simple.
  With `f := Additive.ofMul s`, the record is `fiberSL2Coordinates`.
- `Geometry.Building.algebraicRankOneCoordinatesExistence_of_product_of_su3`:
  `SplitRelativeRootGroupProductStatement → AlgebraicSU3RootCoordinatesExistenceStatement →
  AlgebraicRankOneCoordinatesExistenceStatement`. The SL2 clause is the previous theorem, and
  the SU3 clause is the SU3 statement verbatim.

## Provenance

Internal assembly. The mathematical content is in the modules cited above and in the two
hypotheses. The source for the reduction to restrictions of scalars of `SL₂` and `SU₃` is
Kaletha–Prasad, proof of Proposition 7.1.1 (source `kaletha-prasad-2023-bruhat-tits-new-approach`,
printed p. 239, PDF p. 270), as recorded in the target statement's Markdown. Every step here
is proved in Lean.
