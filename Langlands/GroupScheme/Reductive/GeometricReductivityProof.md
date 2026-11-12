# Haboush's theorem: the proof

Author: Worker 4404.

`Langlands.GroupScheme.reductiveGeometricReductivity` proves exactly the
published proposition
`Langlands.GroupScheme.ReductiveGeometricReductivityStatement.{u}` (module
[`GeometricReductivityStatement`](GeometricReductivityStatement.md)). It holds
for every universe `u` and takes no hypotheses.

Take any algebraically closed field `k : Type u` and any group scheme `G` over
`Spec k` with `IsPseudoReductive G`. Let `n` be a finite coordinate type,
`ρ : MatrixRepresentation G n` a representation and `v : n → k` a nonzero vector
with `ρ.IsFixedVector v`. The theorem gives `d : ℕ` and `F : MvPolynomial n k`
with `0 < d` and `F.IsHomogeneous d`. On every test scheme `T` over `Spec k`,
every point `g : T ⟶ G.X` and every `x : n → Γ(T, ⊤)`, evaluating `F` through
`scalarMap T` at `ρ(g) x` gives the same value as at `x`. Finally
`MvPolynomial.eval v F ≠ 0`.

The target's definitions and quantifiers are unchanged. The proof does not
assume geometric reductivity, linear reductivity, finite generation of
invariants, or any Steinberg-module or Haboush-type premise. Every input it uses
is a published unconditional Library theorem. `lean_check` compiles the module
with no errors or warnings. Its axiom inspection of
`reductiveGeometricReductivity` reports only `propext`, `Classical.choice` and
`Quot.sound`.

## Relation to the conditional assembly

The Library module
[`GeometricReductivityReduction`](GeometricReductivityReduction.md) proves the
target from four explicit hypotheses
(`reductiveGeometricReductivity_of_structural_inputs`). This module discharges
three of them with published proofs:

| Hypothesis | Proposition | Discharged by |
| --- | --- | --- |
| `hproduct` | `ReductiveCentralDerivedProductStatement` | `reductiveCentralDerivedProduct` |
| `hmap` | `SimplyConnectedPositiveCharConjugationMapStatement` | `HaboushReduction.simplyConnectedConjugationMap` (below) |
| `hzero` | `ReductiveCharZeroSemisimplicityStatement` | `reductiveCharZeroSemisimplicityStatement` |

The fourth hypothesis, `SimplyConnectedDerivedCoverExistenceStatement`, is
stated over arbitrary fields and has no published proof. This module does not
use it. Over an algebraically closed field it builds the simply connected cover
of the derived subgroup directly (step 3 below). The proof therefore repeats the
prime-characteristic part of the conditional assembly with `hcover` replaced.
It calls the assembly's unconditional lemmas `separator_of_central_split_product`
and `epi_subgroupProductMap_iso` directly.

## Implemented proof

All declarations below other than the final theorem are in the namespace
`Langlands.GroupScheme.HaboushReduction`.

### 1. The positive-characteristic conjugation-map input

`simplyConnectedConjugationMap` proves
`SimplyConnectedPositiveCharConjugationMapStatement.{u}`. That proposition says
the following. Let `G` be a simply connected group over an algebraically closed
field of prime characteristic, and `v` a nonzero fixed vector of a representation
`ρ`. Then some representation `σ` on `Fin m` with `0 < m` and some
conjugation-equivariant linear map `φ` from `ρ` to `σ` send `v` to a nonzero
scalar identity matrix. The proof composes these published declarations:

- `simplyConnectedPositiveCharConjugationMap_of_bigCell` (module
  [`SteinbergBigCellReduction`](SteinbergBigCellReduction.md)) derives it from
  `SteinbergBigCellStatement.{u}`, through covariant exhaustion and Steinberg
  tensor embeddings;
- `steinbergBigCell_of_rootAndCoroot` (module
  [`SteinbergBigCellRootCorootAssembly`](SteinbergBigCellRootCorootAssembly.md))
  derives `SteinbergBigCellStatement.{u}` from `RootDatumExistenceStatement.{u}`
  and `SplitSimplyConnectedCorootSpanStatement.{u}`;
- `rootDatumExistence` (module [`RootDatumExistence`](RootDatumExistence.md))
  proves `RootDatumExistenceStatement.{u}`;
- `splitSimplyConnectedCorootSpan_of_inputs` (module
  [`SimplyConnected.SplitNecessityAssembly`](../SimplyConnected/SplitNecessityAssembly.md))
  derives `SplitSimplyConnectedCorootSpanStatement.{u}` from the conjunction
  `SplitSimplyConnectedCorootSpanInputsStatement.{u}`. Its three conjuncts are
  the published theorems `splitReductiveExistence` (module
  [`SplitExistence`](SplitExistence.md)), `splitCentralIsogenyExistence` (module
  [`SplitCentralIsogenyExistenceProof`](SplitCentralIsogenyExistenceProof.md))
  and `splitSemisimpleRootDatum` (module
  [`SplitSemisimplicity`](SplitSemisimplicity.md)).

### 2. Simply connected covers of semisimple groups

`exists_simplyConnected_cover_of_isSemisimple` takes `D` over `Spec k`, `k`
algebraically closed, with `IsSemisimple D`. It gives a group scheme `C` and a
homomorphism `π : C ⟶ D` with `IsSimplyConnected C` and `IsCentralIsogeny π`.
Semisimplicity includes connected reductivity, so `D` is smooth and affine. An
algebraically closed field is separably closed, so
`exists_isMaximalTorus_isSplitTorus_of_isSepClosed` (module
[`Torus.StrictHenselianMaximalReduction`](../Torus/StrictHenselianMaximalReduction.md))
gives a maximal torus `t : T ⟶ D` with `T` split. The published theorem
`splitSimplyConnectedCoverExistence` (module
[`SimplyConnected.SplitCoverExistenceProof`](../SimplyConnected/SplitCoverExistenceProof.md))
then gives the cover.

### 3. Separators in standard coordinates, prime characteristic

`separator_fin_of_isAlgClosed` fixes a prime `p` with `CharP k p` and a
pseudo-reductive `G`. For a representation `ρ` on `Fin N` and a nonzero fixed
vector `v`, it gives `r > 0` and `F` homogeneous of degree `r`, with
`ρ.IsInvariantPolynomial F` and `F(v) ≠ 0`.

1. `IsPseudoReductive.isConnectedReductive_of_isAlgClosed` makes `G` connected
   reductive.
2. `reductiveCentralDerivedProduct` gives a central closed torus `i : Z ⟶ G`, an
   actual derived subgroup `d : D ⟶ G` (`IsDerivedSubgroup d`), and an
   epimorphic product map `subgroupProductMap i d`.
3. `D` is semisimple:
   - `IsDerivedSubgroup.isConnectedReductive` (module
     [`Derived.MaximalTorusIntersectionReduction`](../Derived/MaximalTorusIntersectionReduction.md))
     makes `D` connected reductive;
   - `derivedCentralIntersectionFiniteness` (module
     [`Derived.CentralIntersectionProof`](../Derived/CentralIntersectionProof.md))
     gives a finite closed subgroup `c : E ⟶ D` whose range is the inverse image
     of the full centre of `G`;
   - `IsDerivedSubgroup.hasFiniteCenter_of_centralProduct` (module
     [`Derived.SemisimpleReduction`](../Derived/SemisimpleReduction.md)), applied
     with `d` as both derived subgroups, the central torus `i`, the epimorphic
     product and `c`, gives `HasFiniteCenter D`. It needs `G.X.left` affine,
     which follows from `IsAffineHom G.X.hom`.
4. Step 2 gives a simply connected `C` with a central isogeny `π : C ⟶ D`.
5. `D.X.left` is affine: `d` is a closed immersion, so `D.X.hom` (equal to `d`
   followed by `G.X.hom`) is affine.
6. The proved `torusFiniteGaloisSplitting`, through
   `IsTorus.isSplitTorus_of_finiteGaloisSplitting`, gives a finite type `I` and
   an isomorphism `eZ` from `Z` to the split torus on `I`. The map
   `j = eZ.inv ≫ i` is central, since every point of the split torus maps to a
   point of `Z`. `epi_subgroupProductMap_iso` keeps the product map epimorphic.
7. `separator_of_central_split_product` (module
   [`GeometricReductivityReduction`](GeometricReductivityReduction.md)), applied
   to `simplyConnectedConjugationMap`, `j`, `d`, `π` and `ρ`, gives the
   separator. That lemma restricts `ρ` to `D` and then to the cover `C`. On `C`
   the conjugation-map input yields a map whose value at `v` is a nonzero scalar
   identity. Its determinant is a homogeneous invariant of positive degree,
   nonzero at `v`. The flat surjective central isogeny descends invariance to
   `D`. Pullback through the zero-weight projection of the central split torus
   adds torus invariance. The epimorphic product then gives invariance under all
   of `G`.

### 4. Arbitrary finite coordinates, prime characteristic

`separator_of_isAlgClosed` extends step 3 to every finite coordinate type `n`.
This is the same argument as the Library's `separator_of_structural_inputs`.
`Chevalley.exists_affine_finite_regular_map_to_one` gives an intertwiner `C`
from `ρ` to a finite regular representation on some `Fin d`
(`Chevalley.affineRegularRepresentation`). In the chosen basis, `C v` expands
to the constant function `1`. So `C v ≠ 0`: otherwise `0 = 1` in the coordinate
algebra, and applying the counit gives `0 = 1` in `k`. `C v` is fixed by
`Intertwines.isFixedVector`. Step 3 gives a separator for `C v`, and
`Intertwines.pullback_separator` pulls it back to a separator for `v` with the
same degree.

### 5. The final theorem

`reductiveGeometricReductivity` splits on the characteristic of `k` using
`CharP.char_is_prime_or_zero`.

- If `ringChar k` is prime, step 4 applies with `p = ringChar k`.
- If `ringChar k = 0`, then `k` has characteristic zero. The Library's
  `invariant_polynomial_of_reductive_charZero_semisimplicity`, applied to
  `reductiveCharZeroSemisimplicityStatement`, gives a degree-one separator.
  Complete reducibility of the representation of `G(k)` on `n → k` gives a
  fixed vector `c` of the dual representation with `c ⬝ᵥ v = 1`
  (`exists_dual_fixed_of_rational_semisimple`). The linear polynomial of `c` is
  invariant on every test scheme (`exists_invariant_polynomial_of_dual_fixed`).

Invariance uses the Library's unchanged `MatrixRepresentation.IsInvariantPolynomial`,
on every test scheme over `Spec k` with no affineness or reducedness restriction.
It unfolds to the target's displayed `eval₂` equation, so both branches match
the target exactly.

## Comparison with the original source

The task cites D. Mumford, J. Fogarty, F. Kirwan, *Geometric Invariant Theory*,
3rd ed. (1994), registered as `mumford-fogarty-kirwan-1994-git-3rd`: definition
(iii) on printed p. 191 and Theorem A.1.0 (a ⇒ b) on printed p. 192. Their sketch
of Haboush's proof reduces to a semisimple simply connected group and to a
representation `V` inside the coordinate ring. With `W = H⁰(G/B, L(mϱ))` for
`m = p^r − 1`, irreducible and self-dual by Steinberg, it builds a `G`-linear map
`φ : V → W ⊗ W ≅ Hom(W, W)` with `φ(v) = a · id`, `a ≠ 0`, and takes
`det ∘ φ` as the invariant. On p. 191 they note that linear reductivity
implies geometric reductivity, and that reductive groups are linearly reductive
in characteristic zero.

The implemented route has the same structure.

- In prime characteristic, the reductive group is written as a central torus
  times its derived subgroup. The derived subgroup is semisimple, and the proof
  passes to its simply connected cover.
- On the cover, the conjugation-equivariant map into a representation `σ` comes
  from the Library's Steinberg big-cell and tensor-embedding construction. The
  invariant is the determinant of the value of this map, as in the source.
- In characteristic zero, the separator is a linear form built from complete
  reducibility.

Two details differ from the sketch.

- Invariants are descended along the central isogeny by flat surjective descent,
  and extended across the central torus with a zero-weight projection. No
  representation is descended from the cover.
- The reduction to a representation inside the coordinate ring is an explicit
  intertwiner into a finite regular representation, sending `v` to the
  constant function `1`. It is applied to the whole reductive group, before
  the passage to the derived subgroup and its cover.

This module introduces no new structural assertion. All mathematical content
comes from the published Library modules linked above.
