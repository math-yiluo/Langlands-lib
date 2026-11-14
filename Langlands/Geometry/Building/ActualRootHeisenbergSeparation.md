# Heisenberg separation data from actual root partners

This module constructs `HeisenbergUnitarySeparationData` for an actual
multipliable relative root from structural group hypotheses and a supplied
equivariant Heisenberg normal form. It constructs the fields, both rational-point
coordinates, the cocycle in coordinates, its homogeneity and nonsymmetry, the
actual descended character and its actions, and separation of its values.

Provenance: internal. This is an assembly of the actual-root field and coordinate
constructions in `RootPartnerFields`, `RootPartnerCharacterNorm`,
`RootPartnerCharacterSeparation`, `RootQuotientFieldCoordinates` and
`DoubleRootTraceZeroCoordinates`, with the published cocycle homogeneity and
noncommutation results. The partner-existence wrapper uses
`MultipliableRootNoncommutation.exists_partner` and the published maximal-torus
and root-reducedness lemmas. It introduces no new literature assertion or
classification input.

All declarations are in `Langlands.Geometry.Building`. Write `b` for
`algebraBaseMap k L` and use subscripts `L` for base change along `b`.

## Helpers

`card_rootOrbitField_embeddings k L j beta` assumes that `L/k` is finite Galois.
For an actual root `beta` of `j_L : T_L -> G_L`, it proves

```
Nat.card (rootOrbitField k L j beta ->_alg[k] L)
  = Module.finrank k (rootOrbitField k L j beta).
```

The proof rewrites the degree using the index of the fixing subgroup, identifies
that subgroup with the actual root stabilizer, and applies the finite-Galois
quotient-to-embedding equivalence. No splitting field beyond the given `L` is
chosen.

`traceZero_smul_mem k F E c w` works for a compatible tower `k -> F -> E` with
`E/F` separable quadratic. It proves that the additive subgroup
`SU3Root.Parameters.traceZero (SU3Root.fieldInvolution F E)` is stable under
scalars `c : k`. Its proof uses the `k`-linear conjugation automorphism to factor
`c` out of `w + conjugation(w) = 0`. It needs no separate module instance on
that subgroup and does not divide by two.

## Predicate and construction setting

`HasActualRootHeisenbergSeparationData k f j C N : Prop` is

```
Nonempty (HeisenbergUnitarySeparationData C N (CommGroupScheme.groupHom f)).
```

Here `f : S -> T` is a morphism of commutative group schemes over `k`,
`j : T.toGrp -> G`, and `i = CommGroupScheme.groupHom f >> j`.
The affine group schemes `U` and `U2`, with their supplied representing maps,
represent the relative root subgroups for `a` and `2*a`.
`C : DoubleRootCommutatorPairing i a hjU hj2` supplies the quotient `C.V`.
The supplied `N` is an `EquivariantHeisenbergNormalForm` of `C` for conjugation
by `T`, with the hypothesis `hfix` that this action fixes `i(S)` on every test
scheme. The predicate merely asserts existence of separation data; it does not
record identities of the witness's fields with particular stabilizer fields.
The constructors below choose those actual fields.

Both constructors assume the following further setting. The fields `k` and `L`
are in an arbitrary universe `u`; `k` is infinite and `L/k` is finite Galois.
The ambient `G` is affine, smooth and locally of finite type, with supplied
connected reductivity. The torus presentation `T` is affine and locally of
finite type; `j` is a closed subgroup; `i` is a maximal split torus; and `j`
represents its full torus centralizer. The base change `T_L` is split, with
supplied root datum `P` of `j_L` indexed by a finite type in universe `u`.
The quotient `C.V` is affine. Both `a` and `2*a` are relative roots of `i`, and
no `n*a` for `n >= 3` is a relative root.

## Construction from a supplied partner pair

`hasActualRootHeisenbergSeparationData_of_partner` additionally assumes that `j`
is a maximal torus and supplies three actual roots `beta`, `beta'`, `mu0` of
`j_L`. The hypothesis `RootPartnerFields.IsRootPartner k L j beta beta'` says
that `beta'` is a distinct Galois translate of `beta` and their sum is a root.
The other hypotheses state `mu0.val = beta.val + beta'.val`, that `beta`
restricts to `a`, and that `mu0` restricts to `2*a`.

The implemented proof proceeds as follows.

1. The maximal split torus and full torus centralizer imply that every absolute
   root has nonzero restriction, hence nonzero Galois orbit sum. Set
   `F = rootOrbitField k L j mu0` and `E = rootOrbitField k L j beta`.
   The root-partner theorems give `F <= E`, the algebra structure induced by
   that inclusion, compatible scalar towers, and separable quadratic `E/F`.
2. Full centralizer transitivity identifies each chosen actual-root orbit with
   its restriction fiber. `quotientFieldEquiv` then gives additive coordinates
   `first : Multiplicative E ≃* rationalPoints C.V`, linear through the actual
   quotient point-to-Lie comparison. `Multiplicative E` here encodes the
   additive field group, not the unit group.
3. Take the character descended from `beta`. The actual partner character norm
   theorem identifies the descended doubled-root character with its quadratic
   norm. `hasDoubleRootTraceZeroCoordinates` constructs
   `second : Multiplicative (traceZero ...) ≃* rationalPoints U2`, together
   with Lie-linearity and conjugation by that norm.
4. Define `form x y` to be the underlying `E` element of the inverse `second`
   coordinate of the cocycle at `(first x, first y)`. Thus `cocycle_eq` is
   definitional. The two published cocycle homogeneity lemmas, the coordinate
   Lie-linearity laws and `traceZero_smul_mem` prove `k`-homogeneity in both
   arguments.
5. `MultipliableRootNoncommutation.not_pointsCommute` supplies two points of
   `U` on some test scheme that do not commute. The published
   `HeisenbergNormalForm.exists_form_ne_swap` turns this into nonsymmetry of
   `form` in the chosen coordinates.
6. The quotient character action and its restriction to `S`, the doubled-root
   norm action, `card_rootOrbitField_embeddings`, and the infinite-field
   `RootPartnerFields.hasSeparatingCharacterValues` fill the remaining
   separation-data fields, with `splitting = L`.

## Construction from structural multipliable-root hypotheses

`hasActualRootHeisenbergSeparationData` has the construction setting above and
concludes the same predicate without supplying partner roots or maximality of
`j`. The closed-subgroup assumption on `j` is retained explicitly.

The proof first shows `torusCentralizer j = SubgroupFunctor.range j`: the
centralizer of `j` lies in the represented centralizer of `i`, and the range of
`j` centralizes itself. The self-centralizing-torus results make `j` maximal
over `k` and after base change to `L`. Connected reductivity ascends to `L`.
`RootPairNoncommutation.hasNoHigherRoots` gives reducedness of the absolute
roots. The published `exists_partner` now supplies two roots of `P` restricting
to `a`, with pairing `-1`, whose sum is a root and which are Galois translates.
They are distinct because a root paired with itself has pairing `2`. Their sum
restricts to `2*a` by additivity. The preceding constructor applies to these
three actual roots.

## Consequences and retained inputs

The published `HeisenbergUnitarySeparationData.toHeisenbergUnitaryData` can turn
a witness into `HeisenbergUnitaryData` under the splitness, nonzero-root and
no-higher-root hypotheses already available here. That consumer derives
additivity and trace compatibility of the cocycle from the separation data.

The construction imposes no characteristic restriction, including in
characteristic two. Infinitude of `k` is an explicit hypothesis used for
character-value separation. This module retains the supplied represented
commutator quotient and equivariant Heisenberg normal form, finite Galois
splitting field, root datum and all-test fixing hypothesis. It constructs
rational-point coordinate data for this one sign. It supplies no coherent
opposite coordinates, SU3 homomorphism, coroot comparison or affine-root lift,
and does not prove `QuasiSplitIndivisibleDerivativeLiftsStatement`.
