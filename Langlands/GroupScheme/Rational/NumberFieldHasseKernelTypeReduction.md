# The absolutely almost-simple Hasse kernel by Cartan type

Module: `Langlands.GroupScheme.Rational.NumberFieldHasseKernelTypeReduction`.

The module states the Hasse kernel over number fields for seven classes of
simply connected absolutely almost-simple groups. It also proves that these
statements, together with the local-to-global principle for reduced norms and the
quaternionic spin kernel, give
`NumberFieldAbsolutelyAlmostSimpleSimplyConnectedGaloisHasseKernelStatement`.
The seven statements are not proved in this module.

## The common shape of the statements

Each statement quantifies over a number field `F : Type u`, an affine, locally
finite-type group scheme `G` over `Spec F`, actual Tits index data
`d : TitsIndexData G` and a bijection `e` from the simple vertices `d.Vertex` to
`Fin r` that carries the actual Cartan pairings `d.cartan` to a Mathlib Cartan
matrix. It assumes `IsSimplyConnected G` and `IsAbsolutelyAlmostSimple G`. Its
conclusion is the same as in the published type `C` statement
`NumberFieldTypeCSimplyConnectedGaloisHasseKernelStatement`: for every finite Galois
extension `L/F` in the same universe, every cocycle
`ξ : Cocycle G (GaloisCocycle.cover F L)` with `ξ.LocallyTrivial` satisfies
`ξ.IsTrivial`. Local triviality means triviality after pullback to the full cover
`Spec (F_v ⊗_F L) → Spec F_v` at every place `v`, archimedean ones included.

The seven classes are the following.

- `NumberFieldOuterTypeAHasseStatement`: the Cartan matrix is `CartanMatrix.A n`
  and some `σ` in the absolute Galois group and some simple vertex `a` satisfy
  `d.star σ a ≠ a`. This is the reading of "outer type" used in the published
  `OuterTypeAUnitarySplitPresentationStatement`.
- `NumberFieldTypeBSimplyConnectedGaloisHasseKernelStatement`: the Cartan matrix is
  `CartanMatrix.B n` with `3 ≤ n`.
- `NumberFieldTrialitarianTypeDHasseStatement`: the Cartan matrix is
  `CartanMatrix.D 4`, and every vertex `a` with `e a ≠ 1` is moved by some element of
  the absolute Galois group. In Mathlib's numbering of `D_4` the vertex `1` is the
  centre and `0`, `2`, `3` are the three leaves, so the condition says that no leaf
  is fixed by the full star action. Since the star image is a subgroup of the
  symmetric group on the three leaves, this holds exactly when the image contains
  the cyclic subgroup of order three, that is, for the trialitarian forms `³D_4` and
  `⁶D_4`.
- `NumberFieldTypeE6HasseStatement`, `NumberFieldTypeE7HasseStatement` and
  `NumberFieldTypeE8HasseStatement`: the Cartan matrix is `CartanMatrix.E 6`,
  `CartanMatrix.E 7` or `CartanMatrix.E 8`. The type `E_6` statement makes no
  assumption on the star action, so it covers both the inner and the outer forms.
- `NumberFieldTypeF4HasseStatement`: the Cartan matrix is `CartanMatrix.F₄`.

## Sources

The statements are the cases of the Hasse principle for simply connected groups
over number fields: the canonical map `H¹(K, G) → ∏_v H¹(K_v, G)` has trivial
kernel when `G` is semisimple and simply connected. This is Milne, *Algebraic
Groups* (2017), Theorem 25.64(a), printed p. 562, and it is the injectivity part of
Platonov and Rapinchuk, *Algebraic Groups and Number Theory* (1994), Theorem 6.6,
printed p. 286, with the discussion on printed pp. 285–286. Platonov and Rapinchuk
prove it by type: the classical groups in §6.7 (printed pp. 356–368) and the groups
of types `³,⁶D_4`, `¹,²E_6`, `E_7`, `E_8`, `F_4` and `G_2` in §6.8 (printed
pp. 368–397). Milne attributes the number-field case to Harder (1966) for every type
except `E_8`, and to Chernousov (1989) for type `E_8`.

Each Lean statement concerns the classes split by a finite Galois extension inside
the trivial-class preimage of the localization map, with the actual cover in place
of the absolute Galois group. Triviality at the archimedean places is part of the
hypothesis. Twisting by a cocycle, as in the published
`numberFieldHassePrinciple_of_absolute`, recovers injectivity from these kernels.

## The reduction theorem

`numberFieldAbsolutelyAlmostSimpleSimplyConnectedGaloisHasseKernel_of_types` assumes
`Langlands.CentralSimple.NumberFieldReducedNormLocalityStatement`, the published
`NumberFieldQuaternionicSpinHasseStatement` and the seven statements above, and
proves `NumberFieldAbsolutelyAlmostSimpleSimplyConnectedGaloisHasseKernelStatement`.

The proof chooses actual index data with `titsIndexExistence` and applies
`absolutelyAlmostSimpleCartanClassification`, which numbers the simple vertices by
one of the nine irreducible finite Cartan families. The cases are as follows.

- Type `A_n`. When the full star action is trivial the index satisfies
  `HasInnerTypeA n`, and
  `numberFieldInnerTypeASimplyConnectedGaloisHasseKernel_of_reducedNormLocality`
  applies. Otherwise the outer type `A` statement applies.
- Type `B_n`. For `n = 2` the theorem `cartanB_two_swap` shows that exchanging the
  two vertices turns `CartanMatrix.B 2` into `CartanMatrix.C 2`, and the published
  `numberFieldTypeCSimplyConnectedGaloisHasseKernel` applies. For `n ≥ 3` the type
  `B` statement applies.
- Type `C_n` is the published `numberFieldTypeCSimplyConnectedGaloisHasseKernel`.
- Type `D_n`. For `n ≥ 5`, `TitsIndexData.star_fixes_nonfork_of_D` shows that the
  star action fixes every vertex outside the fork, and the published reduction
  `numberFieldClassicalTypeDHasse_of_quaternionic` applies. For `n = 4`, if some
  leaf is fixed by the full star action, the numbering `d.d4NumberingAt e a` places
  it at vertex `0`; `TitsIndexData.d4NumberingAt_cartan` keeps the Cartan matrix and
  `TitsIndexData.star_fixes_nonfork_of_D4_fixed_leaf` gives the fixed nonfork
  vertices, so the same reduction applies. If no leaf is fixed, the trialitarian
  statement applies.
- Types `E_6`, `E_7`, `E_8` and `F_4` are the corresponding statements.
- Type `G_2` is the published `numberFieldTypeG2Hasse`.

In every case the original group, cover and cocycle are passed on unchanged.
