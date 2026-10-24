# Finite local coordinate duality

For a scheme `X : AlgebraicGeometry.Scheme.{u}`, an actual module sheaf `M : X.Modules`, an open `U : X.Opens`, and a finite type `I : Type u`, this module constructs

```lean
Langlands.Scheme.Modules.dualLocalFreeIso
  (e : SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅ M.over U) :
  SheafOfModules.free (R := X.ringCatSheaf.over U) I ≅
    (Langlands.Scheme.Modules.dual M).over U
```

The constructor requires `[Finite I]` and chooses `Fintype.ofFinite I` internally for finite sums. It retains the same index type. There is no inhabitedness assumption on `I`, no nonemptiness assumption on `U`, and no geometric hypothesis on `X`. In particular, the empty basis and empty open are included. The isomorphism's forward map is independent of the choice of a finite enumeration: `dualLocalFreeIso_hom` identifies it with `dualLocalFreeHom e`, which requires no finiteness instance. Its inverse is determined by the inverse laws.

All public names below are in `Langlands.Scheme.Modules`. The existing `ModuleDual` and its imports are unchanged. The target is its actual `dual M = internalHom M (Langlands.SchemeModule.structureModule X)`.

## Implemented construction

Mathlib's `SheafOfModules.free I` is the categorical coproduct of copies of the structure module. `freeCoordinate U I i` is the coproduct map whose composite with the `j`th inclusion is the identity if `j = i` and zero otherwise. This formula is `ιFree_freeCoordinate`. Under `[Fintype I]`, `freeCoordinate_total` proves that the finite sum of coordinate projections followed by their inclusions is the identity. Its proof checks equality after every coproduct inclusion and reduces the resulting finite sum to its single diagonal term. This argument includes an empty index type.

Given the actual trivialization `e`, `localBasisCoordinate e i` is `e.inv` followed by the `i`th coordinate projection. It is an actual morphism `M.over U ⟶ (structureModule X).over U`, hence a section of the published internal dual. `localBasisSection e i` is the compatible family of sections given by the `i`th free generator followed by `e.hom`. The lemma `localBasisCoordinate_basis` proves the Kronecker evaluation formula on each object of `Over U` by cancelling `e.hom ≫ e.inv`.

`localDualSection` restricts a local functional to all objects of `Over U`. Its compatibility proof uses the composition law for `LocalHom.restrict`. The free-sheaf universal property applied to these compatible coordinate sections defines `dualLocalFreeHom e`. The lemma `dualLocalFreeHom_basis` identifies its value on each free generator with the restriction of the corresponding coordinate functional.

For any compatible local section `s` of `M.over U`, `localDualEvaluation s` is the morphism from `(dual M).over U` to the structure module that evaluates a local functional on `s`. Linearity comes from `dualEval`; naturality is the existing `internalHomEval_restrict` law combined with compatibility of `s`. Thus both the forward map and these evaluation maps are morphisms of sheaves on the over-category, compatible with every restriction.

The finite sum of `localDualEvaluation (localBasisSection e i)` followed by the `i`th free inclusion defines `dualLocalFreeInv e`. The proof `dualLocalFreeHom_evaluation` identifies forward map followed by evaluation on the `i`th basis vector with the `i`th free coordinate projection. Together with `freeCoordinate_total`, this proves `dualLocalFreeHom_inv`.

For the other inverse law, `localBasis_expansion` transports the finite identity decomposition through `e` and evaluates it on each smaller open. Every module section is therefore the finite sum of its coordinates times the basis vectors there. The lemma `localDualEvaluation_hom_ext` uses this expansion to distinguish sheaf maps into the internal dual: restrict a candidate functional to an arbitrary still smaller open, compare it on all basis vectors using naturality, then extend equality to all sections using linearity and the expansion. Applying this criterion proves `dualLocalFreeInv_hom`. These two inverse laws construct `dualLocalFreeIso`.

## Evaluation law

For every `V : X.Opens`, inclusion `h : V ⟶ U`, and `i j : I`, `dualLocalFreeIso_eval` states

```lean
dualEval M V
  ((dualLocalFreeIso e).hom.val.app (op (Over.mk h))
    ((SheafOfModules.freeSection i).val (op (Over.mk h))))
  ((localBasisSection e j).val (op (Over.mk h))) =
    if j = i then 1 else 0
```

The value lies in the actual structure ring `Γ(X, V)`. The decision procedure for equality of indices is classical and is not an additional parameter. The lemma `dualLocalFreeIso_basis` gives the stronger description of the dual basis vector itself as `LocalHom.restrict h (localBasisCoordinate e i)`. The evaluation law follows from this description and `localBasisCoordinate_basis`.

## Provenance and scope

This is an elementary derived construction from the finite coordinate dual-basis argument and the published internal-Hom definition. It is not claimed as a separately quoted theorem from the sources below.

The retained Stacks Project source `stacks-relative-differentials-internal-hom-2026-10-21`, folder content SHA256 `9c075370ba97d8876785c5486425c6c661765e747452c026583f4dc51f1e1133`, contains `01CM.html`, Section 17.22, [Internal Hom](https://stacks.math.columbia.edu/tag/01CM). Its opening defines internal-Hom sections as morphisms of restricted module sheaves and scalar multiplication through restriction of regular functions. That opening was read for the meaning of the actual dual used here.

The retained source `stacks-local-freeness-invertibility-sections-2026-10-21`, folder content SHA256 `6d1641a9deb284be889ee6e2630a2be6e57cc5985c80af2c9da7d17543ed0785`, contains `01C5.html`, Section 17.14, [Definition 17.14.1, tag 01C6](https://stacks.math.columbia.edu/tag/01C6). This definition, read in the retained original, describes local freeness by trivializations as direct sums of structure modules; finite local freeness uses finite index sets and specified rank fixes their cardinalities. It motivates retaining exactly `I` in the construction.

The module constructs a local tool. It does not assert the universal preservation of finite local bases or specified local rank, and does not identify arbitrary internal-Hom sections with linear maps on sections. The finite-free argument establishing the isomorphism is proved explicitly above. No claim about duality commuting with pullback is made.
