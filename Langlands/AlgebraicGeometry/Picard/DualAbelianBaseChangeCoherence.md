# Coherence of actual dual abelian base change

This derived construction proves identity and composition equations for the
canonical base change of the actual evaluation-built dual abelian schemes,
their integral dual-valued maps and their rational dual-valued maps. It also
proves that the canonical identity and composition comparisons have geometric
rational dual-pullback multiplier one.

The namespace is `Langlands.AbelianScheme`. Schemes are arbitrary in universe
`u`, and the base maps have no additional flatness or reducedness hypotheses.
Every dual endpoint retains its own `HasDualScheme`, `DualSchemeGeometry`,
inverse Poincare line bundle and evaluation isomorphism. The results retain
the named propositions `pullbackTensorComparisonIsIsoStatement`,
`PicardZeroPullbackStatement`, `PullbackTensorCompositionStatement`,
`PullbackTensorUnitCoherenceStatement`,
`ExplicitPullbackTensorAssociativityStatement`,
`TensorMonoidalLeftUnitorComparisonStatement`,
`PullbackTensorSymmetryStatement`,
`PicardZeroUniversalBaseChangeStatement` and
`DualAbelianBaseChangeStatement` as required by the imported constructions.
They do not prove these propositions.

## Dualizing actual isomorphisms

`dualAbelianSchemeIsoFromEvaluation` dualizes an actual isomorphism by applying
the already constructed dual homomorphisms to its two directions. Its inverse
laws follow from contravariant composition and identity. It asserts an
isomorphism between specified constructions. For `e : A ≅ B`, it has type
`D(B) ≅ D(A)`, where `D` denotes the corresponding
`dualAbelianSchemeFromEvaluation` construction.

## Identity

Let `A_i = (baseChange (𝟙 S)).obj A`, let
`i = baseChangeIdIso A : A_i ≅ A`, and let `iD` be its dual isomorphism.
Write `β_i` for `dualAbelianBaseChangeIso` at the identity base map. Then
`dualAbelianBaseChangeIso_id` proves

```
β_i.hom = (baseChangeIdIso D(A)).hom ≫ iD.hom.
```

Its proof forgets the group-object structure through the faithful underlying
map, substitutes `dualAbelianBaseChangeIso_hom` and applies the existing
`dualSchemeBaseChangeIso_id`.

For an integral `lam : A ⟶ D(A)`, write `F_i(lam)` for
`dualAbelianBaseChangeMap` at the identity map. The lemma
`dualAbelianBaseChangeMap_id` proves

```
F_i(lam) = i.hom ≫ lam ≫ iD.hom.
```

The proof substitutes the dual comparison equation and uses naturality of
the actual abelian-scheme identity comparison.

For rational homomorphisms, write `⟦f⟧` for `homToHom0 f`, use `;` for the
composition `comp0`, and write `F_i` for `rationalDualBaseChangeHom`.
The theorem `rationalDualBaseChangeHom_id` proves

```
F_i(lam) = (⟦i.hom⟧ ; lam) ; ⟦iD.hom⟧.
```

Tensor-product induction reduces a pure tensor to the integral map equation;
the additive case follows from linearity. This covers every rational
dual-valued map.

`rationalDualBaseChangeHom_id_multiple` expresses the same equation using the
existing `IsRationalDualPullbackMultiple` predicate:

```
(⟦i.hom⟧ ; lam) ; dualHom0(⟦i.hom⟧) = 1 • F_i(lam).
```

The theorem takes the named `DualSchemeMapAdditivity` premise for the pair
`A_i, A`. Its proof uses `dualHom0_homToHom0`, the rational identity equation
and `one_smul`.

## Composition

For `b : S' ⟶ S` and `c : S'' ⟶ S'`, put
`A_b = b*A`, `A_d = (c ≫ b)*A`, and `A_c = c*(b*A)`.
The comparison
`k = baseChangeCompIso b c A : A_d ≅ A_c` goes from direct to successive
base change. Its dual is
`kD : D(A_c) ≅ D(A_d)`, with all endpoint evaluation data retained.
Write `β_b`, `β_c`, `β_d` for the corresponding canonical dual comparisons,
and `k_DA = baseChangeCompIso b c D(A)`.

The two equations `dualAbelianBaseChangeIso_comp_inv` and
`dualAbelianBaseChangeIso_comp` are

```
(baseChange c).map β_b.hom ≫ β_c.hom =
  k_DA.inv ≫ β_d.hom ≫ kD.inv,

k_DA.hom ≫ (baseChange c).map β_b.hom ≫ β_c.hom =
  β_d.hom ≫ kD.inv.
```

The inverse-comparison equation follows by faithful passage to the actual
dual-scheme equation `dualSchemeBaseChangeIso_comp_inv`. The forward equation
then cancels `k_DA.hom` with its inverse.

Writing `F_b`, `F_c`, `F_d` for the corresponding integral
`dualAbelianBaseChangeMap` operations,
`dualAbelianBaseChangeMap_comp` proves

```
k.hom ≫ F_c(F_b(lam)) = F_d(lam) ≫ kD.inv.
```

It expands actual functorial pullback, applies naturality of
`baseChangeCompNatIso` and uses the forward dual comparison equation.
`dualAbelianBaseChangeMap_comp_inv` precomposes with `k.inv` to obtain
`F_c(F_b(lam)) = k.inv ≫ F_d(lam) ≫ kD.inv`.
`dualAbelianBaseChangeMap_comp_pullback` instead postcomposes the first
equation with `kD.hom` to recover `F_d(lam)`.

The rational theorems `rationalDualBaseChangeHom_comp` and
`rationalDualBaseChangeHom_comp_inv` state the corresponding equations:

```
⟦k.hom⟧ ; F_c(F_b(lam)) = F_d(lam) ; ⟦kD.inv⟧,

F_c(F_b(lam)) = ⟦k.inv⟧ ; (F_d(lam) ; ⟦kD.inv⟧).
```

Each proof uses tensor-product induction, the integral equation on pure
tensors and linearity on sums.

Finally, `rationalDualBaseChangeHom_comp_multiple` proves the actual geometric
multiplier equation

```
(⟦k.hom⟧ ; F_c(F_b(lam))) ; dualHom0(⟦k.hom⟧) =
  1 • F_d(lam).
```

This is `IsRationalDualPullbackMultiple` for multiplier `1`, source map
`⟦k.hom⟧`, source dual-valued map `F_d(lam)` and target dual-valued map
`F_c(F_b(lam))`. The theorem takes `DualSchemeMapAdditivity` for `A_d, A_c`.
It identifies the actual rational dual of the integral comparison with
`⟦kD.hom⟧`, substitutes the rational composition equation and cancels
`kD.inv ≫ kD.hom`.

## Provenance and scope

This is internal algebraic compatibility of existing constructions, rather
than a translation of a new literature theorem. Its imports are
`DualBaseChangeCoherence` and `RationalDualPullbackBaseChange`; the underlying
inputs include the actual dual-homomorphism construction, the abelian-scheme
identity/composition comparisons, canonical dual comparison lifts, rational
Hom groups and the existing geometric dual-pullback predicate. The proof
routes above explain the derived provenance.

The multiplier laws concern the actual constructed rational dual and every
rational dual-valued map; the map need not satisfy a polarization predicate.
They supply the geometric equation required when the maps are polarizations.
This module does not identify the separately chosen evaluation data, prove
dual existence, or establish preservation of the entire polarization
predicate. It does not yet descend these equations to a polarized moduli
quotient, construct Harris PEL representability or scheme levels, or perform
coefficient descent. These remain further obligations of the host task.
