# The integral torus in a full character-kernel centralizer component

This is derived infrastructure for the integral centralizer construction
preceding Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023),
Theorem 8.2.9, printed p. 293 / PDF p. 324, and its proof on printed
pp. 294–295 / PDF pp. 325–326. The registered source is
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The residue maximality argument also corresponds to the split-torus
specialization assertion in Proposition 8.2.1(1), printed pp. 286–287 /
PDF pp. 317–318. Its implementation reuses the published Henselian split-rank
theorem.

The module retains the full scheme-theoretic character kernel. It constructs
the integral torus map through the relative component, compares that map on
every field fibre with the canonical torus in the ordinary identity
component, and proves maximality under the stated ambient maximality
hypotheses. It does not prove the opposite-factor criterion or the host
depth-zero theorem. The dynamic root models, their intrinsic root-group
comparisons, the residue-radical comparison and Weyl lifting remain separate
obligations.

## Split tori over an arbitrary base

`IsSplitTorus.geometricallyConnected` states that a split torus over any
scheme has geometrically connected structure morphism. The geometric-fibre
criterion reduces this to connectedness after every field-valued base
change. Such a base change is still split, and the published
`IsSplitTorus.connectedSpace` supplies connectedness over the field.

## The integral torus factor

Fix a commutative domain `R`, its fraction field `K`, an integral model `M`
of a `K`-group `G`, a commutative `R`-group scheme `T`, a homomorphism
`i : T.toGrp ⟶ M.group`, a character `a`, and
`D : IntegralModel.KernelCentralizerData M i a`. This datum consists of an
actual smooth affine closed full kernel-centralizer representative `C`,
its inclusion `j`, and a smooth geometrically connected relative identity
component `H` with inclusion `h : H ⟶ C`. Existence from a split torus and
smooth ambient model is supplied by `KernelCentralizerData.ofSplit`.
The following results also apply to any datum satisfying those fields.

Given `hT : IsSplitTorus T.toGrp`, `D.torus hT` is a homomorphism
`T.toGrp ⟶ H`. The published all-test centralizer construction first factors
`i` through `C`. Geometric connectedness of the split torus then lets
`D.isRelativeComponent.exists_hom_lift` factor this homomorphism through
`H`. The chosen lift satisfies

```text
D.torus hT ≫ h = RelativeRoot.kernelCentralizerTorus i a j D.fullRepresents
D.torus hT ≫ (h ≫ j) = i.
```

These are `torus_comp_componentHom` and `torus_comp_ambient`. In particular,
the composite remains the original integral map.
`torus_isClosed` proves closedness in `H` when `i` is closed. It first
reflects closedness through the closed inclusion `j` and then through the
relative component's open inclusion `h`, using the published relative
component factorization lemma. It does not assume that `h` is closed over
`R`.

## Actual field fibres and their torus maps

Let `b : Spec k ⟶ Spec R` be any field-valued base point, and write `C_b`,
`H_b`, `h_b`, `j_b`, `T_b`, `i_b` and `a_b` for the actual base changes.
No residue-quotient or fraction-field hypothesis is imposed on `b`.

`D.fibreIso b` is an isomorphism

```text
H_b ≅ identityComponent C_b.
```

Arbitrary base change preserves the represented relative component of the
smooth group `C`. Its base-changed source remains geometrically connected,
and `IsRelativeIdentityComponent.identityComponentIso` identifies it with
the ordinary field identity component. `fibreIso_hom_comp` records that
the forward isomorphism followed by the ordinary component inclusion is
exactly `h_b`.

`fullFibreRepresents` applies the published full-kernel centralizer
base-change theorem: `j_b` represents the centralizer of the entire kernel
of `a_b` in the base-changed ambient group.
`torus_fibreIso` then states the equality of actual homomorphisms

```text
(D.torus hT)_b ≫ (D.fibreIso b).hom =
  RelativeRoot.kernelCentralizerIdentityTorus i_b (hT.baseChange b) a_b
    j_b (D.fullFibreRepresents b).
```

The proof cancels the ordinary component inclusion and the represented
full-centralizer inclusion. After both cancellations, the equality is the
base change of `torus_comp_ambient`. Thus the comparison respects the
specified ambient map.

## Maximality on field fibres and residue fibres

`torus_fibre_isMaximal` assumes that `i_b` is a maximal split torus of the
ambient field fibre. The published
`IsMaximalSplitTorus.kernelCentralizerIdentityTorus` gives maximality of
the canonical torus in `identityComponent C_b`. The proved torus equality
and invariance under the ambient isomorphism `D.fibreIso b` give maximality
of `(D.torus hT)_b` in `H_b`. This includes the generic fibre by taking
`b = Spec.algebraMap R K`.

`torus_residue_isMaximal` additionally assumes that `R` is Henselian, that
`k` is an `R`-algebra field with surjective `algebraMap R k`, that
`M.group` is smooth, that `G` is connected reductive, that `i` is closed,
and that its actual generic base change is maximal split. The published
`isMaximalSplitTorus_residue_of_generic` first proves maximality of `i_k`
in the ambient residue fibre. Applying `torus_fibre_isMaximal` gives
maximality in the actual component fibre `H_k`.

These constructions are uniform in the arbitrary universe `u`. They need
neither a primitive nor a nonzero character and do not assert that the
full centralizer is connected. Residue maximality does not require `R` to
be a DVR or its residue field to be perfect; the indicated Henselian,
smoothness, closedness, reductivity and generic maximality assumptions are
the ones used by the reused split-rank theorem.
