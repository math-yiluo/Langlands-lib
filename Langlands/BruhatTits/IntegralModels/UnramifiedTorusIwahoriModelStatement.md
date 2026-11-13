# Connected models of torus Iwahori subgroups

This is an unproved general torus prerequisite for the neutral-point
equality in KP Theorem 8.3.13. It concerns arbitrary tori over the maximal
unramified extension of a nonarchimedean local field, independently of
any reductive ambient group, building, apartment or bounded subset.

## Sources

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`:

- Appendix B introduction, printed p. 653 / PDF p. 684, fixes a
  Henselian discrete valuation ring and its maximal unramified extension.
- Definition B.8.1 and Proposition B.8.4(3), printed pp. 680–682 /
  PDF pp. 711–713, construct the smooth connected Néron model `T⁰`.
  The proof on printed p. 682 explicitly gives its affineness.
- Corollary B.8.7 and its proof, printed p. 683 / PDF p. 714, identify
  `T⁰(o)` with the Iwahori subgroup `T(k)⁰`. Over the strictly Henselian
  field `K`, the proof uses the norm from a finite Galois splitting
  field, exactly as in the subgroup below.

The registered corrections `kaletha-prasad-2024-corrections`
(1 November 2024), SHA-256
`23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`,
PDF pp. 49–50, have no amendment to these Appendix B results. The
Appendix B corrections concern Section B.10.

## Exact statement

`UnramifiedTorusIwahoriModelStatement.{u}` quantifies over every
nonarchimedean local field `F : Type u`. Write

```text
K = inertiaFixedField F
O = fixedFieldIntegers F.
```

These are the Library's actual maximal unramified subfield of
`SeparableClosure F` and its valuation ring. The statement does not
require `K` or `O` to be complete.

The input `T` is an actual affine commutative group scheme over `Spec K`.
The input `L` is an actual intermediate field of `SeparableClosure F/K`,
finite Galois over `K`, together with the assertion that `T_L` is a split
torus. This last assertion implies that `T` is a torus by the Library
definition of `IsTorus`; no additional torus hypothesis is necessary.
The torus need not be split over `K`.

The conclusion supplies an actual

```text
M : IntegralModel O K T.toGrp
```

with `M.IsSmooth` and `M.HasGeometricallyConnectedFibres`. The existing
`IntegralModel` structure includes an affine, flat, locally finite type
group scheme over `O` and a specified group-scheme isomorphism from its
generic fibre to `T.toGrp`. Affineness makes this model quasi-compact,
and smoothness therefore makes it of finite type.

Geometric connectedness concerns every fibre of the structural
morphism. It expresses the connected-fibre property of the source's
smooth group model in a form usable by the relative-component
factorization API. For a smooth group over a field, connectedness is
geometric connectedness: its identity section belongs to the identity
geometric component, which descends to the identity component over the
ground field. Thus this formulation does not require the model to be a
torus over `O`; a ramified torus can have a unipotent part in its special
fibre.

The equality is between subgroups of the existing rational-point group
`rationalPoints T.toGrp`:

```text
M.integralPoints =
  torusNormIwahori K L (intermediateValuation F L) T.
```

The left side is the literal image of integral sections under the
generic-fibre identification belonging to `M`. The right side is the
image, under the actual rational norm `T(L) → T(K)`, of the common
kernel of all character valuations on the split torus `T_L`.
`intermediateValuation F L` restricts the chosen valuation on the
separable closure to `L`. This is KP's subgroup `T(K)⁰`, rather than the
usually larger maximal bounded subgroup `T(K)¹`.

All coefficient fields, rings and schemes retain arbitrary universe
`u`. The conclusion is asserted for every supplied finite Galois
splitting field `L`. Its formulation leaves the choice of model inside
that quantifier; it does not assert simultaneous choices or uniqueness.

## Remaining construction

The Lean file defines the target proposition and proves no existence
theorem. The source constructs `T⁰` as the relative identity component
of the finite-type Néron model and identifies its sections using norm
surjectivity on connected torus models. Neither a Néron mapping
property nor a finite-type or locally finite type Néron model is part of
the present interface.

Applying this general existence statement to the torus used in
Theorem 8.3.13 still requires the ambient torus map, its extension to the
ambient integral model, the root models, the generated-subgroup
identification, openness, finite index and the connected-generation
argument. Those KP-specific obligations remain in the parent task.
