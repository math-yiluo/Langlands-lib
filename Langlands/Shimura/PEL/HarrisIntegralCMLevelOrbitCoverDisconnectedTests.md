# Original Harris orbit-cover levels on disconnected tests

This is an internal construction from the published connected-test orbit-cover
correspondence and the reconstruction of a locally Noetherian scheme from its
actual open connected components. It introduces no external literature assertion.
All declarations are in
`Langlands.Shimura.PEL.HarrisPolarizedWeilLevel`.

## Actual component maps over the base

For a locally Noetherian scheme `X.left` over `S`,
`harrisIntegralCMComponentTest X c` is the actual open component scheme
`componentScheme X.left c`, with structural map `componentι X.left c ≫ X.hom`.
`harrisIntegralCMComponentTestInclusion` is its actual inclusion over `S`.
For `f : X ⟶ T` and `Y : Over T.left`,
`harrisIntegralCMComponentHomEquiv` gives

```text
(Over.mk f.left ⟶ Y) ≃
  ∀ c, (Over.mk ((componentInclusion c ≫ f).left) ⟶ Y).
```

The forward map restricts an actual scheme morphism along the component
inclusion. The inverse glues the underlying component maps with the existing
`componentDesc`. The triangle over `T.left` follows by component extensionality
and the component triangles. The two inverse laws are
`componentDesc_restrict` and `componentι_componentDesc`, applied to underlying
scheme maps. The `_apply` and `_symm_left` lemmas expose these operations.
There is no finiteness or nonemptiness assumption on the component index.

## Harris data and supplied points

The arithmetic and scheme carriers have universe zero. Retain the actual number
fields, the totally real and CM conditions, the quadratic extension and scalar
towers, the central simple unitary datum `D`, the auxiliary imaginary quadratic
field, the chosen complex embedding, and the normalized signature charts `C`.
Retain an actual abelian scheme `B` over `S`, a `DualWitness W`, a dual-valued
homomorphism `lam`, and the named tensor, Picard, duality and polarization
prerequisites in `P`. The construction uses the original integral action `a`
on the family over `T`, the finite Weil transition statement `compatibility`,
and the rational adelic comparison `h`.

The base `T.left` is connected, locally Noetherian and quasi-separated. The
point `s` has values in an algebraically closed field `Ω`. As in the existing
orbit-cover construction, assume the finite-fibre witness `hs`, the torsion
finite-etale statement `htor`, invertibility `hu` of all indicated orders,
and finiteness and etaleness of the roots-of-unity schemes over `T.left`.
The source `X.left` is an arbitrary locally Noetherian scheme and
`f : X ⟶ T` is arbitrary.

For each actual component `c`, the construction takes explicit data:

- A point `t c : Spec Ω ⟶ componentScheme X.left c` and the equation
  `t c ≫ (componentInclusion c ≫ f).left = s`.
- A finite-fibre witness `ht c` for that point, and invertibility `huC c`
  of the indicated orders on the component.
- Finiteness and etaleness of the roots-of-unity schemes on each component.

The local connectedness, local Noetherianity and quasi-separatedness instances
come from the actual component schemes. The component integral action is
literally `(relativeEndRestrict B (componentInclusion c ≫ f)).comp a` on the
original family over that component. Its tower and its raw restriction
evaluation are the existing `harrisIntegralCMFullActionLevelTower` and
`harrisIntegralCMRestrictionRawClass` for these data.

## The disconnected-test equivalence

Write `Gamma = FundamentalGroup s hs`. Use the actual rational Tate monodromy
on the base Weil-compatible frames, the original opposite source-similitude
right action, and the proved commuting-action instance. Fix a Harris reference
level `U` with a nonempty original direct-level set, a Harris level `V`, and
a raw base right-orbit class `q` at `V`. Let `Y_q` be the existing finite orbit
cover associated to these data. Then
`harrisIntegralCMFiniteOrbitCoverDisconnectedTestLevelEquiv` gives

```text
(Over.mk f.left ⟶ Y_q.obj) ≃
  ∀ c, {l : original direct tower on component c at V //
    original raw evaluation of l belongs to Gamma-orbit(q)}.
```

It composes the actual component Hom equivalence with the product of the
existing `harrisIntegralCMFiniteOrbitCoverTestLevelEquiv` on the components.
Thus the bijection uses the original direct levels and original evaluation.
The `_component` theorem identifies each value with the connected-test
correspondence applied to the restricted scheme map. The `_symm_left` theorem
identifies the inverse's underlying scheme map with `componentDesc` applied
to the inverse connected correspondences.

The `_val` theorem gives its actual evaluation formula: the original raw
restriction value on component `c` is the existing geometric-fibre comparison
applied to the lift with underlying map `t c ≫ componentι X.left c ≫ k.left`.
The equation over the base is proved from `Over.w k` and the supplied point
equation. The theorem is the connected-test value formula applied to the actual
restricted morphism.

## Original level transitions

For an original level arrow `j : V ⟶ Z`, raw classes `q` and `r`, and the
compatibility equation `translate j q = r`,
`harrisIntegralCMDisconnectedTestLevelOrbitMap` applies the existing
`harrisIntegralCMTestLevelOrbitMap` independently on each component.
Its `_val` theorem states that the underlying component value is literally
the original direct tower map applied to that component's level. The map is
defined before the naturality theorem using these original operations.

`harrisIntegralCMFiniteOrbitCoverDisconnectedTestLevelEquiv_natural` says that
this product map carries the image of `k` to the image of `k` postcomposed
with the actual orbit-cover transporter. Function extensionality reduces it
to the published connected-test naturality square, with scheme-map
associativity identifying restriction followed by postcomposition.

## Scope

The component point family over the same algebraically closed field and its
equations over the single base point `s` are explicit inputs. This file does
not construct that family or compare arbitrary geometric points. The component
index may be empty or infinite, provided the displayed data are supplied.
No finite or etale assumption on `f` is used.

This is a correspondence for the already constructed orbit cover over a supplied
abelian family. General geometric-point independence, the determinant/Lie and
Rosati conditions, the normalized rational-isogeny moduli comparison, and the
existence, admissibility, smoothness and division-case projectivity of a
representing PEL scheme remain separate obligations of the unchanged host
`DivisionCMRepresentabilityStatement`.
