# Finite étale covers and geometric fibre automorphisms

This module constructs the actual category of finite étale schemes over a scheme,
its point functor, and the automorphism group acting on those points. Finite-set
packaging and the resulting topology have an explicit finiteness hypothesis.
No geometric Galois-category theorem is assumed or proved here.

## Source and scope

The source is Edixhoven, van der Geer and Moonen, *Abelian Varieties*, preliminary
version, Chapter X §3, Definition (10.25) and Definition (10.26), printed p.150
(PDF p.154). The registered source is
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
Definition (10.25) specifies the full subcategory of finite étale morphisms and
the set of geometric points over the chosen base point. Definition (10.26)
defines the fundamental group as automorphisms of that functor, for a connected
locally noetherian base.

The Lean constructions are defined for an arbitrary scheme `S : Scheme.{u}`,
field `Ω : Type u`, and morphism `s : Spec Ω ⟶ S`. For the source's geometric
interpretation, specialize to an algebraically closed `Ω`; for the source's
fundamental-group setting, further specialize to connected locally noetherian
`S`. These hypotheses are unnecessary for the definitions and elementary laws
implemented here, so they are not imposed by this module. The naming outside
those hypotheses is a formal extension of the same automorphism construction,
not an assertion of the source's classification theorem in greater generality.

The pullback equivalence, finite packaging, action laws and topology are derived
constructions. The topology and its properties reuse the pinned Mathlib modules
`CategoryTheory.Galois.Action` and `CategoryTheory.Galois.Topology`. Their results
used here apply to any functor to finite sets, without `GaloisCategory` or
`FiberFunctor` assumptions. Theorem (10.28), printed p.151 (PDF p.155), provides
context for the eventual geometric equivalence, but that equivalence is not
established in this definition module.

## Actual covers and point sets

All declarations are in `Langlands.AlgebraicGeometry.FiniteEtale`.

- `coverProperty S` is the predicate `IsFinite Y.hom ∧ Etale Y.hom` on `Over S`.
  `Cover S` is its full subcategory; it is not a supplied abstract category.
  `inclusion S` is the full-subcategory inclusion, and `cover f` bundles a
  morphism with these two properties. A bundled cover supplies both morphism
  properties as instances. Morphisms of covers are all morphisms over `S`.
- `Fiber s Y` is the type of morphisms `Over.mk s ⟶ Y.obj`. Its elements are
  morphisms `x : Spec Ω ⟶ Y` satisfying `x ≫ Y.obj.hom = s`.
  `pointFunctor s` is the restriction of this covariant representable functor to
  `Cover S`. Its maps are postcomposition, as recorded by `pointFunctor_map`.
- `fiberScheme s Y` is the scheme-theoretic pullback of `Y.obj.hom` along `s`.
  `FiberPoints s Y` consists of morphisms over `Spec Ω` from its identity object
  to this pullback with structural map `pullback.snd`.
  `fiberEquivPoints s Y` sends a lift `x` to `pullback.lift x.left (𝟙 _)` and
  recovers `x` by the first projection. The inverse laws use the pullback
  projection identities, the slice commutation equation, and uniqueness in the
  pullback. `fiberEquivPoints_fst` records the first projection explicitly.

Thus the fibres are actual scheme morphisms, and their alternative description
as Ω-points of the scheme-theoretic fibre is constructed, not supplied as data.

## Finite packaging and automorphisms

The remaining constructions take

```lean
hfin : ∀ Y : Cover S, Finite (Fiber s Y)
```

as an explicit theorem hypothesis. This module does not prove it, even when
`Ω` is algebraically closed. `fiberFunctor s hfin` lifts `pointFunctor s` to
`FintypeCat`; the underlying sets and maps remain the actual geometric lifts
and postcomposition. `fiberFunctor_comp_incl` identifies the forgotten functor
with `pointFunctor s` by definitional equality.

`FundamentalGroup s hfin` is `Aut (fiberFunctor s hfin)`, the group of natural
automorphisms of this particular functor. `fundamentalGroupEquiv` is a group
isomorphism to `Aut (pointFunctor s)` obtained from the fully faithful inclusion
of finite sets into types. It establishes that finite packaging does not
replace the automorphism group by arbitrary data. No topological assertion
about the type-valued automorphism group is made by this isomorphism.

`evaluation s hfin Y` evaluates a natural automorphism at a cover, giving a
group homomorphism to `Aut ((fiberFunctor s hfin).obj Y)`. `fiberMulAction` is
the resulting action on `Fiber s Y`; `smul_eq` identifies it with
`g.hom.app Y x`. For each cover morphism `f : Y ⟶ Z`, `smul_naturality` proves

```lean
g • (x ≫ f.hom) = (g • x) ≫ f.hom
```

using Mathlib's naturality law for evaluation. The `MulAction` instance contains
the identity and multiplication laws. `actionFunctor` packages these finite
actions, and `actionFunctor_comp_forget` proves that its underlying finite-set
functor is exactly `fiberFunctor`.

## Evaluation topology and continuity

`fiberTopology` gives every `Fiber s Y` the discrete topology. Mathlib equips the
automorphism group with the topology induced by

```lean
PreGaloisCategory.autEmbedding (fiberFunctor s hfin)
```

into the product over all covers of their finite fibre automorphism groups,
each with discrete topology. `fundamentalGroup_topology` identifies the chosen
topology by definitional equality. Evaluation on a whole finite fibre gives the
same pointwise evaluation topology as its individual points: there are only
finitely many such points. The Lean declaration identifies the product of
finite automorphism groups; it does not separately formalize this description
by individual stabilizers as a neighbourhood basis.

`fiberContinuousSMul` reuses Mathlib's proof that the evaluation action is
jointly continuous. `continuous_evaluation` deduces continuity of evaluation at
a fixed fibre point. `continuousActionFunctor` lifts `actionFunctor` to
`ContAction FintypeCat (FundamentalGroup s hfin)`, using the discrete topology
on finite sets from the scope `FintypeCatDiscrete`.
`continuousActionFunctor_comp_inclusion` proves that forgetting continuity gives
exactly `actionFunctor`.

The final four declarations, `fundamentalGroup_compact`,
`fundamentalGroup_t2`, `fundamentalGroup_totallyDisconnected`, and
`fundamentalGroup_isTopologicalGroup`, reuse Mathlib's instances for the
automorphism group of any finite-set-valued functor. Mathlib realizes compatible
families as a closed subgroup of the product of finite discrete automorphism
groups. These are proved properties conditional on `hfin`, not an invocation
of an unproved geometric Galois-category assertion. In particular, the module
provides compact Hausdorff totally disconnected topological group structure
under precisely that hypothesis; it does not construct an inverse-limit
presentation or state that this group classifies covers.

## Published geometric targets and remaining obligations

The companion module `Langlands.AlgebraicGeometry.FiniteEtale.Statements`
defines three exact `Prop`-valued targets, all with `IsAlgClosed Ω`:

- `GeometricFiberFinite s` asserts `∀ Y : Cover S, Finite (Fiber s Y)`, without
  assuming `hfin`, connectedness or local noetherianity of `S`. The published
  theorem `geometricFiberFinite` in
  `Langlands.AlgebraicGeometry.FiniteEtale.GeometricFiberFiniteProof` proves
  this exact target. Its internal proof uses finite base change, finiteness of
  sections of a finite morphism to a field's spectrum, and `fiberEquivPoints`;
  it does not use a geometric classification theorem.
- `GeometricGaloisFiberFunctor s hfin` additionally assumes `ConnectedSpace S`
  and `IsLocallyNoetherian S`, and retains
  `hfin : ∀ Y : Cover S, Finite (Fiber s Y)` as an explicit parameter. It asserts
  existence of `hG : GaloisCategory (Cover S)` for which the actual
  `fiberFunctor s hfin` satisfies `PreGaloisCategory.FiberFunctor`.
- `GeometricContinuousActionEquivalence s hfin` retains the same hypotheses
  and explicit `hfin` as the preceding target. It asserts exactly
  `(continuousActionFunctor s hfin).IsEquivalence`, for the existing functor
  with its evaluation actions and topology.

The last two targets remain separate proof obligations. The finiteness theorem
can supply `hfin` under its stated hypotheses, but this definition module does
not import its proof module and keeps `hfin` explicit throughout the finite
packaging and topological constructions. It supplies no unconditional geometric
Galois classification and installs no instances for the remaining geometric
claims. Base-point transport, torsion schemes, Tate limits and sheaf cohomology
are outside this module's scope.
