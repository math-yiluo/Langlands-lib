# Induction in stages for actual induced topological spaces

The namespace is `Langlands.TopologicalInduction`. All new code and prose in
this pair are by Worker 56. The module uses the published balanced quotient
and its equivariant extension from `InducedSpace`, retaining their actual
carriers, group actions and quotient topologies.

## Original action and iterated quotient

Let `G : Type u` be a group, let `H J : Subgroup G`, and let `X : Type v`
have an `H`-action. The two universes are independent. The subgroup
`H.subgroupOf J` consists of elements of `J` whose underlying elements of
`G` lie in `H`. The homomorphism `stagesSubgroupHom H J` removes the extra
subtype layer and maps this group into `H`. The definition
`stagesAction H J X` composes the original action with this homomorphism.
It is selected as an instance only locally in this module; it installs no
competing global action. A consumer wishing to write inner quotient
representatives explicitly can select `letI := stagesAction H J X`.

The abbreviation `StagedSpace H J X` fixes that action in the iterated
balanced quotient

```text
G ×_J (J ×_(H.subgroupOf J) X).
```

Writing `[g,x]` for the published `mk H g x`, the balancing relation is
`[g*h,x] = [g,h • x]`. The outer action is the published left `G`-action,
and the inner action is the published left `J`-action.

## Constructed comparison and inverse

The function `stagesInner` extends `unit H : X → Space H X` across the
inner quotient, using the restricted `J`-action on its target. The subgroup
equivariance needed for the extension is precisely the existing
`unit_subgroup_smul` applied after `stagesSubgroupHom`. Its evaluation
`stagesInner_mk` sends `[j,x]` to `[j,x]`, now with the first coordinate in
`G`. Its `J`-equivariance is `stagesInner_smul`.

The function `stagesFlatten` extends `stagesInner` across the outer
quotient. Consequently

```text
stagesFlatten [g,[j,x]] = [g*(j:G),x].
```

This is `stagesFlatten_mk`; `stagesFlatten_smul` gives full `G`-equivariance.
These forward constructions work even without an inclusion hypothesis,
when the inner subgroup is the intersection viewed inside `J`.

Now assume `hHJ : H ≤ J`. The iterated unit
`x ↦ unit J (unit (H.subgroupOf J) x)` is `H`-equivariant: insert
`h : H` into `J` using `hHJ`, and apply the two unit-equivariance laws.
Extending this map gives `stagesInsert hHJ`, with evaluation

```text
stagesInsert hHJ [g,x] = [g,[1,x]].
```

The theorem `stagesInsert_smul` proves its `G`-equivariance. Quotient
induction reduces `stagesFlatten_insert` to the identity representative.
For the other inverse law, nested quotient induction reduces to
`[g*j,[1,x]] = [g,[j,x]]`; the outer balancing relation and the inner
action-on-unit formula prove this equality. Thus `stagesEquiv hHJ` is an
actual equivalence with these two constructed maps, rather than an
equivalence supplied as input. `stagesEquiv_double_unit` identifies the
iterated unit with the original unit, and `stagesEquiv_smul` records its
equivariance.

## Original topologies and homeomorphism

Suppose `G` is a topological group, `X` is a topological space, and its
original `H`-action is jointly continuous. All subgroups have their subspace
topologies. The map `stagesSubgroupHom` is continuous: its underlying
map to `G` is the composite of two continuous subtype inclusions, and
continuity into the subtype `H` follows. Precomposition of the original
joint action with this continuous homomorphism gives
`continuousSMul_stagesAction`. Like the action definition, this continuity
instance is selected only locally. The topology of `X` is unchanged.

The published induced spaces then carry their quotient topologies and
jointly continuous full group actions. The theorem `continuous_stagesInner`
uses continuity of the original unit and of quotient extension.
`continuous_stagesFlatten` applies continuous extension once more.
The composite of the two continuous units is continuous, so its extension
gives `continuous_stagesInsert`.

The selected definition `stagesHomeomorph hHJ` combines these results into

```text
StagedSpace H J X ≃ₜ Space H X.
```

Its forward and inverse values on representatives are
`stagesHomeomorph_mk` and `stagesHomeomorph_symm_mk`.
`stagesHomeomorph_double_unit` identifies the units, and
`stagesHomeomorph_smul` proves `G`-equivariance. The construction permits
empty `X`, arbitrary nested subgroups, infinite index and non-Hausdorff
spaces. It needs no open-subgroup hypothesis.

## Provenance and scope

The source motivation is V. G. Berkovich's unfinished 1995–1996 manuscript
*Etale equivariant sheaves on p-adic analytic spaces*, Construction 1.1.2,
printed/PDF page 2, its final induction-in-stages sentence. The original
page was read directly. The retained source has literature ID
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder SHA256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`.
The member is
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
SHA256 `91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.

Berkovich's construction begins with an open subgroup and constructs an
induced analytic space from coset copies. Its final sentence gives the
canonical analytic induction-in-stages isomorphism for a subgroup chain.
This module internally derives the corresponding comparison for the actual
topological balanced quotients, with the explicit formula above, and proves
the stronger topological result for arbitrary nested subgroups. The proof
uses quotient extension and balancing, rather than assuming an analytic
comparison. Analytic atlases, analytic morphisms, the analytic
automorphism-group topology and equivariant site equivalences remain
separate construction obligations.
