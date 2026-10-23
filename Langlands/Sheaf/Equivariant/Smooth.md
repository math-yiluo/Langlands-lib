# Smooth equivariant sheaves

Author: Worker 13. Built on the published transport category
`Langlands.Sheaf.Equivariant.ActionOpens`, the equivariant sheaf category and
subgroup actions of `Langlands.Sheaf.Equivariant.Topological`, and the limit
results of `Langlands.Sheaf.Equivariant.Limits`.

Let `R` be a commutative ring, `G` a group with a topology, and `X` a
topological space with an action of `G`. The space `X`, `R` and the module
carriers lie in one universe `u`. Sections are taken in an equivariant module
sheaf `F`, an object of `TopologicalSheaf G X (ModuleCat R)`. For a subgroup
`H` and an open `V` stable under `H`, the published `invariantArrow` arrows
make `H` act on the sections over `V`.

## Definitions

`IsLocallyFixedAt R F s x` says the following about a section `s` of the
transport presheaf `F` over `U` and a point `x`. There are an open `V` with
`x ∈ V ⊆ U` and an open subgroup `H` of `G` with `h • V ⊆ V` for all
`h ∈ H`, such that every `h ∈ H` fixes the restriction of `s` to `V` under
this action.

`IsSmoothSheaf R G X F` says that every section of `F` over every open is
locally fixed in this sense at every point of that open.
`smoothSheafProperty R G X` is this property as an `ObjectProperty`.
`SmoothTopologicalSheaf R G X` is the full subcategory it defines, and
`smoothInclusion R G X` is its inclusion functor.

## Basic results

`isSmoothSheaf_of_discreteTopology` proves that every equivariant module
sheaf is smooth when `G` is discrete: the trivial subgroup is open, stabilizes
every open and fixes every section.

`IsSmoothSheaf.of_mono` proves that the source of a monomorphism into a smooth
sheaf is smooth. Evaluation on an open preserves finite limits, hence
monomorphisms, so the morphism is injective on sections. The morphism commutes
with restriction and with the subgroup action, so a subgroup fixing the image
of a restricted section also fixes the section itself.

## Provenance and scope

Berkovich, *Etale equivariant sheaves on p-adic analytic spaces* (unfinished
1995–1996 manuscript), section 1.4, Definition 1.4.1, printed pp.7–8, defines
a G-sheaf, for a topological group `G` acting on an analytic space, as a
sheaf for the discrete group whose sections over compact quasi-étale `U` form
discrete `G_U`-modules. The remark after the definition, printed p.8,
characterizes these sheaves: for every section `f` over an étale `U → X`, each
point of `U` has a distinguished open neighbourhood `U'` on which the
stabilizer of `f|U'` is open in `G_{U'}`. Harris, *Galois properties of
cohomological automorphic forms on GL(n)* (1999), section 2, printed p.304,
uses such sheaves of smooth `S(ẽ)`-modules, which Berkovich calls discrete.
Worker 13 read these passages in the original.

`IsSmoothSheaf` transcribes Berkovich's characterization to the published
ordinary-topological transport site. Here an open subgroup stabilizing a
neighbourhood replaces the open subgroup `G_{U'}` that Berkovich's Key Lemma
provides on analytic spaces. The definition therefore also requires that such
stabilized neighbourhoods exist. If there exists a point `x ∈ U` with no
open neighbourhood `V ⊆ U` stabilized by an open subgroup, then no section
over `U` satisfies the condition at `x`, not even zero. On the empty open,
the condition holds vacuously for every section. No continuity of the action,
no analytic étale site and no smoothness of cohomology are asserted. Statements
that cohomology of smooth sheaves carries smooth or discrete actions remain
separate obligations.

Source registrations:
Berkovich,
`provided-7bb3903652336bd799aad8853b8efd7ff3bcc0c7652745417f4745a14ac08e90`,
folder SHA-256
`e046cadfb9dcec4b0cf6624f80d6316bf532416153b82023f5100bd1ab0726cd`;
member
`Berkovich--Etale equivariant sheaves on p-adic analytic spaces (unfinished manuscript)--1996.pdf`,
member SHA-256
`91567a75866a27cbe6690b6f075693df5afaa02524223d94d52ea37d77bb6637`.
Harris, `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

All imported modules are present in Library commit
`354dfade2c499262492d6db74cb58fd887ffed5f`.
