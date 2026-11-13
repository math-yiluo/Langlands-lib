# The compact induction of a norm-kernel summand lies in the inertia block

Author: Worker 5104.

Supporting module for the proof of Renard VI.4.5, Corollary
(`Langlands.CuspidalSupport.rationalInertiaBlockIndecomposable`). It is also the
membership part of the VI.4.1 and VI.4.5 statements and may be reused by their
proofs.

## Statement

`Langlands.CuspidalSupport.rationalSummandInduction_mem_block G hG π hπ ρ hρ j hj`.
Let `F` be a nonarchimedean local field, `G` a connected reductive group scheme
over `F` (`hG`) and `H = G(F)` with its canonical topology. Let `π` be an
irreducible smooth complex representation of `H` with carrier in `Type uV`, and
`ρ` an irreducible smooth representation of the common norm kernel
`H⁰ = rationalCommonNormKernel G` (Renard's `⁰G`) with an injective
`H⁰`-intertwiner `j : ρ → π|_{H⁰}` (`SmoothRep.restrictSubgroup`). Then the
compact induction `Π = c-Ind_{H⁰}^H ρ`, the published
`(compactInductionFunctor H⁰).obj (SmoothRep.toRep.obj ρ)`, satisfies
`rationalInertiaBlockProperty G (rationalInertiaBaseLift G π)`: every irreducible
subquotient of `Π` is an unramified twist of `π` (lifted to the carrier universe
`max uF uV` by `rationalInertiaBaseLift`). In other words `Π` is an object of the
inertia block `RationalInertiaBlock G (rationalInertiaBaseLift G π)`, Renard's
`M(G)[π]`.

The hypotheses are exactly those on `ρ` and `j` in the published VI.4.1
statements; no cuspidality of `π` and no compactness, admissibility or
finiteness is assumed. The instances on `G` (affine, locally of finite type) and
the topology on `H` are fixed as in the published statements of VI.3.2.

## Provenance

Renard (*Représentations des groupes réductifs p-adiques*, VI.4.1, Proposition,
printed p.149 / PDF p.155, registered source
`renard-2026-representations-groupes-reductifs-padiques`) states that
`Π = ind_{⁰G}^G ρ` is a small progenerator of `M(G)[π]`; that `Π` is an object of
`M(G)[π]` is used there without a separate argument. This module proves that
membership, by its own route described below. It is an internal lemma.

## Proof

Let `D` be an irreducible subquotient of `Π`. By the published
`SmoothRep.isSubquotient_iff_exists` it is given by an injective
`G`-intertwiner `i : B → Π` and a surjective one `q : B → D`. Being irreducible,
`D` is a simple module over the group algebra, hence nontrivial
(`IsSimpleModule.nontrivial`); pick `d ≠ 0`.

Compose `j` with the published `Induction.restrictAlongEquiv` of the equivalence
`SmoothRep.universeLiftEquiv π` to get an injective `H⁰`-intertwiner
`j' : ρ → (rationalInertiaBaseLift G π)|_{H⁰}`. The common norm kernel is open
(`isOpen_rationalCommonNormKernel`) and normal, so the supporting lemma
`Induction.exists_restricted_intertwiningMap_ne_zero_of_subquotient` (module
`Langlands.Representation.Induction.OpenNormalRestrictionSemisimple`, based on
the semisimplicity of `Π|_{H⁰}`) gives a nonzero `H⁰`-intertwiner
`φ : D|_{H⁰} → (rationalInertiaBaseLift G π)|_{H⁰}`.

The lift of `π` is irreducible (`SmoothRep.isIrreducible_universeLift_iff`). The
published Renard VI.3.2(iii), `rationalNormKernelTwistEquivalence`, applied to
`D` and the lift of `π`, first turns the nonzero `φ` into an equivalence of the
restrictions to `H⁰` (its second part) and then into an unramified character `χ`
with `D ⊗ χ ≅ π` (its first part). The isomorphism `SmoothRep.mkIso` of this
equivalence, read backwards, and the symmetry `IsRationalInertiaRelated.symm`
give that `D` is inertia-related to the lift of `π`.
