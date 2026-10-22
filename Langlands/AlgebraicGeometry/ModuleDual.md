# Internal Hom and duals of scheme modules

For an arbitrary `AlgebraicGeometry.Scheme.{u}` S and actual Mathlib module sheaves
M, N in `S.Modules`, this module constructs
`Langlands.Scheme.Modules.internalHom M N : S.Modules`. It uses no finiteness,
quasicoherence, smoothness, or local-freeness hypothesis. All names below are in
`Langlands.Scheme.Modules`, unless qualified otherwise.

The geometric definition follows the opening of the Stacks Project, Section 17.22,
[Internal Hom, tag 01CM](https://stacks.math.columbia.edu/tag/01CM). The registered
source is `stacks-relative-differentials-internal-hom-2026-10-21`, folder content
SHA256 `9c075370ba97d8876785c5486425c6c661765e747452c026583f4dc51f1e1133`, file
`01CM.html` in the HTML snapshot retrieved 2026-10-21. The opening defines sections
as maps of restricted module sheaves and defines scalar multiplication by the
restricted regular function on every smaller open. The dual and its functorial
laws here are derived from that construction and composition of module-sheaf
morphisms. The implementation of descent uses Mathlib's additive sheaf-Hom and
subsheaf results, as described below.

## Sections and their module structure

`LocalHom M N U` is the actual morphism type `M.over U ⟶ N.over U` in
`SheafOfModules (S.ringCatSheaf.over U)`. Its elements specify linear maps on all
opens contained in U, compatible with every restriction. This is not just the
module of linear maps from M(U) to N(U).

`LocalHom.app f i`, for an inclusion i : V → U, evaluates that local morphism on
V. `LocalHom.restrict i` restricts its whole family to V. The identity and
composition laws are `LocalHom.restrict_id` and `LocalHom.restrict_comp`.
The `LocalHom` namespace supplies a module over O_S(U):

```
LocalHom.app (r • f) i x = S.presheaf.map i.op r • LocalHom.app f i x.
```

Commutativity of O_S(V) makes each new component linear. Naturality follows from
semilinearity of the target's restrictions and functoriality of ring restriction.
The module axioms hold on every component. `LocalHom.restrict_smul` proves that
restriction is semilinear along O_S(U) → O_S(V). These constructions define
`internalHomPresheaf` as an actual presheaf of modules.

## Descent and identification on open subschemes

`linearHomSubfunctor` is the subpresheaf of Mathlib's
`presheafHom M.presheaf N.presheaf` consisting of additive local maps whose every
component is linear over its own ring of regular functions. `localHomEquiv`
identifies these sections with `LocalHom`, and `internalHomTypeIso` packages the
identification as an isomorphism of presheaves of types.

`linearHomSubfunctor_isSheaf` proves the sheaf condition. The ambient additive
local Hom is a sheaf by `Presheaf.IsSheaf.hom`, since N is a sheaf. The proof then
uses `Subfunctor.isSheaf_iff`: if a local additive map is linear on a covering
sieve, pull that sieve back to any smaller open V. Naturality and semilinear
restriction show that its value on r x and r times its value on x agree after
restriction to every member of this pulled-back cover. Separatedness of N makes
them equal on V. Thus linearity is local. The type-presheaf isomorphism and the
limit-reflecting forgetful functor from abelian groups give the required sheaf
condition for `internalHom`. No sheafification is used.

`internalHomOverEquiv M N U` is a linear equivalence from the section module to
`LocalHom M N U`. `internalHomSectionsEquiv M N U` gives the equivalence

```
Γ(internalHom M N, U) ≃ (M.restrict U.ι ⟶ N.restrict U.ι).
```

It uses Mathlib's `Scheme.Modules.overEquiv U` and `overFunctorEquiv U` to pass
from the over-category to the actual open subscheme. Its `_app` lemma identifies
evaluation on an open of that subscheme with evaluation of the same local map on
its image in S. The `_zero` and `_add` lemmas prove additivity. The
`_restrict_app` lemma gives the formula after restricting from U to V and then
evaluating on any open of V. `internalHom_restrict` also gives the restriction
formula directly in `LocalHom` form.

## Evaluation and dualization

`internalHomEval M N U` is the bilinear evaluation on U, bundled as a linear map
from the internal-Hom section module to the linear maps M(U) → N(U).
`internalHomEval_restrict` proves compatibility with restricting both arguments.
`internalHomMap f g` acts by precomposition with f and postcomposition with g.
Its `_app` and `_eval` lemmas give these formulas, and
`internalHomSectionsEquiv_naturality` proves that the open-subscheme section
identification respects both module arguments.

The existing `Langlands.SchemeModule.structureModule S` from
[SectionLocus](Modules/SectionLocus.md) is Mathlib's
`SheafOfModules.unit S.ringCatSheaf`, the actual structure sheaf acting on itself.
The definition `dual M = internalHom M (Langlands.SchemeModule.structureModule S)`
therefore gives the sheaf dual.
For f : M → N, `dualMap f : dual N → dual M` precomposes each local functional
with the restriction of f. `dualMap_app` states this local formula.
`dualEval M U` is the bilinear pairing into O_S(U), and `dualMap_eval` states

```
dualEval M U ((dualMap f).app U h) x = dualEval N U h (f.app U x).
```

`dualMap_id`, `dualMap_comp`, `dualMap_zero`, and `dualMap_add` prove the identity,
contravariant composition, zero, and addition laws. They give
`dualFunctor S : S.Modulesᵒᵖ ⥤ S.Modules` with a `Functor.Additive` instance.
The proofs reduce to composition and addition of the actual local module maps.

This contribution provides the internal Hom, dual, and their section API. It
asserts no pullback base-change isomorphism, local-freeness or rank result,
tensor-Hom adjunction, or Lie-module construction. The cited section's later
base-change results are not used.
