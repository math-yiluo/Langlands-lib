# Automorphisms of locally free rank-one sheaves are unique global units

`Langlands.AlgebraicGeometry.Picard.LineBundleAutomorphismScalarStatement`
(universe parameter `u`, module
`Langlands.AlgebraicGeometry.Picard.LineBundleAutomorphismScalarStatement`) is a
Prop-valued statement target. This file supplies no proof.

## The proposition

For every scheme `X : Scheme.{u}` and every module sheaf `M : X.Modules` that
is locally free of rank one (`IsLocallyFreeRankOne M`), and for every
automorphism `e : M ≅ M`, there is exactly one unit `r` of the ring
`Γ(X, ⊤)` of global regular functions such that

`e.hom = scalarHom (r : Γ(X, ⊤)) (𝟙 M)`.

In words, every automorphism of `M` is multiplication by a global unit, and
that unit is determined by the automorphism.

The quantifiers and the equality are as follows.

- `X` ranges over all schemes in universe `u`, and `M` over all sheaves of
  `O_X`-modules on `X`, subject only to `IsLocallyFreeRankOne M`.
- `e : M ≅ M` is an isomorphism in the category `X.Modules`: an `O_X`-linear
  sheaf morphism `e.hom : M ⟶ M` with a two-sided inverse `e.inv`. Only
  `e.hom` appears in the equality, and it determines `e.inv`.
- `∃! r : Γ(X, ⊤)ˣ` asserts existence and uniqueness of an element of the unit
  group `Γ(X, ⊤)ˣ`. Two units are equal exactly when their underlying global
  functions are equal, so this is uniqueness of the global function among
  units. The proposition requires the scalar to be a unit and says nothing
  about non-unit global functions.
- The equality `e.hom = scalarHom (r : Γ(X, ⊤)) (𝟙 M)` is an equality of
  actual morphisms of sheaves of modules, that is, of their components on
  every open set.

## Library objects

- `IsLocallyFreeRankOne M` (from `Langlands.AlgebraicGeometry.Picard.LineBundle`)
  says that every point `x : X` has an open neighbourhood `U` such that the
  restriction `M.restrict U.ι` is isomorphic to the structure sheaf
  `SheafOfModules.unit U.toScheme.ringCatSheaf` of `U`. It is the property
  defining the Library's `LineBundle X`, but the proposition is stated for the
  bare module sheaf `M`.
- `Langlands.Scheme.Modules.scalarHom r f` (from
  `Langlands.AlgebraicGeometry.ModuleLinear`) multiplies a sheaf morphism `f`
  by the global function `r`. On each open `U` it sends a section `x` of `M`
  over `U` to `restrictScalar U r • f.app U x`, where `restrictScalar U r` is
  the restriction of `r` to `U` (lemma `scalarHom_app`, which holds by `rfl`).
  With `f = 𝟙 M` it is multiplication by `r` on all sections. The same module
  defines the action `r • f` of `Γ(X, ⊤)` on morphisms by `scalarHom`, so
  `scalarHom r (𝟙 M)` is `r • 𝟙 M`.
- `Γ(X, ⊤)` is Mathlib's notation for the ring of sections of the structure
  sheaf over the whole scheme, and `(r : Γ(X, ⊤))` is the coercion of a unit to
  that ring.

## Scope

The scheme is arbitrary. No quasi-compactness, quasi-separatedness,
separatedness, noetherianity, reducedness, finiteness, field or base
hypothesis appears, and there is no hypothesis on `Γ(X, ⊤)`. The module sheaf
is not assumed quasi-coherent; only the existing local triviality predicate is
assumed. The trivializations are not given as data.

The empty scheme is included. There `IsLocallyFreeRankOne M` holds vacuously
for every module sheaf, `Γ(X, ⊤)` is the zero ring, and its unit group has
exactly one element.

The rank-one hypothesis is needed for both halves. For uniqueness, take a
nonempty scheme with a unit `r ≠ 1` in `Γ(X, ⊤)`, such as `Spec ℚ` with
`r = 2`, and the zero module sheaf `M = 0`. Every unit then induces the zero
morphism, which equals `e.hom` for the identity automorphism, so the unit is
not unique; `IsLocallyFreeRankOne` excludes `M = 0` on nonempty schemes. For
existence, the free module sheaf of rank two on `Spec ℚ` has automorphisms
that swap the two basis sections, and these are not scalar.

## What is not asserted

The proposition does not state that `e ↦ r` is a group isomorphism
`Aut M ≃* Γ(X, ⊤)ˣ`, although that follows from the uniqueness. It makes no
claim about non-invertible endomorphisms, about morphisms between two
different module sheaves, about rigidifications along a section, or about any
relative situation over a base. It does not construct the unit or assert any
formula for it.

## Source correspondence

This is a derived general lemma. It is not a separately numbered theorem of
the source, and the source does not prove it. The source is Edixhoven, van der
Geer and Moonen, *Abelian Varieties*, preliminary draft, registered as
`edixhoven-vandergeer-moonen-abelian-varieties-draft` (SHA-256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`), Chapter VI
§1, paragraph (6.2), printed page 88 (PDF page 92). Paragraph (6.2) assumes
conditions (∗): the structure morphism `f : X → S` is quasi-compact and
quasi-separated, `f_*(O_{X ×_S T}) = O_T` for all `S`-schemes `T`, and `f` has
a section `ε`. It then defines homomorphisms of rigidified line bundles and
says:

> In particular, an endomorphism of (L, α) is given by an element
> h ∈ Γ(X_T, O_{X_T}) = Γ(T, f_*(O_{X_T})) with ε*(h) = 1. By the assumption
> that f_*(O_{X_T}) = O_T we therefore find that rigidified line bundles on
> X_T have no nontrivial automorphisms.

The first sentence uses, without proof, the general fact that an
endomorphism of a line bundle `L` on the scheme `X_T` is multiplication by a
global function on `X_T`. This proposition states the automorphism case of
that fact for an arbitrary scheme, with the scalar a unit and unique. The
conditions (∗) and the rigidification `α` are used in the source only to pass
from this scalar description to rigidity (via `ε*(h) = 1` and
`f_*(O_{X_T}) = O_T`). They do not belong to the general lemma and are not
hypotheses here. Printed page 89 (PDF page 93) continues the discussion of
`P_{X/S,ε}` and contains no further argument about scalar endomorphisms.

## Errata check

On 2026-10-29 Worker 344, and independently Worker 303, checked the current
author pages: the "Draft for a book on abelian varieties" section of
`https://www.math.ru.nl/~bmoonen/research.html` and
`https://van-der-geer.nl/`, which links the book manuscript. Neither links
source-specific errata. This is a bounded search, not a claim that no errata
exist. Worker 344 reports that the linked chapter and manuscript retain the
scalar-endomorphism argument in (6.2). The retained PDF's SHA-256 matches the
registered hash above.

## Relation to published results

- `Langlands.Scheme.Modules.exists_eq_smul_id_of_isLocallyFreeRankOne` (in
  `Langlands.AlgebraicGeometry.Picard.RigidifiedIsoUniquenessProof`) proves
  that every endomorphism `φ` of a locally free rank-one module sheaf `M`
  satisfies `φ = c • 𝟙 M` for some global function `c`. It asserts existence
  only: it says nothing about uniqueness of `c` or about `c` being a unit.
- `Langlands.SchemeModule.structureAutMulEquiv` (in
  `Langlands.AlgebraicGeometry.Modules.StructureUnitScalars`) identifies the
  automorphism group of the structure module with `Γ(X, ⊤)ˣ`. It concerns only
  the structure module itself, not arbitrary locally free rank-one sheaves.
- `Langlands.Scheme.Modules.pullback_map_smul` (in
  `Langlands.AlgebraicGeometry.ModuleLocalHomPullbackProofs`) proves that
  pullback is compatible with this scalar action. It is not assumed here.

## Proof leads

These are leads for a separate proof task, not part of the statement. The
published existence theorem gives global functions `c` and `d` with
`e.hom = c • 𝟙 M` and `e.inv = d • 𝟙 M`. Then `(c * d) • 𝟙 M = 𝟙 M` and
`(d * c) • 𝟙 M = 𝟙 M`. What remains is faithfulness: if `a • 𝟙 M = b • 𝟙 M`
for a locally free rank-one `M`, then `a = b`. On a trivializing open `U` the
restriction of `M` is the structure sheaf of `U`, where multiplication by the
restriction of `a - b` kills the section `1`, so `a - b` restricts to zero on
`U`; these opens cover `X`, so `a = b`. Faithfulness gives `c * d = 1`, so `c`
is a unit, and it also gives uniqueness of the unit. Alternative routes are
local scalar gluing or tensor cancellation using
`Langlands.AlgebraicGeometry.Picard.LocalComparisonProof`.

## Authorship

Worker 344 designed this interface, including the exact Lean body. Worker 303
wrote the Lean and Markdown files and checked the source and errata.
