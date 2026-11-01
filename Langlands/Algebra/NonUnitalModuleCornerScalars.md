# Inherited complex scalars and linear maps on the actual fixed part

Worker 1149 constructed this pair from David Renard, *Représentations des
groupes réductifs p-adiques*, French version dated 9 July 2026. The governing
registered source is `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
retained at `/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
The original-action conventions on printed pages 5–7 / PDF pages 11–13,
canonical scalars and automatic linearity in I.2.1, printed page 14 / PDF
page 20, fixed-part splitting in I.3.1, printed page 19 / PDF page 25, and
I.4.1, printed pages 22–23 / PDF pages 28–29 were read. The last page was
also visually checked.

The registered supplementary source `renard-2010-corrections-complements`,
SHA256 `fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
PDF pages 1–2, was read. Its nearby corrections concern the tensor
construction, later forgetful comparison, admissible reflexivity, and
injectivity argument. None changes the scalar inheritance or maps here.
The 2026 edition governs. No project errata note for these sources was found.

All declarations are in `Langlands.Algebra.NonUnitalModuleCorner`. This pair
supplies internal construction details needed to express the fixed-part
duality lemma's canonical maps. Renard's scalar compatibility (I.2.1.1)
makes the original idempotent coordinate complex linear. The fixed subgroup
therefore inherits ambient scalars, and the additive splitting and maps
already published in `NonUnitalModuleCorner` acquire complex-linear
adapters. The named structures and complete-map equalities formalize these
implicit choices. They are derived constructions, rather than additional
independent assertions of the book.

## Carriers, actions, and scalar choices

The fixed carrier is exactly `FixedPart e M`, the subtype of the actual
`fixedPart e M : AddSubgroup M`. Its additive structure is the published
`fixedPartAddCommGroup e M`. Its corner action is exactly the published
`fixedPartModule e M` over `Idempotent.Corner e`. No new fixed carrier,
additive group, or corner action is introduced.

The helper `inheritedComplexModule e M` accepts a compatible ambient
`Module ℂ M` with `SMulCommClass ℂ A M`. `smul_mem_fixedPart` proves closure
by commuting the original action of `e` with complex scalars and applying
the fixed-vector equation. Scalar multiplication on the subtype is

```text
c • x = ⟨c • x.val, smul_mem_fixedPart e c x⟩.
```

All module laws descend by subtype extensionality from the ambient module
laws. `inheritedComplexModule_smul` exposes the complete subtype formula;
`inheritedComplexModule_smul_val` exposes its ambient value.
`inherited_smulCommClass` proves that these scalars commute with the
unchanged corner action, using ambient commutation at the corner element's
actual value.

The required specialization is `complexModule hA hM e`. Its only inputs
are the specified `NonUnitalRing A`, `Module ℂ A`, algebra scalar tower
and commuting classes, `hA : IsIdempotented A`, the specified original
`NonUnitalModule A M` on its additive group, and
`hM : IsNondegenerate A M`. It explicitly installs
`NondegenerateScalars.complexModule hA hM` and its published commutation
proof before using `inheritedComplexModule`. It accepts no supplied
complex structure or scalar-linearity witness on `M`.

`complex_smul_mem`, `complex_smul`, and `complex_smul_val` give closure,
the full subtype formula, and
`(c • x).val = c • x.val`, with the precise ambient and fixed-part modules
explicit in their types. `complex_smulCommClass` is the specialized
commutation statement for the published corner action.
`cornerLinearAction hA hM e a` bundles the action of each actual corner
element as a complex-linear endomorphism, with `cornerLinearAction_apply`
identifying the entire vector with `a • x`. Additivity is the original
corner action law; complex homogeneity is scalar commutation.

## The actual linear inclusion and projection

`inclusionLinear hA hM e` and `projectionLinear hA hM e` adapt the existing
additive maps, with the canonical ambient module and the named fixed-part
module explicit in their types. Their `_toAddMonoidHom` theorems identify
the entire underlying additive maps with `inclusion e` and `projection e`.
The inclusion's scalar law is the inherited subtype formula. The
projection's scalar law follows by commuting complex scalars with `e`.

`inclusionLinear_coe` identifies its whole function with `fun x => x.val`;
`inclusionLinear_apply` gives its value. `projectionLinear_coe` identifies
the whole function with the published projection. `projectionLinear_apply`
identifies its whole subtype value with `projection e m`, and
`projectionLinear_val` gives `(e : A) • m`.

`projectionLinear_inclusionLinear` states that the complete linear
composite is `LinearMap.id`. `inclusionLinear_projectionLinear` states
that the opposite composite is the original action of `e`, bundled as
`NondegenerateScalars.toLinearEndHom ℂ hA hM (e : A)`. Both proofs use
injectivity of forgetting a linear map to its additive map and the
published additive identities `projection_inclusion` and
`inclusion_projection`. There is no claim of ambient `A`-linearity.

## Intrinsic intertwiner adapters

For an original `f : NonUnitalModuleHom A M N`,
`restrictLinear hA hM hN e f` uses the entire additive map of the published
corner-linear `restrict e f`. Its scalar law is obtained by evaluating
the published automatic adapter
`NondegenerateScalars.complexToLinearMap hA hM hN f` and using subtype
extensionality.

`restrictLinear_toAddMonoidHom` identifies those entire additive maps.
`restrictLinear_coe` gives the complete subtype-valued function
`fun x => ⟨f x.val, map_mem_fixedPart e f x.property⟩`.
`restrictLinear_apply` identifies the whole subtype value with the
published restriction, and `restrictLinear_val` gives `f x.val`.

`inclusionLinear_naturality` and `projectionLinear_naturality` are
equalities of complete linear composites:

```text
inclusion_N ∘ restrictLinear(f) = complexToLinearMap(f) ∘ inclusion_M
restrictLinear(f) ∘ projection_M = projection_N ∘ complexToLinearMap(f).
```

Their proofs forget to the complete published additive equalities.
`restrictLinear_id` and `restrictLinear_comp` give identity and composition
laws, proved by equality of their underlying additive maps. Every type
selects the named fixed-part modules, together with the named canonical
ambient modules whenever those occur.

The final unapplied interfaces check the entire type of `complexModule`
with independent algebra and carrier universes `uA`, `uM`, and of
`restrictLinear` with independent `uA`, `uM`, `uN`. Composition also retains
an independent `uP`. There are no dimension, admissibility, faithfulness,
unit-action, or nontriviality hypotheses. Zero algebras, zero carriers,
and the zero idempotent remain allowed.

The dual restriction and extension belong to a subsequent construction
pair. Their inverse identities, the fixed-part duality equivalence and
its naturality and right-corner comparison, comparison with full-dual
fixed parts, duality exactness, bidual injection, I.4.2/I.4.3 comparisons,
and admissible reflexivity remain separate statement/proof successors.
