# Renard A.X: proof of the center identification for unital module categories

This module proves the unchanged published proposition
`Langlands.Renard.ModuleCatCenterIdentificationStatement.{u, v} R` from
`Langlands.CategoryTheory.RenardModuleCatCenterStatements`. Here `R : Type u`
has only `[Ring R]`, `v` is independent of `u`, and the actual category is
`ModuleCat.{max u v} R`. The proof includes noncommutative rings and the zero
ring. It uses precisely the homomorphism

```lean
Linear.toCatCenter (Subring.center R) (ModuleCat.{max u v} R)
```

with the scoped linear structure selected by `open scoped ModuleCat.Algebra`.
The target statement and its import closure are imported without modification.

## Source and provenance

David Renard, *Représentations des groupes réductifs p-adiques*, French edition
dated 9 July 2026, Appendix A.X, printed page 269 / PDF page 275, defines the
center of a category as the natural endomorphisms of its identity functor.
Its example identifies the center of the category of unital modules over a
unital ring with the ring center. The source asserts this identification
without a proof. The argument below is an internal proof of that example,
with the scalar-action normalization already fixed by the published statement.

The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`,
retained at
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
PDF275 was read in full as text and as a rendered image. The module
conventions on printed pages 5–6 / PDF11–12 were also read: modules are left
modules, and “unital” means that the ring unit acts as the identity. Although
the book generally allows rings and modules without units, the A.X example
explicitly assumes a unital ring and unital modules.

No current project source-specific errata file was found. The registered
2010-edition errata `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
were searched for center/category entries and their appendix corrections on
PDF18–19 were read. No correction to this example was found; the 2026 edition
governs the present result.

Worker 490 implemented this proof. The lifted-regular-module proof lead was
recorded in Worker 6's task and Worker 713's published statement documentation;
both are credited for that lead. No complete prior proof draft was reused.

## Implemented proof

Write `P = ModuleCat.of R (ULift.{v} R)`. Its carrier has universe `max u v`,
so it is an object of the category in the target even when `u` and `v` are
independent. The ordinary regular left action on `R` lifts to `P`.

For `z : CatCenter (ModuleCat.{max u v} R)`, the private definition
`centerEvaluation` is the ring element

```lean
((z.app (ModuleCat.of R (ULift.{v} R))).hom (ULift.up 1)).down
```

Denote it by `c`. The proof establishes the following facts in order.

1. **Reconstruction.** For every module `M` and element `m : M`, the private
   morphism `regularTo R M m : P ⟶ M` sends `r` to `r.down • m`.
   Its additivity is `add_smul`; its R-linearity is `mul_smul`, with the
   multiplication order unchanged. Apply `CatCenter.naturality` to this
   morphism and evaluate the resulting equality at `ULift.up 1`.
   The equation becomes `(z.app M).hom m = c • m`, proved by the private
   lemma `center_component`.
2. **Centrality.** Apply reconstruction to `M = P` and `m = ULift.up r`.
   It gives that the underlying ring element of `z_P(ULift.up r)` is `c * r`.
   R-linearity of `z_P`, applied to
   `r • ULift.up 1 = ULift.up r`, identifies the same element with `r * c`.
   Consequently `r * c = c * r` for every `r`, exactly
   `Subring.mem_center_iff`. This proves the private lemma
   `centerEvaluation_mem_center`. In the reconstruction step used here,
   `regularTo R P (ULift.up r)` is right multiplication by `r`.
3. **Injectivity.** If two central elements give equal natural
   endomorphisms, apply `centerEvaluation` to their equality. Their values
   are respectively `c * 1` and `d * 1`, hence they are equal in `R`.
   Subtype extensionality gives equality in `Subring.center R`.
4. **Surjectivity.** For any `z`, use the central element `c` from steps 1–2.
   Its scalar-action natural endomorphism agrees with `z` on every module
   element by reconstruction. Extensionality of linear maps, module
   morphisms, and natural transformations gives equality of the centers.
5. **Ring equivalence and aggregate.** Apply `RingEquiv.ofBijective` to the
   existing scalar-action ring homomorphism and the proved bijectivity.
   Its forward ring homomorphism is definitionally the input map, so the
   required equation is proved by `rfl`. The final theorem pairs
   bijectivity with this exact ring-equivalence statement.

The separate scalar-component theorem is also `rfl`: the component of
`Linear.toCatCenter` is the scalar multiple of the identity. In this scoped
module-category structure, applying it to `m` is definitionally `(c : R) • m`.
No cancellation, nonzero element, basis, finiteness assumption, or
commutativity assumption on `R` enters the proof.

## Public declarations

All four theorems are in namespace `Langlands.Renard`, have universe
parameters `{u, v}`, and take `(R : Type u) [Ring R]`.

| Theorem | Exact published proposition proved |
| --- | --- |
| `moduleCatCenterScalarComponent` | `ModuleCatCenterScalarComponentStatement.{u, v} R` |
| `moduleCatCenterBijective` | `ModuleCatCenterBijectiveStatement.{u, v} R` |
| `moduleCatCenterRingEquiv` | `ModuleCatCenterRingEquivStatement.{u, v} R` |
| `moduleCatCenterIdentification` | `ModuleCatCenterIdentificationStatement.{u, v} R` |

The last theorem is the required aggregate: bijectivity of the existing
homomorphism and existence of a ring equivalence whose underlying ring
homomorphism equals that homomorphism.

## Mathlib reuse and scope

At the pinned Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`, the proof reuses:

- `CategoryTheory.CatCenter`, its `naturality` and `ext`, and
  `CategoryTheory.Linear.toCatCenter`, from the category-center modules;
- the actual `ModuleCat` morphisms, `ModuleCat.ofHom`, `hom_comp`,
  `hom_ofHom`, and `hom_ext`;
- the lifted module instances in `Mathlib.Algebra.Module.ULift`;
- ordinary linear-map additivity, scalar compatibility and extensionality,
  `Subring.mem_center_iff`, and `RingEquiv.ofBijective`.

These declarations supply the categorical and algebraic infrastructure.
Reconstruction, centrality, and bijectivity of this specific scalar map are
proved in this module.

The result makes no claim for module carriers in a universe too small to
contain a lifted copy of `R`, or for compatibility with ring homomorphisms.
The nonunital idempotented-ring center in I.1.7, categorical decompositions
in A.IX, and later Bernstein-center assertions remain separate obligations.
