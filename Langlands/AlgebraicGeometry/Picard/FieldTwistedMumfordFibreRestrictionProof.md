# Proof of both field fibre restrictions of a twisted ordinary Mumford tensor

`Langlands.AbelianScheme.fieldTwistedMumfordFibreRestriction` proves exactly
`Langlands.AbelianScheme.FieldTwistedMumfordFibreRestrictionStatement.{u}`:

```lean
theorem fieldTwistedMumfordFibreRestriction :
    FieldTwistedMumfordFibreRestrictionStatement.{u}
```

The universe `u` is arbitrary. The theorem introduces every binder and local
`let` of the statement (`preservation`, `K`, the field instance, `A`, `L`, `N`,
`R`, `Z`, `p1`, `p2`, `m`, `Q`, `x`, `i1`, `i2`, `D`) and adds no hypotheses.
Inspection reports only the standard axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Imports

The module imports the published statement and two published Library modules,
all unchanged:

- `Langlands.AlgebraicGeometry.Picard.FieldTwistedMumfordFibreRestrictionStatement`,
  the target;
- `Langlands.AlgebraicGeometry.Picard.MumfordBundlePicardZeroReduction`, for
  `MumfordPicardZero.pullbackTensorIso` (the invertible pullback-tensor
  comparison obtained from `preservation`), `MumfordPicardZero.pullbackCompIso`
  (pullback along `h` is pullback along `g` then `f` when `f ≫ g = h`),
  `MumfordPicardZero.tensorIsoOf` (tensor product of two isomorphisms) and
  `MumfordPicardZero.constantIso` (pullback along a constant endomorphism of a
  group scheme over a field is trivial, given a triviality theorem for line
  bundles on the field spectrum);
- `Langlands.AlgebraicGeometry.Picard.FieldLineBundleTrivialityProof`, for the
  unconditional theorem `fieldLineBundleTriviality`: every line bundle on
  `Spec K` is isomorphic to the structure sheaf.

## Notation

As in the statement's Markdown, `Z = A ×_K A`, `p1`, `p2` are its projections,
`m = mumfordAddition A`, and `Q = ((m^*L ⊗ p1^*N) ⊗ p2^*N) ⊗ p2^*R`. Write
`c_x` for the constant endomorphism `Over.mkIdTerminal.from A.X ≫ x` of `A.X`;
its underlying scheme map is `A.X.hom ≫ x.left`. Write
`t_x = (GroupScheme.translation A.toGrp x).left`; in the Library,
`GroupScheme.translation A.toGrp x` is by definition `c_x * 𝟙`, left
translation `y ↦ x * y`.

## Implemented proof

The auxiliary declarations live in the namespace
`Langlands.AbelianScheme.FieldTwistedMumford`. The module sets
`backward.isDefEq.respectTransparency` and its `.types` variant to `false`, and
uses explicit lemma terms such as `pullback.lift_fst` rather than `simp` for the
pullback coordinate computations.

1. **Coordinates.** `constPoint A x` is `c_x`, and `constPoint_left` computes
   its underlying map as `A.X.hom ≫ x.left`. `firstLift A x` and
   `secondLift A x` are abbreviations whose bodies are literally the
   statement's `i1` and `i2`. The lemmas `firstLift_fst`, `firstLift_snd`,
   `secondLift_fst` and `secondLift_snd` give the composites with `p1` and `p2`:
   `i1` has coordinates `(c_x, 𝟙)` and `i2` has coordinates `(𝟙, c_x)`.

2. **The lifts over the base.** `firstLiftOver` and `secondLiftOver` are the
   same maps as morphisms `A.X ⟶ mumfordProduct A` in `Over (Spec K)`, built
   with `Over.homMk`. Their composites with `mumfordFirst A` and
   `mumfordSecond A` are `c_x` and `𝟙` respectively in the first case, and `𝟙`
   and `c_x` in the second (`firstLiftOver_first`, `firstLiftOver_second`,
   `secondLiftOver_first`, `secondLiftOver_second`, all by
   `Over.OverMorphism.ext` from step 1).

3. **Addition becomes translation.** Since
   `mumfordAddition A = (mumfordFirst A * mumfordSecond A).left`,
   `MonObj.comp_mul` distributes precomposition over the product of points.
   - `firstLift_addition`: `i1 ≫ m = t_x`, because
     `firstLiftOver ≫ (mumfordFirst A * mumfordSecond A) = c_x * 𝟙`, which is
     `GroupScheme.translation A.toGrp x` by definition.
   - `secondLift_addition`: `i2 ≫ m = t_x`. Here the product is `𝟙 * c_x`,
     and `mul_comm` (commutativity of the abelian scheme's point monoid)
     turns it into `c_x * 𝟙`.

   Taking `left` components gives both scheme equations.

4. **Module helpers.** These are stated for an arbitrary
   `preservation : pullbackTensorComparisonIsIsoStatement.{u}`.
   - `pullbackTensorFourIso` applies `pullbackTensorIso` three times to move a
     pullback inside the left-nested fourfold tensor product.
   - `pullbackIdFactorIso f g w M`, for `w : f ≫ g = 𝟙`, combines
     `(pullbackCompIso f g 𝟙 w M).symm` with `Scheme.Modules.pullbackId` to
     give `f^*g^*M ≅ M`.
   - `pullbackConstFactorIso A x f g w N`, for `w : f ≫ g = c_x.left` and a
     line bundle `N`, combines `(pullbackCompIso f g _ w N.obj).symm` with
     `constantIso fieldLineBundleTriviality A.toGrp x N` to give
     `f^*g^*N ≅ O_A`. The scalar triviality premise of `constantIso` is thus
     supplied by the published unconditional theorem, not by a hypothesis.

5. **The first restriction.** `firstRestrictionIso` constructs the module
   isomorphism

   ```text
   i1^*(((m^*L ⊗ p1^*N) ⊗ p2^*N) ⊗ p2^*R) ≅ (t_x^*L ⊗ N) ⊗ R
   ```

   as `pullbackTensorFourIso`, followed by `tensorIsoOf` applied factorwise:
   `i1^*m^*L ≅ t_x^*L` by `pullbackCompIso` with `firstLift_addition`;
   `i1^*p1^*N ≅ O_A` by `pullbackConstFactorIso` with `firstLift_fst`, after
   which `tensorRightUnitor` removes this factor; and `i1^*p2^*N ≅ N`,
   `i1^*p2^*R ≅ R` by `pullbackIdFactorIso` with `firstLift_snd`.

6. **The second restriction.** `secondRestrictionIso` constructs

   ```text
   i2^*(((m^*L ⊗ p1^*N) ⊗ p2^*N) ⊗ p2^*R) ≅ t_x^*L ⊗ N
   ```

   in the same way: `i2^*m^*L ≅ t_x^*L` by `secondLift_addition`;
   `i2^*p1^*N ≅ N` by `pullbackIdFactorIso` with `secondLift_fst`; and both
   `i2^*p2^*N` and `i2^*p2^*R` are trivialized by `pullbackConstFactorIso` with
   `secondLift_snd`, each removed by `tensorRightUnitor`.

7. **The theorem.** After `intro`, the underlying module of
   `(LineBundle.pullback i1).obj Q` is definitionally the source of
   `firstRestrictionIso preservation A x L N R`, and the underlying module of
   `LineBundle.tensor preservation D R` is definitionally its target; similarly
   for `i2`, `D` and `secondRestrictionIso`. Since `LineBundle A.X.left` is a
   full subcategory of module sheaves, `ObjectProperty.isoMk` lifts each module
   isomorphism to an isomorphism of line bundles. The pair of these, each
   wrapped in `Nonempty`, is the conclusion.

## Relation to the planned route

The statement's Markdown names `pullbackTensorIso`, `pullbackCompIso`,
`tensorIsoOf` and `constantIso`, the actual pullback coordinate identities and
the group-law identities as the intended route, with the triviality premise of
`constantIso` supplied by `fieldLineBundleTriviality`. The implementation
follows that route exactly. It does not use `MumfordPicardZero.mumfordFibreIso`
or the `FieldMumfordPoint` helpers; it computes directly on `A ×_K A`. The
constant-factor isomorphisms are not canonical, which is why the statement only
asserts `Nonempty`.

## Provenance and authorship

The statement is an internal tensor generalization of the two displayed
restrictions in the proof of Edixhoven, van der Geer and Moonen,
*Abelian Varieties*, preliminary version of the first chapters, Proposition
(7.21), printed p.106 / PDF p.110 (registered source
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`). With
`𝒦 = Λ(L) ⊗ p₂^*M⁻¹`, the source displays
`𝒦|_{ {x} × X } ≅ t_x^*L ⊗ L⁻¹ ⊗ M⁻¹` and `𝒦|_{ X × {x} } ≅ t_x^*L ⊗ L⁻¹`.
The slice `{x} × X` is the image of `i1 = (c_x, 𝟙)`, and `X × {x}` the image of
`i2 = (𝟙, c_x)`; with `N = L⁻¹` and `R = M⁻¹` the two conclusions specialize to
these displays. The source gives the restrictions without a detailed
computation; the Lean proof above is internal.

On 30 October 2026 the registered PDF hash was re-verified, the display on
PDF p.110 was re-read, and the retained literature filenames and the published
notes mentioning this source were searched for source-specific errata. None
was found in those locations. The later citation of Lemma (7.15) on printed
p.106, apparently intended as (7.19) with (7.20), concerns a subsequent
cohomological step and does not affect the displayed restrictions.

Worker 1089 wrote the Lean proof and this documentation. It reuses no
unpublished drafts.
