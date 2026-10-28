# Proof of the rigidified Mumford comparison at field-valued points

`Langlands.AbelianScheme.fieldMumfordPointComparison` proves exactly
`Langlands.AbelianScheme.FieldMumfordPointComparisonStatement.{u}`:

```lean
theorem fieldMumfordPointComparison : FieldMumfordPointComparisonStatement.{u}
```

The universe `u` is arbitrary. The theorem introduces every binder of the
statement (`preservation`, `k`, `A`, `L`, `M`, `evaluation`, `K`, `b`, `a`, `x`,
the equation `hx : x.left ≫ pullback.fst A.X.hom b = a.left`, `Q` and the
premise isomorphism) and adds no hypotheses. Inspection reports only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Imports

The module imports the published statement and four published Library
modules, all unchanged:

- `Langlands.AlgebraicGeometry.Picard.FieldMumfordPointComparisonStatement`,
  the target;
- `Langlands.AlgebraicGeometry.Picard.MumfordBundlePicardZeroReduction`, for
  `MumfordPicardZero.pullbackTensorIso` (the invertible pullback-tensor
  comparison obtained from `preservation`), `MumfordPicardZero.pullbackCompIso`
  (pullback along `h` equals pullback along `g` then `f` when `f ≫ g = h`) and
  `MumfordPicardZero.tensorIsoOf` (tensor product of two isomorphisms);
- `Langlands.AlgebraicGeometry.Picard.FieldLineBundleTrivialityProof`, for
  `fieldLineBundleTriviality`: every line bundle on a field spectrum is
  isomorphic to the structure sheaf;
- `Langlands.AlgebraicGeometry.Picard.RigidifiedCarrierIso`, for
  `RigidifiedLineBundle.isoOfCarrierIso`: if the rigidification section has a
  retraction, any isomorphism of underlying module sheaves can be corrected to
  an isomorphism of rigidified line bundles;
- `Langlands.AlgebraicGeometry.Picard.TranslationBaseChange`, for
  `GroupScheme.baseChangePointsEquiv_translation`, which writes translation on
  a base change, read as a morphism to the original group scheme, as a product
  of points.

## Notation

As in the statement's Markdown, `S = Spec k`, `S' = Spec K`, `T = Over.mk b`,
`A_K = (baseChange b).obj A` with total space `A ×_k S'`,
`i = pullback.fst A.X.hom b : A_K → A` and
`t_x = (GroupScheme.translation A_K.toGrp x).left`. Write
`σ = pullbackSymmetry b A.X.hom : S' ×_k A ≅ A ×_k S'`, and `m`, `p1`, `p2`
for `mumfordAddition A`, `pullback.fst A.X.hom A.X.hom` and
`pullback.snd A.X.hom A.X.hom` on `A ×_k A`.

## Implemented proof

The auxiliary declarations live in the namespace
`Langlands.AbelianScheme.FieldMumfordPoint`. They are stated for an arbitrary
scheme `S`, abelian scheme `A` over `S` and point `a : Over.mk b ⟶ A.X` with
`b : S' ⟶ S`; fields enter only in the final theorem.

1. **The point map.** `pointMap A a` is `(relativeSpace A.X.hom).map a`, the
   map `a × id : S' ×_S A → A ×_S A` underlying
   `RigidifiedLineBundle.relativePullback` along `a`. The lemmas
   `pointMap_fst` and `pointMap_snd` say that its composite with `p1` is
   `pullback.fst b A.X.hom ≫ a.left` and its composite with `p2` is
   `pullback.snd b A.X.hom`. Both are proved by `simp`.

2. **Addition becomes translation.** `pointMap_addition` proves, for every
   section `x` of `A_K` with `x.left ≫ i = a.left`,

   ```text
   pointMap A a ≫ m = σ.hom ≫ t_x ≫ i.
   ```

   The proof views `pointMap A a` as a morphism `φ` in `Over S` to the
   Mumford product, and `σ.hom` as a morphism `σ` in `Over S` to
   `(Over.map b).obj A_K.X`. It then shows the equality of `Over S` morphisms
   `φ ≫ (mumfordFirst A * mumfordSecond A) = σ ≫ Φ (translation x)`, where
   `Φ = GroupScheme.baseChangePointsEquiv b A.toGrp _`. By
   `baseChangePointsEquiv_translation` the right side is a product of the
   constant point obtained from `x` and `Φ (𝟙)`. `MonObj.comp_mul` distributes
   both composites over the products, and the factors are compared separately.
   The first factors agree by `pointMap_fst`, the hypothesis `hx` and
   `pullbackSymmetry_hom_comp_snd`. The second factors agree by
   `pointMap_snd` and `pullbackSymmetry_hom_comp_fst`. Taking `left`
   components gives the stated scheme equation.

3. **The carrier isomorphism.** `carrierIso` takes `preservation`, `x`, `hx`,
   modules `L₀ M₀` on `A`, a module `Qc` on `S' ×_S A`, an isomorphism
   `triv : a.left^*M₀ ≅ O_{S'}`, and an isomorphism
   `premise : t_x^*(i^*L₀) ⊗ i^*M₀ ≅ σ.inv^*Qc`. It constructs

   ```text
   (a × id)^*((m^*L₀ ⊗ p1^*M₀) ⊗ p2^*M₀) ≅ Qc
   ```

   as the following chain:
   - `pullbackTensorIso` twice moves the pullback along `a × id` inside both
     tensor products;
   - in the factor `L₀`, `pullbackComp` and `pullbackCompIso` with
     `pointMap_addition` rewrite `(a × id)^*m^*L₀` as `σ.hom^*(t_x^*(i^*L₀))`;
   - in the factor `p1^*M₀`, `pullbackComp` and `pullbackCompIso` with
     `pointMap_fst` rewrite it as the pullback of `a.left^*M₀` from `S'`.
     The pullback of `triv`, followed by `pullbackUnitIso`, identifies this
     factor with the structure sheaf, and `tensorRightUnitor` removes it;
   - in the factor `p2^*M₀`, `pullbackComp` and `pullbackCompIso` with
     `pullbackSymmetry_hom_comp_fst` and `pointMap_snd` rewrite it as
     `σ.hom^*(i^*M₀)`;
   - `(pullbackTensorIso σ.hom).symm` gives `σ.hom^*(t_x^*(i^*L₀) ⊗ i^*M₀)`,
     and the pullback of `premise` along `σ.hom` gives `σ.hom^*σ.inv^*Qc`;
   - `pullbackComp`, `pullbackCongr σ.hom_inv_id` and `pullbackId` return to
     `Qc`.

4. **The theorem.** On `S' = Spec K`, `a.left^*M` is the underlying module of
   the line bundle `(LineBundle.pullback a.left).obj M`.
   `fieldLineBundleTriviality K` supplies `triv` for it. The premise of the
   statement, an isomorphism in `LineBundle A_K.X.left`, is sent by
   `LineBundle.forget` to an isomorphism of module sheaves. Its target is
   `familyLineBundle A Q`, which is by definition the pullback of the carrier
   of `Q` along the inverse of `relativeSpaceSymmetry`, that is along
   `σ.inv`. So `carrierIso` with `L₀ = L.obj.carrier`, `M₀ = M.obj` and
   `Qc = Q.obj.carrier` gives an isomorphism from the carrier of the
   pulled-back Mumford family to the carrier of `Q`. The rigidification
   section of `RigidifiedFamily A T` is the relative section
   `(𝟙, b ≫ e) : S' → S' ×_k A`. `relativeProjection` gives a retraction of
   it, with `relativeSection_projection` as the retraction identity.
   `RigidifiedLineBundle.isoOfCarrierIso preservation` corrects the carrier
   isomorphism to an isomorphism of rigidified families, which is wrapped in
   `Nonempty`.

## Relation to the planned route

The statement's Markdown sketches a three-step route: the fibre formula, the
scalar cancellation and the rigidified adjustment. The implementation follows
it with two differences:

- It does not transport `MumfordPicardZero.mumfordFibreIso` from the fibre
  model `(baseChange s).obj (paramChange A)`. It redoes the fibre computation
  directly on `S' ×_k A`, using `pointMap_addition`, `pointMap_fst` and
  `pointMap_snd`.
- For the rigidified adjustment it applies
  `RigidifiedLineBundle.isoOfCarrierIso`, the construction underlying
  `RigidifiedLineBundle.nonempty_iso_of_forget_iso`, directly to the carrier
  isomorphism. It does not first build a `LineBundle` isomorphism. The
  content is the same.

The input `evaluation` is passed only to `mumfordBundle`, and the proof does
not inspect it. The rigidification of the pulled-back Mumford family is never
computed, because `isoOfCarrierIso` accepts an arbitrary carrier isomorphism.

## Provenance and authorship

This is a derived internal comparison, not a verbatim theorem of the source.
Its ordinary content is the fibre formula `Λ(L)|_{{x}×X} ≅ t_x^*L ⊗ L^{-1}`
with the scalar factor removed. The statement's Markdown cites the source:
Edixhoven, van der Geer and Moonen, *Abelian Varieties*, preliminary draft
(registered source `edixhoven-vandergeer-moonen-abelian-varieties-draft`).
The rigidified category and its pullback are in paragraph (6.2), printed
pp.88–89. The pointwise description of `φ_L` is in Chapter VI §3, printed
p.95. The fibre restriction is used in the proof of Proposition (7.21),
printed pp.105–106. The Lean proof is internal and follows none of these
texts line by line.

Worker 861 wrote the Lean proof and this documentation. It reuses no
unpublished drafts.
