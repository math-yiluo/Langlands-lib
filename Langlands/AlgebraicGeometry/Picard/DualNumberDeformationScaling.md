# Actual epsilon scaling of first-order line-bundle deformations

Module `Langlands.AlgebraicGeometry.Picard.DualNumberDeformationScaling`,
namespaces `Langlands.AlgebraicGeometry.Picard.CocycleGluing` and
`Langlands.AlgebraicGeometry.Picard.DualNumberThickening`.

Let `k : Type u` be an arbitrary field, `X : Scheme.{u}` and
`f : X ⟶ Spec k`. For `c : k`, the Library morphism `scale f c` (module
`DualNumberScaling`) is the actual endomorphism of the dual-number thickening
`thickening f` induced by `ε ↦ c ε`. This module shows that actual line-bundle
pullback along `scale f c` sends the bundle glued from the unit cocycle
`1 + ε z` to the bundle glued from `1 + ε (c z)`. Under the comparison
`deformationH1AddEquiv` of module `DualNumberDeformationH1`, actual pullback
along `scale f c` therefore becomes multiplication by `c` on actual derived
`H¹(X, O_X)`. This holds for every `c`, including `c = 0`.

## Conventions

The gluing conventions are those of `CocycleLineBundleProof`. For a family of
opens `T : ι → X.Opens` and units `g i j ∈ Γ(X, T i ⊓ T j)ˣ` satisfying
`IsCocycle g`, `glued g` is the glued line bundle, and `genSec g hg i hV` is
its local generator over an open `V ≤ T i`. `IsFrameOn`, `IsTransition` and
`frameIso` are from `CocycleLineBundleFrame`: if local sections `e i` of a
module sheaf `M` are frames on `T i`, have transition units `g`, and
`⨆ i, T i = ⊤`, then `frameIso` is the isomorphism `M ≅ glued g` sending `e i`
to `genSec g _ i`. `pullbackCocycle q g` and `pullbackIso` are from
`CocycleLineBundlePullback`. The first is the cocycle `q.appLE (g i j)` on the
opens `q ⁻¹ᵁ T i`; the second is the isomorphism
`(pullback q).obj (glued g) ≅ glued (pullbackCocycle q g)` sending the
pullback of `genSec g _ i` to `genSec (pullbackCocycle q g) _ i`.

On the thickening, `thickenedOpens f T i = projection f ⁻¹ᵁ T i`, and for an
additive cochain `z i j ∈ Γ(X, T i ⊓ T j)` the unit cochain
`unitCochain f T z i j = coefficientUnit f (T i ⊓ T j) (z i j)` is the actual
unit `1 + ε z i j` (module `DualNumberCocycles`). By
`isCocycle_unitCochain_iff`, it is a multiplicative cocycle exactly when `z` is
an additive Čech cocycle. `baseSectionMap f U : k → Γ(X, U)` is the normalized
base-field section map.

## Gluing on a smaller cover

These declarations concern a scheme `X`, families `T T' : ι → X.Opens` with
`hle : ∀ i, T' i ≤ T i`, and a cocycle `g` on `T`.

- `isFrameOn_genSec_of_le`: the local generator `genSec g hg i (hle i)` of
  `glued g` over `T' i` is a frame on `T' i`. Its restrictions are local
  generators (`map_genSec`), and every local generator is a frame
  (`smul_genSec_bijective`).
- `isTransition_genSec_of_le`: let `g'` be a family of units on the overlaps
  `T' i ⊓ T' j` that are the restrictions of the `g i j` (hypothesis `hres`).
  Then the generators `genSec g hg i (hle i)` have transition units `g'`. The
  proof uses `genSec_eq_smul_genSec`.
- `shrinkIso g hg hle hT' g' hres : glued g ≅ glued g'`, when
  `⨆ i, T' i = ⊤`. It is the specific isomorphism `frameIso` for these
  restricted generators.
- `shrinkIso_hom_app_genSec`: if `g'` is a cocycle, then for `V ≤ T' i` the
  forward map of `shrinkIso` sends `genSec g hg i _` over `V` to
  `genSec g' hg' i hV`. The proof is `frameIso_hom_app_frame` after rewriting
  the generator over `V` as a restriction (`map_genSec`).

## Scaling of unit cochains and their bundles

- `scale_preimage_projection`: `scale f c ⁻¹ᵁ (projection f ⁻¹ᵁ U)` equals
  `projection f ⁻¹ᵁ U` for every open `U` of `X`, because
  `scale f c ≫ projection f = projection f` (`scale_projection`).
- `res_pullbackCocycle_scale_unitCochain`: let `w` be a cochain with
  `w i j = baseSectionMap f (T i ⊓ T j) c * z i j` for all `i j` (hypothesis
  `hwz`). Restricted to the overlaps of `projection f ⁻¹ᵁ T i`, the cocycle
  `pullbackCocycle (scale f c) (unitCochain f T z)` equals
  `unitCochain f T w`. The proof combines `res_pullbackCocycle` with the
  Library unit formula `scaleSectionMap_coefficientUnit`:

  ```
  Units.map (scaleSectionMap f c U) (coefficientUnit f U a)
    = coefficientUnit f U (baseSectionMap f U c * a).
  ```

- `scaleCocycleBundleIso f T hT c z w hz hwz`, for a cover `T` with
  `⨆ i, T i = ⊤`, an additive cocycle `z` (hypothesis `hz`) and `w` as above,
  is the isomorphism

  ```
  (Scheme.Modules.pullback (scale f c)).obj (glued (unitCochain f T z))
    ≅ glued (unitCochain f T w).
  ```

  It is the composite of `pullbackIso (scale f c)` and `shrinkIso` from the
  cover `scale f c ⁻¹ᵁ (projection f ⁻¹ᵁ T i)` to the cover
  `projection f ⁻¹ᵁ T i`. These two covers are equal, so the hypothesis of
  `shrinkIso` follows from `scale_preimage_projection`. The cocycle property
  of `w` is not a hypothesis of this isomorphism.
- `scaleCocycleBundleIso_hom_app_genSec`: if `w` is also an additive cocycle,
  then for `V ≤ projection f ⁻¹ᵁ T i` the forward map sends the actual
  pullback of `genSec (unitCochain f T z) _ i hV` to the local generator
  `genSec (unitCochain f T w) _ i _` over `scale f c ⁻¹ᵁ V`. The proof is
  `pullbackIso_hom_app_genSec` followed by `shrinkIso_hom_app_genSec`.

## Deformation classes

Here `preservation : pullbackTensorComparisonIsIsoStatement.{u}` is the
pullback/tensor preservation property on which the Library line-bundle class
group `LineBundle.IsoClasses` and its pullback homomorphisms
`LineBundle.pullbackHom` depend. This module takes it as a hypothesis, like
`DualNumberDeformationH1`; the Library proves it as
`pullbackTensorComparisonIsIso` (module
`Langlands.AlgebraicGeometry.Modules.PullbackTensorProof`). `DeformationClasses preservation f` is the subgroup
of line-bundle isomorphism classes on `thickening f` whose pullback along
`closedPoint f` is trivial.

- `pullbackHom_scale_mem`: actual pullback along `scale f c` maps
  `DeformationClasses` into itself. The proof uses
  `closedPoint f ≫ scale f c = closedPoint f` (`closedPoint_scale`) and
  `LineBundle.pullbackHom_comp_eq`.
- `scaleClass f preservation c` is the group endomorphism of
  `DeformationClasses preservation f` obtained by restricting
  `LineBundle.pullbackHom preservation (scale f c)` to the subgroup.
  `coe_scaleClass` states, by `rfl`, that the underlying class of
  `scaleClass f preservation c q` is
  `LineBundle.pullbackHom preservation (scale f c) q`.
- `scaleClass_cocycleDeformationClass`: for an ordered affine cover `𝒰` of
  `X` and an all-pairs additive cocycle `z`,

  ```
  scaleClass f preservation c (cocycleDeformationClass preservation f 𝒰 z)
    = cocycleDeformationClass preservation f 𝒰 (c • z).
  ```

  The scalar action of `k` on additive cocycles is the action through
  `baseSectionMap`, so `(c • z) i j` is definitionally
  `baseSectionMap f _ c * z i j`. The proof applies
  `LineBundle.isoClass_eq_of_iso` to `scaleCocycleBundleIso` with
  `w = (c • z).1` and `hwz` given by `rfl`.
- `deformationH1AddEquiv_scaleClass`: if moreover `f` is separated, then for
  every `q : DeformationClasses preservation f`,

  ```
  deformationH1AddEquiv preservation f 𝒰 (Additive.ofMul (scaleClass f preservation c q))
    = c • deformationH1AddEquiv preservation f 𝒰 (Additive.ofMul q).
  ```

  Proof: `allPairsH1Map` is surjective, so the image of `q` is the class of
  some cocycle `z`. By `deformationH1AddEquiv_cocycleDeformationClass` and
  injectivity of `deformationH1AddEquiv`, `q` is then
  `cocycleDeformationClass preservation f 𝒰 z`. The previous lemma, the same
  formula for `c • z`, and the `k`-linearity of `allPairsH1Map` (`map_smul`)
  give the identity. As in `DualNumberDeformationH1`, the file declares the
  local instance `structureSheaf_isQuasicoherent` for this theorem.

No declaration assumes that `c` is nonzero, that `X` is proper, or that `k` has
characteristic zero.

## Provenance and scope

Provenance: derived.

Source: B. Edixhoven, G. van der Geer and B. Moonen, *Abelian Varieties*,
preliminary version of the first chapters (registered source
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, PDF SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`), Chapter 6,
proof of Corollary (6.6)(i), printed page 90 (PDF page 94). The corollary is
stated for a proper variety `X` over a field `k`. The proof takes `S` to be the
spectrum of the dual numbers `k[ε]` and sends a Čech cocycle `{fαβ}` to "the
line bundle on XS which is trivial on each Uα (now to be viewed as an open
subset of XS) and with transition functions 1 + εfαβ". It then states: "Hence
γ deﬁnes an element of T , and this gives a linear map ξ: H 1(X,OX )→T". Here
`T` is the tangent space of `Pic_{X/k}` at the identity element. The source
asserts that this map is linear without proving it.

Correspondence with the source. `cocycleDeformationClass` is the source's
bundle with transition functions `1 + ε fαβ`. The scalar structure on the
tangent space comes from the endomorphisms `ε ↦ c ε` of `k[ε]`, whose base
change to the thickening is `scale f c`. This module proves the scalar half of
the asserted linearity for the actual classes: pulling back along `scale f c`
corresponds to multiplying the cohomology class by `c`. The additive half is
the additivity of `deformationH1AddEquiv` in `DualNumberDeformationH1`, whose
addition law comes from `cocycleBundleTensorIso` (module
`DualNumberCocycleBundles`), built on `CocycleGluing.tensorIso`. The Lean results are more general than the corollary in one
respect: they hold for any scheme over a field, and only the comparison with
derived `H¹` uses separatedness. The gluing lemmas `shrinkIso` and
`shrinkIso_hom_app_genSec`, needed because the pulled-back cover is equal but
not definitionally equal to the original cover, are internal.

This module does not identify `DeformationClasses` with the tangent module of
a rigidified Picard parameter, and it does not construct the final k-linear
tangent-to-`H¹` equivalence; those are separate parts of the final theorem.
