# Proof: fppf Picard classes of a proper flat integral family with a section

Authors: Worker 22.

Worker 22 wrote this module for task `07219dde-fd87-48cf-83be-db16cbb3707c`
(Task 5705). It proves the published proposition
`Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralSheafClassTwistStatement`
(module `Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralSheafClassTwistStatement`,
by Worker 5705). Task 6213 (`3965814b-e507-48ee-80c8-b2ccec73242c`) requests the
same proof and points to this module.

The main theorem is

```lean
theorem Langlands.AlgebraicGeometry.Picard.properFlatIntegralSheafClassTwist :
    ProperFlatIntegralSheafClassTwistStatement.{u}
```

Its type is the target proposition exactly, for an arbitrary universe `u`. The
proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## What is proved

Let `f : X ⟶ S` be proper, flat, locally of finite presentation and
geometrically integral, with a section `ε`. Fix `T : Over S`. Write
`X_T = (relativeSpace f).obj T` and `g = (relativeProjection f).app T : X_T ⟶ T.left`.
Then:

1. every element of the fppf Picard class sheaf
   `RelativePicard.classSheafPresheaf f` at `T` is `sheafClassOf f T L` for a
   line bundle `L` on `X_T`;
2. `sheafClassOf f T L = sheafClassOf f T L'` holds if and only if
   `L.obj ≅ L'.obj ⊗ g^* N` for an invertible module `N` on `T`.

This is Kleiman's description `Pic_{(X/S)(fppf)}(T) = Pic(X_T)/Pic(T)`
(S. L. Kleiman, *The Picard scheme*, arXiv math/0504020v1, Theorem 2.5, p.18,
with Exercise 3.11, p.25). The Lean proof does not follow Kleiman's argument
step by step. It uses the Library's rigidified comparison isomorphism
`RigidifiedLineBundle.properFlatIntegralClassIso`, which already carries the
geometric input (`O_T ⥲ g_* O_{X_T}` and the rigidified-sheaf argument), and
adds the bookkeeping in Picard groups described below.

## Library results used

- `RigidifiedLineBundle.properFlatIntegralClassIso f ε hε`
  (`Langlands/AlgebraicGeometry/Picard/ProperFlatIntegralRigidifiedComparison.lean`):
  a natural isomorphism `Θ` between the presheaf of `ε`-rigidified line-bundle
  classes and `RelativePicard.classSheafPresheaf f`, whose forward map is
  `RigidifiedLineBundle.toClassPicardSheaf f ε hε`. On a class it forgets the
  rigidification and takes `sheafClassOf` (`toClassPicardSheaf_app_classOf`).
- `RelativePicard.toSheaf`, `RelativePicard.forgetSheafIso`,
  `toSheaf_forgetSheafIso_hom`, `toClassSheaf`, `classSheafPresheaf_isSheaf`,
  `classOf_tensor`, `classOf_trivial`
  (`Langlands/AlgebraicGeometry/Picard/RelativePicardSheaf.lean`). Here
  `toSheaf` is the fppf sheafification unit of the Picard group presheaf, and
  `forgetSheafIso` identifies the underlying set-valued presheaf of that group
  sheaf with `classSheafPresheaf f`.
- The Picard-group API: `Group.pullback` (an additive homomorphism),
  `Group.pullback_comp`, `Group.pullback_id`, `Group.pullback_lineBundle_classOf`,
  `Group.lineBundleRepresentative`, `Group.classOf_lineBundleRepresentative`,
  `LineBundle.classOf_eq_iff`, `LineBundle.classOf_trivial`.
- `relativeSection_projection f ε hε T : σ ≫ g = 𝟙 T.left`, where
  `σ = (relativeSection f ε hε).app T` is the section of `g` induced by `ε`.
- `portedTensorExplicitIso`, which identifies the FLT port's tensor product
  `⊗` used in the statement with the Library's `Scheme.Modules.tensorObj`, the
  tensor product behind `LineBundle.tensor`.

## Auxiliary lemmas (namespace `ProperFlatIntegralSheafClassTwist`)

- `sheafClassOf_eq_forgetSheafIso` and `sheafClassOf_eq_iff`: `sheafClassOf f T L`
  is the image under `forgetSheafIso` of `toSheaf (classOf f T L)`. Since
  `forgetSheafIso` is an isomorphism, two line bundles have the same
  `sheafClassOf` exactly when their Picard classes have the same image under
  `toSheaf`.
- `unitHom f T`: the component of `toSheaf` at `T`, written as an additive
  homomorphism `Group X_T →+ (sheafPresheaf f).obj (op T)`.
  `sheafClassOf_eq_iff_unitHom` restates the previous lemma with it. This lets
  the main proof rewrite with `map_add`, `map_sub` and `map_neg`.
- `map_classOf_pullback_projection`: if `k : T' ⟶ T` is a morphism over `S` and
  `N` becomes trivial in `Pic(T')`, then the class of `g^* N` pulls back to `0`
  in `Pic(X_{T'})`. The proof uses the naturality of `relativeProjection`
  (`g_T ∘ X_k = k ∘ g_{T'}`) and functoriality of `Group.pullback`.
- `sheafClassOf_pullback_projection` (the key lemma): for every line bundle `N`
  on `T.left`, `sheafClassOf f T (g^* N) = sheafClassOf f T 𝒪`, where `𝒪` is
  the trivial bundle. Proof: `N` is trivial on each open `N.trivializingOpen y`,
  so by the previous lemma both classes agree after restriction to every member
  of this Zariski open cover of `T`. The sieve on which they agree
  (`Presheaf.equalizerSieve`) is therefore a Zariski covering sieve in
  `Scheme.zariskiTopology.over S`. It is also an fppf covering sieve, because
  the Zariski precoverage is contained in the fppf precoverage
  (`Scheme.zariskiPrecoverage_le_fppfPrecoverage`). The presheaf
  `classSheafPresheaf f` is an fppf sheaf (`classSheafPresheaf_isSheaf`), hence
  separated, so the two sections are equal.
- `unitHom_classOf_pullback_projection`: the group form of the key lemma,
  `unitHom f T (classOf (g^* N)) = 0`.
- `isInvertible_lineBundle` and `lineBundleOfIsInvertible`: a `LineBundle` is a
  module satisfying `Scheme.Modules.IsInvertible`, and conversely. Both
  directions only change the local trivialisations, using
  `Scheme.Modules.restrictFunctorIsoPullback` to compare restriction to an open
  with pullback along its inclusion.

## Proof of the theorem

Introduce the data, choose the section `ε`, and set
`Θ = properFlatIntegralClassIso f ε hε`. Since `Θ` is an isomorphism, its
forward component `toClassPicardSheaf.app (op T)` is injective (`hinj`, from
`Θ.hom_inv_id_app`).

**Conclusion 1 (surjectivity).** Given `ξ`, pick a rigidified line bundle `r`
representing the class `Θ⁻¹ ξ` (`Quotient.exists_rep`). Its underlying line
bundle `L` works: `sheafClassOf L = Θ (class of r) = Θ (Θ⁻¹ ξ) = ξ`, by
`Θ.inv_hom_id_app`.

**Conclusion 2, (⇒).** Assume `sheafClassOf L = sheafClassOf L'`, so
`unitHom (cl L) = unitHom (cl L')`, where `cl` is the class in `Pic(X_T)`.
The library's Picard group has no `AddCommGroup` instance, so the proof only
uses group laws that hold in any additive group.

- Let `d = -cl L' + cl L`, `n = σ^* d ∈ Pic(T)`, `N` a line bundle representing
  `n` (`Group.lineBundleRepresentative`), and `d₀ = d - g^* n`.
- `hgN`: `cl (g^* N) = g^* n`.
- `hσ`: `σ^* d₀ = 0`, because `σ^* g^* n = (g ∘ σ)^* n = n` by
  `relativeSection_projection`.
- `hτ`: `unitHom d₀ = 0`. Expand `d₀` with `map_sub`, `map_add` and `map_neg`;
  use the hypothesis to replace `unitHom (cl L)` by `unitHom (cl L')`; and use
  `unitHom_classOf_pullback_projection` to kill `unitHom (g^* n)`.
- Let `M₀` represent `d₀`. By `hσ`, `σ^* M₀` is isomorphic to the trivial
  bundle (`LineBundle.classOf_eq_iff`), which gives a rigidification `α` of `M₀`
  along `σ`. The rigidified bundle `R₀ = ofLineBundle M₀ α.symm` and the trivial
  rigidified bundle have the same image under `toClassPicardSheaf`, by
  `toClassPicardSheaf_app_classOf`, `sheafClassOf_eq_iff_unitHom` and `hτ`.
  By `hinj` they are isomorphic as rigidified bundles (`Quotient.exact`).
  Forgetting the rigidification, `M₀` is isomorphic to the trivial bundle, so
  `d₀ = 0` (`hc0`).
- Hence `-cl L' + cl L = g^* n`, i.e. `cl L = cl L' + g^* n`
  (`neg_add_eq_iff_eq_add`). By `classOf_tensor` and `hgN` this is
  `cl L = cl (L' ⊗ g^* N)` (`hcL`), with the Library tensor
  `LineBundle.tensor`.
- `LineBundle.classOf_eq_iff` turns `hcL` into an isomorphism of modules. It is
  composed with the inverse of `portedTensorExplicitIso` to land in the
  statement's tensor product. The witness is `N.obj`, invertible by
  `isInvertible_lineBundle`.

**Conclusion 2, (⇐).** Given `N` invertible and `e : L.obj ≅ L'.obj ⊗ g^* N`,
let `N'` be `N` viewed as a line bundle (`lineBundleOfIsInvertible`) and
`P = L' ⊗ g^* N'` with the Library tensor. Composing `e` with
`portedTensorExplicitIso` gives `cl L = cl P`. Then
`unitHom (cl P) = unitHom (cl L') + unitHom (cl (g^* N')) = unitHom (cl L')`,
by `classOf_tensor`, `map_add` and `unitHom_classOf_pullback_projection`. So
`sheafClassOf L = sheafClassOf L'` by `sheafClassOf_eq_iff_unitHom`.

## Relation to Kleiman's proof

Kleiman proves injectivity in Theorem 2.5 (Part 1, p.19) by pushing a line
bundle forward along `g` and using Lemma 2.7. He proves surjectivity (Part 2,
pp.19–20) through rigidified sheaves. In the Lean proof, all use of
`O_T ⥲ g_* O_{X_T}` sits inside the Library's `properFlatIntegralClassIso`.
Injectivity is reduced to the injectivity of that isomorphism by the
normalisation `d₀ = d - g^* σ^* d`, which is rigidifiable along `σ`. The only
new sheaf-theoretic input is the key lemma: pullbacks of line bundles from `T`
die in the fppf sheaf, because they are Zariski-locally trivial.
