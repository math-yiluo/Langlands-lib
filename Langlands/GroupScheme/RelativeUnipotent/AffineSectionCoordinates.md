# Canonical tensor coordinates for affine pullback sections

This internal construction compares tensor coordinates with the canonical
pullback of sections of one fixed module sheaf. The base scheme `S` and all
test schemes have arbitrary universe `u`. No noetherian, connectedness,
constant-rank or flatness hypothesis is used.

For a module sheaf `M` on `S` and a test object `T : Over S`, `Points M T` is
the module

`Γ(T,O_T) ⊗_{Γ(S,O_S)} Γ(S,M)`,

using the actual structural ring map `T.hom.appLE ⊤ ⊤ le_top`. The canonical
additive map `toSection M T` takes `r ⊗ m` to `r • pullbackSection T.hom M m`.
It is defined for every `M` and `T`. If `S` and `T.left` are affine and `M`
is quasi-coherent, `toSection_bijective` identifies this map as a bijection;
`equiv M T` packages that same map as an additive equivalence.

For `a : W ⟶ T` in `Over S`, `scalarMap a` is the map on global functions
`a.left.appTop`, linear over `Γ(S,O_S)` for the two structural algebra
structures. Its linearity follows from `Over.w a`. The additive tensor map
`pullback M a` changes the first tensor factor by this ring map and fixes the
coefficient section.

The main compatibility lemma `toSection_natural` states

`toSection M W (pullback M a z) =
  RelativeUnipotent.sectionPullback M a (toSection M T z)`.

This compatibility holds without affineness or quasi-coherence assumptions.
The right side uses exactly the module-pullback composition and
equal-morphism comparisons from `RelativeUnipotent.Basic`. First,
`sectionPullback_pullbackSection` proves compatibility on a pulled-back
coefficient section: rewrite actual section pullback as the adjunction-unit
section map on top opens, then apply the published
`pullbackComp_hom_sectionPullbackLE` and
`pullbackCongr_hom_sectionPullbackLE`. The supporting addition, zero and
scalar identities follow from the semilinear adjunction-unit map and the
linearity of these comparisons. Tensor induction then proves naturality.
For affine `S`, `T.left` and `W.left` and quasi-coherent `M`,
`equiv_symm_natural` gives the corresponding formula for inverse coordinates.

The construction does not assert finite projectivity of global sections,
invertibility on arbitrary nonaffine test schemes, cocycle or torsor
vanishing, or affine Levi existence. It supplies the affine section comparison
needed to use module-valued descent for actual vector-bundle additive groups.

Provenance is internal. The construction specializes
`Langlands.Scheme.Modules.pullbackTensorMap_bijective` from
`Langlands.AlgebraicGeometry.Modules.PullbackAffineSections` to top opens,
using the actual-section identification
`Langlands.SchemeModule.pullbackSection_eq_sectionPullback` from
`Langlands.AlgebraicGeometry.Modules.SectionPullbackBridge`. The new results
are formal consequences of those published constructions and the fixed
`RelativeUnipotent.sectionPullback` definition; no additional literature
assertion is introduced.
