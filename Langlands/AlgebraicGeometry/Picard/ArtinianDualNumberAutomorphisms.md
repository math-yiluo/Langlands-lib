# Actual automorphisms in Artinian dual-number Picard fibres

This internal construction composes the actual pointed equivalence in
`ArtinianDualNumberComparison` with the actual pointed automorphism
calculations in `DualNumberPointedDeformations` and
`DualNumberInfinitesimalAutomorphisms`. The module and finiteness
consequences use `FieldGlobalFunctions` and `DerivedSections`.
No additional deformation-existence or representability theorem is used.

Fix a commutative ring `k : Type u`, a field `K : Type u` with its
specified `k`-algebra structure, and an actual scheme morphism
`f : X → Spec k`. Let `M` be any actual line bundle on
`residueSpace f = Spec K ×_k X`, and let `A` be an object of the actual
pointed deformation groupoid over `ArtinianTest.dualNumbers k K`.
Its chosen reduction identification with `M` is part of this object.

`autEquiv` is the automorphism-group equivalence induced by the fully
faithful functor of `pointedEquivalence`. Its arrow formulas
`autEquiv_apply` and `autEquiv_bundle` retain ordinary pullback of the
actual bundle automorphism along `spaceIso f`. Composing with the
published pointed-automorphism kernel equivalence gives `autKernelEquiv`;
`autKernelEquiv_val` identifies its underlying automorphism with that
same ordinary pullback. The target is the actual kernel of reduction
along the zero section, rather than a separately specified abstract group.

`autGlobalFunctionsEquiv` identifies the original group `Aut A` with
the multiplicative notation for the additive group of actual global
functions on the residue fibre. The formula
`autGlobalFunctionsEquiv_formula` identifies the pulled-back
automorphism with the scalar unit `1 + ε a`, including the existing
top-open identification. This proves uniqueness of its coefficient
without choosing a trivialization of either bundle.

`scalePullbackComparison` combines ordinary pullback composition
comparisons with the proved actual square `scale_spaceIso`.
Its component on the bundle of `A` is `scaleBundleComparison`.
The naturality lemma states that this comparison intertwines actual
Artinian restriction of a pointed automorphism along
`ArtinianTest.dualScale k K c` with ordinary pullback along epsilon
scaling on the residue-fibre thickening. Its proof is ordinary
naturality after the published restriction and kernel arrow formulas.
Combining it with `pullback_infinitesimalAutEquiv` proves
`restrictAut_coefficient`: the unique coefficient becomes
`baseSectionMap (residueStructure f) ⊤ c * a`. The target automorphism
acts on the actually pulled-back bundle, with the displayed coherence
comparison. Every `c : K`, including zero, is allowed.

`artinianAutCommGroup` proves commutativity for the existing composition
law on `Aut A` using injectivity of its coefficient equivalence.
`autAddEquiv` expresses the same group in additive notation.
`artinianAutSMul` acts on the unique global-function coefficient;
`autAddEquiv_smul` proves compatibility. `Function.Injective.module`
then supplies the module laws while retaining automorphism composition
as addition. `autLinearEquiv` packages this coefficient map linearly.

`autH0LinearEquiv` composes that linear equivalence with the inverse
zeroth-derived-cohomology comparison, giving actual derived relative
structure-sheaf `H⁰` on the residue fibre. If the original `f` is proper,
its actual base change `residueStructure f` is proper, and
`finiteDimensional_artinianAut` transfers finite dimensionality of
actual global functions along the inverse coefficient equivalence.

The basic comparisons and module need no properness, separatedness or
quasi-compactness assumption. Arbitrary universe `u`, imperfect fields
and empty schemes are retained. No splitting or `K`-algebra structure is
required of general Artinian tests. This contribution computes
automorphisms in the particular actual dual-number pointed fibre.
Formal versality, effectivity, algebraization, openness of versality
and existence of the smooth scheme atlas remain further obligations.
