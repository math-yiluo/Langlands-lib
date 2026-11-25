# Compact cohomology vanishing for c-soft module sheaves

The theorem `Langlands.Cohomology.cSoftAcyclicity` proves the published proposition
`Langlands.Cohomology.CSoftAcyclicityStatement` without changing its definition.
For every universe `u`, locally compact Hausdorff `X : TopCat.{u}`, commutative
ring `R : Type u`, and `F : TopCat.Sheaf (ModuleCat.{u} R) X` satisfying the
existing `Langlands.Sheaf.CompactSoft.IsCSoft F`, it proves

```text
∀ q : ℕ, IsZero ((TopologicalDerivedSections.compactCohomology X R (q + 1)).obj F).
```

Here `compactCohomology` is the published right derived functor of the
germ-defined compact-section functor. The conclusion covers every positive
degree and has the original single universe parameter.

## Injective module sheaves are flasque

The supporting theorem `CompactSoft.isFlasque_of_injective` works on any
topological space; local compactness and separation are not required for this
step. Its proof adapts the free-representable argument of the published
`AbelianSheafFlasque.surjective_map_of_injective` from free abelian groups to
free `R`-modules.

For an open set `U`, write `L(U)` for the presheaf of free `R`-modules on the
representable presheaf `yoneda.obj U`. The free/forgetful adjunction and Yoneda
give a natural equivalence between presheaf morphisms `L(U) ⟶ F.obj` and
sections of `F` over `U`. The private definitions `freeYonedaEquiv` and
`freeYonedaEquiv_naturality` implement this equivalence and its compatibility
with restriction.

For an inclusion `V ⟶ U`, the map `L(V) ⟶ L(U)` is a monomorphism. Pointwise this
follows from injectivity of the map on representables and
`Finsupp.mapDomain_injective`. Sheafification preserves this monomorphism.
A section over `V` corresponds, by the two adjunctions, to a map from the
sheafification of `L(V)` to `F`. Injectivity of `F` extends that map across the
sheafified monomorphism. Naturality translates the extension back into a
section over `U` restricting to the original section. Thus every restriction
map is surjective, which is `F.IsFlasque`.

The theorem `CompactSoft.isCSoft_of_injective` then applies the published
`Langlands.Sheaf.CompactSoft.isCSoft_of_isFlasque`. Its regularity hypothesis
is supplied by the locally compact Hausdorff hypotheses. In particular, the
chosen injective sheaf `Injective.under F` is c-soft.

## Dimension shifting for compact sections

Set `T := Langlands.Sheaf.CompactSupport.functor`. The proof unfolds
`TopologicalDerivedSections.compactCohomology` to `T.rightDerived` and inducts
on `q`, generalizing the c-soft sheaf `F`. It uses the short exact sequence

```text
0 → F → Injective.under F → Q → 0,
```

where the first map is Mathlib's chosen injective embedding `Injective.ι F`
and `Q` is its cokernel. Monicity of the embedding and the universal cokernel
sequence give short exactness.

For degree one, the first part of the published `cSoftShortExact` shows that
`T(Injective.under F) ⟶ T(Q)` is an epimorphism. The natural isomorphism
`T.rightDerivedZeroIsoSelf` transports this to the map in degree-zero derived
functors. The connecting morphism

```text
δ : (T.rightDerived 0).obj Q → (T.rightDerived 1).obj F
```

is an epimorphism, since positive derived functors vanish on the injective
middle term. The preceding degree-zero epimorphism followed by `δ` is zero.
Cancelling that epimorphism shows `δ = 0`; an epimorphism equal to zero has
zero target. This proves the degree-one case.

For the induction step, the second part of `cSoftShortExact` shows that `Q`
is c-soft, since both `F` and the injective middle term are c-soft.
The induction hypothesis gives
`IsZero ((T.rightDerived (q + 1)).obj Q)`. Again injective acyclicity makes the
connecting morphism from that object onto
`(T.rightDerived (q + 2)).obj F` an epimorphism. An epimorphic image of a zero
object is zero, finishing the induction.

The connecting morphisms and their exactness are the published
`DerivedPlus.rightDerivedδ`,
`DerivedPlus.rightDerived_map_comp_δ`, and
`DerivedPlus.epi_rightDerivedδ_of_isZero` from
`Langlands.Cohomology.RightDerivedSequence`. The proof supplies
`HasDerivedCategory.standard` for the sheaf and module categories to use that
interface. These are choices of derived categories, not acyclicity premises.
Mathlib supplies enough injectives for the actual module-sheaf category and
`Functor.isZero_rightDerived_obj_injective_succ` supplies injective acyclicity.

## Provenance and scope

This is an internal derived proof from the published compact-section,
c-softness, and long-exact-sequence results. Its small free-module argument
is an adaptation of the published abelian-sheaf proof described above.
The literature correspondence belongs to the unchanged paired Markdown of
`Langlands.Cohomology.CompactSoft.Statement`; this file explains the implemented
dimension-shifting route.

The proof assumes only the hypotheses of `CSoftAcyclicityStatement`. It uses
the existing softness predicate, compact supports, and actual right derived
functors. The target statement and its imports are unchanged. The two supporting
injective-sheaf theorems are proved in this module. The result concerns ordinary
topological module sheaves; it asserts no comparison with smooth, equivariant,
or analytic cohomology.
