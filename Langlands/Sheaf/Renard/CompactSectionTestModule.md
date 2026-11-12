# Compact sections of a complex vector sheaf as a nondegenerate test module

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, II.2.5 Theorem and the first paragraph of
its proof, printed pp.39–40 / PDF pp.45–46, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The Theorem says that for every sheaf `M` of `C^∞_X`-modules, `M_c(X)` is a
nondegenerate `D(X)`-module, and that `M ↦ M_c(X)` is an equivalence onto
nondegenerate `D(X)`-modules. The proof's first paragraph: if `s ∈ M_c(X)`
and `U` is a compact open containing `Supp s`, then `χ_U` fixes `s`.
This file constructs the module, its nondegeneracy and the functor.
It does not state or prove the equivalence.

## Objects and sizes

`X : Type` carries a topology. A complex vector sheaf is
`VectorSheafScalars.VectorSheaf X`, Mathlib's
`TopCat.Sheaf (ModuleCat.{0} ℂ) (TopCat.of X)`. The compact sections are the
published `Langlands.Sheaf.CompactSupport.submodule F.presheaf`, unchanged:
global sections whose support (nonzero germs) is compact. `CompactSupport`
ties the space, coefficient ring and module carriers to one universe; since
`ℂ : Type`, this file works with `X : Type` and carriers in `Type`. The scalar
action of `VectorSheafScalars` is available at every universe, but it is not
generalized here. The test algebra is the published
`PointwiseTestAlgebra.Carrier X` (Renard's `D(X)`), and the target category is
the published `NondegenerateModuleCat.{0, 0}` of that algebra.

## Construction

- `testScalar` composes the published inclusion `PointwiseTestAlgebra.inclusion`
  into `LocallyConstant X ℂ` with Mathlib's `LocallyConstant.comapₐ` along the
  inclusion `topInclusion` of the largest open. It is a nonunital complex
  algebra map, and `testScalar f x = f x`.
- `Γgerm_smul` is the source formula `(f s)(x) = f(x) s(x)` on global germs;
  `support_smul_subset` follows from it.
- `testSmul` and the instance `testModule` define `f • s` as the
  `VectorSheafScalars` action of `testScalar f` on the original section `s`.
  The result has compact support, as a closed subset of the support of `s`.
  The nonunital module laws come from the ring-homomorphism laws of
  `testScalar` and the module laws of the locally constant action.
  `coe_testSmul` and `Γgerm_testSmul` record the formula.

## Nondegeneracy

`exists_compactOpen_superset` proves that in a space with a compact open
neighborhood basis every compact set lies in a compact open, using a finite
subcover by compact open neighborhoods.
`characteristic_smul_eq_self` is the source's step: if the support of `s` lies
in a compact clopen `V`, then the published `PointwiseTestAlgebra.characteristic`
of `V` fixes `s`. It compares germs: `1 • germ` on `V`, and outside `V` both
germs vanish because the point is outside the support.
`isNondegenerate` assumes `hX : Langlands.Topology.IsLocallyProfinite X`
(Hausdorff with a compact open neighborhood basis, Renard's t.d. spaces).
It takes a compact open containing the support, which is clopen because `X`
is Hausdorff, and uses the published `characteristicIdempotent`.

## Complex structure

`isScalarTower` proves `(c • f) • s = c • (f • s)` for the original complex
structure of the compact-section submodule. Therefore `complexModule_eq`
identifies the published canonical complex structure
`NondegenerateScalars.complexModule PointwiseTestAlgebra.isIdempotented` of
the nondegenerate module with the original complex structure of
`CompactSupport.submodule F.presheaf`, by the published
`NondegenerateScalars.module_eq_of_compatible`.

## Morphisms and the functor

`compactSectionMap φ` is the published `CompactSupport.map φ.hom`, with its
additive structure, and it commutes with the test action by
`VectorSheafScalars.app_smul`.
`compactSectionFunctor hX : VectorSheaf X ⥤ NondegenerateModuleCat.{0, 0}
(PointwiseTestAlgebra.Carrier X)` sends `F` to the bundled original carrier
with the proved nondegeneracy, and `φ` to `compactSectionMap φ`. The identity
and composition laws hold by definition. `compactSectionFunctor_map_hom` and
`compactSectionMap_eq_functor_map` show that the underlying maps are those of
the published `CompactSupport.functor`.

The inverse functor, the comparison maps and the equivalence are not
constructed or asserted here.

Worker 184 implements this unit for Task 5338.
