# Proof: the original-module comparison is an isomorphism

Worker 109 implemented this proof for Task 5533. The entry theorem is
`Langlands.Sheaf.Renard.ModuleProjectorComparison.moduleComparisonIsIso :
ModuleComparisonIsIso`. It proves the published statement
`ModuleProjectorComparison.ModuleComparisonIsIso` from
`Langlands/Sheaf/Renard/ModuleProjectorComparisonStatement.lean`, unchanged. For
every `X : Type` with a topology satisfying
`Langlands.Topology.IsLocallyProfinite X`, and every
`M : NondegenerateModuleCat.{0, 0} (PointwiseTestAlgebra.Carrier X)`, the
published comparison
`moduleComparison hX M : M ⟶ (ProjectorVectorSheaf.functor hX ⋙ compactSectionFunctor hX).obj M`
is an isomorphism (`IsIso`) in `NondegenerateModuleCat`. No premise is added:
the proof assumes no compactness, countability or nonemptiness of `X`, and no
inverse functor law, comparison certificate or equivalence.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French version
dated 9 July 2026, II.2.5, final paragraph of the proof of the Theorem, printed
p.40 / PDF p.46, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. PDF pp.45–46
were read for this proof. Starting from a nondegenerate `D(X)`-module `M` and
its sheaf `M(U) = χ_U · M`, the source writes
`M_c(X) = ⋃_{U ∈ T_c} M(U) = ⋃_{U ∈ T_c} χ_U · M = M` "car `M` est non
dégénéré". The source gives no further detail. The Lean proof makes the
identification explicit through the published comparison map: the map is
injective and surjective, and a bijective morphism of nondegenerate modules is
an isomorphism.

## Implemented proof

The file `ModuleProjectorComparisonProof.lean` contains five declarations.

- `isIso_homMk_of_bijective`: for any nonunital ring `A`, any nondegenerate
  modules `M N : NondegenerateModuleCat.{u, v} A` and any test-linear map
  `f : NonUnitalModuleHom A M.obj N.obj` whose underlying function is bijective,
  the full-subcategory morphism `ObjectProperty.homMk f : M ⟶ N` is an
  isomorphism. The inverse is built by hand. `AddEquiv.ofBijective` gives an
  additive equivalence `e`. Its inverse `e.symm` commutes with the action
  because `f` is injective and
  `f (e.symm (a • n)) = a • n = a • f (e.symm n) = f (a • e.symm n)`, by
  `NonUnitalModuleHom.map_smul`. The resulting `NonUnitalModuleHom` is wrapped
  with `ObjectProperty.homMk`. Both composites are identities by
  `ObjectProperty.hom_ext`, `NonUnitalModuleHom.ext` and the two inverse laws of
  `e`. The lemma uses no concrete-category structure, since
  `NonUnitalModuleCat` has none in the Library.
- `compactOriginal_injective`: let `M` be an additive group with a nondegenerate
  action `hM` of `PointwiseTestAlgebra.Carrier X`, and give it the canonical
  complex structure `originalModule hM`. Then the published complex-linear
  comparison `ProjectorVectorSheaf.compactOriginal hX hM` is injective. Suppose
  `compactOriginal m = compactOriginal n`. The published
  `exists_compactOpen_action_eq` gives a compact open `K` with
  `χ_K · (m - n) = m - n` (this is where nondegeneracy enters). The component of
  `compactOriginal m` at the compact open `K ⊆ ⊤` is `action hX M K m = χ_K · m`
  by definition (`compactOriginal_component` holds by `rfl`). Equal sections
  have equal components, so `χ_K · m = χ_K · n`. Hence
  `m - n = χ_K · (m - n) = χ_K · m - χ_K · n = 0`, using `map_sub` for the
  additive map `action hX M K`.
- `compactOriginal_surjective`: the same comparison is surjective. Let `t` be a
  compactly supported global section of `ProjectorVectorSheaf.sheaf hX hM`. Its
  support is compact. The published
  `CompactSectionTestModule.exists_compactOpen_superset`, applied to the
  compact-open neighbourhood basis `hX.2`, gives a compact open set `V`
  containing it. Call `K` the corresponding compact open. Put `m = t_K`, the
  component of `t` at `K`, an element of `Value hX M K = χ_K · M`. The
  underlying sections `originalSection ⊤ m` and `t` are compared through their
  germs at each `x`, by `VectorSheafScalars.ext_germ` for the sheaf
  `ProjectorVectorSheaf.sheaf hX hM`.
  - If `x ∈ K`, both germs are germs at `x` of the restrictions to `K`
    (Mathlib's `TopCat.Presheaf.Γgerm_res_apply`). The two restrictions agree by
    the published `ProjectorVectorSheaf.section_ext`. On a compact open
    `U ⊆ K`, the restricted original section has component `χ_U · t_K`. The
    restriction of `t` has component `t_U`. These agree by the compatibility of
    the family `t` (`section_compatible` for `U ⊆ K`, the restriction map being
    `s ↦ χ_U · s`).
  - If `x ∉ K`, both germs vanish. The germ of `t` vanishes because `x` lies
    outside its support, which is contained in `K`; `CompactSupport.support` is
    the set of points with nonzero germ. The germ of `originalSection ⊤ m`
    vanishes because the published `support_originalSection_subset` puts its
    support in `K`, as `χ_K · m = m` (`value_fixed`, since `m ∈ χ_K · M`).

  The Lean proof thus avoids the decomposition `t_U = χ_{U∩K} t_U + χ_{U∖K} t_U`
  of the route sketched in the task. Germs separate sections of a sheaf, so the
  agreement on `K` and the vanishing off `K` are enough.
- `moduleComparisonHom_bijective`: the published `moduleComparisonHom hX M` has
  underlying function `compactOriginal hX M.property`. It is therefore bijective
  by the two previous lemmas, applied to `M.obj` and `M.property`.
- `moduleComparisonIsIso`: introduce `X`, its topology, `hX` and `M`. The
  published `moduleComparison hX M` is by definition
  `ObjectProperty.homMk (moduleComparisonHom hX M)`, so
  `isIso_homMk_of_bijective` applies, with the target object
  `(ProjectorVectorSheaf.functor.{0, 0} hX ⋙ compactSectionFunctor hX).obj M`
  given explicitly.

The proof imports only
`Langlands.Sheaf.Renard.ModuleProjectorComparisonStatement`, which brings in the
published constructions, and it edits no Library file. A development check of
`moduleComparisonIsIso` compiled with no errors or warnings. It reported only
the standard axioms `propext`, `Classical.choice` and `Quot.sound`.
