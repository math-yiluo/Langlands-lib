# The original-module comparison with compact sections of the projector sheaf

The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French version dated 9 July 2026, II.2.5, proof of the Theorem, printed
pp.39–40 / PDF pp.45–46, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The inverse functor sends a nondegenerate `D(X)`-module `M` to the sheaf
`M(U) = χ_U · M` on compact opens. The final paragraph of the proof says
`M_c(X) = ⋃_U M(U) = ⋃_U χ_U · M = M` because `M` is nondegenerate. In the
construction, this identification sends `m` to the global section whose value
on each compact open `U` is `χ_U · m`. This file constructs that map as a
morphism of nondegenerate test modules `M ⟶ Γc(P M)` and proves its
naturality. It does not prove that it is an isomorphism; that is a separate
statement for a later proof task.

## Objects and sizes

`X : Type` carries a topology with `hX : Langlands.Topology.IsLocallyProfinite X`.
`M` ranges over the published `NondegenerateModuleCat.{0, 0}` of the pointwise
test algebra `PointwiseTestAlgebra.Carrier X`. `P` is Worker 188's
`ProjectorVectorSheaf.functor.{0, 0} hX` with `P M = sheaf hX M.property`.
`Γc` is `CompactSectionTestModule.compactSectionFunctor hX`: the published compact
sections `CompactSupport.submodule (P M).presheaf` with the test action through
locally constant scalars. Everything is at `Type` because the published
`CompactSupport` ties the universes.

The underlying complex-linear map is Worker 188's published
`ProjectorVectorSheaf.compactOriginal hX hM`. Its value at `m` is the global
section `originalSection ⊤ m` with components `χ_U · m`. It is compactly
supported because some compact-open `χ_K` fixes `m`. Its naturality is
`ProjectorVectorSheaf.compactOriginal_naturality`.

## Test-linearity

`compactOriginal` must intertwine the original action `f • m` with the action
on compact sections from `CompactSectionTestModule`. The latter is
`testScalar f • s` for the `VectorSheafScalars` gluing action. The proof
compares germs at each point `x`:

- `exists_compactOpen_eq`: a test function `f` is constant `f x` on some
  compact open neighborhood `W` of `x`, from local constancy and the compact
  open neighborhood basis.
- `test_mul_eq`: for compact opens `U ⊆ W`, `χ_U * f = c • χ_U` in the test
  algebra, checked pointwise on indicators.
- `originalSection_test_smul`: over `W`, the section of `f • m` equals `c`
  times the section of `m`. The complex structure here is the canonical one of
  the projector sheaf, componentwise `NondegenerateScalars.complexModule`.
  The components are `χ_U • (f • m) = (χ_U f) • m = (c χ_U) • m = c • (χ_U • m)`.
  The last step is the published `NondegenerateScalars.smul_action`.
- `Γgerm_originalSection_test_smul`: hence the global germ of
  `originalSection ⊤ (f • m)` at `x` is `f x` times that of `originalSection ⊤ m`.
  It is read through the restriction to `W`, with the published
  `originalSection_restrict`.
- `compactOriginal_test_smul`: with the germ formula
  `VectorSheafScalars.germ_smul` for the test action, both sides have equal
  germs everywhere, so they are equal (`VectorSheafScalars.ext_germ`).

## The comparison morphisms

- `moduleComparisonHom hX M` is the `NonUnitalModuleHom` with additive part
  `compactOriginal` and the test-linearity above.
  `moduleComparisonHom_component` states its literal compact-open formula:
  the component at a compact open `U` of the image of `m` is
  `action hX M U m`, i.e. `χ_U · m`.
- `moduleComparison hX M : M ⟶ (ProjectorVectorSheaf.functor hX ⋙
  compactSectionFunctor hX).obj M` is the morphism of nondegenerate test
  modules. It is automatically complex-linear for the canonical structures.
- `moduleComparisonNat : 𝟭 _ ⟶ ProjectorVectorSheaf.functor hX ⋙
  compactSectionFunctor hX` is the natural transformation. Naturality is
  `compactOriginal_naturality`.

No inverse, isomorphism or equivalence is constructed or assumed here.

Worker 184 implements this unit for Task 5338. Worker 188 designed the
module-side comparison: `compactOriginal`, its support and naturality
proofs, and the germ-formula route. Those published pieces are imported
unchanged.
