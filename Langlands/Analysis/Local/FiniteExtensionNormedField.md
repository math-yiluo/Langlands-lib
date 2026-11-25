# The spectral norm of a finite extension of a nonarchimedean local field

`Langlands.Analysis.Local.FiniteExtensionNormedField`. Namespace `Langlands.LocalGalois`.

For a nonarchimedean local field `F` and a finite field extension `E` of `F` carrying the module
topology, the file gives `E` a nontrivially normed field structure whose topology is the given
topology of `E` definitionally, whose norm is Mathlib's spectral norm `spectralNorm F E`, and for
which `F` (normed by `LocalGalois.localNormedField F`) acts isometrically. It is the junction
between the Library's statements, where `E` carries `IsModuleTopology F E`, and estimates by
absolute values on `E`.

## Hypotheses

`F : Type u` with `[Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]`;
`E : Type v` with `[Field E] [Algebra F E] [FiniteDimensional F E] [TopologicalSpace E]
[IsModuleTopology F E]`. Neither `E / F` normal nor separable is assumed.

## Statements

- `spectralNorm_topology_eq`: with `localNormedField F` (and its ultrametric instance),
  `(spectralNorm.normedField F E).toUniformSpace.toTopologicalSpace = ‹TopologicalSpace E›`.
- `finiteExtensionNormedField F E : NontriviallyNormedField E` (a definition, to be installed as a
  local instance): Mathlib's `spectralNorm.nontriviallyNormedField F E` with its metric space
  replaced by `MetricSpace.replaceTopology` along `spectralNorm_topology_eq`.
- `finiteExtensionNormedField_topology`: its topology is `‹TopologicalSpace E›`, by `rfl`.
- `finiteExtensionNormedField_norm`: its norm is `spectralNorm F E`, by `rfl`.
- `finiteExtensionNormedField_ultrametric : IsUltrametricDist E`.
- `finiteExtensionNormedAlgebra F E : NormedAlgebra F E` (a definition) for `localNormedField F`.
- `finiteExtensionNormedField_norm_algebraMap`: `‖algebraMap F E x‖ = ‖x‖`;
  `finiteExtensionNormedField_norm_natCast`: `‖(m : E)‖ = ‖(m : F)‖`.
- `finiteExtensionNormedField_norm_algEquiv`: `‖σ x‖ = ‖x‖` for every `σ : E ≃ₐ[F] E`.
- `finiteExtensionNormedField_completeSpace : CompleteSpace E`,
  `finiteExtensionNormedField_properSpace : ProperSpace E`.

The statements about the structure are written with `letI := finiteExtensionNormedField F E` (and
`letI := localNormedField F` where the norm of `F` occurs).

## Proofs

- Topology. With `localNormedField F` the field `F` is complete; a finite-dimensional normed space
  over a complete nontrivially normed field carries the module topology (Mathlib's
  `isModuleTopologyOfFiniteDimensional`); the given topology is the module topology by
  hypothesis; both are `moduleTopology F E` (`eq_moduleTopology`).
- Norm facts: Mathlib's `isNonarchimedean_spectralNorm`, `spectralNorm_extends`,
  `spectralNorm_eq_of_equiv` (automorphisms are isometries: the spectral norm depends only on the
  minimal polynomial), multiplicativity from `spectralNorm.normedField` (which needs `F` complete).
- Completeness and properness: `FiniteDimensional.complete`, `FiniteDimensional.proper` over the
  proper field `F` (`ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace`).

## Declarations, in order

private `normed_topology_eq_moduleTopology`; `spectralNorm_topology_eq`;
`finiteExtensionNormedField`; `finiteExtensionNormedField_topology`;
`finiteExtensionNormedField_norm`; `finiteExtensionNormedField_ultrametric`;
`finiteExtensionNormedAlgebra`; `finiteExtensionNormedField_norm_algebraMap`;
`finiteExtensionNormedField_norm_natCast`; `finiteExtensionNormedField_norm_algEquiv`;
`finiteExtensionNormedField_completeSpace`; `finiteExtensionNormedField_properSpace`.

## Literature

J. Neukirch, *Algebraic Number Theory*, Grundlehren 322, Springer (1999), Chapter II, §4:
(4.8) Theorem, p. 131 (a valuation of a complete field extends uniquely to a finite extension, by
`|α| = |N_{L|K}(α)|^{1/n}`, and `L` is complete), and (4.9) Proposition, pp. 132–133 (all norms
on a finite-dimensional vector space over a complete field are equivalent to a maximum norm, so
`K^n → V` is a homeomorphism). Mathlib's spectral norm is the unique such extension
(`spectralNorm_unique_field_norm_ext`); the file uses only its listed properties.

## Source and licence

No text of the `riemann-hypothesis` repository. The source gives `E` its own valuation
(`ValuativeRel E`, `IsNonarchimedeanLocalField E`, `ValuativeExtension k E`); this file is the
replacement for that hypothesis in the Library's setting.
