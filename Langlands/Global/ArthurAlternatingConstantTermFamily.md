# Constant terms of extended norm-one functions

Let `G` be a connected reductive group over a number field `F` with maximal split torus `i`,
generic cocharacter `ν`, and let `P ⊆ Δ₀` index a standard parabolic subgroup. Let `ψ` be a
continuous function on `G(𝔸_F)¹` that is left invariant under the rational norm-one points, and
`normOneExtension hG ψ` its continuous left `G(F)`-invariant extension
(`Langlands.Global.AdelicNormOneExtension`). The module
`Langlands.Global.ArthurAlternatingConstantTermFamily` records the properties of the constant term
`constantTerm F i ν P (normOneExtension hG ψ)` along the unipotent radical of `P` that are used for
families. Each result applies the corresponding statement for a closed smooth connected unipotent
subgroup to the standard radical, whose geometry is `Standard.parabolicStructure`. All declarations
are in `Langlands.Global.ArthurTruncation`.

- `continuous_constantTerm_normOneExtension`: the constant term is continuous
  (`continuous_subgroupConstantTerm_of_unipotentInvariant`).
- `measurable_constantTerm_normOneExtension_family`: for a jointly measurable family `ψ o` of such
  functions, `(o, x) ↦ constantTerm F i ν P (normOneExtension hG (ψ o)) x` is jointly measurable
  (`measurable_subgroupConstantTerm_family`).
- `isNormOnePathDerivative_constantTerm_normOneExtension`: if the extensions of `ψ` and of `ψ' l`
  satisfy `IsNormOnePathDerivative At`, so do their constant terms
  (`isNormOnePathDerivative_subgroupConstantTerm`).
- `exists_lintegral_constantTerm_normOneExtension_le`: there is a compact set `C ⊆ G(𝔸_F)¹` (points
  of the radical) such that for every family over an arbitrary measure space and every `x ∈ G(𝔸_F)¹`,
  `∫_Ω ‖constantTerm F i ν P (normOneExtension hG (ψ o)) x‖ dm ≤ sup_{h ∈ C} ∫_Ω ‖ψ o (h x)‖ dm`
  (`exists_lintegral_enorm_subgroupConstantTerm_le`; `h x` is a norm-one point, where the extension
  is `ψ`).
