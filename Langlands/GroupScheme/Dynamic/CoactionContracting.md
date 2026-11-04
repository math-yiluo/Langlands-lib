# Contracting points of the coaction of a cocharacter

This module is an internal helper for the proof of Conrad--Gabber--Prasad,
*Pseudo-reductive groups* (2nd ed., 2015), Proposition C.1.6. It connects the
Library's coordinate description of dynamic subgroups
(`Langlands.GroupScheme.Dynamic.Representability`,
`Langlands.GroupScheme.Dynamic.CoactionGrading`) to the graded-algebra language
of `Langlands.CommutativeAlgebra.GradedDVRIntegrality`. No external result is
used; everything is derived from the cited Library lemmas.

Setting: `k` is a field, `G = Corepresented.groupScheme F e` is a corepresented
affine group over `Spec k` with coordinate `k`-algebra `B`, and
`χ : 𝔾_m ⟶ G` is a cocharacter. `Corepresented.coaction χ : B → B[T, T⁻¹]` is
the conjugation coaction and `Corepresented.counit e : B → k` the counit.

- `isGrading_coaction χ`: the coaction is an `IsGrading`. The three fields are
  the Library lemmas `coaction_algebraMap`, `sum_coeff_coaction` and
  `coaction_coeff_coaction`.
- `counitAlgHom e : B →ₐ[k] k`: the counit as a `k`-algebra map. Its
  compatibility with scalars comes from `algebraMap_comp_pointRing` for the
  identity point. `counitAlgHom_apply` unfolds it.
- `counit_coeff_coaction χ b n`: `ε((c b)ₙ) = ε b` when `n = 0`, and `0`
  otherwise. Proof: the identity point lies in the centralizer `Z_G(χ)`, so by
  the Library's `mem_centralizer_iff` the counit kills every coefficient of
  `c(b) - C b`.
- `pointAlgHom x : B →ₐ[k] A`: for a `k`-algebra `A` and a point `x` of `G`
  over `Spec A` (structure map `Spec A → Spec k`), the classifying ring map
  `pointRing x`, made into a `k`-algebra map using `algebraMap_comp_pointRing`.
  `pointAlgHom_apply` unfolds it.
- `isContracting_pointAlgHom_iff χ x`: `IsContracting (coaction χ) ε
  (pointAlgHom x)` holds iff `x ∈ U_G(χ)`. This is the Library's
  `mem_unipotent_iff`. The second condition there, `x((c b)₀ - ε b) = 0`, is
  rewritten as `x((c b)₀) = ε b`, using that `x` is a `k`-algebra map.
