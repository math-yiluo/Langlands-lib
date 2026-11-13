# The Hecke characters of a Galois type decomposition and their global relation

Author: Worker 5093. This is a supporting unit for task
`92a3d086-a5ad-476f-9fd9-aa9d4eaa3778`, which must prove
`Langlands.LocalFactor.NonabelianBrauer.KernelCompatibilityStatement`. In Deligne's global
argument (1973, proof of Lemma 4.12) the local relation among the characters `χ_g` of the
generators is lifted to a relation among Hecke characters `Λ_g` of global fields `𝕃_g`. For this
lift, each `Λ_g` is twisted by a global character `α` of the base field `k`, so that its local
behaviour can be controlled at finitely many auxiliary places. This unit puts the published
global relation `globalRelation` (module `Langlands.LocalFactor.BrauerKernel.GlobalRelation`) into
that Hecke-character form.

Everything is in `Langlands.LocalFactor.NonabelianBrauer`. Throughout, `D` is a
`GaloisTypeDecomposition F e z`, `K'/k` is a Galois extension of number fields, `θ` identifies
`Gal(K'/k)` with `Gal(K/F)`, `c` is a class family with restriction compatibility `h`, and
`globalField D k K' θ g` is the global field `𝕃_g` of a generator `g`.

## Definitions

- `generatorHecke D k K' θ g α t Θ` is the Hecke character `(α ∘ N_{𝕃_g/k}) · ‖·‖^t · Θ` of
  `𝕃_g`. Here `α` is a Hecke character of `k`, `t : ℂ`, and `Θ` is a Hecke character of `𝕃_g`.

## Results

- `comp_restrictionInclusion_mul_eq`: the restriction to `W_{K'/𝕃_g}` of the reciprocity
  character of `α · ‖·‖^t`, times the reciprocity character of `Θ`, is the reciprocity character
  of `generatorHecke D k K' θ g α t Θ`. Proof: the published
  `continuousReciprocityCharacter_comp_restrictionInclusion` applies, because
  `transferNormCompatibilityStatement` (proved in the Library) holds for every tower. Then
  `continuousReciprocityCharacter_mul` is used, together with `normComp_normPower`
  (`‖·‖^t ∘ N = ‖·‖^t`, from the unit `PlaceNorm`).
- `globalRelation_generatorHecke`: let `gs : Fin n ≃ z.support` enumerate the support of `z`.
  Suppose Hecke characters `Θ₁ g`, `Θ₂ g` have as reciprocity characters the inflated characters
  `globalCharacter D c k K' θ h g (D.θ_i g)`. Then for every Hecke character `α` of `k`,
  `Σ_i z(g_i) Ind_{W_{K'/𝕃_{g_i}}}([τ ∘ Λ₁ g_i] - [τ ∘ Λ₂ g_i]) = 0` in the continuous virtual
  group of `W_{K'/k}`, where `Λ_j g = generatorHecke D k K' θ g α (D.t_j g) (Θ_j g)`. Proof:
  apply `globalRelation` with `Ω τ` the reciprocity character of `α · ‖·‖^τ`. Rewrite each term
  with the previous item. Reindex the sum over `z.support` along `gs`.

- `globalCharacter_inclusion`: the inflated character `globalCharacter D c k K' θ h g χ` is
  trivial on the idele classes of `K'`. Proof: the restriction inclusion maps the inclusion of
  `a` over `𝕃_g` to the inclusion of `a` over `k` (`restrictionInclusion_inclusion`). That image
  lies in the kernel of the projection to `Gal(K'/k)` (`exact`). So the Galois character is
  evaluated at `1`.
- `globalCharacter_apply`: the value of `globalCharacter D c k K' θ h g χ` at `x` is `χ` at
  `θ` applied to the Galois projection of `x`, restricted to `k`. The membership in the Galois
  image is part of the statement. Proof: the restriction inclusion lands in the preimage of
  `globalSubgroup` (`range_restrictionInclusion_fixedField`). Its projection is the restricted
  projection (`projection_restrictionInclusion`).
- `generatorHecke_infiniteComponent`: let `K'` be totally real, let `α` have trivial infinity
  component (`HasPrescribedInfinityComponent 1`), and let the reciprocity character of `Θ` be an
  inflated character. Then `generatorHecke D k K' θ g α t Θ` has the archimedean components of
  `‖·‖^t`. Proof: the archimedean components are multiplicative. The component of `α ∘ N` is
  trivial (`normComp_infiniteComponent_eq_one`). The component of `Θ` is trivial by the unit
  `ArchimedeanTrivial` (`infiniteComponent_eq_one_of_isTotallyReal`), whose hypothesis is the
  previous item.

The indexing by `Fin n` matches the published product package `hasGlobalEquation_brauerProduct`.
