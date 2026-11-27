# Formal degrees on the central quotient of GL_n

Lean module: `Langlands.BaseChange.CentralQuotientFormalDegree`.

## The predicate

For a topological group `G`, a measure `μ` on the central quotient `G ⧸ Z(G)`, a complex
representation `π` of `G` on `W` and a real number `d`,
`IsCentralFormalDegree μ π d` says:

- `0 < d`, and
- for all vectors `v₁ v₂ : W` and smooth functionals `ℓ₁ ℓ₂ : SmoothDual π` there is a function
  `s` on `G ⧸ Z(G)` with `s(gZ) = ℓ₁(π(g) v₁) ℓ₂(π(g⁻¹) v₂)` for every `g`, which is
  `μ`-integrable with

  `∫ s dμ = d⁻¹ ℓ₂(v₁) ℓ₁(v₂)`.

These are the Schur orthogonality relations of J.-L. Waldspurger, *La formule de Plancherel
pour les groupes p-adiques, d'après Harish-Chandra*, J. Inst. Math. Jussieu 2 (2003), III.1 (3),
printed p. 265 (PDF p. 31), with `A_G` replaced by the full center: there the integral
`I(v₁, v̌₁, v₂, v̌₂) = ∫ ⟨π(g) v₁, v̌₁⟩ ⟨v₂, π̌(g) v̌₂⟩ dg` equals
`d(π)⁻¹ ⟨v₁, v̌₂⟩ ⟨v₂, v̌₁⟩`, and `⟨v₂, π̌(g) v̌₂⟩ = v̌₂(π(g⁻¹) v₂)`. So
`IsCentralFormalDegree μ π d` says that `d` is the formal degree of `π` for `μ`. The function
`s` is determined by its values on cosets, so the existential quantifier only names it.

## Existence for GL_n

`centralQuotient_isInvInvariant` shows that every Borel Haar measure on
`GL_n(F) ⧸ Z` is invariant under inversion, for a nonarchimedean local field `F`. The group
`GL_n(F)` is Hausdorff, locally compact and second countable, and its center is closed (it is
the centralizer of the whole group). Hence the quotient is locally compact and second
countable, Haar measures on it are regular, `GeneralLinear.haar_centralQuotient_isMulRightInvariant`
gives right invariance, and `isInvInvariant_of_isMulRightInvariant` gives inversion invariance.

`exists_isCentralFormalDegree` proves: if `π` is a representation of `GL_n(F)` with
`IsSquareIntegrable π` and `π.IsIrreducible`, then for every Borel Haar measure `μ` on the
central quotient there is `d` with `IsCentralFormalDegree μ π d`. The proof converts the
square-integrability to the central-subgroup form with
`isSquareIntegrableModCentralSubgroup_center_iff`, takes the scalar action of the center from
the unitary central character in `IsSquareIntegrable`, and the compact open subgroups from
`LevelZero.compactOpen_cofinal`. Then `d` is `HarishChandraSchwartz.formalDegree`; its
positivity is `formalDegree_pos`, the function `s` is `orthogonalityIntegrand`, its
integrability is `integrable_orthogonalityIntegrand`, and the value of the integral is
`orthogonalityIntegral_eq_formalDegree`.

Literature ID `waldspurger-2003-plancherel`, SHA-256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
