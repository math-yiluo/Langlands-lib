# Integrality of dynamic unipotent points through a comparison homomorphism

This module is an internal helper for the proof of Conrad--Gabber--Prasad,
*Pseudo-reductive groups* (2nd ed., 2015), Proposition C.1.6. It packages the
step of that proof where a point of `U_G(λ)` over the fraction field is shown to
be integral by comparing with the reductive quotient over an algebraic closure.
CGP argue through root groups. Here the step is derived from
`CommutativeAlgebra.GradedDVRIntegrality.integral_of_contracting_tensor` and the
coordinate lemmas of `Dynamic.BaseChangeCoordinates` and
`Dynamic.BaseChangeComparison`. The statement is not quoted from the source.

- `classifying_bcPoint_includeRight φ m`: for `φ : B →ₐ[k] A`, the classifying
  map of the base change of the point `φ` over `Ω ⊗[k] A` is `Ω ⊗ φ`.
- `classifying_bcPoint_ofId a m`: for a `k`-point `a : B →ₐ[k] k`, the
  classifying map of its base change over `Ω` is `Ω ⊗ a` followed by
  `Ω ⊗[k] k ≅ Ω`.
  Both are checked on pure tensors.

## `integral_of_baseChange_comparison`

Setting: `G = Spec B` is a corepresented affine group over `k`, with `B` a
finitely generated `k`-algebra. `ν` is a cocharacter, `Ω` a field extension of
`k`, and `π : G_Ω ⟶ H` a homomorphism to an affine `Ω`-group. `R : Type u` is a
DVR over `k` whose residue field is geometrically reduced over `k`.

Hypotheses:
- (`hker`) If a contracting `k`-point `a` of `B` satisfies
  `π(a_Ω) = π(ε_Ω)` (as points over `Spec Ω`), then `a = ε`.
- (`hrat`) Every nontrivial finitely generated geometrically reduced
  `k`-algebra in `Type u` has a `k`-point.
- `u` is a point of `G` over `Spec (Frac R)` lying in `U_G(ν)`.
- (`hint`) For every function `f` on `H`, the value of `f` at `π(u_Ω)` lies in
  the image of `Ω ⊗[k] R → Ω ⊗[k] Frac R`. Here `u_Ω` is the base change of `u`,
  a point over `Spec (Ω ⊗[k] Frac R)`.

Conclusion: every value `(pointAlgHom u) b` lies in the image of `R`.

Proof as implemented. Apply `integral_of_contracting_tensor` with test set
`M = range (comparisonMap π)`:
- the point `pointAlgHom u` is contracting by `isContracting_pointAlgHom_iff`;
- `M` is stable under the base-changed weight components by
  `lTensor_weightPart_comparisonMap`;
- the kernel hypothesis: if `Ω ⊗ a` and `Ω ⊗ ε` agree on `M`, then by
  `pointRing_comp_eq` and `classifying_bcPoint_ofId` the points `π(a_Ω)` and
  `π(ε_Ω)` have the same classifying map, hence are equal, and `hker` applies;
- integrality on `M`: by `pointRing_comp_eq` and
  `classifying_bcPoint_includeRight`, the value of `(Ω ⊗ u)` at
  `comparisonMap π f` is the value of `f` at `π(u_Ω)`, which is integral by
  `hint`.

## `exists_point_of_baseChange_comparison`

Under the same hypotheses, there is a point `uR` of `G` over `Spec R` (over
`Spec k`) that lies in `U_G(ν)` and restricts to `u` along
`Spec (Frac R) → Spec R`. The restriction morphism is
`Over.homMk (Spec.map (R → Frac R))`, and `specMap_algebraMap_fractionRing`
supplies its compatibility with the structure maps.

Proof as implemented. By `integral_of_baseChange_comparison`, `pointAlgHom u`
takes values in the image of the injective map `R → Frac R`. Restricting the
codomain and composing with the inverse of `AlgEquiv.ofInjective` gives
`ξR : B →ₐ[k] R`, with `ξR` followed by `R → Frac R` equal to `pointAlgHom u`.
Take `uR = ofAlgHom ξR`. `ξR` is contracting because `pointAlgHom u` is, and
`R → Frac R` is injective; so `uR ∈ U_G(ν)` by `isContracting_pointAlgHom_iff`.
The restriction of `uR` has the same classifying map as `u`, hence equals `u`
(`hom_ext_of_pointRing`).
