# The comparison map to the reductive quotient, and the kernel condition

This module is an internal helper for the proof of Conrad--Gabber--Prasad,
*Pseudo-reductive groups* (2nd ed., 2015), Proposition C.1.6. It turns the data
of that proof over an algebraic closure `Ω` into the hypotheses `φ`/`hφ` and
`hker` of `Corepresented.exists_extension_of_comparison`
(`Langlands.GroupScheme.Dynamic.ComparisonExtension`). It is derived from the
Library's `HomogeneousQuotientComparison`, `Dynamic.Functoriality`, kernel API
(`mem_range_kernelι_iff`) and the coordinate lemmas of `BaseChangeCoordinates`.

Notation: `G = Spec B` is corepresented over a field `k`, `Ω` a field with
`Algebra k Ω`, `π : G_Ω ⟶ H` a homomorphism of `Ω`-groups, and `bcPoint` as in
`BaseChangeCoordinates`.

- `exists_comparison_desc χ q hfΩ q₀ hf₀`: suppose the base change `q_Ω` of
  `q : G ⟶ Q` is flat, surjective and quasi-compact, with fibers the right
  cosets of `P(χ_Ω)` (`hfΩ`). Suppose `q₀ : H ⟶ Q₀` has fibers the right cosets
  of `P_H(χ_Ω ≫ π)` (`hf₀`). Then there is `φ : Q_Ω ⟶ Q₀` with
  `q_Ω ≫ φ = π ≫ q₀`. Proof: `q_Ω` is an effective epimorphism (Mathlib's fpqc
  instance), so `HomogeneousQuotientComparison.desc` applies. Constancy on
  fibers holds because `π` carries `P(χ_Ω)` into `P_H(χ_Ω ≫ π)`
  (`parabolic_le_comap`).
- `bcPoint_counit`: the base change of the counit is the identity point of
  `G_Ω` (compare classifying maps through the pullback point equivalence).
- `rationalPoint a` and `pointRing_rationalPoint`: the point of `G` over
  `Spec k`, with identity structure map, given by a `k`-point `a : B → k`, and
  its classifying map `a`.
- `hker_of_kernel ν i hπ hc`: suppose the kernel of `π` has the same points as
  a subgroup `i : U ⟶ G_Ω` (`hπ`). Suppose also (`hc`) that any `k`-point `u`
  of `U_G(ν)` whose base change to `Ω` is the image of an `Ω`-point of `U` is
  trivial. Then every contracting `k`-point `a` of `B` with `π(a_Ω) = π(ε_Ω)` is
  the counit `ε`. Proof:
  - `a` gives `u = rationalPoint a ∈ U_G(ν)`, by the Library's
    `mem_unipotent_iff`;
  - by `bcPoint_counit`, `π(a_Ω) = 1`, so `a_Ω` lies in the kernel of `π`
    (`mem_range_kernelι_iff`) and hence comes from an `Ω`-point `y` of `U`;
  - after identifying `Spec Ω` over itself with `testOver Ω Ω`, the base change
    of `u` is the image of `y`, so `hc` gives `u = 1`;
  - comparing classifying maps (`pointRing_one`) gives `a = ε`.
  In the C.1.6 argument `hc` is an instance of the statement
  `PseudoReductiveRationalUnipotentPointStatement` proposed in TaskHub
  statement task `78895528-a2ff-490b-a6dd-816ced8667eb` (not yet in the
  Library), for `U` the unipotent radical of `G_Ω`.
