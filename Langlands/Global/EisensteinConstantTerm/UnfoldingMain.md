# Stabilizers, the inner identity and conjugated lattices

Module `Langlands.Global.EisensteinConstantTerm.UnfoldingMain`, namespace
`Langlands.Global.LeftCosetSpace`.

## Stabilizers

For subgroups `X`, `Z` of a topological group and a point `w`:

- `conjStab X Z w`: the elements `x ∈ X` with `w⁻¹ x w ∈ Z`, as a subgroup of `X`
  (`mem_conjStab`, closed when `Z` is closed: `isClosed_conjStab`);
- `conjStabConj X Z w = Z ∩ w⁻¹ X w` and `conjStabEquiv : conjStab X Z w ≃ₜ* conjStabConj X Z w`,
  conjugation by `w⁻¹`;
- `conjStabLattice R V w Z = (V ∩ R ∩ w Z w⁻¹)` inside `conjStab V Z w`;
  `conj_mem_iff`: for `w ∈ R`, `w⁻¹ x w ∈ R ↔ x ∈ R`.

## The inner identity

`setIntegral_inner_eq`: let `R` be a discrete subgroup of a second countable locally compact
group, `w ∈ R`, and `V`, `U ≤ U'`, `A ≤ U'` closed subgroups with `w A w⁻¹ ⊆ V`, such that
`U' = U ⋊ A` compatibly with `R`: `U` is normalized by `U'`, `A ∩ U = 1`, `U' = U A`, and the
`A`-component of every element of `U' ∩ R` lies in `R`. Suppose compact sets meet every orbit of
the lattices `U ∩ R` in `U`, `U' ∩ R` in `U'`, `V ∩ R ∩ w U w⁻¹` in `V ∩ w U w⁻¹` and
`V ∩ R ∩ w U' w⁻¹` in `V ∩ w U' w⁻¹`. For every `h` left invariant under `U` and under `U' ∩ R`
and every `x`,

`∫_{fd(U' ∩ R)} h(u x) du = ∫_{fd(V ∩ R ∩ w U' w⁻¹)} h(w⁻¹ n w x) dn`,

all Haar measures normalized by these lattices (`normalizedHaar`). Both sides equal
`∫_{fd(A ∩ R)} h(a x) da`: the left side by `setIntegral_latticeOf_eq_of_semidirect` for
`U' = U ⋊ A`, the right side by the same theorem for
`U' ∩ w⁻¹ V w = (U ∩ w⁻¹ V w) ⋊ A` after transport along `conjStabEquiv`
(`setIntegral_fundamentalDomain_map`).

## Conjugated lattices

Let `G` be a second countable locally compact Hausdorff group, `H` a closed subgroup with an
s-finite, left and right invariant measure `μH` finite on compacts, `μG` a measure on `G` finite
on compacts, and `ν` a measure on `H \ G` compatible with `μG` and `μH` (`IsCompatible`). Let
`φ` be a topological group automorphism of `G` preserving `μG` and restricting to an automorphism
`φH` of `H` preserving `μH`. Let `Δ ≤ H` be discrete, and let `t ⊆ H` be a measurable transversal
of `Δ` in `H` with `μH(t) = 1`.

- `conj_transversal_data`: `φ(Δ)` lies in `H` and is discrete; the preimage under `φ⁻¹` of the
  chosen fundamental domain of `Δ` is a measurable transversal of `φ(Δ)` in `G`, and the preimage
  of `t` under `φH⁻¹` is a measurable transversal of `φ(Δ)` in `H`.
- `lintegral_conj_eq_of_invariant`: for a measurable left `H`-invariant `f : G → ℝ≥0∞`,
  `∫⁻_{fd Δ} f(φ x) dμG = ∫⁻_q f(q̄) dν(q)`, where `q̄` is the chosen representative of `q`.
- `integral_conj_eq_of_invariant`: for a strongly measurable left `H`-invariant `f` with values in
  a real Banach space such that `q ↦ f(q̄)` is `ν`-integrable, `x ↦ f(φ x)` is integrable on the
  chosen fundamental domain of `Δ` and `∫_{fd Δ} f(φ x) dμG = ∫_q f(q̄) dν(q)`. The integrability
  premise on the quotient cannot be dropped: for `H` trivial and `G = ℝ`, the constant `1` has
  infinite integral on both sides.

The proofs transport the fundamental domain to the lattice `φ(Δ)` and apply
`lintegral_transversal_eq` and `integral_transversal_eq`.

## Provenance

The inner identity is the step `∫_{(U_Q ∩ w U_{P_w} w⁻¹)(F) \ (U_Q ∩ w U_{P_w} w⁻¹)(A)} φ(w⁻¹ v u g) dv
= C_{P,P_w} φ(w⁻¹ u g)` of the proof of Bernstein–Lapid Lemma 6.10 (journal pp. 208–209), in
abstract form. The rest is internal.
