# The intertwining side of the unfolding identity

Module `Langlands.Global.EisensteinConstantTerm.UnfoldingRight`, namespace
`Langlands.Global.LeftCosetSpace`.

## Results

Throughout, `R` is a discrete subgroup of a second countable locally compact Hausdorff group and
all normalized Haar measures are `normalizedHaar` for the intersections with `R`.

- `measurePreserving_normalizedHaar`: an automorphism `φ` of modulus one
  (`mulEquivHaarChar φ = 1`) preserves `normalizedHaar Δ hΔ` for every discrete subgroup `Δ` such
  that one compact set meets every orbit of `Δ`.
- `exists_conj_measurePreserving`: let `V, B ≤ V'` and `U'` be closed subgroups with
  `w⁻¹ B w ⊆ U'`, and let `pB : V' → B` be a continuous homomorphism with `pB = id` on `B`,
  `pB = 1` on `V` and kernel `V` (a retraction for `V' = V ⋊ B`). Suppose the `B`-component of
  every element of `V' ∩ R` lies in `R`, and that compact sets meet every orbit of `V ∩ R` in `V`,
  of `V' ∩ R` in `V'` and of `V ∩ R ∩ w U' w⁻¹` in `conjStab V U' w = V ∩ w U' w⁻¹`. Then for
  every `b ∈ B`, conjugation by `b⁻¹` gives automorphisms of `V` and of `V ∩ w U' w⁻¹`, compatible
  with the inclusion, preserving their normalized Haar measures. The moduli are trivial by
  `Semidirect.mulEquivHaarChar_conj_eq_one`, applied to `V' = V ⋊ B` and to
  `V' ∩ w U' w⁻¹ = (V ∩ w U' w⁻¹) ⋊ B`.
- `integral_rightTransversal_eq`: let `V' = V ⋊ B` be a closed semidirect decomposition (`V`
  normal in `V'`, `V ∩ B = 1`, `V' = V B`) with `w⁻¹ B w ⊆ U'` and with the `B`-component of every
  element of `V' ∩ R` in `R`, with the same three compact covers as above. Let `μN` be the
  normalized Haar measure of `V ∩ w U' w⁻¹` and `ν` a measure on `(V ∩ w U' w⁻¹) \ V` compatible
  with it and the normalized Haar measure of `V`. A measurable function `Φ : V' → ℂ`, left
  invariant under `V' ∩ w U' w⁻¹`, whose values `Φ(q̄)` at the chosen representatives `q̄ ∈ V` are
  `ν`-integrable, is integrable on the chosen fundamental domain of `V' ∩ R ∩ w U' w⁻¹` in `V'`,
  and `∫_{fd} Φ = ∫_q Φ(q̄) dν`.

## Proof of `integral_rightTransversal_eq`

The normalized Haar measure of `V'` is the image of the product of those of `V` and `B`
(`semidirect_haar`), and the lattice `V' ∩ R ∩ w U' w⁻¹` is the semidirect product of
`V ∩ R ∩ w U' w⁻¹` and `B ∩ R`. So the integral over its fundamental domain is
`∫_{fd(B ∩ R)} ∫_{fd(V ∩ R ∩ w U' w⁻¹)} Φ(v b) dv db` (`setIntegral_transversal_eq_prod` and
Fubini). Since `b` lies in `V' ∩ w U' w⁻¹`, `Φ(v b) = Φ(b⁻¹ v b)`. For fixed `b`, the inner
integral is `∫_q Φ(q̄) dν` by `integral_conj_eq_of_invariant`, so the outer integral is the mass
one of `fd(B ∩ R)` times it. Integrability follows from the same computation for `‖Φ‖`.

## Provenance

This is the identification `∫_{(U_{Q_w} ∩ w U_{P_w} w⁻¹)(A) \ U_{Q_w}(A)} = ∫_{(U_Q ∩ w U_{P_w}
w⁻¹)(A) \ U_Q(A)}` of the proof of Bernstein–Lapid Lemma 6.10 (journal p. 209), with the
normalizations of the Library's intertwining measure, in abstract form.
