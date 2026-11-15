# Proof of the "property (1)" step of Stacks 07FH

`Langlands.CommutativeAlgebra.Popescu.regularParameterExtension :
RegularParameterExtensionStatement.{u}` proves the statement for every universe `u`. It applies
`RegularParameter.regularParameterExtension_of (hN3 : RegularSequenceFlatStatement)
(h00NQ : RegularLocalParametersStatement) : RegularParameterExtensionStatement` to the Library
proofs `regularSequenceFlat` (Stacks 10.128.2, Tag 07DY) and `regularLocalParameters`
(Stacks 10.106.3, Tag 00NQ). It uses only the standard axioms.

Notation: `B₀ = k[y]_{𝔭₀}`, `B = k[y, z]_𝔭`, `g : B → Λ_q`.

1. **Generators** (`comap_eq_map_sup_span`). `𝔭 = 𝔭₀ k[y, z] + (z)`. Hence
   `𝔪_B = J + (z)` for `J = 𝔭₀ B`, and `𝔭Λ_q = 𝔭₀Λ_q + (φ(z)) = 𝔪_{Λ_q}`. The second equality holds
   because the images of `φ(z)` generate the maximal ideal of `Λ_q/𝔭₀Λ_q`. This gives the second
   conclusion.
2. **Flatness** (`flat_of_fibre` along `J`):
   - `J ⊗_B Λ_q → Λ_q` is injective. Indeed `J = 𝔪_{B₀}B`, and `Λ_q` is flat over `B₀` through
     `B₀ → B → Λ_q` (`Langlands.Algebra.extendedIdeal_rTensor_injective`, reused from
     `Langlands.Algebra.NoetherianFiberwiseFlatness`). No flatness of `B₀ → B` is needed.
   - The `z̄_j` are weakly regular on `B/J`. `B/J` is a localization of `k[y, z]/𝔭₀k[y, z]`
     (Mathlib instance in `Localization/Ideal`), hence flat over it. The `z_j` are weakly regular
     there (`isWeaklyRegular_quot`), and weak regularity passes to flat base change
     (`isWeaklyRegular_lTensor`).
   - The images are weakly regular on `Λ_q/JΛ_q = Λ_q/𝔭₀Λ_q`, which is regular local. They are a
     regular system of parameters (`spanFinrank = r`, generating), so `h00NQ` applies.

## Source comparison

Stacks, Smoothing Ring Maps, proof of Lemma 16.11.2 (Tag 07FH; smoothing.pdf of
`stacks-artin-axioms-approximation-2026-11-06`, printed p. 27) obtains property (1) from the choice
of `λ_{t+1}, …, λ_m` mapping to a regular system of parameters of `Λ_q/𝔭'Λ_q` without further
argument. The statement's Markdown suggests the fibrewise criterion of flatness over
`k[y]_{𝔭₀} → k[y, z]_𝔭`. The implemented proof instead applies the Library's ideal local flatness
criterion along `J = 𝔭₀B` (`Langlands.Algebra.idealLocalFlatnessCriterion`, Stacks Algebra
Lemma 10.99.10, Tag 00ML, in tensor-injectivity form). The closed fibre `B/J → Λ_q/𝔭₀Λ_q` is flat
by 07DY, and 00NQ supplies the regular sequence, as described above.
