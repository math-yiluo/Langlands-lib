# The transfer identity for Tits obstructions in matrix form

This module proves the ground-field half of this development's proof of the
integral-weight transfer law of `Reductive/TitsTransfer`, a derived analogue
of Tits, *Représentations linéaires irréductibles d'un groupe réductif sur un
corps quelconque*, J. reine angew. Math. 247 (1971), Proposition 5.1, printed
p. 207 / PDF p. 12, which is stated for `β` on central characters. It computes the Tits
obstruction over `k` of a sum of conjugate weights as the class of a tensor
descent. Tits's proof is cohomological (his reference [14], S. Lang,
*Rapport sur la cohomologie des groupes* (1966), Proposition 13, p. 57). The
matrix argument here is this development's own.

## Declaration

`GaloisPinningData.titsObstructionValue_eq_classOf_corCSAOf`. Setting:

- `d` is Galois pinning data for `G` over `K`, with `K/k` Galois, and
  `hspan : corootSpan ℤ = ⊤`.
- `E` and `N` are fields with `k`-algebra maps to `K`, `E/k` finite, `N/k`
  finite Galois and `K/E` Galois.
- `e : (E →ₐ[k] N) ≃ Fin (m + 1)` indexes the `k`-embeddings, and
  `ε σ ∈ Gal(K/k)` extends `σ`
  (`ε σ (algebraMap E K x) = algebraMap N K (σ x)`).
- `ρ` is a representation of `G_K` on a nonempty finite type `n`, with top
  weight `λ` (`SplitPinning.HasTopWeight`).
- `Q h` is invertible for `h ∈ Gal(K/E)` and intertwines `ρ` with its twist
  by `h` viewed in `Gal(K/k)`. The `E`-algebra `twistedFixed Q` spans
  `M_n(K)` over `K` (`hQspan`).
- The sum `ν = ∑_i ε(e⁻¹ i) ⋆ λ` of star conjugates is star-fixed (`hfix`).

Conclusion: `titsObstructionValue d ν = [corCSAOf k E N A]`, where
`A = toCSA Q (twistedFixed Q)` is the central simple `E`-algebra fixed by
`Q` and `corCSAOf` is the published tensor descent.

Proof.

1. `A` has `E`-dimension `|n|²` (`GaloisTwistedMatrix.finrank_eq`), and its
   inclusion `j` into `M_n(K)` satisfies `Q h · j a = h(j a) · Q h`.
   `classOf_corCSAOf_eq` (`Algebra/CorestrictionTwistedFixed`) identifies
   `[corCSAOf k E N A]` with the class of `toCSA C (twistedFixed C)`, where
   `C = inducedMatrix (inductionData e ε hε) Q`.
2. Let `Π = piTensor (i ↦ ρ^{ε(e⁻¹ i)})`. By `hasTopWeight_galoisTwist` and
   `HasTopWeight.piTensor`, `Π` has top weight `ν`, so `ν` has multiplicity
   one and is maximal among the weights of `Π` (`HasTopWeight.eq_of_sub_mem`).
3. `C τ` intertwines `Π` with `Π^τ` (`intertwines_galoisTwist_piTensor`) and
   is invertible (`isUnit_inducedMatrix`). Hence `titsAlgebra Π` lies in
   `twistedFixed C` (`titsAlgebra_le_twistedFixed`), which spans the matrix
   algebra (`span_twistedFixed_inducedMatrix`).
4. `titsObstructionValue_of_maximal` (`Reductive/TitsMaximalWeight`) applied
   to `Π`, `C` and `B = twistedFixed C` gives
   `titsObstructionValue d ν = [toCSA C (twistedFixed C)]`.

The hypothesis `hQspan` is supplied by `Reductive/TitsTransferBaseChange`,
and `hfix` by `Reductive/TitsTransfer`.
