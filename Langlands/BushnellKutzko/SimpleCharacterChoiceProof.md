# Choice independence and equivalent-stratum twisting of simple characters

Bushnell–Kutzko, *The admissible dual of GL(N) via compact open subgroups*
(1993), (2.4.2), (3.2.3) and (3.3.20), printed pp. 65–66, 99 and 113–114
(PDF pp. 77–78, 111 and 125–126). The proof also uses the domain comparisons
of (3.1.9)(ii) and (v), the conjugation formula of (3.3.9) and the determinant
criterion of (2.4.11), printed pp. 91, 108 and 72–73 (PDF pp. 103, 120 and
84–85). Literature ID `bushnell-kutzko-1993-admissible-dual-gln`, SHA-256
`811693b94c03fcbc2cfe33955bc5a00b0fc0b5645ca343f8cc1a3c6511de9c73`.

`simpleCharacterChoice` proves both clauses of
`SimpleCharacterChoiceStatement` by comparing two defining sequences
whose simple initial strata are equivalent at depth `ℓ`. Their critical
depths agree. If the sequences have successors, those successors are
equivalent at the common critical depth `r`, and dropping the initial
terms gives defining sequences for them.
`simpleStratumLatticeProperties` gives equality of the initial character
domains for `⌊ℓ/2⌋ ≤ m < n`, and equality with the successor domains at
indices `j ≥ ⌊r/2⌋`. The perturbation `β′ − β` belongs to `𝔓^{−ℓ}`.
At `k = m + 1`, the bound `2k − ℓ ≥ 1` makes its trace factor a group
homomorphism on `U^k` by `elementCharacterHom`.

The new parameter belongs to the common stratum coset, so its centralizer
lies in the formal intertwining set of the original stratum.
`simpleIntertwining` puts it in the double coset for the conjugation formula
of (3.3.9), supplied by `simpleCharacterCovariance`.
Adding the twist coefficient changes the conjugation formula to that of the
new parameter. Its conjugation difference is zero on its centralizer.
`intertwinedUnitCharacter` and
`factorsThroughCentralizerDet_of_intertwined_simpleHGroup` then supply the
relative determinant condition. The lattice properties also give
preservation of the domain by the relative order normalizer. This
normalizer lies in the new centralizer and thus fixes the twisted
character.

Below the critical depth, the proof uses the character comparison at the
pair of successor strata, with index `max m ⌊r/2⌋`. The two trace factors
combine by addition of their coefficients. Writing `γ` and `γ′` for the
successor parameters, the equality of coefficients is
`(β − γ) + (β′ − β) = (γ′ − γ) + (β′ − γ′)`. At and above the critical
depth `elementCharacter_eq_one_of_depth` gives triviality of the trace
factors from the two perturbations, so the recursion compares the
successor characters by transport. If one sequence
terminates, both terminate. The local determinant condition still
applies, and multiplying the trace on the intersection with
`U^{⌊n/2⌋+1}` by the positive twist replaces its coefficient `β` by `β′`.

Exchanging the two strata gives the reverse inclusion by the inverse
trace twist. The independence clause compares the initial stratum with
itself at depth zero with zero perturbation. The equivalent-stratum
clause replaces the starting depth by `ℓ` and retains the defining tail.
