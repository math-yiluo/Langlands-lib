# Fundamental weights of a split simply connected group

This internal helper module, used in the proof of
`SplitSimplyConnectedFactorialStatement`, is the only place where simple
connectedness enters. It produces fundamental weights for the coordinate root
datum of a `CellData k G` (module `FactorialCellData`).

- `span_coroot_eq_top`: if `G` is simply connected, the coroots of `D.P` span the
  cocharacter lattice `I → ℤ` over `ℤ`. The proof takes:
  - `isSimplyConnectedFieldExtension k k`, which gives simple connectedness after
    the trivial base change;
  - `splitTorus.isMaximalTorus_baseChangeHom_of_fibrewise`, which gives
    maximality of the base-changed torus;
  - the field realization `fieldRealization k D.P`, which is reduced
    (`AffineSplitSurjection.isReduced_fieldRealization`) and is a root datum of
    the base-changed torus (`D.hP.field k`).

  It then applies `splitSimplyConnectedCorootSpan` and transports the result
  along `splitTorus.cocharacterLatticeEquiv`.
- `exists_fundamentalWeights`: if `G` is simply connected, there are characters
  `ω i : I → ℤ` with `⟨ω i, j∨⟩ = 1` if `j = i` and `0` otherwise, for all
  simple roots `i` and `j`. Here `⟨χ, ν⟩ = coPairing χ ν = ∑ₗ χ l · ν l`. The
  simple coroots are linearly independent (`Base.linearIndepOn_coroot`) and span
  the same lattice as all coroots (`Base.span_int_coroot_support`), so by
  `span_coroot_eq_top` they form a basis of `I → ℤ`. Then `ω i` is the `i`-th
  coordinate functional of this basis, written as a vector through the standard
  pairing.

Provenance: internal. This is step 4 of the route suggested in the task
context: simple connectedness makes the coroots span the cocharacter lattice
(`splitSimplyConnectedCorootSpan`), so fundamental weights exist as characters.
