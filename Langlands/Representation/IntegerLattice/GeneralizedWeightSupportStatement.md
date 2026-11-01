# Actual generalized-weight support and common eigenvectors

Statement prepared by Worker 709. This proposition supplies no proof. Its
actual construction is imported from the published
`Langlands.Representation.IntegerLattice.GeneralizedWeightBlock` module.

`Langlands.CommutingTupleGeneralizedWeightSupportStatement` quantifies over
every natural `d`, every finite-dimensional complex vector space
`V : Type u`, the actual commuting invertible tuple `A`, and all unit labels
`c : Fin d → ℂˣ`. It states

```text
generalizedWeightBlock A c ≠ ⊥
  ↔ ∃ v : V, v ≠ 0 ∧ ∀ i, A_i v = c_i • v.
```

Thus the full nonzero support consists exactly of the tuples of common
eigenvalues. The vector is an actual vector of the original space, and the
eigenvector equations use the actual tuple entries. A supplied eigenbasis,
decomposition, nilpotence hypothesis or list of support labels is absent.
The carrier universe is arbitrary; rank zero, zero `V` and zero blocks
remain included. At rank zero both sides say that the space has a nonzero
vector; for zero `V` both sides are false.

The governing source is Renard, *Représentations des groupes réductifs
p-adiques*, 9 July 2026, Appendix C.III, printed p.279 / PDF285, proof of
the proposition: its character list is obtained from all common eigenspaces.
Registered source `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
PDF285–286 were read directly for this draft. This is a derived identification
between that source list and the basis-free intersections. It is additional
to the separate finite-support, independence, spanning and invariance
statement; it does not redefine that statement.

For provenance, a common eigenvector lies in every maximal generalized
eigenspace. In the reverse direction, the actual commuting nilpotent
differences on a nonzero block admit a common nonzero kernel vector; the
normalization equation turns it into the displayed eigenvector. This is
an intended proof route, not an implemented proof.

The registered supplementary errata
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
were read at PDF18–19. Their C.III entry corrects the later power grouping
and makes no change to this support identification.
