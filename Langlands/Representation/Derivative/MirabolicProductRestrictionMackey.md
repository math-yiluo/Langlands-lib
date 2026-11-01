# The two-step Mackey sequence for the mirabolic restriction

Author: Worker 1163.

This helper module of the proof of
`Langlands.Derivative.MirabolicProductRestrictionStatement` turns the published
closed-subgroup Mackey filtration into the natural short exact sequence of
compact inductions that underlies Bernstein–Zelevinsky (1977), §7.1, printed
p.471, where Theorem 5.2 is applied to the two orbits.

## A two-step filtration gives a short exact sequence

`Langlands.RepFunctorFiltration.exists_exact_of_two` is a general statement
about the published `RepFunctorFiltration`: for a natural filtration
`0 = S₀ ≤ S₁ ≤ S₂ = F` of a functor `F : C ⥤ Rep R G` and natural isomorphisms
`graded 0 ≅ A` and `graded 1 ≅ B`, there are natural transformations
`i : A ⟶ F` and `q : F ⟶ B` such that at every object `i` is injective, its range
is the kernel of `q`, and `q` is surjective.

The implemented maps are: `i` is the inverse of `graded 0 ≅ A`, followed by the
published `quotientNatLift` of the identity of `S₁` (bijective because `S₀ = 0`,
by the published `quotientNatLift_bijective`), followed by the inclusion of
`S₁`; `q` is the inclusion of `F` into its top step `S₂ = ⊤`, followed by the
published natural projection onto `graded 1 = S₂/S₁` and the isomorphism
`graded 1 ≅ B`. The range of `i` and the kernel of `q` are both `S₁`.

## The Mackey application

`Langlands.Derivative.MirabolicProductRestriction.exists_exact_restrictedCompactInduction`
takes the actual `F : PadicField p`, `T : F.TopologicalData` and `m n : ℕ`, with
`letI := T.topology`. With `P` the binary parabolic and `Q` the mirabolic
subgroup of `GL_((m+1)+(n+1))(F)`, it gives natural transformations

`orbitPiece P Q w ⟶ restrictedCompactInduction P Q ⟶ orbitPiece P Q 1`

of functors from smooth representations of `P` to representations of `Q`, with
the same three exactness properties at every object. The proof installs the
published instances `T.fieldT2`, `T.generalLinearNonarchimedean`,
`T.generalLinearLocallyCompactSpace`, `T.generalLinearT2Space` and
`T.generalLinearSigmaCompactSpace`, uses the published closedness
`BlockShape.isClosed_parabolic` and `Mirabolic.isClosed`, applies the published
theorem `Langlands.Geometric.closedSubgroupMackeyFiltration` to the ordering
`orbitOrdering m n` (open orbit first, closed orbit second), and concludes with
`exists_exact_of_two`.

## Imports

`Filtration.QuotientFirstIso`, `Geometric.ClosedSubgroupMackeyProof`,
`Derivative.MirabolicProductRestrictionOrbits`, `Group.GL.CompactOpen` and
`Group.GL.CountabilityProof`.
