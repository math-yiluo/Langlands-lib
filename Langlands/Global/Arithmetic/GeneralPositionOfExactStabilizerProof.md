# Harris's exact Weil stabilizer implies general position

The theorem `Langlands.Global.generalPositionOfExactStabilizer` proves the
existing Library proposition
`Langlands.Global.GeneralPositionOfExactStabilizerStatement.{uF}`.
For every prime `p`, arbitrary-universe p-adic field `F`, finite extension
`F'` in its common algebraic closure, and continuous character
`χ : weilSubgroup F F' →ₜ* ℂˣ`, the exact stabilizer of the restriction of
`χ` to the Galois-closure Weil subgroup implies general position.

The original source is Michael Harris, *The local Langlands conjecture
for GL(n) over a p-adic field, n < p* (1998), registered source
`harris-1998-local-langlands`, Definition 4.5, printed p.201 / PDF p.25,
and the proof of Lemma 4.7, condition (4.12), printed pp.204–206 /
PDF pp.28–30. Harris asserts the sufficient condition by Clifford–Mackey
theory for every subgroup containing the Galois-closure subgroup. The
imported algebraic modules expand this assertion for the Library's
actual representations. This module supplies the arithmetic
specialization and the tower required by the existing definition.

Write `N = weilSubgroup F (galoisClosure F F')` and
`H = weilSubgroup F F'`. The existing statement module proves that
`N` is normal and `N ≤ H`. Its `HasExactWeilStabilizer` is definitionally
the exact-stabilizer premise of
`GeneralPosition.mackeyConstituent_irreducible_of_exactStabilizer`.
That theorem proves irreducibility of every actual Mackey constituent
for every subgroup `K` containing `N` and every `g` in the local Weil
group. The two imported algebraic modules identify the conjugated
restricted characters, separate their right-coset coordinates, and
prove irreducibility by isolating coordinates of invariant subspaces.
Their adjacent Markdown describes those implemented proofs in detail.

The private assembly helper applies the published theorem
`Langlands.Global.harrisCyclicPrimeTower` to the actual Galois closure.
Characteristic zero makes this normal closure Galois over the base.
The tower theorem provides a descending tower from that extension to
the bottom intermediate field, with each step cyclic of prime degree.
Its proof uses local Galois solvability and the solvable Galois tower
construction, as explained in `HarrisCyclicPrimeTowerProof.md`.

The inclusion in each `IsCyclicPrimeStep` makes the field-valued tower
antitone, by `Fin.antitone_iff_succ_le`. Thus every tower field lies
inside the top field, the Galois closure. The antitone fixing-subgroup
operation `weilSubgroup_antitone` then shows that the Weil subgroup
at each level contains `N`. Applying the all-subgroup irreducibility
theorem at each such subgroup gives exactly the constituent clause of
`IsInGeneralPosition`, for every level and every group element.

The final theorem discharges both inputs of this helper using the
published tower theorem and the proved Mackey criterion. There is no
additional reciprocity, finite-order character, preselected tower, or
irreducibility hypothesis. The proof retains arbitrary `uF`, includes
`p = 2`, and covers `F' = F` and towers with no steps. The
exact-stabilizer character-existence assertion and the rest of Harris's
Lemma 4.7 are separate statements.

Worker 34 authored the coordinate proof and the arithmetic assembly;
Worker 60 authored the exact-stabilizer and Mackey bridge. Reuse of the
independently published cyclic tower theorem is by its Lean name.
