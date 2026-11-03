# Finite-family independence of actual distribution characters

Authors: Worker 34 (Lean proof and route), Worker 751 (checking and
documentation).

The theorem `Langlands.Character.finiteFamilyLinearIndependence` has exactly
the type `FiniteFamilyLinearIndependenceStatement.{uG, uV}`. That is the
complete, unapplied proposition of
`Langlands.Representation.Character.ExactK0Targets`. The group universe `uG`
and the representation carrier universe `uV` are independent. The theorem has
no additional premises. The target pair is imported unchanged.

## Statement proved

Fix a locally profinite group `G` with a regular left Haar measure `μ`. Let
`A : Fin r → SmoothRep.{0, uG, uV} ℂ G` be a family of admissible, irreducible
actual smooth complex representations. Assume that distinct members admit no
genuine equivariant complex linear equivalence `Representation.Equiv`. Then
the actual distribution characters `distribution μ (A i).representation (hA i)`
are linearly independent over `ℂ`. This includes the empty family. The carriers
are arbitrary complex vector spaces in `Type uV`. Only their fixed-vector
spaces are finite-dimensional, which is part of the target's admissibility
hypothesis.

## Implemented proof

1. **Nonzero vectors.** Each `A i` is irreducible, so its carrier is nontrivial
   (`Langlands.CharacterSeparation.nontrivial_of_isIrreducible`). Choose
   `v i ≠ 0`.
2. **One compact open subgroup.** Smoothness of `A i` gives an open subgroup
   `U i` fixing `v i`. Apply
   `Langlands.Hecke.TestFunction.commonCompactOpenBiInvariance` to the empty
   set of test functions and the finite intersection `Finset.univ.inf U`. This
   gives a compact open subgroup `K` contained in every `U i`. Hence every
   `v i` is `K`-fixed.
3. **Corner modules.** Let `M i` be the `K`-fixed vectors of `A i`. Each is a
   module over the actual Hecke corner `Hecke.HeckeAlgebra.Corner μ K hK`
   through `Hecke.cornerModule`, compatible with the complex structure
   (`Hecke.cornerModule_isScalarTower`). Admissibility (`(hA i).2 K`) makes
   `M i` finite-dimensional. Since `v i ∈ M i` is nonzero,
   `Langlands.CompactCoefficientClass.isSimpleModule_fixedVectors` makes `M i`
   a simple corner module (Bernstein–Zelevinsky 2.10).
4. **Pairwise inequivalence of the corner modules.** Suppose
   `φ : M i ≃ₗ[Corner] M j` for some `i ≠ j`. The vector `a = v i` and its image
   `φ a` are nonzero. Corner-linearity and injectivity of `φ` show that a corner
   element kills `a` if and only if it kills `φ a`. Then
   `Langlands.Hecke.nonempty_equiv_of_cornerAction_eq_zero_iff`
   (Bernstein–Zelevinsky 2.10(b), annihilator form) gives a genuine
   equivalence of `A i` and `A j`. This contradicts the pairwise inequivalence
   hypothesis.
5. **Trace relation.** By `Fintype.linearIndependent_iff`, take `c : Fin r → ℂ`
   with `∑ i, c i • distribution μ (A i).representation (hA i) = 0`. Evaluate
   this distribution on the test function
   `Hecke.HeckeAlgebra.toTestFunction μ (Hecke.HeckeAlgebra.Corner.toHeckeAlgebra μ K hK e)`
   of each corner element `e`. By
   `Langlands.CharacterSeparation.distribution_corner`, each character value is
   the trace of the corner action of `e` on `M i`. So
   `∑ i, c i * trace (e acting on M i) = 0` for every `e`.
6. **Conclusion.** `Langlands.FiniteSimpleTrace.eq_zero_of_sum_trace_eq_zero`
   (the helper pair `Langlands/LinearAlgebra/FiniteSimpleTrace`) applies to the
   family `M` over the corner ring and gives `c = 0`.

The listed declarations are the proof's mathematical dependencies, apart from
standard Mathlib lemmas. They come from the imports
`Langlands.Representation.Character.ExactK0Targets`,
`Langlands.Representation.Character.SeparationProof` and
`Langlands.LinearAlgebra.FiniteSimpleTrace`. Other theorems in those modules
are not used. The proof uses no classification, geometric lemma, adjointness,
cuspidal-support theorem, induction-character formula or reductive
admissibility theorem. A kernel check of the theorem reports only `propext`,
`Classical.choice` and `Quot.sound`.

## Source

Bernstein and Zelevinsky (1976), *Representations of the group GL(n,F) where F
is a non-Archimedean local field*, Proposition 2.19, printed/PDF page 21. The
character convention is in 2.17 on the same page. Registered source ID:
`bernstein-zelevinsky-1976-representations-gln`, SHA256
`72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`. The
printed proof chooses one compact open subgroup with all fixed spaces nonzero.
It uses 2.10 for irreducibility and pairwise inequivalence of the fixed-space
representations, then quotes independence of finite-dimensional characters.
Steps 2–4 implement the first two parts. The helper pair implements the
finite-dimensional fact by Jacobson density.
