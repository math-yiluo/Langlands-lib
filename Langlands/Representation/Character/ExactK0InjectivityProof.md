# Injectivity of actual characters on exact finite-length K₀

Authors: Worker 34 (Lean proof and route), Worker 751 (checking and
documentation).

The theorem `Langlands.Character.exactK0CharacterInjectivity` has exactly the
type `ExactK0CharacterInjectivityStatement.{uG, uV}`. That is the complete,
unapplied proposition of `Langlands.Representation.Character.ExactK0Targets`.
The group universe `uG` and the representation carrier universe `uV` are
independent. The theorem has no additional premises. The target pair is
imported unchanged.

## Statement proved

Fix a locally profinite group `G` with a regular left Haar measure `μ`. Assume
`hAdm`: every actual finite-length smooth complex representation
`A : SmoothRep.{0, uG, uV} ℂ G` is admissible. Let
`χ : SmoothRep.FiniteLengthGrothendieckGroup.{0, uG, uV} ℂ G →ₗ[ℤ]
HarmonicAnalysis.Distribution G` be any integer-linear map that sends the class
`ofRepresentation A hA` of every actual finite-length `A` to its actual
distribution character `distribution μ A.representation (hAdm A hA)`. Then `χ`
is injective on the whole exact finite-length Grothendieck group. The
admissibility premise `hAdm` remains a hypothesis. It is not proved here for any
particular group.

## Implemented proof

1. **Composite on irreducible labels.** Let `F` be `χ` composed with
   `SmoothRep.realizeIrreducibles ℂ G`. Its domain is the free integral lattice
   `SmoothRep.IrreducibleLattice` on genuine irreducible isomorphism classes
   `SmoothRep.IrreducibleIsoClass`. Let `f c` be the value of `F` on the
   lattice generator of the class `c`.
2. **Finite subfamilies.** By Mathlib's
   `linearIndependent_iff_finset_linearIndependent`, it suffices to prove
   complex linear independence of `f` on each finite set `s` of classes.
   Enumerate `s` by `Fin (Fintype.card s)`. Choose actual irreducible
   representatives `A i` with `SmoothRep.IrreducibleIsoClass.exists_eq`.
3. **Hypotheses of finite-family independence.** Distinct members of `s` are
   distinct classes. By `SmoothRep.irreducibleIsoClass_eq_iff_nonempty_equiv`,
   their representatives admit no genuine `Representation.Equiv`. Every
   irreducible has finite length (`SmoothRep.hasFiniteLength_of_isIrreducible`).
   So `hAdm` makes every representative admissible.
4. **Identifying the values.** By
   `SmoothRep.realizeIrreducibles_generator_irreducibleIsoClass`, the generator
   of the class of `A i` realizes `ofRepresentation (A i) _`. The generator
   formula for `χ` then identifies `f` on that class with the actual
   distribution character of `A i`. Then
   `Langlands.Character.finiteFamilyLinearIndependence` gives independence on
   `s`, transported along the enumeration by `linearIndependent_equiv'`.
5. **Integral injectivity of the composite.** `F` equals the integer-linear
   combination map `Finsupp.linearCombination ℤ f`. The check is
   `Finsupp.lhom_ext` on single generators. Complex independence restricts to
   integral independence (`LinearIndependent.restrict_scalars'`), because the
   integers act faithfully on `ℂ`. So `F` is injective.
6. **The whole quotient.** The second component of
   `SmoothRep.irreducibleGrothendieckStatement`, the bijectivity of
   `realizeIrreducibles`, gives surjectivity. Write two classes `x` and `y` as
   realizations of lattice elements `a` and `b`. Then `χ x = χ y` means
   `F a = F b`, so `a = b` and `x = y`.

Only surjectivity of the realization is used. The class-indexed family is
proved independent as a whole, so no kernel element has to be expanded. This is
equivalent to the coefficient-vanishing route planned in the target Markdown.

The listed declarations are the proof's mathematical dependencies, apart from
standard Mathlib lemmas. They come from the imports
`Langlands.Representation.Character.FiniteFamilyProof` (which imports the
target pair) and `Langlands.Representation.Smooth.IrreducibleGrothendieckProof`.
Other theorems in those modules are not used. The proof uses no Langlands
classification, geometric lemma, adjointness, cuspidal-support theorem,
parabolic character formula or reductive admissibility theorem. The carriers
are not resized or assumed finite-dimensional. A kernel check of the theorem
reports only `propext`, `Classical.choice` and `Quot.sound`.

## Source and provenance

This target is a derived interface, not a statement printed in the source; see
the provenance section of `Langlands/Representation/Character/ExactK0Targets.md`.
Its mathematical input is Bernstein and Zelevinsky (1976), *Representations of
the group GL(n,F) where F is a non-Archimedean local field*, Proposition 2.19,
printed/PDF page 21. That is the finite-family independence used in step 4.
Registered source ID: `bernstein-zelevinsky-1976-representations-gln`, SHA256
`72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`. The
remaining steps are the generic Jordan–Hölder realization theorem cited above
and linear algebra.
