# Transport of a Mackey child and its induced complex-place parameters

`Langlands.Global.Harris.proposition48MackeyChildTransport` proves exactly
`Langlands.Global.Harris.Proposition48MackeyChildTransportStatement`
(`Langlands/Global/Arithmetic/HarrisProposition48MackeyTransportStatement.lean`). It holds for
every double coset representative `a`, every pair of compatible isomorphisms
`e : R.E ≃+* D`, `e' : R.E' ≃+* D · a(E')` identifying the child's character with the
Mackey character, and independent universes `uF` (local field) and `uV` (spectral carrier),
with no further hypothesis.

## Source

Michael Harris, *The local Langlands conjecture for GL(n) over a p-adic field, n < p*,
Invent. Math. 134 (1998), 177–210 (registered source `harris-1998-local-langlands`), proof of
Proposition 4.8, printed pp.202–203. The child problem for `a` is
`(E_i, a(E') · E_i, a(ξ) ∘ N_{a(E')·E_i/a(E')})`, and its solution `Π(a, i)` is used directly
as a constituent over `E_i` (`math_9611226v1.tex`, lines 1583–1597, and lines 1630–1633 for
`Π_{t-1} = ⊞_a Π(a, t-1)`). In the Library a child is an abstract problem linked to the
parent by field isomorphisms, so the solution has to be moved to `D` along them. Harris does
not track the infinity type through the induction. The second clause follows the design of
the exact-stabilizer branches (`HarrisProposition48ExactStabilizerParameterData`): solutions
carry the complex-place parameters of the induced representation. This design is in the plan
note `operator-external-inputs-plan-2026-11-16` (`external-inputs-plan.tex`, lines 910–912,
the infinity type).

## Implemented proof

Write `C = D · a(E')` (`Q.mackeyField D a`) with the inclusion algebra `D → C` of the
statement, and `χ = Q.mackeyCharacter D a`.

1. *The square.* The compatibility hypothesis says
   `e' (algebraMap R.E R.E' x) = algebraMap D C (e x)` (`Subtype.ext`). Hence the inverse
   square commutes:
   `e'.symm (algebraMap D C x) = algebraMap R.E R.E' (e.symm x)`. The character hypothesis
   says `R.ξ = HeckeCharacter.comap e' χ` by definition of `comap`, so
   `HeckeCharacter.comap e'.symm R.ξ = χ` (`HeckeCharacter.comap_symm_comap`).
2. *First clause.* `IsWeakAutomorphicInductionOf.arithmeticComap`
   (`Langlands.Automorphic.WeakAutomorphicInductionArithmeticTransport`), applied to the
   inverse square, gives that `IsoClass.arithmeticComap e.symm S.isoClass`, which is
   `(S.arithmeticComap e.symm).isoClass`, is a weak automorphic induction of
   `comap e'.symm R.ξ = χ`. This is `IsMackeyConstituent` for `a`. The same transport proves
   `proposition48MackeyConstituentGaloisConjugate`.
3. *Second clause, the place.* Every complex place `u` of `D` is `v ∘ e⁻¹` for the complex
   place `v = u ∘ e` of `R.E` (`ArchimedeanCompactTransport.complexPlace`). By hypothesis
   `S` has at `v` a parameter list `ds`. There are an enumeration `en` of the places of `R.E'`
   above `v` and actual parameters `dξ w` of `R.ξ` at these places with
   `ds ~ complexPlaceLanglandsSum v en (fun w => [dξ w])`.
4. *The actual parameter over `D`.* `cuspidal_hasComplexPlaceParameter_arithmeticComap`
   (`Langlands.Automorphic.ComplexPlaceParameterArithmeticTransport`) gives
   `(S.arithmeticComap e.symm).isoClass.HasComplexPlaceParameter u (parameterList e.symm v ds)`.
   The list is `ds` when the embedding of `v` composed with `e⁻¹` is the selected embedding
   of `u`, and the conjugate blocks otherwise. The witness is the actual standard-module
   embedding of `S` at `v`, composed with the arithmetic pullback. In the conjugate case it
   is first composed with precomposition by entrywise conjugation of `GL_n(ℂ)`, which carries
   the embedding-oriented compact and Lie actions at `v` to those at `u`.
5. *The Mackey character.* The places of `C` above `u` are the images `w ∘ e'⁻¹` of the places
   `w` of `R.E'` above `v` (`placesAboveEquiv`). Enumerate them by `en` followed by this
   bijection. Put `dχ (w ∘ e'⁻¹) = parameter e'.symm w (dξ w)`. By
   `hasComplexPlaceParameter_comap` and step 1, `dχ (w ∘ e'⁻¹)` is an actual parameter of
   `χ = comap e'.symm R.ξ` at `w ∘ e'⁻¹`.
6. *The list comparison.* `perm_parameterList` gives
   `parameterList e.symm v ds ~ parameterList e.symm v (complexPlaceLanglandsSum v en …)`.
   `parameterList_complexPlaceLanglandsSum` identifies the right side with
   `complexPlaceLanglandsSum u (en.trans β) (fun w₂ => [dχ w₂])`. Its block identity
   (`isAligned_iff_iff`) is the orientation bookkeeping. The four identity-or-conjugation
   choices are at `v` along `e⁻¹`, from `w` to `v`, from `w ∘ e'⁻¹` to `u`, and at `w` along
   `e'⁻¹`. They have equal parity, because each is a comparison of two embeddings of `D`
   that define the complex place `u`. The comparison of lists is made only after the actual
   parameter of step 4 is established.

The theorem uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.
