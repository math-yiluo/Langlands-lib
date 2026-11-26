# Proof of the Galois induction of a compatible Hecke-character family

Module `Langlands.Galois.HeckeCharacterGaloisInductionProof`, name space
`Langlands.GaloisRepresentation`. The theorem `heckeCharacterGaloisInduction` proves the
Library statement `HeckeCharacterGaloisInductionStatement` of
`Langlands.Galois.HeckeCharacterGaloisInductionStatement`, with its universes `uK`, `uE`, `uL`.
The auxiliary `residueCharacteristic_eq_of_liesOver` states that a place `w` of `E` above `v`
has the residue characteristic of `v` (`Algebra.ringChar_eq` for the residue field extension).

## The construction

Let `e`, `ι`, `χ` and `ψ` be as in the statement, and let `S_E` be the common exceptional set of
`IsCompatibleLambdaAdicRealization ι χ ψ`, with the common coefficient `a w ∈ L` chosen for every
place `w` of `E` outside `S_E`.

- Members of the family: for every `λ`, `R λ = HeckeInduction.inducedObject e (ψ λ)`, the
  finite-index induction from the image of `restrictionAlongClosure e` of the descended
  character. `IsGaloisInductionOfCharacter` holds with the finite-index instance of
  `HeckeInduction.imageSubgroup`, the character `HeckeInduction.descended e (ψ λ)`
  (`descendedCharacter_comp_rangeRestrict`) and the identity equivalence: `R λ` is literally the
  representation `FiniteRepresentation.induce j.range (twist φ (of 1))` of the statement.
- Rank: `HeckeInduction.inducedObject_rank` gives `[E : K]`.
- Exceptional set: `S` is the union of the places of `K` below a place of `S_E`, the places of
  `K` below a place of `E` ramified over `K`, and the places below a place of the normal closure
  `HeckeInduction.normalClosureField` ramified over `K`
  (`ClassFieldTheory.Global.Artin.finite_setOf_ramified`). For `v ∉ S`, no place above `v` lies in
  `S_E`, every place above `v` has ramification index `1` (`Ideal.ramificationIdx_eq_one`), and the
  induced place of the normal closure at `v` is unramified.
- Polynomials: `P v = ∏_{w | v} (1 - a w X ^ f(w|v))` in `L[X]`, independent of `λ`.

## Matching

- `MatchesOutside ∅ R S P`: for `v ∉ S` and `λ` of residue characteristic different from that of
  `v`, every `w` above `v` has the residue characteristic of `v`, so the compatibility hypothesis
  makes `ψ λ` unramified at `w` with value `a w` (in `L_λ`) at every geometric Frobenius lift.
  `HeckeInduction.hasEulerPolynomialAt_inducedObject` then gives
  `HasEulerPolynomialAt (R λ) v (∏ w, (1 - a w X ^ f(w|v)))`, which is the image of `P v` in
  `L_λ[X]`.
- `MatchesHeckeInductionEulerPolynomials χ (P · mapped by ι)`: for `v ∉ S`, `IsUnramifiedAbove χ v`
  holds (ramification indices `1` and `χ` unramified at every `w ∉ S_E`). For every family of
  uniformizers `ϖ`, the coefficient `ι (a w)` equals `χ_w` at the uniformizer supplied by the
  hypothesis, which equals `χ_w (ϖ w)` because both have valuation `exp (-1)` and `χ` is
  unramified at `w` (`HeckeCharacter.finiteComponent_eq_of_valued_eq`). So the image of `P v`
  is `inducedEulerPolynomial χ v ϖ`, and this holds outside the finite set `S`.

## Supporting modules

The modules `Langlands.Galois.HeckeInduction.MonomialDeterminant`,
`InducedCharacter`, `RestrictionIndex`, `LocalCosets` and `GoodPlace` contain the
constructions and the local computation; their Markdown pages describe the proofs. The key local
fact is that at a good place the cycles of geometric Frobenius on the right cosets are indexed by
the places `w` above `v`, with lengths `f(w|v)`, and that the return element of each cycle is the
image of a geometric Frobenius lift at `w` up to inertia.

## Source

The statement follows Harris 1998 (`harris-1998-local-langlands`), Lemma 1.6. In its proof
(companion TeX `math_9611226v1.tex`, lines 735–737) Harris takes "the compatible family of
λ-adic representations of `Gal(Q̄/E)` obtained by inducing `σ'`", where `σ'` is the family
attached to the Hecke character `χ` of `E'`; Harris's `E'/E` is the extension `E/K` here. The
source gives no details for this step. The present proof constructs the induction and computes
its unramified Euler polynomials directly, as described above.
