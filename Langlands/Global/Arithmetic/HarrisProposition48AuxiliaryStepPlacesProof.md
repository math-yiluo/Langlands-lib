# The auxiliary places of a CM step field in Harris's Proposition 4.8

`proposition48AuxiliaryStepPlaces` proves `Proposition48AuxiliaryStepPlacesStatement`
(module `Langlands.Global.Arithmetic.HarrisProposition48SingletonChildStatement`) for
every universe level `uF`. The data are a problem `Q`, an intermediate field
`Q.E ⊆ D ⊆ Q.L` that is a CM field, the hypothesis `Q.IsAuxiliaryValid`, and a place
`w` of `D` above the auxiliary base place `Q.Ps.v`.

## Proof

1. *The hypotheses used.* `Q.IsAuxiliaryValid` is `Q.IsAuxiliaryValidAtParity` at the
   parity `[E' : E] - 1`. The proof takes from it only two conjuncts:
   `HasUniquePlaceAbove Q.L Q.Ps.v` and `HasUniquePlaceAbove Q.L (conjPlace Q.E Q.Ps.v)`.
   Each says that one place of the normal closure `Q.L` lies above the base place.

2. *The conjugate place.* The witness `wc` is the place `conjPlace D w` of `D` with
   the lying-over proof `HarrisDatum.conjPlace_liesOver Q.Ps.v w` (module
   `Langlands.Global.Arithmetic.HarrisDatumCharacterRealizationProof`). That lemma
   rests on `HarrisDatum.complexConj_algebraMap`. Fix a complex embedding `φ` of `D`.
   The complex conjugation of `D` composed with `φ` is the complex conjugate of `φ`.
   The same holds on `Q.E` for the embedding `φ ∘ algebraMap Q.E D`. Since `φ` is
   injective, complex conjugation of `D` restricts on `Q.E` to complex conjugation of
   `Q.E`. Hence the image of `w` under conjugation of `𝓞 D` contracts to the image of
   `Q.Ps.v` under conjugation of `𝓞 Q.E`, which is `conjPlace Q.E Q.Ps.v`. The equation
   `wc.val = conjPlace D w.val` then holds by `rfl`.

3. *Uniqueness.* `finitePlacesAbove_subsingleton` (module
   `Langlands.Global.Arithmetic.HarrisUniquePlace`) is applied to the tower
   `Q.E → D → Q.L` given by the intermediate field. It turns the uniqueness in `Q.L`
   into `Subsingleton (FinitePlacesAbove D v)`. Its proof uses lying over: above two
   places of `D` over `v` lie places of `Q.L` (`exists_place_above`). These lie over
   `v` by transitivity, so they coincide. Each place of `D` is the contraction of the
   place of `Q.L` above it. Applied at `Q.Ps.v` this gives `w' = w` for every `w'`.
   Applied at `conjPlace Q.E Q.Ps.v` it gives `w' = wc` for every `w'`.

The theorem uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Provenance

The statement records the tower comparison of finite places in the proof of
Proposition 4.8 of Michael Harris, *The local Langlands conjecture for GL(n) over a
p-adic field, n < p*, Invent. Math. 134 (1998), 177–210 (registered source
`harris-1998-local-langlands`). Printed p. 202 speaks of "the prime dividing" the
auxiliary place in each field `Eᵢ` of the tower. Section 2, printed p. 192, sets up a
place divisible by exactly one place of the normal closure and its splitting in the
CM field into two conjugate primes `v₁, v₂`. The argument above is the standard
lying-over argument, which Harris does not write out.
