# Actual Hecke-family endpoints for supplied isobaric chains

This module supplies internal vocabulary for B6 of the operator plan
`operator-external-inputs-plan-2026-11-16`, Section 2.2, and Section 4.8,
Remark 4.2, claim (1), proof (1)–(2), and “The remark and the Library's
statements”. It uses the tower and supplied chain of
`PrimeCyclicBaseChangeTower`, with no further condition on intermediate
cuspidal ranks or numbers of constituents.

For a family `χ : Fin r → HeckeCharacter K` of actual continuous characters
of the idele-class group, the definition
`Langlands.Automorphic.Unramified.HeckeFamily.eulerPolynomial χ v π` is
the polynomial

```text
∏ i : Fin r, (1 - C ((χ i).finiteComponent v π : ℂ) * X).
```

The factors use the actual continuous local characters on
`(FiniteCompletion K v)ˣ`. The polynomial can be evaluated at any invertible local element;
the endpoint below uses it only at uniformizers outside a common finite
exceptional set. This is the Euler denominator convention of the existing
`HeckeEulerProductRigidityStatement`. A repeated character contributes a
separate factor, and the product for an empty family is one.

`Langlands.Automorphic.IsobaricData.HasHeckeFamily D χ` requires:

- the actual total rank `D.rank` to equal `r`;
- a spectral system `s` of that rank with the existing
  `IsobaricData.HasSpectralSystem D s` attachment to the actual cuspidal
  constituents of `D`;
- one finite set `S` of finite places containing `s.exceptional`, outside
  which every actual Hecke character in the family is unramified;
- for every `v ∉ S` and every `π : (FiniteCompletion K v)ˣ` with
  `Valued.v (π : FiniteCompletion K v) = WithZero.exp (-1 : ℤ)`, equality of
  `s.eulerPolynomial v` with the displayed product.

Thus the equality holds on a cofinite set of places, uniformly for the whole
finite family. The inclusion of `s.exceptional` in `S` supplies the proof
needed to evaluate its Euler polynomial. Character unramifiedness is precisely
the existing `HeckeCharacter.IsUnramifiedAt`, triviality of `finiteComponent`
on the actual local integral units. The definition supplies witnesses and
conditions; it proves neither finite ramification nor independence of the
choice of uniformizer.

`Langlands.Automorphic.Unramified.PrimeCyclicBaseChangeTower.IsobaricChain.EndsAtHeckeFamily
D χ` applies this relation to `D.terminal`, an `IsobaricData K` over the
actual top field. The terminal datum is the last supplied datum pulled back
along the specified inverse equivalence `topEquiv.symm : K ≃ top`. No
identification of the last intermediate-field carrier with `K` is implicit.
At the bottom, the separate `StartsAtCuspidal D c` predicate uses the
pullback along `bottomEquiv : bottom ≃ F` of
`IsobaricData.ofCuspidal (PositiveRankCuspidalClass.ofFixedRank c)`, for an
actual fixed-rank cuspidal class over `F`. The separate
`IsSuccessiveWeakBaseChange D` predicate always says that the upper datum
is a weak base change of the immediately lower datum for the actual inclusion
algebra; `IsUnitary D` is also separate. Two chains over the same field tower
can therefore start at two classes over the same actual `F` and end in
independently supplied Hecke families over the same actual `K`. Length zero
uses the same endpoint equivalences and has no adjacent transfer condition.

`Langlands.Automorphic.Unramified.HeckeFamily.SameFiniteComponentsAt χ η v`
means that there is a bijection between the two finite index sets under which
the actual continuous local characters at `v` are equal. It records
multiplicities, permits repetitions, and asserts equality of characters on
the entire local multiplicative group, rather than merely their values at a
uniformizer. The bijection is required only at this specified place.
No global equality of the Hecke characters or matching at other places is
asserted.

Arthur–Clozel (1989), Chapter III Definition 4.1 and Theorem 4.2(c),
printed p.202 (registered PDF page 216), and Theorem III.5.1, printed p.212
(PDF page 226), motivate the general data induced from unitary cuspidal
constituents along the tower. The uniqueness of local lifting in I.6.2,
printed p.51 (PDF page 65), and its extension by the Langlands classification
in I.6.4, printed pp.59–60 (PDF pages 73–74), belong to the later B6 proof.
This module uses these sources as provenance for internal definitions and
does not state their conclusions.

In particular, this endpoint does not construct rank-one cuspidal classes
from Hecke characters or identify constituent multisets with such classes.
It asserts no B6 implication, existence of a chain or terminal family,
uniqueness, transitivity, or local compatibility theorem. The cofinite Euler
relation imposes no condition at an excluded place; a later B6 theorem must
justify its conclusion about components at the specified top place.
