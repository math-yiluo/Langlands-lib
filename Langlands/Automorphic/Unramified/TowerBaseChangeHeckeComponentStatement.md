# Local components distinguished by terminal Hecke families

Worker 290 prepared these proposition definitions for Task 7478 using the
interfaces agreed by Workers 514 and 390. Both declarations are in
`Langlands.Automorphic.Unramified`:

- `TowerBaseChangeHeckeComponentStatement` states standard B6.
- `TowerBaseChangeHeckeComponentTCStatement` adds only
  `[NumberField.IsTotallyComplex F]` after `[NumberField F]`.

## Supplied fields, tower, and chains

The actual fields `F : Type uF` and `K : Type uK` are number fields with
`[Algebra F K]`. Compactness of their adele quotients is explicit.
`T : PrimeCyclicBaseChangeTower F K` supplies a finite increasing tower of
intermediate fields of `K/F`, with cyclic Galois steps of prime degree,
bottom field equivalent to actual `F`, and top field equivalent to actual `K`.
The explicit endpoint equivalences handle the intermediate-field subtype
carriers. Compactness of `AdeleQuotient (T.level i)` is assumed for every
level. The tower can have length zero; then there are no adjacent conditions.

`D` and `D'` are separately supplied `T.IsobaricChain` values. They give actual
`IsobaricData` at every level. Both `D.IsUnitary` and `D'.IsUnitary` are
explicit hypotheses, requiring every cuspidal constituent at every level to
be unitarizable. Intermediate data can contain several cuspidal constituents
of different positive ranks.

Each chain satisfies
`IsSuccessiveWeakBaseChange.{uF,uK,uV,uW}`. At each inclusion step this applies
the existing `IsobaricData.IsWeakBaseChangeOf` to the upper datum first and
the lower datum second. The relation includes rank equality and witnesses of
attached spectral systems; it compares unramified data at almost all finite
places. These are supplied adjacent weak lifts. The statement introduces
neither a composite weak-transfer relation for `K/F` nor an existentially
chosen tower or chain, and establishes no equivalence between those
formulations.

## Bottom and top data

For `r : ℕ`, the actual cuspidal realizations `S` and `S'` over `F` both
have positive rank `r + 1`. Each has a unitary central character, expressed
by `ClassField.Global.RelativeWeilGroup.HasUnitaryCentralCharacter`.
`D.StartsAtCuspidal S.isoClass` and
`D'.StartsAtCuspidal S'.isoClass` identify the bottom entries with
`IsobaricData.ofCuspidal (PositiveRankCuspidalClass.ofFixedRank _)`,
pulled back along the tower's bottom equivalence.

Central unitarity of these two input realizations and the explicit
unitarity of all chain entries are distinct hypotheses in this target.
The published
`CuspidalOperatorRealization.isUnitarizable_of_hasUnitaryCentralCharacter`
is available for a later comparison of the singleton bottom data; no such
comparison is proved here.

At the top there are actual families
`μ μ' : Fin (r + 1) → HeckeCharacter K`, with every character unitary.
`D.EndsAtHeckeFamily.{uF,uK,uV} μ` and
`D'.EndsAtHeckeFamily.{uF,uK,uW} μ'` use the imported endpoint predicate.
The last datum is transported to actual `K` by pullback along the inverse
of the top equivalence. The endpoint requires its rank to be the family
size and an attached spectral system whose Euler polynomials, outside a
finite set of places, equal the product of the actual rank-one character
factors. It uses the characters' `finiteComponent`, unramifiedness, and
actual local uniformizers. It does not construct cuspidal classes from
Hecke characters or assume equality of local components at the chosen
place as part of the endpoint.

## Actual finite-place comparison and conclusion

For `v : FinitePlace F` and `w : FinitePlacesAbove K v`, assume
`∀ w' : FinitePlacesAbove K v, w' = w`. Thus the chosen actual place of
`K` is the only one above `v`. Also assume
`¬ HeckeFamily.SameFiniteComponentsAt μ μ' w.1`.
The negated predicate says there is no bijection of the finite index sets
identifying the actual continuous local characters
`(μ i).finiteComponent w.1` and `(μ' i).finiteComponent w.1`.
Repetitions count with multiplicity; this is not merely a comparison of
character values on a uniformizer.

For every pair of genuine cuspidal spectral presentations
`P : CuspidalSpectralPresentation.{uF,uV} S` and
`P' : CuspidalSpectralPresentation.{uF,uW} S'`, the conclusion is
`(P.localComponent v).isoClass ≠ (P'.localComponent v).isoClass`.
There is no supercuspidality hypothesis and no E2-map parameter.

The declarations' universe order is `uF uK uV uW`: the actual base and top
field universes followed by spectral-presentation witness universes. The
intermediate-field carriers lie in `uK`. In both adjacent-chain predicates,
`uV` is used for lower-level spectral witnesses and `uW` for upper-level
witnesses. The two terminal endpoint witnesses use `uV` and `uW`
respectively, matching the two universally quantified bottom presentations.
These explicit choices are retained in both the general and totally complex
targets; no relation between the universes is imposed.

## Provenance and later proof obligations

The immediate source is the registered operator plan
`operator-external-inputs-plan-2026-11-16`,
*Formalizing the large external inputs of the local Langlands correspondence
for GL_n* (16 November 2026), folder fingerprint
`c429afd5b4f28270a0619b3292f8825a9bfa77c3d842ac3a2a81fc2042cc0463`,
file `external-inputs-plan.tex`. Section 2.2 B6, lines 197–198, states
the local-component distinction through a prime cyclic tower. Section 4.6,
especially lines 769–771, distinguishes the general and restricted forms of
strong lifting. Section 4.8 Remark 4.2, claims (1)–(2) and their proof,
and the final Library comparison, lines 861–924, explain the tower argument
and its use in the exact-stabilizer prime branch.

The Lean target is an internal formulation of standard B6 using the published
supplied-chain and Hecke-endpoint vocabulary. It retains the general unitary
isobaric intermediate data. It does not add the whole-tower cuspidal solutions
required by the restricted variant in Remark 4.2.

The original mathematical source is Arthur–Clozel (1989), registered as
`arthur-clozel-1989-base-change`, SHA256
`c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`.
The later B6 derivation needs:

- III.4.1 and III.4.2(c), printed p.202 / PDF p.216, for general unitary
  isobaric weak lifts and their uniqueness;
- III.5.1, printed p.212 / PDF p.226, for strong compatibility for
  representations induced from unitary cuspidal data, at every adjacent step;
- I.6.2, printed p.51 / PDF p.65, and the extension by Langlands
  classification after I.6.8, printed pp.59–60 / PDF pp.73–74, for uniqueness
  of the relevant local lifts;
- rigidity identifying the unitary isobaric endpoints with the prescribed
  Hecke families, as in the plan's use of Jacquet–Shalika;
- irreducibility of unitary principal series and recovery of their inducing
  characters up to order.

These proposition definitions prove none of those inputs or B6 itself.
The totally complex declaration states the corresponding specialization
without providing a new existence or compatibility proof. The separate
conditional proof assembly and its scope ruling remain outside this statement
unit.
