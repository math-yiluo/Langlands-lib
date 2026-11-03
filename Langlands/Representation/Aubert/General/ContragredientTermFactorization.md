# From actual duality isomorphisms to contragredient term comparison

This is an internal factorization of the published normalized functors and
exact finite-length Grothendieck classes. It uses a locally compact
nonarchimedean group `G` in universe `uG`, complex smooth representations with
carriers in `max uG uV`, and an independent finite index type in universe `uI`.
It proves no induction or Jacquet duality theorem.

`inductionJacquetDualityFactorizationIso` considers an actual decomposition
`P = M ⋉ U` with closed radical and an actual smooth Levi object `B`. Write
`iP` and `rP` for the published normalized induction and Jacquet functors and
`D` for the actual smooth contragredient. Given isomorphisms

* `rP (D A) ≅ D B`, and
* `D (iP B) ≅ iP (D B)`,

it constructs `iP (rP (D A)) ≅ D (iP B)`. The construction applies
`iP.mapIso` to the first isomorphism and composes with the inverse of the
second. It requires no finite-length or admissibility hypothesis beyond the
existence of these two supplied isomorphisms. No naturality assertion is made
for this objectwise construction. In the family application below,
`B` is the actual opposite Jacquet object `rQ A`.

`inductionJacquet_class_eq_of_duality` supplies the objectwise exact-K0 step.
Given the finite-length witnesses for the source, `iP B`, and an ambient
object `C`, together with a class equality `[iP B] = [C]`, it applies
`contragredientK0` to that equality. The published generator formula gives
`[D (iP B)] = [D C]`. The constructed isomorphism identifies the source
class with the first of these classes.

`contragredientTermComparison_of_duality` works with the existing standard
family `P I = M I ⋉ U I`, its displayed `ParabolicFiniteLength` premises,
ambient compact-open cofinality and ambient smooth-dual finite-length
preservation. Its additional inputs are:

* actual decompositions `Q I = M I ⋉ V I` with closed radicals and
  finite-length preservation for their Jacquet functors;
* an equivalence `e` of the finite-subset indices preserving cardinality;
* actual elements `g I` conjugating all three subgroups of `Q I` to those of
  the standard decomposition at `e I`, with membership convention
  `x ∈ P (e I) ↔ (g I)⁻¹*x*g I ∈ Q I`, and the same convention for the Levi
  and radical;
* the two displayed duality isomorphisms, supplied respectively for all
  finite-length ambient objects and finite-length standard Levi objects;
* equality of the exact-K0 classes of `iQ σ` and `iP σ` for each actual
  finite-length inducing object `σ`, allowing arbitrary finite-length proofs
  for both induced objects.

Here `iQ` and `rQ` denote the actual normalized functors from `Q I`.
All these are explicit hypotheses. The family `Q` need not be identified as
opposite in this generic theorem. In a rational opposite-parabolic application,
that identification, both duality inputs, the actual subgroup conjugation,
and the induction class comparison still have to be established.

For a finite-length object `A`, the proof sets `B = rQ A`. Its finite length
is supplied by the stated Jacquet preservation premise, so standard induction
gives finite length of `iP B`. The published
`inductionJacquetConjugationIso` identifies `iQ (rQ A)` with the standard
term at `e I`. Standard-family preservation gives finite length of that term;
`hasFiniteLength_of_iso` therefore gives finite length of `iQ B`.
No separate finite-length or exactness premise for induction from `Q` is
assumed.

The supplied induction class equality and the actual conjugate term
isomorphism give `[iP B] = [iQ B] = [i(e I) (r(e I) A)]`.
The objectwise class lemma applies `contragredientK0` to this equality and
composes with the constructed factorization. The isomorphism class laws allow
all output finite-length witnesses to be the ones already used by
`ContragredientTermComparison`. Together with `e` and its cardinality law,
these equalities prove that published predicate.

This proof uses only the named published functors, actual isomorphism
composition, isomorphism preservation of finite length, the exact-K0
isomorphic-object law and the smooth-dual generator formula. The Grothendieck
groups retain all actual short-exact-sequence relations. The result supplies a
conditional input to `contragredientCommutation_of_termComparison`; it does
not prove the closed rational-point commutation target or any of the
representation-theoretic premises listed above.
