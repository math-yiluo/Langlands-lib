# Fixed-level visibility from actual association invariance

Worker 146. This internal adapter supplies the ambient-support transport needed
for the fixed-vector splitting route to VI.10.6(iii)–(iv). Its mathematical
inputs are the published actual objects and theorems imported by the Lean file.
It retains VI.9.4 and untwisted association invariance as explicit hypotheses;
it proves neither of these source statements nor the host proposition.

`bernsteinInertiaRepresentativeOnSourceLevi` takes two actual Bernstein
cuspidal data, an actual algebraic conjugacy of their embedded Levis, and a
same-Levi inertia relation between the first action and the pullback of the
second. It constructs a datum on the first Levi with the pulled-back second
action. Irreducibility follows from the actual rational-point homeomorphism.
The published `BernsteinCuspidalDatum.replaceInertia` supplies the precise
standard-family cuspidality condition using inertia preservation of the
proper inside-Levi Jacquet vanishing tests. This avoids needing a general
conjugation comparison for those tests. The replacement is untwisted-associated
to the second datum through the given conjugacy and the identity isomorphism
of its pulled-back action.

`nontrivial_fixedVectors_iff_of_bernsteinInertiaRelated` assumes actual untwisted
association invariance of cuspidal support and constituent visibility for
every fixed standard Levi. Given actual constituents supported by two
inertially related data, the construction puts the second datum on the first
Levi. Association invariance transfers the second constituent's support to
this replacement datum. The published same-Levi rational-inertia constituent
comparison then compares the two actual fixed spaces. A private support-transport lemma
explicitly unfolds the support and induction definitions to expose this
coefficient; a private pullback lemma supplies irreducibility. No induction
isomorphism between different Levis is asserted.

`bernsteinFixedVectorVisibility_of_association_and_constituentVisibility`
chooses the actual data witnessing the two inertial support relations.
Equality of their genuine quotient classes gives the actual inertia relation
by `bernsteinInertialClass_eq_iff`; the preceding theorem proves the desired
fixed-vector comparison. This argument needs no support existence theorem,
support uniqueness theorem, finite length or Bernstein decomposition.

`bernsteinFixedVectorVisibility_of_subquotientGeneration_and_association`
supplies the constituent visibility input using the earlier standard induction
adapter and the explicitly assumed VI.9.4 subquotient-generation statement.
The compact open K is contained and normal in compact K₀, the minimal standard
Iwasawa factorization holds with K₀, and K has the stated standard basis-member
property along every standard parabolic. The proof keeps this exact K.

The global theorem
`standardBernsteinFixedVectorVisibility_of_subquotientGeneration_and_association`
specializes the local result to the exact geometry of
`StandardBernsteinFixedVectorVisibilityStatement`. It constructs the canonical
topology, local compactness, nonarchimedean group structure and actual standard
family from the host's hypotheses. VI.9.4 at carrier universe `max uF uV` and
the displayed global form of actual untwisted support invariance remain
explicit. The independent field universe `uF` and coefficient-carrier universe
`uV` are preserved. Support witnesses and induced representations use the
saturated carrier universe `max uF uV`.

These are derived consequences with internal provenance. The exact
unconditional `FixedVectorCategoryStatements` and its import closure are
unchanged, and this contribution does not discharge that target.
