# Finite-order determinant twists between supplied full realizations

Authors: Workers 523 and 528. Local instance names: Worker 35.

This is a derived relation on supplied actual automorphic realizations. It
compares their full finite, compact and infinitesimal actions, and descends to
the existing `CuspidalOperatorRealization.IsoClass`. It does not assert that a
twist of every supplied realization exists, construct a twist functor, or
choose representatives or multiplication maps on form spaces.

## Actual objects and twisting orientation

The auxiliary predicate
`OperatorRealization.DeterminantTwistEquations χ S T e` takes an actual
`HeckeCharacter F`, actual same-rank `OperatorRealization F n` objects, and a
complex linear equivalence `e : S.Space ≃ₗ[ℂ] T.Space`. It requires exactly
the following three equations:

- For every finite adelic matrix `d` and vector `f`,
  `T.finiteRepresentation d (e f)` equals
  `χ.onIdeles (AdelicGL.determinant F n (AdelicGL.ofFinite F n d))`
  coerced to a complex scalar, times `e (S.finiteRepresentation d f)`.
- For every `k : standardInfiniteCompact F n` and vector `f`,
  `T.compactRepresentation k (e f)` equals
  `χ.onIdeles (AdelicGL.determinant F n (AdelicGL.ofInfinite F n k.val))`
  coerced to a complex scalar, times `e (S.compactRepresentation k f)`.
  Thus the compact element is embedded using its actual underlying infinite
  adelic matrix.
- For every `a : ArchimedeanGL.EnvelopingAlgebra F n` and vector `f`,
  `T.envelopingAction a (e f) = e (S.envelopingAction a f)`.
  This quantifies over the whole enveloping algebra.

`determinantTwistScalar` abbreviates the actual character value in these
equations. Its identity, multiplication, inverse and nonvanishing properties
follow from the complex-unit-valued character.

The orientation is fixed by the existing right-translation convention. A
prospective multiplication operator `Mχ f(g) = χ(det g) f(g)` would satisfy
`R_d Mχ = χ(det d) Mχ R_d`. Accordingly `T` is related to the
character twist of `S`, with `e` directed from the source to the target.
The file specifies equations for a supplied `e`; it does not construct `Mχ`
or prove it preserves the defining properties of actual forms.

`OperatorRealization.IsFiniteOrderDeterminantTwist χ S T` means
`χ.HasFiniteOrder` together with existence of such an `e`. Although the
auxiliary equations can be written for any character, this public relation
explicitly retains finite order. Its cuspidal specialization uses the actual
underlying `.realization` without changing any equation.

The general operator predicate makes sense at any `n`. Cuspidal realizations
and their classes use the existing index `r : ℕ` and actual rank `r + 1`,
so their rank is positive. They retain the explicit existing hypothesis
`CompactSpace (AdeleQuotient F)` needed by the actual constant-term
construction. No unitarity premise is imposed on the cuspidal inputs.

## Intrinsic laws and descent

The identity linear equivalence satisfies the equations for the identity
character. Composing equivalences for `χ` and `ψ` gives the equations for
the actual character product `χ * ψ`, using complex linearity and
commutativity of the scalar product. Inverting an equivalence gives the
equations for `χ⁻¹`; the finite and compact equations use the nonzero
complex scalar, and the enveloping equation is transported through the
inverse. The accompanying character module proves that identity, product and
inverse preserve `HasFiniteOrder`, so these constructions give the stated
laws of the finite-order relation.

For the identity character, the three equations are exactly the generator
criterion for full operator equivalence, with the equalities reversed.
`OperatorRealization.isFiniteOrderDeterminantTwist_one_iff` uses
`Equivalence.ofGenerators` in one direction and the finite, compact and
differential consequences of a full intertwiner in the other. It therefore
proves equivalence with `Nonempty (S.Equivalence T)`. No inference from
finite-component equivalence is used.

Transport in both arguments composes with these full identity-character
equivalences. On cuspidal objects,
`isFiniteOrderDeterminantTwist_iff_of_isoClass_eq` expresses representative
independence with exactly the existing full quotient relation.

`CuspidalOperatorRealization.IsoClass.IsFiniteOrderDeterminantTwist χ c d`
is the resulting Prop-valued quotient lift. Its representative computation
lemma is
`IsoClass.isFiniteOrderDeterminantTwist_isoClass_iff`. Its complete criterion,
`IsoClass.isFiniteOrderDeterminantTwist_iff`, says that for every pair of
actual representatives `S,T` with `S.isoClass = c` and `T.isoClass = d`,
the character has finite order and some actual complex linear equivalence
satisfies all three equations. In particular the criterion is independent
of the chosen representatives.

On classes the identity-character relation is precisely equality.
Composition and inverse descend by quotient induction.
`IsoClass.IsFiniteOrderDeterminantTwist.target_unique` states that for a
fixed source class and fixed character there is at most one target class.
Its proof composes the inverse of one witness with the other, obtaining the
identity character, and applies the full identity-character criterion.
It proves no uniqueness of the character: distinct characters may give the
same target because self-twists are possible.

## Finite order and norms

The imported module `Langlands.Global.HeckeCharacterFiniteOrder` proves that
finite-order continuous complex characters are locally constant, by
factoring through a finite roots-of-unity subtype. Its determinant pullback
consequences include the whole infinite adelic factor. At the identity this
factor has value one, so it is one on a neighborhood of the identity. This is
the topological reason a finite-order multiplier supports an unchanged
infinitesimal action. The third equation remains an explicit requirement on
the supplied equivalence; no differentiation formula for multiplication on
actual forms is inserted as an unproved field or proved in this group.

`HeckeCharacter.IsTrivialOnNorm E χ` uses the actual quotient norm and
means `∀ x : IdeleClasses E, χ (ideleClassNorm x) = 1`. For number fields
`F : Type u` and `E : Type v` with independent universes and an algebra
structure, `IsTrivialOnNorm.pow_finrank_eq_one` proves
`χ ^ Module.finrank F E = 1` using the published
`AdelicFunctoriality.ideleClassNormInclusionPower`.
`IsTrivialOnNorm.hasFiniteOrder` then supplies the finite-order conjunct of
the relation from positivity of the extension degree. Thus a norm-trivial
character and an equivalence satisfying the three equations give an
immediately usable instance of the relation. The converse implication from
finite order to norm-triviality is not claimed; norm-triviality depends on
the specified extension.

## Local instance names

The module uses six local `AddCommGroup` instances, each equal to
`Submodule.addCommGroup _`. Five are on the form spaces
`RationalInvariantFunctions`, `ContinuousRationalFunctions`,
`FiniteSmoothRationalFunctions`, `AutomorphicForms` and
`StableAutomorphicFunctions`, and one is on `S.Space` for
`S : OperatorRealization F n`. They have explicit names beginning with
`finiteOrderTwist`. Anonymous instances got the same generated declaration
names as the corresponding anonymous local instances of
`Langlands.Automorphic.CuspidalFiniteSlice`. Neither module imports the other, so
no module could import both. The names have no mathematical content, and
renaming them changes no definition, theorem statement or proof.

## Provenance and remaining scope

The source motivating this relation is Arthur and Clozel, *Simple Algebras,
Base Change, and the Advanced Theory of the Trace Formula* (1989),
Chapter III, printed pp.199 and 201 (one-based PDF pp.213 and 215),
especially Theorem III.3.1. Registered source:
`arthur-clozel-1989-base-change`, SHA256
`c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`.
The original passages were read directly.

III.3.1 compares arbitrary cuspidal representations whose unramified
Satake classes have equal residue-degree powers almost everywhere and
concludes that the second is the first twisted by a character trivial on
principal ideles and norms from the specified cyclic extension. Its statement
does not require prime degree or unitarity of the two representations.
The unitary reduction in its proof is not a premise of the present relation.

The relation, its quotient descent and its algebraic laws are internal
formalization content describing full representation equivalence in that
conclusion; they are not separately attributed definitions in AC89.
This group does not prove III.3.1 or use or discharge its spectral-power
comparison hypothesis. Actual multiplication on forms, preservation of
analytic and cuspidality conditions, general-character differentiation and
total twist existence remain separate obligations. No weak-transfer
relation, Galois action, normalized induced representation, isobaric class,
rigidity theorem or transfer theorem is constructed or assumed.
