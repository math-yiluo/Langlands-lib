# Support lemmas for the forward association intertwiner

Author: Worker 240. This module contains internal lemmas for the proof of
`Langlands.CuspidalSupport.AssociatedCuspidalInductionHomTheorem`, the
implication (i) ⇒ (ii) of Bernstein–Zelevinsky (1977), Theorem 2.9(a). It
introduces no new representation-theoretic notion. Each lemma derives a fact
from the existing Library constructions: canonical normalized Jacquet modules,
canonical normalized parabolic induction, object filtrations, and smooth
subquotients.

## Frobenius reciprocity, easy direction

`parabolic_le_normalizer_unipotentSubgroup` states that the standard upper
parabolic `C.parabolic F.Carrier` normalizes its unipotent radical
`C.unipotentSubgroup F.Carrier` inside `GL_n`. The unipotent subgroup is the
image of the normal subgroup `unipotentRadical` of the parabolic. Its
normalizer inside the parabolic is therefore everything
(`Subgroup.normalizer_eq_top`), and `Subgroup.le_normalizer_map` transfers
this to `GL_n`.

`exists_ne_zero_to_normalizedParabolicInduced` takes a smooth complex
representation `ρ` of `GL_n(F)` and an arbitrary complex representation `τ` of
the Levi `C.Levi F.Carrier`. It assumes a nonzero intertwiner `φ` from the
canonical normalized Jacquet module `T.normalizedJacquet C ρ` to `τ`. It
concludes that some nonzero intertwiner goes from `ρ` to the canonical
normalized induction `T.normalizedParabolicInduced C τ`.

The proof uses the generic map `Jacquet.CharacterReciprocity.backward` of the
Library's character reciprocity. In that map, `P` is the standard parabolic,
`N` its unipotent radical, `σ` is `τ` inflated along the Levi projection, and
the character is the inflated positive half-modulus `T.leviHalfCharacter C`.
With these choices, `Induction.normalizedSmoothInduced` is definitionally
`T.normalizedParabolicInduced C τ`.

The input map of `backward` is `φ` composed with the inverse of the comparison
equivalence `C.jacquetModuleEquiv ρ`. Its source is the generic Jacquet
action, twisted by the inverse character. The proof checks intertwining on
generators `Jacquet.mk ρ N v`. Two Library facts are used:
`Parabolic.mk_action_eq_levi` says the parabolic acts on Jacquet classes
through its Levi part, and `normalizedJacquet_mk_eq_inv_halfModulus` says the
normalized Jacquet action is the inverse half-modulus times the embedded
action. The resulting intertwiner `f` sends `v` to the function
`g ↦ A(Jacquet.mk(ρ(g) v))`. Its value at `g = 1` is `φ` applied to the
Jacquet class of `v`. If `f` were zero, `φ` would vanish on every Jacquet class.
Every element of the Jacquet module is such a class
(`C.jacquetMk_surjective`), so `φ` would be zero. Therefore `f ≠ 0`.

## Graded pieces as actual smooth subquotients

Let `A` be a smooth representation, and let `s` be an
`ObjectRepFiltration (Rep.of A.representation) r`. For `i : Fin r`,
`filtrationSubquotient A s i` is the actual `SmoothRep.subquotient` of `A`.
Its upper subspace is the step `s.subrepresentation i.succ`. Its lower
subspace is the preceding step, pulled back into the upper step by
`lowerInUpper`. `filtrationSubquotient_isSubquotient` records that it is a
`SmoothRep.IsSubquotient` of `A`, witnessed by the identity isomorphism.
`filtrationSubquotientEquiv` is the identity equivalence between its
representation and `s.gradedRepresentation i`; the two are definitionally equal.

## From a quotient graded piece to a nonzero map

`exists_ne_zero_of_isQuotient_filtrationSubquotient` assumes the following:
the graded representation `s.gradedRepresentation i` is equivalent to an
irreducible `τ`, and the subquotient `filtrationSubquotient A s i` is a
`SmoothRep.IsQuotient` of `A`, that is, an actual surjective intertwiner
`A → D` exists. Under these assumptions the lemma produces a nonzero
intertwiner `A → τ`, namely the surjection followed by the equivalence.
Irreducibility gives `⊥ ≠ ⊤` among subrepresentations of `τ`, so `τ` has a
nonzero vector `w`. Lift the preimage of `w` under the equivalence to a vector
of `A` along the surjection; the composite sends that vector to `w ≠ 0`.

## Constituent theorem plus reciprocity

`exists_ne_zero_of_gradedRepresentation_equiv` fixes a prime, a p-adic field
`F`, a topological realization `T`, block shapes `B` and `C` of a rank `n`,
and the proposition `LeviCuspidalConstituentTheorem.{uF, max uF uV} F T C`
as a hypothesis. The universe `max uF uV` is the carrier universe of the
Jacquet module of the induced representation. Consider a smooth `σ` of the
`B`-Levi and a smooth `τ` of the `C`-Levi that is irreducible and satisfies
`IsLeviCuspidal C`. Put `A = r_C(i_B σ)`, the normalized Jacquet functor of the
`C`-parabolic applied to the normalized induction functor of the
`B`-parabolic at `σ`. Assume `A` is admissible. Assume also that some graded
representation of some object filtration of `A` is equivalent to `τ`. Then
there is a nonzero intertwiner from `T.normalizedParabolicInduced B σ` to
`T.normalizedParabolicInduced C τ`.

The proof transfers irreducibility and cuspidality from `τ` to the
filtration subquotient `D` along the equivalence. It uses
`Langlands.isIrreducible_iff_of_equiv` and `isLeviCuspidal_iff_of_equiv`.
Then the constituent proposition, applied to `A`, `D` and the
subquotient witness, makes `D` an actual quotient of `A`. The previous lemma
gives a nonzero map `A → τ`. The Frobenius lemma, applied with the smoothness
of `T.normalizedParabolicInduced B σ`, gives the result. The assembly module
`AssociationForwardHomProof` discharges this lemma's hypotheses. It takes the
constituent proposition from the published `leviCuspidalConstituentTheorem`.
It derives the admissibility of `A` and the graded equivalence there. None of
this lemma's hypotheses is therefore a hypothesis of the assembly theorem.
That theorem's own hypotheses are described in its Markdown.

## Provenance

Bernstein and Zelevinsky, *Induced representations of reductive p-adic groups
I* (1977), section 2.15(2), printed page 449 / PDF page 10 (registered source
`bernstein-zelevinsky-1977-induced-i`). Worker 240 read this original page.
That paragraph obtains the nonzero intertwiner in three steps: the filtration
of `r_C(i_B σ)` has `τ` as a factor, a cuspidal constituent is a quotient, and
Frobenius reciprocity applies. The lemmas above implement the second and third
steps for the Library's actual constructions. The Frobenius step uses only the
direction of reciprocity that turns a Jacquet-module map into a map to the
induced representation, so no inverse of the reciprocity map is needed.
