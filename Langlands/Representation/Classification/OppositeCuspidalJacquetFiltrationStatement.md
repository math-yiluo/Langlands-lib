# Opposite associated Jacquet filtration from the upper theorem

Author: Worker 698.

`Langlands.GLOppositeCuspidalJacquetFiltrationFromUpperStatement` is a
proposition definition for a transfer of the existing upper associated
Jacquet filtration. This pair states the interface; it proves no
representation-theoretic theorem.

For every prime `p`, every `PadicField.{uF} p`, compatible topological data
`T`, and every natural rank `n`, assume explicitly
`AssociatedJacquetFiltrationTheorem.{uF,uV} F T n`. For every ordered block
pair `B, C` with associated embedded Levis and every actual smooth complex
representation `ρ` of `B.Levi F.Carrier` satisfying
`IsLeviQuasicuspidal B ρ.representation`, put

```lean
Jo := CuspidalJacquetMultiplicity.oppositeJacquet T C
  (CuspidalJacquetMultiplicity.induced T B (Rep.of ρ.representation)).
```

The conclusion supplies a natural number `r`, an equivalence

```lean
e : Fin r ≃ MinimalConjugatingPermutations (F := F.Carrier) B C,
```

and an actual `ObjectRepFiltration Jo r`. For every index `i`, its graded
quotient has an actual representation equivalence to

```lean
transport B C (e i).val.val (e i).property ρ.representation.
```

Thus the filtration runs from zero to the full opposite Jacquet
representation and has one quotient per original minimal whole-Levi
conjugating permutation. In particular, its number of steps is the
cardinality of that exact finite type. The equivalence counts distinct
indices even when their transported representations are isomorphic.

The field and source-carrier universes `uF` and `uV` are independent.
Induction and the opposite quotient have carrier universe `max uF uV`;
the graded equivalences compare this universe with `uV`. The statement
includes rank zero and the zero inducing representation. Smoothness is
provided by `SmoothRep`; quasicuspidality is the existing vanishing
condition on proper standard refinements. No irreducibility, admissibility,
finite length, semisimplicity, splitting, or opposite filtration is an
input. The finite filtration conclusion does not assert that its factors
are simple, nor does it assert a composition series.

## Actual quotient and normalization

The constructions are imported unchanged from
`CuspidalJacquetMultiplicityStatement` and `JacquetInductionStatement`.
`induced` is the actual normalized upper parabolic induction with positive
upper half-modulus. `oppositeJacquet` is the actual quotient by
`C.oppositeUnipotentSubgroup F.Carrier`. It restricts the action to the
embedded Levi and uses `Jacquet.normalizedActionOfModulus` with

```lean
δ := (T.leviModulus C).comp (C.leviEquiv F.Carrier).symm.toMonoidHom
```

and full modulus `δ⁻¹`, then pulls back by `C.leviEquiv`. Its scalar on
the quotient is the positive upper half-modulus. This construction is
already fixed by the imported consumer; the statement introduces no
replacement action or unspecified isomorphism predicate.

## Intended transfer and permutation orientation

The following is a proof plan, not additional assumed data or a claim that
these compatibilities are already proved.

1. Use the published `GeneralLinear.BlockShape.reverse`. Write
   `t = C.reversePermutation` and
   `q = C.reverseMatrix F.Carrier`. Their coordinate convention is
   `t (C.reverse.index j a) = C.index j.rev a`: whole blocks reverse, and
   positions inside a block retain their order. In general `t` is not an
   involution. Conjugation by `q` identifies the reversed embedded Levi
   with the original one; construct the corresponding product-Levi
   equivalence `κ : C.reverse.Levi F.Carrier ≃* C.Levi F.Carrier`.
   The published `reverse_unipotentSubgroup_map_conj` gives the actual
   subgroup equality from the upper radical of `C.reverse` to the
   opposite radical of `C`. This also transfers the given association of
   `B` with `C` to association of `B` with `C.reverse`.

2. Prove the explicit block-modulus identity
   `T.leviModulus C.reverse m' =
     (T.leviModulus C (κ m'))⁻¹`.
   Reversal interchanges the ordered pairs of distinct blocks in the
   determinant formula. Consequently the inverse half-modulus of the
   reversed upper action becomes the positive half-modulus of the
   original upper modulus, exactly as in `oppositeJacquet`. The transfer
   uses this explicit algebraic identity, rather than assuming a new
   opposite Haar-modulus comparison.

3. For the actual induced representation `I`, descend its action `I.ρ q`
   to the quotients: the class of `x` for the reversed upper radical maps
   to the class of `I.ρ q x` for the original opposite radical.
   The inverse uses `q⁻¹`. The subgroup equality makes these maps
   well-defined; the modulus identity makes them intertwine after
   pulling the reversed upper action back along `κ.symm`.
   The Library's upper Jacquet functor uses coinvariants inside the
   restricted parabolic, whereas `oppositeJacquet` uses the ambient
   opposite subgroup. The proof must construct the corresponding
   quotient-model identification, rather than assume definitional
   equality of those carriers.

4. Apply the supplied upper theorem to `B, C.reverse, ρ`. Reindex its
   minimal whole-Levi conjugating permutations by
   `v ↦ t * v`, with inverse `w ↦ t⁻¹ * w`. Multiplication of permutations
   is composition, so `t * v` first sends `B` to `C.reverse` and then
   sends `C.reverse` to `C`. Right multiplication or replacement of `t`
   by `t⁻¹` in the forward map has the wrong orientation.
   Whole-Levi conjugation carries each source coordinate block onto
   one whole target block. Minimality makes its inner-coordinate
   bijection increasing; `t` preserves this order, as does its inverse
   on each target block. Prove both minimality clauses and whole-Levi
   conjugacy in both directions, yielding an equivalence of the existing
   `MinimalConjugatingPermutations B C.reverse` and
   `MinimalConjugatingPermutations B C` types. The current
   `MinimalWeylTransportProof` supplies reusable whole-block and inner-order
   lemmas. No assertion that arbitrary minimal Weyl permutations are
   preserved is required.

5. Pull back and carry the actual invariant-subspace filtration through
   the constructed group and quotient equivalences, and identify each
   graded quotient. Inverse conjugation in the existing `transport`
   gives, on the original target Levi,
   `ρ(v⁻¹ t⁻¹ m t v) = ρ((t * v)⁻¹ m (t * v))`.
   Composing the upper enumeration with the minimal-index equivalence
   gives the required `e`. The published filtration transport modules
   provide group pullback, invariant-subspace order isomorphisms, and
   graded quotient equivalences; these work without simple factors.
   The proof must supply the normalized Jacquet comparison and the
   index bijection, rather than take either as a premise.

This route leaves the inducing parabolic and representation fixed. It uses
the inner action on the induced representation to compare the two target
radicals. It needs no Langlands quotient classification or generic relative
comparison. The main upper geometric-lemma proof remains the explicit
input theorem, not a second obligation hidden in this interface.

## Original sources and derived provenance

The retained originals were read directly for this pair on 2026-10-26.
The formulas on Silberger 1979 pp.287–288 were also checked in page images.
No errata file for these sources was present in the current Library's
`notes/errata` directory.

- Bernstein and Zelevinsky, *Induced representations of reductive p-adic
  groups. I* (1977), Corollary 2.13(c) and §2.15(3), printed p.449
  (PDF p.10). Literature ID `bernstein-zelevinsky-1977-induced-i`;
  SHA-256
  `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
  Corollary 2.13(c) gives the gluing of quasicuspidal Weyl transports
  indexed by `W(M,N)/W_M`. Section 2.15(3) counts the cosets that transport
  the inducing representation to a given constituent. The current upper
  theorem encodes the former as a finite actual filtration with minimal
  conjugating representatives.
- Silberger, *Introduction to Harmonic Analysis on Reductive p-adic
  Groups* (1979), Theorem 5.4.1.1, printed pp.287–288 (PDF pp.293–294).
  Literature ID `silberger-1979-harmonic-analysis`; SHA-256
  `b9432812bb48ce0bcd3975144baa6b3cca99bcaaf0d33d785ce68e94e02854fc`.
  The cuspidal case describes the full Jacquet module for either
  fixed-Levi parabolic, with its length and half-modulus-weighted Weyl
  character sum. The bracketed discrete-series case uses only the maximal
  tempered submodule and is not used here.
- Silberger, *The Langlands quotient theorem for p-adic groups* (1978),
  §2 and the preceding multiplicity convention, printed p.97 (PDF p.3).
  Literature ID
  `provided-5423f8a28c0b7ad5a7f9a07a3d55d399d5162a798fecd70bf11a5d75fa8b9354`;
  SHA-256
  `4f437d7ee21c65e43ede0a34b9a6b274cf4d947c23ad7637976bd38fd72fdac5`.
  This page defines multiplicity by composition factors, uses the opposite
  Jacquet module with the positive upper half-modulus in class exponents,
  and records the cuspidal Weyl factors with their multiplicities.

The present conditional proposition is derived, not a direct transcription
of an additional theorem in these sources. Its general smooth
quasicuspidal scope comes from the assumed BZ77 upper filtration and the
algebraic conjugation transfer; it does not generalize Silberger's
irreducible admissible cuspidal theorem by assertion. `ReverseBlocks`,
the existing actual Jacquet wrappers, and the inverse-conjugation
definition of `transport` fix the concrete implementation conventions.
The cited multiplicity results explain the consumer, but this interface
asserts only the actual filtration and its indexed graded equivalences.
Irreducibility transport, composition-factor counts, and Jordan–Hölder
independence can be applied downstream under their separate hypotheses.
