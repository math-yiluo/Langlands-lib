# Endomorphism dichotomy from the represented geometric lemma

Module `Langlands.Representation.Exponents.MaximalLeviEndomorphismAssembly`.
Namespace `Langlands.Aubert.General.RepresentedParabolic`.

This is a derived supporting construction and a conditional implication for
Renard III.2.5 and VI.5.3, as used in VII.1.3. It does not provide a closed proof of
`MaximalLeviSupercuspidalInductionEndomorphismStatement`. Its theorem explicitly
assumes the full `RepresentedGeometricLemmaStatement`, whose proof remains a
separate obligation. The original statement and its imports are unchanged.

## Provenance

Renard's *Représentations des groupes réductifs p-adiques*, edition dated
9 July 2026, gives normalized Frobenius reciprocity in III.2.5 (printed p.73,
PDF p.79), the supercuspidal consequences of the geometric lemma in VI.5.3
(printed p.173, PDF p.179), and the maximal-Levi application in VII.1.3
(printed pp.224–226, PDF pp.230–232). The implementation combines proved
Frobenius reciprocity, scalar Schur for actual Levi points, finite-filtration Hom
bounds, and the identification of a supplied nonzero self-intersection piece.
It assumes the actual full geometric lemma rather than constructing its
filtration.

The algebraic Hom-space and twisted-piece arguments are internal deductions.
The self-intersection identification comes from
`GeometricLemmaIntersectionDatum.subsingleton_or_exists_selfPieceEquiv`.
That result uses supercuspidal Jacquet vanishing and the full-parabolic Jacquet
and induction equivalences. The double-coset exclusion uses
`not_mem_pointImage_levi_of_ne_identityDoubleCosetIndex`.

## Endomorphism-to-Hom equivalence

`endomorphismReciprocityEquiv` fixes a nonarchimedean local field `k : Type u`,
a connected reductive group scheme `G` over `k`, the canonical ambient point
topology, local compactness and a nonarchimedean group structure on `G(k)`.
For represented parabolic data `p : P ⟶ G`, `l : M ⟶ P`, `r : U ⟶ P`
with a rational Levi, geometric unipotent radical and multiplication
isomorphism, it constructs the complex-linear equivalence

```text
End_G(i_P^G ρ) ≃ₗ[ℂ] Hom_M(r_P^G(i_P^G ρ), ρ).
```

Both sides are the full actual intertwining-map spaces. The definition chooses
the equivalence supplied by the proved `leviFrobeniusReciprocity`, specialized
to the induced representation and `ρ`. The Jacquet-induction composite is
`leviJacquetInductionFunctor`. The representation `ρ` has carrier universe `v`
independently of the field universe `u`; induction has carrier universe
`max u v`. No finite-dimensionality, admissibility, irreducibility or
supercuspidality is required for this equivalence.

## Conditional endomorphism theorem

`maximalLeviSupercuspidalInductionEndomorphism_of_geometricLemma` has type

```text
RepresentedGeometricLemmaStatement.{u,v} →
  MaximalLeviSupercuspidalInductionEndomorphismStatement.{u,v}.
```

The conclusion is the exact published proposition, including all its field,
topology, parabolic, properness, maximality, irreducibility and supercuspidality
hypotheses. The proof never uses properness or maximality: the supplied
self-intersection data and finite filtration give the required alternative
without those two hypotheses. It adds no admissibility or finite-dimensionality
premise. The only premise outside the target is the full represented geometric
lemma shown above.

The implemented proof proceeds as follows.

1. Apply the assumed geometric lemma with the same represented parabolic on
   both sides. This supplies a finite enumeration of the actual double cosets
   `P(k) \ G(k) / P(k)`, compatible representatives `z i`, actual intersection
   data `D i`, and a natural filtration giving `IsGluedFrom` for
   `r_P^G ∘ i_P^G`.
2. For every piece, use supercuspidality and
   `subsingleton_or_exists_selfPieceEquiv`. Either its carrier is a
   subsingleton, so all maps to `ρ` vanish, or there are an actual scheme
   automorphism `ψ : M ≅ M` and a linear equivalence `T` from the piece to `ρ`
   satisfying
   `T(piece(m)x) = ρ(ψ(k)(m))(T x)`.
   The same `ψ` satisfies
   `ψ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso (z i)).hom`.
3. The point map of `ψ` is surjective, with inverse given by the point map of
   `ψ.inv`. Scalar Schur for `ρ` in its canonical Levi topology follows from
   `Schur.leviPoint_scalarEndomorphism`. Then
   `Schur.length_hom_le_one_of_twistedPiece` bounds the complex module length
   of the full Hom space from each nonzero piece to `ρ` by one.
   The zero pieces have Hom length zero. In particular, the distinguished
   piece at the identity double-coset index has Hom length at most one.
4. Use `HomSpace.scalar_or_exists_off_piece_of_isGluedFrom` with the actual
   Frobenius equivalence and that distinguished-piece bound. For the given
   induced endomorphism, either it is a scalar multiple of the identity as an
   intertwiner, or a different supplied piece admits a nonzero map `S` to `ρ`.
   Evaluating intertwiner equality gives the target's pointwise scalar
   alternative.
5. A subsingleton piece cannot admit this nonzero `S`. In the other case,
   `Schur.inverseTwistedPieceEquiv` produces an actual representation
   equivalence `ρ.Equiv (ρ.comp (rationalPoints.map ψ.hom))`.
   Its underlying linear equivalence has precisely the target's covariance:
   `E(ρ(m)x) = ρ(ψ(k)(m))(E x)`.
6. Set `g = z i` and `φ = ψ`. The scheme compatibility is the one supplied by
   the piece identification. Since `i` differs from the identity double-coset
   index, `g` is outside the parabolic point image, hence outside
   `pointImage (l ≫ p)`. This gives every part of the exceptional alternative.

The identity representative is only known to lie in the parabolic image.
The proof needs no assertion that it lies in the Levi image and no comparison
of its conjugation with an inner Levi action.

## Remaining obligation

A closed proof of `RepresentedGeometricLemmaStatement.{u,v}` is still needed
to apply this implication without an extra premise. This module provides no
such proof and does not complete the maximal-Levi endomorphism task.
