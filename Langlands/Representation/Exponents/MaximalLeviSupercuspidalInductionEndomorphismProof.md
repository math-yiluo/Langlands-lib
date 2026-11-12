# Proof of the endomorphism dichotomy for inductions from supercuspidals of maximal Levis

Module `Langlands.Representation.Exponents.MaximalLeviSupercuspidalInductionEndomorphismProof`.
Namespace `Langlands.Aubert.General.RepresentedParabolic`.

## Statement proved

`maximalLeviSupercuspidalInductionEndomorphism` has type exactly
`MaximalLeviSupercuspidalInductionEndomorphismStatement.{u, v}` (module
`Langlands.Representation.Exponents.MaximalLeviReducibilityUnitaryInputs`). The field universe
`u` and the carrier universe `v` are independent. The theorem has no premises.

The statement fixes the following data:

- a nonarchimedean local field `k`;
- a connected reductive `G` over `k`, whose points `G(k)` carry the canonical point topology
  and are locally compact and nonarchimedean;
- a rational parabolic `p : P ⟶ G` with rational Levi `l : M ⟶ P`, geometric unipotent
  radical `r : U ⟶ P` and multiplication isomorphism;
- `p` is not an isomorphism (properness);
- `p` is maximal: every factorization `j ≫ q = p` through a parabolic `q : Q ⟶ G` has `j` or
  `q` an isomorphism;
- an irreducible `ρ` of `M(k)` with its Levi topology, carrier universe `v`;
- `ρ` is supercuspidal: its Jacquet module along every proper rational parabolic of `M` is a
  subsingleton.

Then every endomorphism `f` of `i_P^G ρ` satisfies one of two alternatives:

1. `f` is a scalar, `f x = c • x` for one `c : ℂ`;
2. there are `g ∈ G(k)` outside `pointImage (l ≫ p)` and an automorphism `φ : M ≅ M` with
   `φ ≫ l ≫ p = l ≫ p ≫ inn(g)`, and a linear automorphism `T` of `ρ` with
   `T (ρ(m) x) = ρ(φ(m)) (T x)`.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, edition dated 9 July 2026
(`renard-2026-representations-groupes-reductifs-padiques`):

- normalized Frobenius reciprocity, III.2.5 (printed p.73, PDF p.79);
- the geometric lemma, VI.5.1 (printed pp.161–162, PDF pp.167–168);
- its supercuspidal consequences, VI.5.3 (printed p.173, PDF p.179);
- the maximal-Levi application, VII.1.3 (printed pp.224–226, PDF pp.230–232).

## Proof

The proof is one application. The published conditional theorem
`maximalLeviSupercuspidalInductionEndomorphism_of_geometricLemma` (module
`Langlands.Representation.Exponents.MaximalLeviEndomorphismAssembly`) has type
`RepresentedGeometricLemmaStatement.{u, v} → MaximalLeviSupercuspidalInductionEndomorphismStatement.{u, v}`.
It is applied to the published closed proof `representedGeometricLemma` of the represented
geometric lemma (Renard VI.5.1; module
`Langlands.Representation.Geometric.RepresentedGeometricLemmaProof`), at the same universes.

The Markdown of the conditional theorem describes its argument. In summary:

1. Frobenius reciprocity (`leviFrobeniusReciprocity`) identifies `End_G(i_P^G ρ)` with
   `Hom_M(r_P^G i_P^G ρ, ρ)`.
2. The geometric lemma with `Q = P` gives a finite filtration of `r_P^G i_P^G ρ`. It is indexed
   by the double cosets `P(k) \ G(k) / P(k)` and has intersection data at representatives `z`.
3. Supercuspidality and `subsingleton_or_exists_selfPieceEquiv` make each piece either zero or
   isomorphic to a twist `ρ ∘ ψ`. Here `ψ` is an automorphism of `M` that is conjugation by `z`
   (Renard VI.5.3). By Schur's lemma, the Hom space from each nonzero piece to `ρ` has length at
   most one.
4. The Hom-gluing lemma then gives two cases. Either `f` is a scalar, or some piece other than
   the identity piece has a nonzero map to `ρ`. In the second case the piece is a twist
   `ρ ∘ ψ`, and Schur's lemma makes the nonzero map an isomorphism. Its representative `z` lies
   outside the parabolic image, hence outside the Levi image. This is the second alternative
   with `g = z` and `φ = ψ`.

The proof does not use properness or maximality of `P`. It adds no admissibility or
finite-dimensionality premise.
