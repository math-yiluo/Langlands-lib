# Proof of the morphism dichotomy between inductions from supercuspidals of maximal Levis

Module `Langlands.Representation.Exponents.MaximalLeviSupercuspidalInductionHomProof`.
Namespace `Langlands.Aubert.General.RepresentedParabolic`.

## Statement proved

`maximalLeviSupercuspidalInductionHom` has type exactly
`MaximalLeviSupercuspidalInductionHomStatement.{u, v}` (module
`Langlands.Representation.Exponents.MaximalLeviReducibilityUnitaryInputs`). The field
universe `u` and the carrier universe `v` are independent, and the theorem has no
hypotheses. The setting:

- `k` is a nonarchimedean local field;
- `G` is a connected reductive group over `k`, and `G(k)` carries the canonical point
  topology and is locally compact and nonarchimedean;
- `p : P ⟶ G` is a proper maximal rational parabolic, with rational Levi `l : M ⟶ P` and
  geometric unipotent radical `r : U ⟶ P`;
- `τ, τ'` are irreducible supercuspidal representations of `M(k)` with its Levi topology.

Let `f : i_P^G τ' → i_P^G τ` be nonzero. Then `τ' ≅ τ`, or there are `g ∈ G(k)` outside
the image of `M(k)` and an automorphism `φ : M ≅ M` that is conjugation by `g` inside `G`,
with a linear equivalence `T : τ ≃ τ'` satisfying `T (τ(m) x) = τ'(φ(m)) (T x)`.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*
(`renard-2026-representations-groupes-reductifs-padiques`): Frobenius reciprocity in
III.2.5 (printed p.73, PDF p.79), the normalized adjunction `r_P^G ⊣ i_P^G` in the VI.1.2
Proposition (printed p.136, PDF p.142), the supercuspidal consequences of the geometric
lemma in VI.5.3 (printed p.173, PDF p.179), and their use in the proof of VII.1.3 (printed
pp.224–226, PDF pp.230–232).

## Proof

The theorem applies two published results:

- the conditional theorem `maximalLeviSupercuspidalInductionHom_of_geometricLemma` (module
  `Langlands.Representation.Exponents.MaximalLeviHomAssembly`). Its only premise is
  `RepresentedGeometricLemmaStatement.{u, v}`;
- the unconditional proof `representedGeometricLemma : RepresentedGeometricLemmaStatement.{u, v}`
  (module `Langlands.Representation.Geometric.RepresentedGeometricLemmaProof`, Renard VI.5.1).

The Markdown of `MaximalLeviHomAssembly` describes the argument of the conditional
theorem. In summary:

1. Frobenius reciprocity (`leviFrobeniusReciprocity`, Renard III.2.5 with VI.1.2) sends `f`
   to a nonzero map `r_P^G i_P^G τ' → τ`.
2. The geometric lemma with `Q = P` gives a finite natural filtration of `r_P^G i_P^G τ'`,
   indexed by the double cosets `P(k) \ G(k) / P(k)`, with intersection data for the
   representatives `z`. Some graded piece therefore has a nonzero map to `τ`.
3. By the supercuspidality of `τ'` and `subsingleton_or_exists_selfPieceEquiv`, that piece
   is the twist `τ' ∘ ψ` of `τ'` by an automorphism `ψ` of `M` that is conjugation by `z`
   (Renard VI.5.3). Schur's lemma makes the nonzero map an isomorphism, which gives
   `E : τ ≃ τ'` with `E(τ(m) x) = τ'(ψ(m)) (E x)`.
4. If `z` lies outside the Levi image, this is the second alternative with `g = z` and
   `φ = ψ`. If `z = m₀` lies in the Levi image, then `ψ` is conjugation by `m₀`, and
   `τ'(m₀)⁻¹ ∘ E` is an isomorphism `τ ≅ τ'`.

Properness and maximality of `P` and the supercuspidality of `τ` are not used.
