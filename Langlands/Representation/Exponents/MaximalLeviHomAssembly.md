# Morphism dichotomy from the represented geometric lemma

Module `Langlands.Representation.Exponents.MaximalLeviHomAssembly`.

This module is a derived supporting construction and a conditional implication for
Renard III.2.5 and VI.5.3, as used in VII.1.3. It does not give a closed proof of
`MaximalLeviSupercuspidalInductionHomStatement`. Its main theorem takes the full
`RepresentedGeometricLemmaStatement` as an explicit premise, and that statement is
still unproved in the Library. The target statement and everything it imports are
unchanged.

## Provenance

The source is D. Renard, *Représentations des groupes réductifs p-adiques*, French
edition dated 9 July 2026 (literature ID
`renard-2026-representations-groupes-reductifs-padiques`). It gives Frobenius
reciprocity in III.2.5 (printed p.73, PDF p.79), the normalized adjunction
`r_P^G ⊣ i_P^G` in the VI.1.2 Proposition (printed p.136, PDF p.142), and the
supercuspidal consequences of the geometric lemma in VI.5.3 (printed p.173,
PDF p.179). The proof of VII.1.3 (printed pp.224–226, PDF pp.230–232) uses them
through `Hom_G(π, π') ≃ Hom_{M'}(r_{P'}^G i_P^G ρ, ρ')`.

The Lean proof is an internal deduction. It combines:

- the proved `leviFrobeniusReciprocity` (module
  `Langlands.Representation.Exponents.LeviFrobeniusReciprocityProof`);
- the Hom-length bound `HomSpace.length_le_sum_of_isGluedFrom` for naturally glued
  representations (module `Langlands.Representation.Filtration.HomGluing`);
- the identification of the pieces of a self-intersection,
  `GeometricLemmaIntersectionDatum.subsingleton_or_exists_selfPieceEquiv` (module
  `Langlands.Representation.Geometric.SelfIntersectionPiece`), which uses
  supercuspidality;
- `Schur.twistedIntertwinerEquiv` (module `Langlands.Representation.Schur.TwistedHom`):
  a nonzero twisted map between irreducibles is bijective;
- the rational-point formula `rationalPoints_map_innerIso` for inner automorphisms
  and the Levi-point equivalence `leviPointsEquiv`.

It is the morphism counterpart of the published endomorphism assembly
`MaximalLeviEndomorphismAssembly`, which proves
`RepresentedGeometricLemmaStatement → MaximalLeviSupercuspidalInductionEndomorphismStatement`.

## Nonzero maps out of a glued representation

`HomSpace.exists_piece_ne_zero_of_isGluedFrom` (namespace `Langlands.HomSpace`). Let
`F : C ⥤ Rep k G` be glued (`IsGluedFrom F pieces`) from finitely many functors
`pieces i`, let `X` be an object of `C`, and let `σ` be a representation of `G` over the
field `k`. If `f : F(X) → σ` is a nonzero intertwining map, then there are an index `i`
and a nonzero intertwining map `pieces i (X) → σ`.

Proof: if every piece had only the zero map to `σ`, each Hom space would have module
length zero. `length_le_sum_of_isGluedFrom` bounds the length of the Hom space from
`F(X)` by the sum of these lengths, so that space has length zero. It is then a
subsingleton, which contradicts `f ≠ 0`.

## The reciprocity equivalence

`homReciprocityEquiv` (namespace `Langlands.Aubert.General.RepresentedParabolic`).
The data are a nonarchimedean local field `k : Type u`, a connected reductive group
scheme `G` over `k` with its canonical point topology (locally compact and
nonarchimedean), and represented parabolic data `p : P ⟶ G`, `l : M ⟶ P`,
`r : U ⟶ P` with rational Levi, geometric unipotent radical and multiplication
isomorphism. For smooth representations `τ, τ'` of `M(k)` (Levi topology, carrier
universe `v`), it is the complex-linear equivalence

```text
Hom_G(i_P^G τ', i_P^G τ) ≃ₗ[ℂ] Hom_M(r_P^G(i_P^G τ'), τ)
```

chosen from the proved `leviFrobeniusReciprocity`, with `π = i_P^G τ'` and `σ = τ`.
The right side is written with `leviJacquetInductionFunctor`, the composite
`r_P^G ∘ i_P^G` of `RepresentedGeometricLemmaStatement`. Both sides are full spaces of
intertwining maps. No admissibility, irreducibility or supercuspidality is needed.

## Conditional morphism theorem

`maximalLeviSupercuspidalInductionHom_of_geometricLemma` has type

```text
RepresentedGeometricLemmaStatement.{u,v} →
  MaximalLeviSupercuspidalInductionHomStatement.{u,v}.
```

The conclusion is the exact published proposition, with all of its field, topology,
parabolic, properness, maximality, irreducibility and supercuspidality hypotheses. The
only premise beyond the target's own hypotheses is the full represented geometric lemma
at the same universes. The proof uses neither properness nor maximality of `P`, nor
the supercuspidality of `τ`. It does use the irreducibility of `τ` and `τ'` and the
supercuspidality of `τ'`.

The implemented proof proceeds as follows. Let `f : i_P^G τ' → i_P^G τ` have a vector
`x` with `f x ≠ 0`.

1. Apply the assumed geometric lemma with the same represented parabolic on both sides.
   This gives an enumeration `c` of the double cosets `P(k) \ G(k) / P(k)`,
   representatives `z i`, intersection data `D i`, and `IsGluedFrom` for
   `r_P^G ∘ i_P^G` with pieces `(D i).pieceFunctor`.
2. The equivalence `homReciprocityEquiv` is injective, so it sends `f` to a nonzero map
   `r_P^G(i_P^G τ') → τ`. By `exists_piece_ne_zero_of_isGluedFrom` there are an index
   `i` and a nonzero intertwining map `S` from the piece `(D i).pieceFunctor.obj τ'` to
   `τ`.
3. Apply `subsingleton_or_exists_selfPieceEquiv` to `τ'`. A subsingleton piece admits
   only the zero map, which contradicts `S ≠ 0`. Otherwise there are `ψ : M ≅ M` with
   `ψ.hom ≫ l ≫ p = l ≫ p ≫ (G.innerIso (z i)).hom` and a linear equivalence `T` from
   the piece to `τ'` with `T(m · y) = τ'(ψ(m)) (T y)`.
4. The point map `α` of `ψ` is surjective, with inverse the point map of `ψ.inv`. The
   linear map `S ∘ T⁻¹ : τ' → τ` is nonzero and satisfies
   `(S ∘ T⁻¹)(τ'(α m) y) = τ(m) ((S ∘ T⁻¹) y)`. Since `τ'` and `τ` are irreducible,
   `Schur.twistedIntertwinerEquiv` makes it an equivalence between `τ' ∘ α` and `τ`.
   Its inverse `E : τ ≃ₗ[ℂ] τ'` satisfies `E(τ(m) x) = τ'(α m) (E x)`.
5. Case `z i ∉ pointImage (l ≫ p)`: the second alternative holds with `g = z i`,
   `φ = ψ` and `T = E`.
6. Case `z i = (l ≫ p)(m₀)` for some `m₀ ∈ M(k)`: the point map of `l ≫ p` is injective,
   through `leviPointsEquiv`. Evaluating the scheme identity of step 3 on points with
   `rationalPoints_map_innerIso` gives `α(m) = m₀ m m₀⁻¹` for all `m`. Then
   `τ'(m₀)⁻¹ ∘ E` is a linear equivalence `τ → τ'` that commutes with the actions:
   `τ'(m₀⁻¹) τ'(m₀ m m₀⁻¹) = τ'(m) τ'(m₀⁻¹)`. Its inverse, made into an isomorphism by
   `SmoothRep.mkIso`, gives `τ' ≅ τ`, the first alternative.

The proof does not use the identity double-coset index. Every piece that admits a
nonzero map to `τ` gives one of the two alternatives, according to whether its
representative lies in the Levi image.

## Remaining obligation

To apply this implication without an extra premise, a closed proof of
`RepresentedGeometricLemmaStatement.{u,v}` is still needed (Renard VI.5.1, task
`c060fb34-b423-4ac5-8448-788ac7627913`). This module gives no such proof and does not
complete the morphism task.
