# The cuspidal support map is surjective with finite fibres

Author: Worker 6. Module `Langlands.Representation.Exponents.LeviCuspidalSupportSurjectiveStatement`, namespace `Langlands.Aubert.General.RepresentedParabolic`. Statement `LeviCuspidalSupportSurjectiveStatement : Prop`; nothing is proved here.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, VI.7.1, Proposition, printed p.180 / PDF p.186, with its proof on the same page. The registered source ID is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. The Lemma of VI.7.1 defines the cuspidal support map `Sc : Irr(G) → Ω(G)`, sending `π` to the class of a cuspidal datum `(M, (ρ, W))` such that `ρ` is a composition factor of `r_P^G π` for some `P ∈ P(M)`. In translation, the Proposition says: the map `Sc` is a surjection with finite fibres. Its proof says:

- surjectivity is evident by Frobenius reciprocity, taking for `(M, (ρ, W))_G` an irreducible subrepresentation of the induced representation;
- for `P ∈ P(M)` and a cuspidal datum `(M, (ρ, W))`, one wants to show that there are only finitely many `π ∈ Irr(G)` such that `ρ` is a composition factor of `r_P^G π`. Since `r_P^G π` is admissible, Lemma VI.3.6 realizes `ρ` as a quotient of `r_P^G π`, so `Hom_M(r_P^G π, ρ) = Hom_G(π, i_P^G ρ)`, and `i_P^G ρ` has finite length by Lemma VI.6.2.

This is a **derived partial** formulation. It states the two assertions that the proof establishes, for a fixed actual parabolic `P` with Levi `M`, rather than the assertion about the map `Sc` on isomorphism classes (see "Scope"). The functors are the published normalized functors of the represented-parabolic interface, and supercuspidality is written out as the vanishing of normalized Jacquet modules.

## Statement

The statement quantifies over a field `k : Type u` with `[Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [T2Space k]`, so every nonarchimedean local field of any characteristic, and over a group scheme `G` over `Spec k` with `hG : IsConnectedReductive G`. It installs `hG.isAffineHom` and the canonical topology `RationalPointFamily.pointTopology` on `rationalPoints G`, and assumes `[LocallyCompactSpace (rationalPoints G)]` and `[NonarchimedeanGroup (rationalPoints G)]` for that topology. It then quantifies over every actual rational parabolic `p : P ⟶ G` with rational Levi `l : M ⟶ P`, matching geometric unipotent radical `r : N ⟶ P` and `hmul`, and installs on `rationalPoints M` the affine instance, the canonical topology `leviPointTopology l hl` and the derived local-compactness and nonarchimedean-group instances.

For every `ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M)` that is irreducible and supercuspidal, it asserts the conjunction of

- **surjectivity:** there is `π : SmoothRep.{0, u, max u v} ℂ (rationalPoints G)` with `π.IsIrreducible` and an intertwiner `f : ((leviJacquetFunctor p l r …).obj π).representation.IntertwiningMap ρ.representation` with `Function.Surjective f`;
- **finite fibres:** there are `n : ℕ` and `π₀ : Fin n → SmoothRep.{0, u, v} ℂ (rationalPoints G)` such that every `π : SmoothRep.{0, u, v} ℂ (rationalPoints G)` with `π.IsIrreducible` and `SmoothRep.IsSubquotient ρ ((leviJacquetFunctor p l r …).obj π)` is isomorphic to some `π₀ i`.

Supercuspidality of `ρ` means: for every actual rational parabolic `p' : P' ⟶ M` of `M` with rational Levi `l'`, matching radical `r'` and `hmul'`, `¬ IsIso p'` implies `Subsingleton ((jacquetFunctor p' l' r' …).obj ρ)`.

## Interfaces

- `leviJacquetFunctor` is the published normalized Jacquet functor `r_P^G`, valued in smooth representations of `M(F)` with the canonical topology; it keeps the carrier universe.
- `Representation.IntertwiningMap` is Mathlib's type of equivariant linear maps; it allows the carriers of `r_P^G π` and `ρ` to lie in different universes.
- `SmoothRep.IsSubquotient`, `SmoothRep.IsIrreducible` and isomorphism `≅` in the category of smooth representations are the published interfaces.
- Supercuspidality is as in the published `MaximalLeviSupercuspidalReducibilityStatement`, following Renard's definition (VI.2.1, printed p.137 / PDF p.143).

## Scope

- **Surjectivity.** The source takes an irreducible subrepresentation `π` of `i_P^G ρ`; its carrier lies in the universe `max u v` of the induced representation, which is why `π` is taken there. A surjective intertwiner `r_P^G π → ρ` makes `ρ` a quotient, hence a composition factor, of `r_P^G π`, so `Sc(π)` is the class of `(M, ρ)`. The statement asserts this for every `P` with Levi `M`, which is what the proof gives.
- **Finite fibres.** The fibre of `Sc` over the class of `(M, ρ)` consists of the irreducible `π` such that some associated cuspidal datum `(M', ρ')` is a composition factor of `r_{P'}^G π` for some `P' ∈ P(M')`. The proof treats one `P ∈ P(M)` and one `ρ`, and the statement asserts exactly that finiteness, up to isomorphism, for representations with carriers in an arbitrary universe `v`. Deducing finiteness of the whole fibre also uses conjugation of associated data and finiteness of `P(M)`; these are not part of the statement.
- **Composition factors.** In the finiteness clause, "composition factor" is read as "subquotient", which is equivalent for the irreducible `ρ` and the finite-length representation `r_P^G π` (VI.6.4).
- Every actual rational parabolic is allowed, not only standard ones.

## Remaining obligations

The proof is a separate obligation. It uses finite length of `i_P^G ρ` (VI.6.2; represented form `LeviInductionFiniteLengthStatement`), admissibility of `r_P^G π` (Corollary VI.6.1; published `ArbitraryParabolicJacquetAdmissibilityStatement`), Lemma VI.3.6 and Frobenius reciprocity (published `LeviFrobeniusReciprocityStatement`). Lemma VI.3.6 is not stated for represented parabolics.

## Provenance

This is a derived partial statement of the Proposition of VI.7.1 for the represented-parabolic interface. It states the two assertions proved in the source for a fixed parabolic; the functors are the published `leviJacquetFunctor` and `jacquetFunctor`.
