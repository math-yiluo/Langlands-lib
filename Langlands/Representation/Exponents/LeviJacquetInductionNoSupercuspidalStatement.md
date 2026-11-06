# Jacquet modules of supercuspidal inductions along non-conjugate Levis

Author: Worker 6. Module `Langlands.Representation.Exponents.LeviJacquetInductionNoSupercuspidalStatement`, namespace `Langlands.Aubert.General.RepresentedParabolic`. Statement `LeviJacquetInductionNoSupercuspidalStatement : Prop`; nothing is proved here.

The source is David Renard, *Représentations des groupes réductifs p-adiques*, French edition dated 9 July 2026, VI.5.3, Proposition, assertion (ii), printed p.173 / PDF p.179, with its proof on the same page. The registered source ID is `renard-2026-representations-groupes-reductifs-padiques`, SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. In translation, the Proposition says: let `P = MN` and `Q = LU` be parabolic subgroups of `G`, `(ρ, W)` a supercuspidal representation of `M`, and put `τ = r_Q^G i_P^G ρ`. Then (ii) if `M` is not conjugate to `L` in `G`, then `τ` has no supercuspidal subquotient. The proof says this is an immediate consequence of (i) and of the Lemma of VI.5.2, which concerns irreducible subquotients. Assertion (i) is the separate statement `LeviJacquetInductionVanishingStatement`; assertion (iii) is not stated.

This is a **derived** formulation, because the functors are the published normalized functors of the represented-parabolic interface, supercuspidality is written out as the vanishing of normalized Jacquet modules, conjugacy of `M` and `L` is expressed through an isomorphism of group schemes, and "subquotient" is read as "irreducible subquotient" (see "Faithfulness notes").

## Statement

The statement quantifies over a field `k : Type u` with `[Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [T2Space k]`, so every nonarchimedean local field of any characteristic, and over a group scheme `G` over `Spec k` with `hG : IsConnectedReductive G`. It installs `hG.isAffineHom` and the canonical topology `RationalPointFamily.pointTopology` on `rationalPoints G`, and assumes `[LocallyCompactSpace (rationalPoints G)]` and `[NonarchimedeanGroup (rationalPoints G)]` for that topology. It then quantifies over two actual rational parabolic triples:

- `P = MN`: `p : P ⟶ G`, `l : M ⟶ P`, `r : N ⟶ P` with `hp`, `hl`, `hr`, `hmul`;
- `Q = LU`: `q : Q ⟶ G`, `lQ : L ⟶ Q`, `rQ : U ⟶ Q` with `hq`, `hlQ`, `hrQ`, `hmulQ`.

It assumes that there are no `g : rationalPoints G` and `φ : M ≅ L` with `φ.hom ≫ lQ ≫ q = l ≫ p ≫ (G.innerIso g).hom`, that is, `g M g⁻¹ ≠ L` for every `g ∈ G(F)`.

On `rationalPoints M` and `rationalPoints L` it installs the affine instances, the canonical topologies `leviPointTopology l hl` and `leviPointTopology lQ hlQ`, and the derived local-compactness and nonarchimedean-group instances from `ArbitraryParabolicLeviPoints`. For every `ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M)` that is supercuspidal, and every `σ : SmoothRep.{0, u, max u v} ℂ (rationalPoints L)` with `σ.IsIrreducible` and

`SmoothRep.IsSubquotient σ ((leviJacquetFunctor q lQ rQ hq hrQ hlQ hmulQ).obj ((leviInductionFunctor p l r hp hr hl hmul).obj ρ))`,

it asserts that `σ` is not supercuspidal as a representation of `L(F)`: it is not the case that for every actual rational parabolic `p' : P' ⟶ L` with rational Levi `l'`, matching radical `r'` and `hmul'`, `¬ IsIso p'` implies `Subsingleton ((jacquetFunctor p' l' r' hp' hr' hl' hmul').obj σ)`. Supercuspidality of `ρ` is the same condition for the parabolics of `M`.

## Interfaces

- `leviInductionFunctor p l r …` is the published normalized parabolic induction `i_P^G`; it raises the carrier universe from `v` to `max u v`.
- `leviJacquetFunctor q lQ rQ …` is the published normalized Jacquet functor along `Q`, valued in smooth representations of `L(F)` with its canonical topology. It keeps the carrier universe, so `σ` has carriers in `Type (max u v)`.
- `SmoothRep.IsSubquotient` and `SmoothRep.IsIrreducible` are the published smooth-representation predicates.
- `jacquetFunctor p' l' r' …` is the published normalized Jacquet functor. Supercuspidality is as in the published `MaximalLeviSupercuspidalReducibilityStatement`, following Renard's definition (VI.2.1, printed p.137 / PDF p.143).

## Faithfulness notes

- The zero representation is supercuspidal in Renard's sense, since all of its Jacquet modules vanish, and it is a subquotient of every representation. The assertion "no supercuspidal subquotient" therefore concerns nonzero subquotients. The proof in the source applies the Lemma of VI.5.2, which is about irreducible subquotients. The statement accordingly asserts that no irreducible subquotient of `τ` is supercuspidal.
- The Proposition is stated for arbitrary parabolics `P` and `Q`, and so is the statement. `ρ` is supercuspidal but not necessarily irreducible or admissible.
- "Not conjugate" is the negation of `g M g⁻¹ = L` for some `g ∈ G(F)`, as subgroup schemes of `G`, expressed by the nonexistence of an isomorphism `φ` compatible with conjugation by `g`.

## Remaining obligations

The proof is a separate obligation. The source deduces (ii) from (i) and the Lemma of VI.5.2 applied to `L`. By (i), `τ = 0` unless some Levi subgroup of `L` is conjugate to `M`, which is then proper in `L`. The pieces of the geometric lemma are then normalized inductions from proper parabolics of `L`, and none of their irreducible subquotients is supercuspidal. The relevant published statements are `LeviJacquetInductionVanishingStatement`, `LeviInductionNoSupercuspidalSubquotientStatement` and `RepresentedGeometricLemmaStatement`. A proof also needs that an irreducible subquotient of a representation with a finite filtration is a subquotient of one of its graded pieces.

## Provenance

This is a derived statement of assertion (ii) of the Proposition of VI.5.3 for the represented-parabolic interface. The functors are the published `leviInductionFunctor`, `leviJacquetFunctor` and `jacquetFunctor`, and conjugation is the published `GroupScheme.innerIso`.
