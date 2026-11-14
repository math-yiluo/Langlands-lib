# Geometric conjugators between presentations of the algebraic fundamental group

Author: Worker 149 (Task 6302). This is a helper module for the proof of
`Langlands.GroupScheme.AlgebraicFundamentalGroup.AlgebraicFundamentalGroupComparisonStatement`
in `Langlands.GroupScheme.AlgebraicFundamentalGroupComparisonProof`.

## Setting

Everything works with the definitions of
`Langlands/GroupScheme/AlgebraicFundamentalGroup.lean`. Fix a field `k`, a field
extension `E` of `k` (no separable closure hypothesis is needed in this module), and a
group scheme `G` over `Spec k`. Write `_E` for base change along
`algebraBaseMap k E`. For two presentations `a b : Choice k G` (maximal torus and
simply connected derived cover), a pair `(g, e)` of a point
`g ∈ G_E(E)` and an isomorphism `e : (T_a)_E ≅ (T_b)_E` is a *conjugator* when
`a.IsConjugationComparison E b g e` holds, that is
`(i_a)_E ≫ int(g) = e ≫ (i_b)_E`.

All declarations are in the namespace
`Langlands.GroupScheme.AlgebraicFundamentalGroup.Choice`.

## Declarations

- `latticeMap E e`: postcomposition with a torus homomorphism
  `e : (T_a)_E ⟶ (T_b)_E`, as a `ℤ`-linear map `a.lattice E →ₗ[ℤ] b.lattice E`;
  `latticeMap_apply` says `latticeMap E e ν = ν ≫ e`.
- `isConjugationComparison_refl`: `(1, Iso.refl)` is a conjugator from `a` to `a`.
- `IsConjugationComparison.trans`: conjugators `(g, e)` from `a` to `b` and `(h, e')` from
  `b` to `c` give the conjugator `(h * g, e ≪≫ e')` from `a` to `c`.
- `IsConjugationComparison.symm`: a conjugator `(g, e)` from `a` to `b` gives the conjugator
  `(g⁻¹, e.symm)` from `b` to `a`.
- `IsConjugationComparison.isNormalizingPoint`: two conjugators `(g, e)`, `(g', e')` from
  `a` to `b` give the normalizing point `g' * g⁻¹` of `(i_b)_E` acting through
  `e.symm ≪≫ e'`. This is `h.symm.trans h'`, since `IsNormalizingPoint` and a conjugator
  from `b` to `b` are the same equation.
- `IsConjugationComparison.exists_galois` (Galois transport): for a conjugator `(g, e)` from
  `a` to `b` and `σ : E ≃ₐ[k] E` there is another conjugator `(g', e')` from `a` to `b`
  such that for every `ν : a.lattice E`
  `cocharacterLattice.galoisRepresentation k E b.torus σ (ν ≫ e.hom) =
   cocharacterLattice.galoisRepresentation k E a.torus σ ν ≫ e'.hom`.
- `projection_comp_eq_of_conjugation`: suppose every conjugator `(n, σ)` from `b` to itself
  satisfies `ξ ≫ σ.hom - ξ ∈ b.corootImage E` for all `ξ`. Then two conjugators `(g, e)`,
  `(g', e')` from `a` to `b` give the same class: `b.projection E (ν ≫ e'.hom) =
  b.projection E (ν ≫ e.hom)`.
- `atChoice_hom_ext`: two `ℤ`-linear maps out of `a.atChoice E` agree if they agree on all
  `a.projection E ν`.
- `isCanonicalComparison_mapQ`: if `(g, e)` is a conjugator and `latticeMap E e.hom` maps
  `a.corootImage E` into `b.corootImage E`, then the induced quotient map `mapQ` is a
  canonical comparison (`IsCanonicalComparison`).
- `comparison_projection_of_conjugation`: under the two hypotheses "every conjugator from
  `a` to `b` preserves coroot images" and "conjugators from `b` to itself act trivially
  modulo `b.corootImage E`", the epsilon-chosen `a.comparison E b` satisfies
  `a.comparison E b (a.projection E ν) = b.projection E (ν ≫ e.hom)` for every conjugator
  `(g, e)` from `a` to `b`.
- `comparison_of_conjugators` (**assembly**): for fixed `k`, `E` and `G`, four hypotheses
  give every clause of the body of `AlgebraicFundamentalGroupComparisonStatement` (the
  part after the quantifiers over `k`, `E`, `G` and `IsConnectedReductive G`). The
  hypotheses are:
  - `hA` (existence): for all `a b` some conjugator from `a` to `b` exists;
  - `hB` (coroot preservation): every conjugator `(g, e)` from `a` to `b` satisfies
    `a.corootImage E ≤ (b.corootImage E).comap (latticeMap E e.hom)`;
  - `hC` (Weyl triviality): every conjugator `(n, σ)` from `b` to `b` satisfies
    `ξ ≫ σ.hom - ξ ∈ b.corootImage E` for all `ξ : b.lattice E`;
  - `hD` (Galois transport): exactly the conclusion of `IsConjugationComparison.exists_galois`.

## Provenance

These are internal lemmas. They split the comparison argument of Kaletha–Prasad (2023),
Construction 11.3.1 (printed p. 427, PDF p. 458) into its four geometric inputs. The
source says that conjugation of maximal tori over a separable closure gives an
isomorphism of the quotients `X_*(T)/X_*(T_sc)`, independent of the conjugating element
because the Weyl group acts trivially on the quotient. No literature statement is
claimed for the Lean declarations.

## Proofs

- `trans`, `symm`, `isConjugationComparison_refl`: rewrite with `innerIso_mul_hom`,
  `innerIso_inv_hom`, `innerIso_one_hom` (`Langlands.GroupScheme.InnerAutomorphismHom`)
  and reassociate.
- `exists_galois`: let `α` be the Galois base map of `σ` and
  `e' = descentBaseChangeIso⁻¹ ≫ (base change of e along α) ≫ descentBaseChangeIso`
  (`CommGroupScheme.descentBaseChangeIso`,
  `Langlands.GroupScheme.Reductive.RootDatumGaloisCoroots`). The conjugacy
  `HomConjugate (i_a)_E (e ≫ (i_b)_E)` is base changed along `α`, then postcomposed and
  precomposed with the descent isomorphisms (`HomConjugate.baseChange`, `.postcomp`,
  `.precomp`, `Langlands.GroupScheme.ConjugacyBaseChange`). This gives `g'`. The
  conjugator equation then follows from `descentBaseChangeIso_naturality`
  (`Langlands.GroupScheme.CocharacterTransportNaturality`). The Galois identity holds
  because the Galois action on cocharacters is `transportCocharacter`, which unfolds to the
  same three-step composite. The underlying group homomorphism of `e'` is given by an
  explicit `rfl` formula to avoid unfolding large transports.
- `projection_comp_eq_of_conjugation`: apply the hypothesis to the conjugator
  `h.symm.trans h'` from `b` to `b` at `ν ≫ e.hom`. Then
  `(ν ≫ e.hom) ≫ (e.symm ≪≫ e').hom = ν ≫ e'.hom`, so the difference lies in the coroot
  image and `Submodule.Quotient.eq` closes the goal.
- `comparison_projection_of_conjugation`: `isCanonicalComparison_mapQ` gives existence of a
  canonical comparison, so `comparison_spec` makes `a.comparison E b` canonical through
  some conjugator `(g₀, e₀)`. Then `projection_comp_eq_of_conjugation` replaces `e₀` by `e`.
- `comparison_of_conjugators`: call the formula of the previous item `happly`.
  - Identity law: apply `happly` to the conjugator `(1, Iso.refl)` and use
    `atChoice_hom_ext`.
  - Composition law: take conjugators `a → b` and `b → c` from `hA`, compose them with
    `trans`, and apply `happly` three times.
  - Canonicity: `comparison_spec`, using `hA`, `hB` and `isCanonicalComparison_mapQ`.
  - Uniqueness: any canonical `f` comes with a conjugator, and `happly` for that conjugator
    and `atChoice_hom_ext` give `f = a.comparison E b`.
  - Bijectivity: `b.comparison E a` is a two-sided inverse by the identity and composition
    laws.
  - Galois equivariance: lift `x` to some `ν` (`mkQ_surjective`) and use
    `galoisRepresentation_projection`. Apply `happly` to `(g', e')` from `hD` and to
    `(g, e)`, then rewrite with the Galois identity of `hD`.
  - Conjugator formula: `happly` itself.
