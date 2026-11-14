# The Hilbert scheme of a projective flat family on all test schemes, with its universal closed subscheme and projective Hilbert-polynomial pieces

Author: Worker 22, for task `07219dde-fd87-48cf-83be-db16cbb3707c` (Task 5705).
This is a prerequisite statement under Task 5705, as permitted by the operator's
answer to request `98389b48910e54088e0e2b2ba6aaad9c`. Together with
`Langlands.AlgebraicGeometry.Picard.RelativeEffectiveCartierLocusStatement`, it
is one of the two hypotheses of a planned reduction of the published
`Langlands.AlgebraicGeometry.Picard.RelativeEffectiveDivisorHilbertPiecesStatement`
(Task 6002).

## Statement

`Langlands.AlgebraicGeometry.HilbertSchemeUniversalFamilyStatement.{u}` is a
proposition with no proof asserted here.

**Data and hypotheses.** It quantifies over

- a commutative ring `A : Type u`, with `S = Spec (CommRingCat.of A)`. `A` need
  not be noetherian;
- a scheme `X`, a morphism `f : X ⟶ S` and a module `𝓛X : X.Modules`.

It assumes

- `Flat f` and `LocallyOfFinitePresentation f`;
- `Scheme.Modules.IsInvertible 𝓛X`;
- `Scheme.Modules.ClosedImmersionBySections 𝓛X f`: finitely many global
  sections of `𝓛X` define a closed immersion of `X` into a finite projective
  space over `A`.

These are exactly the hypotheses of the Library theorem
`AlgebraicGeometry.exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPieces_of_closedImmersionBySections`
(the "FLT Hilbert theorem", ported from the Anthropic FLT formalization). There
the first two are instance arguments; here they are explicit hypotheses.

**Conclusion.** There are a scheme `H`, a morphism `πH : H ⟶ S` and an ideal
sheaf `W : (pullback f πH).IdealSheafData` on `X ×_S H` with the following
properties.

1. `LocallyOfFinitePresentation πH` and `IsSeparated πH`.
2. *The Hilbert functor on all test schemes.* Let `T : Scheme.{u}` and
   `s : T ⟶ S`. For `g : T ⟶ H` with `hg : g ≫ πH = s`, write
   `g_X = pullback.map f s f πH (𝟙 X) g (𝟙 _) _ _ : X ×_S T ⟶ X ×_S H`, the
   morphism induced by `g`.
   - For every such `g`, the closed subscheme of the pulled-back ideal
     `W.comap g_X` is flat and locally of finite presentation over `T`. Formally,
     the composite `(W.comap g_X).subschemeι ≫ pullback.snd f s` is `Flat` and
     `LocallyOfFinitePresentation`.
   - For every ideal sheaf `I : (pullback f s).IdealSheafData` such that
     `I.subschemeι ≫ pullback.snd f s` is flat and locally of finite
     presentation, there is exactly one `g : T ⟶ H` with `g ≫ πH = s` and
     `W.comap g_X = I`.

   So pulling back `W` is a bijection from the morphisms `T ⟶ H` over `S` onto
   the ideal sheaves on `X ×_S T` whose closed subschemes are flat and locally
   of finite presentation over `T`. This holds for every scheme `T` in universe
   `u`: noetherian or not, quasi-compact or not, separated or not. `W` is the
   universal closed subscheme.
3. *Hilbert-polynomial pieces.* There is a family `U : Polynomial ℚ → H.Opens`.
   Its members are pairwise disjoint (`Pairwise (Disjoint on U)`) and cover `H`
   (`⨆ θ, U θ = ⊤`). For every `θ`:
   - `IsHProjective ((U θ).ι ≫ πH)`: the open subscheme `U θ` has a closed
     immersion into some `ProjectiveSpace A n` over `S`. This is the Library
     notion from `Langlands.AlgebraicGeometry.ProjectiveSpace`.
   - Take an affine test: a ring `B : Type u`, `s : Spec B ⟶ S`, and
     `g : Spec B ⟶ H` with `hg : g ≫ πH = s`. Let `I = W.comap g_X` be the
     classified ideal and `ι = I.subschemeι`. Then `g` lands in `U θ`
     (`Set.range g.base ⊆ U θ`) if and only if the following holds. For every
     algebraically closed field `k : Type u` and every ring map `sk : B →+* k`,
     there is `n₀` such that for all `n ≥ n₀`,
     `Scheme.Modules.geomFibreH0Finrank (ι ≫ pullback.snd f s) (M^{⊗ n}) k sk = θ(n)`
     in `ℚ`. Here `M` is the pullback of `𝓛X` along
     `ι ≫ pullback.fst f s : I.subscheme ⟶ X`. The tensor power `M^{⊗ n}` is
     written, exactly as in the FLT Hilbert theorem, as `Nat.rec` on `n`, starting
     from the monoidal unit and tensoring with `M` on the right. In words, `θ(n)`
     is the dimension of the global sections of `M^{⊗ n}` on the geometric fibre
     of the classified closed subscheme over `Spec k`.

   The piece clause is token-for-token the piece clause of the FLT Hilbert
   theorem, specialised to `Z = I.subscheme` and `ι = I.subschemeι`. It has
   exactly the same form as item 3 of
   `Picard.RelativeEffectiveDivisorHilbertPiecesStatement`.

## Sources

The statement has provenance *derived*. It packages the FLT Hilbert theorem in
the form used in the literature: a Hilbert scheme with a universal family whose
pieces are projective. The FLT theorem lacks this form in three ways. Its tests
are affine. It has no universal family. Its pieces are only shown to be clopen
and quasi-compact over `S`.

- **FLT Hilbert theorem** (Library,
  `Langlands/AnthropicFLT/Theorems/Thm_AlgebraicGeometry_exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPieces_of_closedImmersionBySections.lean`).
  Under the hypotheses above it gives `Hilb`, `πH : Hilb ⟶ S` and a classifier
  `pt`. The classifier sends each closed immersion `ι : Z ⟶ X ×_S Spec B`,
  flat and locally of finite presentation over `Spec B`, to a morphism
  `Spec B ⟶ Hilb` over `S`, for every ring `B`. The theorem states that `pt` is
  natural for ring maps `B → B'` acting by base change, surjective, and
  injective up to isomorphism of `Z` over `X ×_S Spec B`. It also states that
  `πH` is separated and locally of finite presentation. Finally, it gives
  clopen pieces `U θ`, quasi-compact over `S`, with the piece clause of item 3.
- **FLT per-polynomial theorem**
  `AlgebraicGeometry.exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPolynomial_eq_of_closedImmersionBySections`.
  For each `θ` it gives a scheme `C_θ`, proper and locally of finite
  presentation over `S`, that represents the same functor on affine tests,
  restricted to the closed subschemes satisfying the `θ` clause. Its solution
  file
  `Langlands/AnthropicFLT/P2M/Sol/S_AlgebraicGeometry_exists_scheme_represents_flat_lfp_closedSubscheme_hilbertPolynomial_eq_of_closedImmersionBySections.lean`
  (lines 377–412) constructs `C_θ` as a closed subscheme of
  `HS = H_m ×_{Spec ℤ} Spec A`. Here `H_m` is a scheme over `ULift ℤ` that
  represents the graded Hilbert functor `Point · n (hilbertFunctionOf n θ m)` of
  `ℙⁿ` for a large degree `m`.
- **FLT projective embedding of `H_m`**
  `AlgebraicGeometry.HilbertFunctor.exists_scheme_represents_and_isClosedImmersion_toProjSpace_hilbertFunctionOf`.
  The same point functor is represented by a scheme with a closed immersion into
  `Proj (MvPolynomial (Fin (N + 1)) (ULift ℤ))`. This is the Grassmannian
  embedding of the Hilbert scheme.
- N. Nitsure, *Construction of Hilbert and Quot schemes*
  (`nitsure-2005-hilbert-quot-arxiv-math0504590v1`). pp.3–4 define `Hilb_{X/S}`
  as a functor of closed subschemes, flat over the test scheme, and decompose it
  by Hilbert polynomials computed with respect to a line bundle `L`. Theorem 5.3
  (p.24): over a noetherian `S`, for `X` closed in `ℙⁿ_S` and `L = O(1)|_X`,
  each `Hilb^Φ` is represented by a closed subscheme of some `ℙʳ_S`. Nitsure's
  tests are locally noetherian (p.3).
- S. L. Kleiman, *The Picard scheme*
  (`kleiman-2005-picard-scheme-arxiv-math0504020v1`). The proof of Theorem 3.7
  (p.24) uses `Hilb_{X/S}` together with its universal closed subscheme
  `W ⊂ X × H` and the universal property "there exists a unique map
  `g : T → H` such that `g_X⁻¹ W = D`". This is item 2, with ideal sheaves in
  place of closed subschemes. The proof of Theorem 4.8 (p.30) uses that the
  pieces `Hilb^θ` are projective over `S`.

## Derivation

These steps explain why the statement is expected to hold and how a proof can
be organised. They are not Lean proofs.

1. **Pieces as schemes.** Take `H := ∐_θ C_θ` with the per-polynomial schemes
   `C_θ`, or equivalently the FLT `Hilb`, whose pieces represent the same
   functors on affine tests. Then `πH` is locally of finite presentation and
   separated, since each `C_θ` is proper and locally of finite presentation over
   `S`. The FLT Hilbert theorem states both properties for `Hilb` directly.
2. **Universal family.** For each affine open `V ⊆ H`, surjectivity of `pt`
   gives a flat, locally finitely presented closed subscheme of `X ×_S V`
   classified by the inclusion `V ⟶ H`. On an affine open `V'' ⊆ V ∩ V'`,
   naturality along `V'' ⟶ V` and `V'' ⟶ V'`, together with injectivity, shows
   that the two restrictions agree. The ideal sheaves therefore glue to one
   ideal sheaf `W` on `X ×_S H`. Its closed subscheme is flat and locally
   finitely presented over `H`, because both properties are local on `H`.
   Naturality, checked on an affine open cover of `Spec B`, shows that `pt` of
   the pullback of `W` along any `g : Spec B ⟶ H` over `S` is `g`.
3. **All test schemes.** Let `T` be any scheme over `S`. Flatness and local
   finite presentation are stable under base change. The closed subscheme of
   `W.comap g_X` is the base change of the closed subscheme of `W` along `g`,
   because `comap` is the kernel of the pulled-back closed immersion. This gives
   the first clause of item 2. For the second clause, let `I` be given. On each
   affine open `T_i ⊆ T`, take the FLT classifying morphism of `I|_{T_i}`.
   On affine opens of the pairwise overlaps these agree, by naturality and
   injectivity, so they glue to `g : T ⟶ H`. Then `W.comap g_X = I`, since
   ideal sheaves are determined locally and both restrict to `I|_{T_i}` by
   step 2. Uniqueness holds because a morphism is determined by its restrictions
   to an open cover, and on affine opens it is determined by injectivity of
   `pt`. No quasi-compactness or separatedness of `T` is used.
4. **Piece clause.** Let `g : Spec B ⟶ H` classify `I`. By step 2, `pt` of
   `ι = I.subschemeι` is `g`. So the FLT piece clause for `(I.subscheme, ι)`
   is exactly the piece clause of item 3.
5. **Projectivity of the pieces.** By the solution file, `C_θ` is a closed
   subscheme of `H_m ×_{Spec ℤ} Spec A`. The scheme `H_m` represents the graded
   point functor on all affine tests, so it is isomorphic to the scheme of the
   FLT projective-embedding theorem. Hence it is closed in
   `Proj ℤ[x_0, …, x_N] = ℙᴺ_ℤ`. Base change gives a closed immersion of `C_θ`
   into `ℙᴺ_ℤ ×_ℤ Spec A ≅ ProjectiveSpace A N` over `S`. This is Nitsure's
   Theorem 5.3, obtained through the same Grassmannian embedding, but here over
   any ring `A`. That is possible because `X ⟶ S` is finitely presented and
   the construction is a base change from `ℤ`.

## Relation between the Lean statement and the sources

- **Projectivity hypothesis.** "`X/S` projective" is given by
  `ClosedImmersionBySections 𝓛X f`, and `𝓛X` plays the role of `O(1)|_X`, which
  is Nitsure's `L`. The Library theorem
  `Langlands.AlgebraicGeometry.Picard.exists_closedImmersionBySections_iff_isHProjective`
  shows that such a pair `(𝓛X, presentation)` exists exactly when
  `IsHProjective f`.
- **Ideal sheaves instead of closed subschemes.** Closed subschemes of
  `X ×_S T` are represented by their ideal sheaves
  (`Scheme.IdealSheafData`), so equality in the uniqueness clause is equality
  of actual ideal sheaves, and no isomorphism of closed subschemes is involved.
  Pulling back along `g_X` is `IdealSheafData.comap`.
- **Test schemes.** Nitsure and Kleiman use locally noetherian tests. The FLT
  theorem uses affine tests `Spec B` for every ring `B`. Item 2 holds for all
  `T : Scheme.{u}`; step 3 gives this extension. On locally noetherian tests,
  every closed subscheme of `X_T` is locally of finite presentation over `T`.
  The functor of item 2 therefore restricts there to Nitsure's `Hilb_{X/S}`.
- **Measuring the Hilbert polynomial.** As in the FLT theorem, the fibre
  Hilbert polynomial is detected by `h⁰` of large twists rather than by Euler
  characteristics. By Serre vanishing the two agree for large `n` on a
  projective scheme over a field, and both are unchanged by field extension.
- **Projective pieces.** The FLT theorems give the pieces only as clopen and
  quasi-compact (`Hilb`) or proper (`C_θ`). The closed immersion into a
  projective space over `S` is extra content, justified in step 5.

## Use

The planned reduction of
`Picard.RelativeEffectiveDivisorHilbertPiecesStatement` takes `D` to be the
relative effective Cartier locus of `W`, an open subscheme of `H` given by
`Picard.RelativeEffectiveCartierLocusStatement`. That locus is Kleiman's
`Div_{X/S} ⊆ Hilb_{X/S}` (Theorem 3.7). Its Hilbert-polynomial pieces are open
in the projective `U θ`, hence H-quasi-projective.
