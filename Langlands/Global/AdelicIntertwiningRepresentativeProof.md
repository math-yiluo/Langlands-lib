# The intertwining operator depends only on the Weyl element

`Langlands.Global.intertwiningRepresentativeIndependence` proves the published
`Langlands.Global.IntertwiningRepresentativeIndependenceStatement` with its hypotheses
unchanged. Take parabolics `P = MU` and `Q = M'V` of a connected reductive `G` over a number
field, with `l' ≫ π' = 𝟙 M'`. Let `(w₁, c₁)` and `(w₂, c₂)` be two Weyl conjugations from `P`
to `Q` with `weylParameter l c₁ π' = weylParameter l c₂ π'`. Then
`M(w₁, λ)φ(g) = M(w₂, λ)φ(g)` for every automorphic form `φ` on `U(𝔸)M(F) \ G(𝔸)`, every
`λ` and every `g`.

## Implemented proof

The module proves four auxiliary results and then the target.

1. `Langlands.GroupScheme.characterRestrict_eq_of_one_tmul_eq`. Let `A` be a split torus over
   a field and `r : A → H` a homomorphism. If `1 ⊗ x = 1 ⊗ y` in `ℂ ⊗_ℤ X^*(H)`, then `x` and
   `y` have the same restriction to `A`. Proof: for each cocharacter `ν` of `A`, the
   `ℤ`-linear form `ψ ↦ ⟨ψ ∘ r, ν⟩` on `X^*(H)` gives, after `ℂ ⊗ -` and `ℂ ⊗_ℤ ℤ ≅ ℂ`, two
   equal integers. The character–cocharacter pairing of a split torus is perfect
   (`CocharacterUniformizer.latticePairing_isPerfPair`), so the two restrictions agree.
2. `Langlands.GroupScheme.IsSplitComponent.automorphismRestriction_eq_id_of_characters`. Let
   `a : A → M` be a split component of a connected reductive `M`, and let `φ` be an
   automorphism of `M` with `χ ∘ φ ∘ a = χ ∘ a` for every rational character `χ` of `M`. Then
   the restriction of `φ` to `A` is the identity. The proof follows the published
   `IsSplitComponent.automorphismRestriction_eq_id_of_norm`, with the character equality in
   place of the norm equality. The restriction fixes the image of `X^*(M) → X^*(A)`, which
   has finite index (`IsSplitComponent.finiteIndex_range_characterRestrict`). Multiplying by
   the index and cancelling in the perfect pairing shows that it fixes all of `X^*(A)`, and
   characters determine endomorphisms of a split torus. The companion
   `IsSplitComponent.comp_automorphism_eq_of_characters` concludes `a ≫ φ = a`.
3. `Langlands.Global.AdelicGroupPoints.IsWeylConjugation.exists_levi_of_weylParameter_eq`.
   Under the hypotheses of the target, `w₂ = w₁ · y` for a rational point `y` of `M`, sent to
   `G` by `l ≫ p`. The proof has four steps.
   - Let `θ = c₂⁻¹ ∘ c₁ : M ≅ M`. The two identities `cᵢ ≫ l ≫ p = l' ≫ q ≫ Int(wᵢ)⁻¹`
     together with `innerIso_mul_hom` and `innerIso_inv_hom` give
     `θ ≫ l ≫ p = l ≫ p ≫ Int(w₁⁻¹ w₂)`. So `θ` is conjugation by `w₁⁻¹ w₂` on `M`.
   - Take a split component `a : A → M` (`splitComponentStatement`). For `χ ∈ X^*(P)`,
     evaluate the parameter equality at `1 ⊗ χ` (`weylParameter_tmul`). This gives
     `1 ⊗ (χ ∘ l ∘ c₁ ∘ π') = 1 ⊗ (χ ∘ l ∘ c₂ ∘ π')` in `ℂ ⊗ X^*(Q)`. Apply step 1 with
     `r = a ≫ c₂⁻¹ ≫ l'` and use `l' ≫ π' = 𝟙`; this gives `χ ∘ l ∘ θ ∘ a = χ ∘ l ∘ a`.
     Restriction `X^*(P) → X^*(M)` along `l` is surjective
     (`IsRationalLeviSubgroup.characterRestrict_bijective`), so `θ` fixes every character
     of `M` on `A`. Step 2 then gives `a ≫ θ = a`.
   - `P` is a dynamic parabolic (`exists_dynamicParabolic_isRepresentedBy`, from Milne's
     Theorem 25.1 in the Library), so the published
     `IsRationalLeviSubgroup.exists_splitComponentCocharacter_of_dynamicParabolic` identifies
     the centralizer of `A` in `G` with the image of `l ≫ p`.
   - `a ≫ l ≫ p ≫ Int(w₁⁻¹ w₂) = a ≫ θ ≫ l ≫ p = a ≫ l ≫ p`, so `w₁⁻¹ w₂` centralizes `A`
     (`mem_torusCentralizer_base_iff`). Hence `w₁⁻¹ w₂ = y ≫ l ≫ p` for some rational
     `y : M`.
4. `intertwiningRepresentativeIndependence`. The operator is
   `heightPower (-weylParameter l c π' λ) g · intertwiningIntegral iU (iV ≫ q) w φ λ g`. The
   two height factors agree because the parameters are equal. By step 3, `w₂ = w₁ · y` with
   `y` the image of a rational point of `P` (`y ≫ l`). The published
   `IsIwasawaCompact.intertwiningIntegral_mul_rational_parabolic` shows that this right
   multiplication leaves the intertwining integral unchanged. It needs only the left
   `U(𝔸)M(F)`-invariance of `φ`, the first clause of `IsAutomorphicFunctionOn`. The other
   automorphy clauses, the maximal-compactness hypothesis and the matrix representation are
   unused.

## Provenance and scope

The argument is the classical one recorded in the statement's docstring:
Mœglin–Waldspurger, *Spectral decomposition and Eisenstein series*, II.1.6 (i), and
Bernstein–Lapid 2024, §2.1–§2.2. An element of `W(P, Q)` is the coset `wM(F)`. Two
representatives with the same action on parameters differ by an element normalizing `M`
that acts trivially on its rational characters. Such an element centralizes `A_M`, so it
lies in `M(F)`. The integral over `(V(F) ∩ wU(𝔸)w⁻¹) \ V(𝔸)` does not change under
`w ↦ wm` for `m ∈ M(F)`. Steps 1 and 2 are new auxiliary lemmas: step 2 is the
character-level analogue of the published norm-rigidity lemma for local fields, and holds
over any field. The module proves only the representative independence. It is one premise
of the symmetric-family density bridge `symmetricFamilyDensityBridge` used toward the unitary
spectral transform, and it does not prove `SpectralTransformStatement`.
