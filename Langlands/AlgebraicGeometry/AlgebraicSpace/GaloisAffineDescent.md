# Descent of invariant affine opens along a finite field extension

Internal step in the proof of `SeparatedAddCommGroupSheafSchemeRepresentabilityStatement`.
It uses the statement `FiniteLocallyFreeEquivalenceRelationAffineQuotientStatement`
(Stacks Project, Groupoids, Proposition 39.23.9, Tag 03BM) as a hypothesis.

`exists_affine_quotient` (scheme part). The data are an affine `A` over `Spec k`, a section
`x₀ ∈ F(A)` and `α₀ : A ⟶ Λ`, with `Λ ⟶ Spec k` finite, flat and locally of finite
presentation. Assume:
- (inj) a test point of `A` is determined by its image in `F` and its composite with `α₀`;
- (lift) every pair `(F.map a x₀, β)` is realised by a test point of `A`.

The proof:
1. Put `R := A ⨯ Λ` with `s := fst`. Applying (lift) to `(F.map s x₀, snd)` gives
   `t : R ⟶ A`.
2. "Same image in `F`" is exactly the relation `(t, s)`.
3. `swap := ⟨t, s ≫ α₀⟩` is an involution with `swap ≫ s = t`. So `t` is finite, flat and
   locally of finite presentation because `s` is, `s` being a base change of `Λ ⟶ Spec k`.
4. The monomorphism, reflexivity, symmetry and transitivity hypotheses of 03BM are checked
   on absolute test schemes, which are made into schemes over `Spec k` through `R`.
5. 03BM gives `q : A ⟶ M` with `M` affine and `IsPullback t s q q`.
6. `M` is a scheme over `Spec k` by `EffectiveEpi.desc`, since `q` is quasi-compact, flat
   and surjective.
7. The conclusion is that two test points have the same image in `F` if and only if they
   agree after `q`; `q` is moreover finite.

`isLFTAffineOpen_universalImage_fst` (main result). Let `L/k` be finite, `F` an fppf sheaf and
`W ⊆ F × Spec L` an affine open subfunctor represented by a scheme locally of finite type
(`IsLFTAffineOpen`), whose membership depends only on the `F`-component. Then the universal
image `W₀` of `W` in `F` is again LFT-affine and `W₀.preimage fst = W`. The quotient `M` is
locally of finite type by `FiniteFlatSourceDescent`, since `q : A → M` is finite, flat and
surjective. The proof:
- The preimage identity is Worker 1150's `universalImage_preimage_eq_of_invariant`.
- Openness is `universalImage_open_of_finite`, since `fst` is finite.
- For representability, apply `exists_affine_quotient` to `x₀, α₀` read off from
  `Y(A) ≅ W`. Then use `exists_iso_of_locallySurjective_of_same_kernel` with the map
  `Y(A) ⟶ W₀`. That map is fppf-locally surjective, which is checked on the cover
  `T ⨯ Λ ⟶ T`.

The small helper `app_up_eq` evaluates a natural transformation out of a represented functor
at a test morphism `a` as `P.map a.op` of its Yoneda element.
