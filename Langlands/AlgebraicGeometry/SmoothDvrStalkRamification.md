# Stalks of smooth schemes over a DVR at generic points of the closed fibre

The module `Langlands.AlgebraicGeometry.SmoothDvrStalkRamification` proves that the stalk
of a smooth scheme over a discrete valuation ring at a generic point of its closed fibre
is an extension of ramification index one of the base, in the sense of
`Langlands.AlgebraicGeometry.IsRamificationIndexOne`.

## Source

Bosch, Lütkebohmert and Raynaud, *Néron Models* (literature ID
`bosch-lutkebohmert-raynaud-1990-neron-models`), §3.6, remark after Definition 1, printed
p. 78 (PDF p. 85): a local ring of a smooth `R`-scheme at a generic point of the special
fibre has ramification index 1 over `R`. The proof is internal to the Library.

## Declarations

All declarations are in the namespace `Langlands.AlgebraicGeometry.SmoothDvrStalk`. Here
`V` is a discrete valuation ring and `t : T ⟶ Spec V` a morphism of schemes.

- `stalkStructureMap V t x : V ⟶ 𝒪_{T,x}` is the ring map from `V` to the stalk at `x`:
  the inverse of `Γ(Spec V) ≅ V`, the germ of `Spec V` at `t x`, and the stalk map of `t`
  at `x`.
- `fromSpecStalk_comp V t x`: the canonical morphism `Spec 𝒪_{T,x} ⟶ T` followed by `t`
  is `Spec` of `stalkStructureMap V t x`.
- `stalk_isRamificationIndexOne`: let `t` be smooth and `η` a point of `T` with
  `t η` the closed point of `Spec V` and with no other point of the closed fibre
  generizing to `η` (a generic point of the closed fibre). For any `V`-algebra structure
  on the stalk whose algebra map is `stalkStructureMap V t η`, the algebra map is a
  local homomorphism and `IsRamificationIndexOne V 𝒪_{T,η}` holds.

The algebra structure on the stalk is an argument of `stalk_isRamificationIndexOne`, with
the hypothesis `hφ` identifying its algebra map, so that the theorem applies to whichever
instance a caller has in scope.

## Proof as implemented

Write `O` for the stalk and `φ` for `stalkStructureMap V t η`, and choose a uniformizer
`π` of `V`.

1. A prime `𝔮` of `O` containing `φ π` is the maximal ideal. Its image `y` in `T` under
   `Spec O ⟶ T` generizes `η` (Mathlib's `Scheme.range_fromSpecStalk`). The contraction of
   `𝔮` to `V` contains `π`, so it is nonzero and hence the maximal ideal, since `V` has
   dimension one. Thus `y` lies in the closed fibre, so `y = η` by hypothesis.
   Injectivity of `Spec O ⟶ T` then gives `𝔮 = 𝔪_O`.
2. The contraction of `𝔪_O` to `V` is `𝔪_V`, because the closed point of `Spec O` maps to
   `η`, which lies over the closed point.
3. Choose an affine open `U ∋ η` with coordinate ring `A = Γ(T, U)`. The `V`-algebra `A`
   is smooth (Mathlib's `Scheme.Hom.smooth_appLE`), `O` is the localization of `A` at the
   prime `p` of `η` (`IsAffineOpen.isLocalization_stalk`), and `V → A → O` composes to
   `φ`.
4. By step 2, `𝔪_V A ≤ p`. If `q` is a prime with `𝔪_V A ≤ q ≤ p`, then `q O` is a prime
   of `O` containing `φ π`, so `q O = 𝔪_O` by step 1, and contracting back gives
   `q = p`. So `p` is minimal over `𝔪_V A`.
5. `Langlands.CommutativeAlgebra.SmoothDvrPrimeLocalization.isLocalHom_algebraMap` and
   `Langlands.CommutativeAlgebra.SmoothDvrPrimeLocalization.isRamificationIndexOne`
   now give the conclusion.
