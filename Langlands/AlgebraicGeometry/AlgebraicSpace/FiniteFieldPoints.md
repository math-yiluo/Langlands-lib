# Finitely many points over a finite field

Author: Worker 105.

Conrad, *Weil and Grothendieck approaches to adelic points* (December 31, 2011), printed
p.17, proof of Corollary 5.7: "the residue field is a finite field and X is of finite type,
so by using a finite stratification of X by schemes we see that there are only finitely many
rational points in the special fiber." This module proves the finiteness for algebraic
spaces in the Library's sense. Its Lean proof does not stratify; it bounds residue degrees in
étale charts instead. All names are in the namespace
`Langlands.AlgebraicGeometry.AlgebraicSpace.FiniteFieldPoints`.

## Statements

- `exists_extension_embedding (κ) [Field κ] [Finite κ] (D : ℕ)`: there is a field `M` with a
  `κ`-algebra structure, finite-dimensional over `κ`, such that every finite-dimensional
  field extension `L/κ` (in the same universe) with `finrank κ L ≤ D` admits a
  `κ`-embedding `L →ₐ[κ] M`.
- `finite_ringPoint (M)`: for `V` over `Spec C` with `V.left` affine and `V.hom` locally of
  finite type, and a finite `C`-algebra `M`, the set `RingPoint C V M` of relative scheme
  points is finite.
- `finite_ringPoints (X) (hX : IsQuasiSeparated X) (hft : FiniteTypeOverRing C X) (κ)`: for
  an algebraic space `X` over `Spec C` that is quasi-separated and of finite type over `C`
  (`FiniteTypeOverRing`, a surjective étale atlas that is locally of finite type and
  quasi-compact over `Spec C`), and a finite field `κ` with any `C`-algebra structure,
  `RingPoints C X κ` is finite. No surjectivity of `C → κ` is assumed.

## Proofs

`exists_extension_embedding`: with `q = #κ`, take `M` the splitting field of
`X ^ (q ^ D!) - X`. If `[L : κ] = d ≤ D`, then `L` is the splitting field over `κ` of
`X ^ #L - X` (`FiniteField.isSplittingField_sub`) with `#L = q ^ d`. Since `d ∣ D!`, this
polynomial divides `X ^ (q ^ D!) - X` (`dvd_pow_pow_sub_self_of_dvd`), so it splits in `M`.
`IsSplittingField.lift` gives the embedding.

`finite_ringPoint`: the coordinate ring is a finitely generated `C`-algebra
(`affineCoordinate_finiteType`). Algebra maps to `M` are determined by their values on the
finitely many generators (`AlgHom.ext_of_adjoin_eq_top`), so there are finitely many. They
correspond to the points through `affineSchemePointEquiv`.

`finite_ringPoints`:

1. Take the atlas `a : h_U ⟶ X.presheaf`. `U` is compact, so a finite set `t` of affine opens
   `W` covers it. Each gives an affine chart `V W = OverAction.resOver W` with étale map
   `aW W = h(W ↪ U) ≫ a`, locally of finite type over `C`. Let `D_W` be the fibre bound of
   `EtaleChartFibreCount.exists_fibre_card_le` for `aW W`, and let `M` come from
   `exists_extension_embedding κ (∑_{W ∈ t} D_W)`. Each `V W` has finitely many `M`-points
   (`finite_ringPoint`).
2. Fix `x ∈ X(κ)`. The represented pullback `P` of `a` along `x` is étale and surjective
   over `Spec κ`. `FieldPointEtaleLift.exists_separable_point_mono` gives a finite separable
   `L/κ` and a monomorphism `Spec L → P` over `Spec κ`. Its image in `U` lies in some
   `W ∈ t`; let `ℓ : Spec L → V W` be the factorization.
3. For `σ ∈ Gal(L/κ)` the twisted points `Spec σ ≫ ℓ` all have the image of
   `Spec L → Spec κ → X` in `X`. They are pairwise distinct: equal twists give equal points
   of `P` (pullback property, both lying over `Spec κ`), and then `σ = τ` because the point of
   `P` is a monomorphism and `Spec` is faithful. So
   `[L : κ] = #Gal(L/κ) ≤ D_W ≤ ∑ D_W` (`IsGalois.card_aut_eq_finrank`; finite extensions of
   finite fields are Galois).
4. Embed `e : L → M`. Then the image of `x` in `X(M)` is the image of the `M`-point
   `Spec e ≫ ℓ` of `V W`. This is computed through `uliftYonedaEquiv` and
   `uliftYonedaEquiv_naturality`, as in `FieldPointEtaleLift`.
5. Hence `X(κ) → X(M)` lands in the finite union over `W ∈ t` of the images of the finite
   sets of `M`-points of the charts. It is injective (`FieldPointEtaleLift.changeRing_injective`,
   fppf descent along `Spec M → Spec κ`). So `X(κ)` is finite.

All proofs use only the standard axioms.
