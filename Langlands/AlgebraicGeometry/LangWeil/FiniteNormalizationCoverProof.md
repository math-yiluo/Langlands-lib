# Proof: finite normalization covers over Noetherian bases

Author: Worker 185.

This module proves the published statement
`Langlands.AlgebraicGeometry.LangWeil.FiniteNormalizationCoverStatement` with the theorem
`Langlands.AlgebraicGeometry.LangWeil.finiteNormalizationCover`. The statement's Lean/Markdown
pair is imported unchanged and no hypotheses are added. For a scheme morphism `f : X ⟶ S` with
`S` Noetherian and `f` locally of finite type and quasi-compact, the theorem constructs an
element of `FiniteNormalizationCover f`. It has the covering condition for field-valued points
over the same field and the bound `dᵢ ≤ dim f.fiber(tᵢ t)` for every base point `t`.

## Modules

The proof uses three helper modules, all in the namespace
`Langlands.AlgebraicGeometry.LangWeil.NormalizationCoverConstruction`:

- `FiniteNormalizationCoverAlgebra`: generic Noether normalization over a domain in finite
  injective form, from the Library theorem
  `Algebra.exists_ne_zero_algebraicIndependent_forall_isIntegral_pow_smul_of_finiteType`, and a
  chain of `d + 1` primes over every prime of the base for a finite injective map from a
  polynomial algebra in `d` variables (lying over and going up);
- `FiniteNormalizationCoverPieces`: the auxiliary structure `Piece f` (one index of the cover,
  with a specialization chain in its own fibre in place of the dimension bound), the dimension
  bound derived from that chain, transport of pieces along immersions, assembly of finitely many
  covering pieces into a `FiniteNormalizationCover`, and Noetherian induction over primes;
- `FiniteNormalizationCoverAffine`: the affine case, finitely many pieces of
  `Spec A ⟶ Spec R` covering all field-valued points for a finite-type algebra `A` over a
  Noetherian ring `R`.

Each helper module has its own Markdown with the details.

## The route

The proof stratifies the source, not the base. For an affine chart `Spec A ⟶ Spec R`, each prime
`Q` of `A` gives a piece. Generic Noether normalization of `A ⧸ Q` over the domain
`R ⧸ (Q ∩ R)` gives, after inverting the image of one element `g ∉ Q`, a finite injective map
`(R ⧸ (Q ∩ R))[1/r][X₁, …, X_d] → (A ⧸ Q)[1/g]`. The piece has base
`Spec (R ⧸ (Q ∩ R))[1/r]` and source `Spec (A ⧸ Q)[1/g]`. Both immerse (open in closed) into
`Spec R` and `Spec A`. The piece covers every field-valued point whose kernel contains `Q` and
avoids `g`. Noetherian induction on the ideals of `A` leaves finitely many pieces. Over a base
point, going up along the finite injective polynomial map gives a chain of `d + 1` distinct
specializing points in the source fibre. The source immersion carries it into the fibre of `f`,
which bounds the fibre dimension. The statement's Markdown sketches a different route, Noetherian
induction on reduced closed subsets of the base. The implemented proof does not follow it.

## The proof of `finiteNormalizationCover`

1. Charts. Every point `x` of `X` has an affine open `W x` of `S` containing `f x` and an affine
   open `V x` of `X` containing `x` with `V x ≤ f⁻¹(W x)`. Affine opens form a basis of both
   schemes (`isBasis_affineOpens`).
2. Local covers. Fix `x`. The ring `Γ(S, W x)` is Noetherian
   (`IsLocallyNoetherian.component_noetherian`). The ring `Γ(X, V x)` is a finite-type algebra
   over it through `f.appLE` (`f.finiteType_appLE`, from `LocallyOfFiniteType f`).
   `exists_finite_affine_pieces` gives a finite set of pieces of
   `Spec Γ(X, V x) ⟶ Spec Γ(S, W x)`. The square formed with the open immersions
   `(V x).fromSpec` and `(W x).fromSpec` commutes (`IsAffineOpen.SpecMap_appLE_fromSpec`), so
   `Piece.comp` transports these pieces to pieces of `f`. A morphism `y : Spec K ⟶ X` with image
   in `V x` lifts through `(V x).fromSpec`, whose range is `V x`
   (`IsOpenImmersion.lift`, `IsAffineOpen.range_fromSpec`). The lift factors through one of the
   affine pieces. Composing with `(V x).fromSpec` (`IsOpenImmersion.lift_fac`) shows that `y`
   factors through the transported piece.
3. Finiteness. `S` is Noetherian, hence quasi-compact, and `f` is quasi-compact, so `X` is
   compact (`QuasiCompact.compactSpace_of_compactSpace`). Finitely many `V x`, for `x` in a
   finite set `t`, cover `X`. The pieces from step 2 for `x ∈ t` form a finite set.
4. Covering. Let `y : Spec K ⟶ X` with `K` a field. `Spec K` has exactly one point. That point
   maps into some `V x` with `x ∈ t`, so the whole range of `y` lies in `V x`, and step 2
   factors `y` through a piece from the finite set.
5. `nonempty_cover_of_pieces` turns the finite covering set of pieces into a
   `FiniteNormalizationCover f`. Its `dimension_le` field comes from `Piece.dimension_le`.

All three hypotheses are used. Noetherianity of `S` gives the Noetherian section rings and the
compactness of `S`. `LocallyOfFiniteType f` gives the finite-type chart algebras.
`QuasiCompact f` gives the compactness of `X`. The proof uses only the axioms `propext`,
`Classical.choice` and `Quot.sound`.
