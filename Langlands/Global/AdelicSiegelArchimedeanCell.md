# The archimedean open cell for an algebraic Siegel setup

Module `Langlands.Global.AdelicSiegelArchimedeanCell`, namespace
`Langlands.Global.AdelicSiegelFactors`.

## Main result

`exists_siegel_archimedeanCell`. Let `G` be a connected reductive group over a number field `F`
(affine, locally of finite type), `(T, i, ν, T₀, j)` an algebraic Siegel setup
(`IsSiegelAlgebraicSetup`) and `t` a threshold. Write `N = Standard.unipotentScheme i ν ∅` with
its inclusion `Standard.unipotentHom i ν ∅`, and `a ↦ positiveMap a` for the positive torus
`A_{T₀}` in `G(𝔸)`. There are

- an identity neighborhood `W` of `G(𝔸)`,
- a compact set `N₁ ⊆ N(𝔸)`,
- a compact set `Q ⊆ G(𝔸)`,

such that for every `g ∈ W` there is `n ∈ N₁` with `a (n⁻¹ g) a⁻¹ ∈ Q` for every `a` in the weak
simple-root chamber `|β(a)| ≥ t` (`PositiveRealTorus.weakSimpleRootChamber`). In words: near the
identity, `g = n q` with `n` in a compact subset of `N(𝔸)` and `q` uniformly bounded under
conjugation by the chamber.

## Proof

1. *The cocharacter.* `standardCocharacter` gives `ζ` standard for `(ν, ∅)` (positive on every
   simple root), with `standardLevi i ν ∅ = Z(ζ)` and `standardUnipotent i ν ∅ = U(ζ)` for the
   cocharacter `ζ ≫ i` of `G`. Its opposite `t ↦ ζ(t⁻¹)` equals `-ζ`
   (`powerHom_neg_one_comp_groupHom`, from `GmOrbitInversion.comp_groupHom_neg`). The relative
   root system (`relativeRootSystem`) is closed under negation, so the positive and simple roots
   of `-ν` are the negatives of those of `ν` (`neg_mem_positiveRelativeRoots_of_neg`,
   `neg_mem_simpleRelativeRoots_of_neg`), `-ν` is generic (`isGenericCocharacter_neg`) and `-ζ` is
   standard for `(-ν, ∅)` (`isStandardCocharacter_neg`, using
   `IsStandardCocharacter.pairing_pos_iff_not_mem_closure`). Hence, by `standardCocharacter` for
   `-ν`, `U(-ζ) = standardUnipotent i (-ν) ∅`, the opposite unipotent subgroup `N⁻`.
2. *Archimedean cells.* At each archimedean place `v`, `Dynamic.affinePoints_opposite_cell_mem_nhds_one`
   for `S = F_v` and the cocharacter `ζ ≫ i` gives identity neighborhoods of products
   `u⁻ m n` with factors in `N⁻(F_v)`, `M(F_v)`, `N(F_v)` (`M` the standard Levi subgroup). The
   carriers of the represented subgroup functors are the images of the points of their
   representatives (`carrier_eq_range_of_isRepresentedBy`, with
   `Standard.isRepresentedBy_unipotentHom` and `Standard.isRepresentedBy_leviHom`).
3. *Assembly.* `exists_nhds_eq_ofFinite_mul_triple` (module
   `Langlands.Global.AdelicArchimedeanTripleCell`) gives an identity neighborhood `W₀` of `G(𝔸)`
   whose points are `g = f · u⁻ · m · n` with `f` included from a compact subset `L` of `G(𝔸_f)`
   and `u⁻`, `m`, `n` in the images of compact subsets `K₁ ⊆ N⁻(𝔸)`, `K₂ ⊆ M(𝔸)`, `K₃ ⊆ N(𝔸)`.
4. *Inversion.* Take `W = W₀⁻¹` and `N₁ = K₃⁻¹`. For `g ∈ W`, `g⁻¹ = f u⁻ m n`, so with the
   point `n⁻¹ ∈ N₁` one has `n g = m⁻¹ (u⁻)⁻¹ f⁻¹`.
5. *Conjugation by the chamber.* For `a` in the chamber, `a` commutes with `M(𝔸)`
   (`positiveMap_commute_of_mem_standardLevi`, using `standardLevi i ν ∅ = torusCentralizer i`
   from the setup) and with the finite adelic points (its finite part is `1` because `T₀` is split,
   `finite_positiveMap`, and `factors_commute`). Hence
   `a (n g) a⁻¹ = m⁻¹ · (a (u⁻)⁻¹ a⁻¹) · f⁻¹`.
6. *Contraction of `N⁻`.* `exists_isCompact_conj_unipotent_of_generic` says: for a maximal split
   torus, any generic cocharacter `μ` and a compact set `Ω` of points of the standard unipotent
   subgroup of `μ`, the conjugates `a'⁻¹ x a'` (`x ∈ Ω`, `a'` in the weak chamber of `μ`) lie in
   one compact set. Its proof takes a closed matrix embedding `rho : G → GL_N`
   (`affineLinearEmbeddingStatement`); if `N = 0` the adelic points form a singleton, and if
   `N > 0` the published height bound `exists_adelicHeight_conj_unipotent_le_of_maximalSplit` and
   the properness of the height (`adelicRepresentationHeightProperness`) give a compact sublevel
   set. It is applied with `μ = -ν` and `a' = a⁻¹`: by `inv_mem_weakSimpleRootChamber_neg`, `a⁻¹`
   lies in the weak chamber of `-ν` with the same threshold, because the norm of `-α` is the
   inverse norm of `α` (`normCharacter_comp_neg`) and the simple roots of `-ν` are the negatives
   of those of `ν`.
7. *The compact set.* `Q = M₁ · K_c · L'`, where `M₁` is the image of `K₂⁻¹` in `G(𝔸)`, `K_c` is
   the compact set of step 6 for `Ω = K₁⁻¹`, and `L'` is the inclusion of `L⁻¹`.

## Provenance

Internal and derived. It is the "Coordinates" step of the route recorded in
`Langlands/Global/AdelicSiegelRationalConjugateCountingStatement.md`, with the roles of the
unipotent radical and its opposite exchanged. The point `n` comes from `N(F_∞)`. The
archimedean component of the bounded factor `q` lies in `M(F_∞) N⁻(F_∞)`. Its finite component
lies in `L⁻¹ ⊆ G(𝔸_f)`, and the image of that component in `G(𝔸)` commutes with `a`. The
scheme-level input is the opposite open cell `oppositeCellStatement`, from
Conrad–Gabber–Prasad, *Pseudo-reductive groups*, Proposition 2.1.8(3), and Conrad,
*Reductive group schemes*, Theorem 4.1.7(4). The chamber contraction is the
opposite-chamber form of Delorme 2023, (2.4).

The module uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.
