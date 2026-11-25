# Archimedean coordinates of the Iwasawa height of a line character

Module `Langlands.Global.EisensteinGenericInjectivity.PlaceHeight` defines the complex
coordinate of an adele at an infinite place and the complex matrix of a representation at that
place. It proves the **archimedean formula for height differences**
(`exp_two_mul_height_sub`): if two points of `G(𝔸)` have the same finite part, the difference of
their Iwasawa heights at a line character of a parabolic `P` is computed, place by place, by
invariant energies of their inverse orbit vectors. The module
`Langlands.Global.EisensteinGenericInjectivity.Separation` uses the formula through
`heightEnergy`.

All declarations are in the namespace `Langlands.Global.EisensteinGenericInjectivity`, universe
`u`, for a number field `F`.

## Notation

- `𝔸 = AdeleRing (𝓞 F) F` and `G(𝔸) = AdelicGroupPoints F G`; `finite F G` and
  `infinite F G` are the finite and infinite parts of a point, `ofFinite F G` includes a finite
  point with trivial infinite part.
- `σ` is a matrix representation `G → GL_N`, `adelicMatrix F G σ : G(𝔸) → GL_N(𝔸)` its adelic
  matrix, `e_j = Pi.single j 1` the `j`-th coordinate vector.
- `p : P → G` is a closed subgroup and `K ≤ G(𝔸)` a subgroup with
  `hK : IsIwasawaCompact p K` (`K` compact and `P(𝔸) K = G(𝔸)`); `hK.height g χ` is the Iwasawa
  height `⟨χ, H_P(g)⟩` of the module `Langlands.Global.AdelicIwasawaHeight`.
- `χ : AlgebraicCharacter F P` (or a rational character `χ : rationalCharacters P`, used through
  `χ.toMul`); `character F P χ : P(𝔸) → 𝔸ˣ` is its value as an idele and `characterNorm F P χ`
  the idele norm of that value.

Complete types below are printed by `PrettyPrinter.ppSignature` (the `#check` form), with the
namespaces `CategoryTheory`, `AlgebraicGeometry`, `NumberField`, `IsDedekindDomain`,
`TensorProduct`, `Langlands.Global`, `Langlands.Global.EisensteinGenericInjectivity`,
`Langlands.GroupScheme`, `Langlands.Global.AdelicGroupPoints`,
`Langlands.Global.RepresentationGrowth`, `Langlands.Automorphic.GroupSchemeFunctions` and
`Langlands.Analysis.Meromorphic` open; `↧A` is the bundled object `CommRingCat.of A` or
`CommAlgCat.of F A`.

## Declarations

### The place coordinate and the place matrix

- `placeHom w : 𝔸 →+* ℂ` is the coordinate of an adele at the infinite place `w`: the Library
  projection `infiniteProjection F w` to the completion `F_w`, followed by Mathlib's isometric
  embedding `InfinitePlace.Completion.extensionEmbedding w : F_w → ℂ`.
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.placeHom.{u} {F : Type u} [Field F] [NumberField F]
    (w : Langlands.Global.InfinitePlace F) : AdeleRing (𝓞 F) F →+* ℂ
  ```
- `placeHom_apply`: `placeHom w x` is the embedding of the `w`-coordinate of the infinite part
  of `x`.
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.placeHom_apply.{u} {F : Type u} [Field F]
    [NumberField F] (w : Langlands.Global.InfinitePlace F) (x : AdeleRing (𝓞 F) F) :
    (placeHom w) x = (InfinitePlace.Completion.extensionEmbedding w) (x.1 w)
  ```
- `placeHom_algebraMap`: on principal adeles `placeHom w` is Mathlib's complex embedding
  `w.embedding`. This is the Library lemma
  `Langlands.ClassFieldTheory.Global.extensionEmbedding_algebraMap` (module
  `Langlands.ClassFieldTheory.Global.IdeleArchimedean`).
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.placeHom_algebraMap.{u} {F : Type u} [Field F]
    [NumberField F] (w : Langlands.Global.InfinitePlace F) (x : F) :
    (placeHom w) ((algebraMap F (AdeleRing (𝓞 F) F)) x) = (InfinitePlace.embedding w) x
  ```
- `norm_placeHom`: `‖placeHom w x‖` is the norm of the `w`-coordinate in `F_w` (the embedding is
  an isometry).
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.norm_placeHom.{u} {F : Type u} [Field F]
    [NumberField F] (w : Langlands.Global.InfinitePlace F) (x : AdeleRing (𝓞 F) F) :
    ‖(placeHom w) x‖ = ‖x.1 w‖
  ```
- `continuous_placeHom`: `placeHom w` is continuous (`continuous_infiniteProjection` and the
  isometry).
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.continuous_placeHom.{u} {F : Type u} [Field F]
    [NumberField F] (w : Langlands.Global.InfinitePlace F) : Continuous ⇑(placeHom w)
  ```
- `placeMatrix σ w x`, written `σ_w(x)`, is the complex matrix of `σ` at `w`: the entries of
  `adelicMatrix F G σ x` mapped by `placeHom w`.
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.placeMatrix.{u} {F : Type u} [Field F] [NumberField F]
    {G : Langlands.GroupScheme (Spec ↧F)} {N : ℕ} (σ : G.MatrixRepresentation (Fin N))
    (w : Langlands.Global.InfinitePlace F) (x : AdelicGroupPoints F G) : Matrix (Fin N) (Fin N) ℂ
  ```
- `placeMatrix_mul`, `placeMatrix_one`: `σ_w` is multiplicative and sends `1` to `1`.
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.placeMatrix_mul.{u} {F : Type u} [Field F]
    [NumberField F] {G : Langlands.GroupScheme (Spec ↧F)} {N : ℕ} (σ : G.MatrixRepresentation (Fin N))
    (w : Langlands.Global.InfinitePlace F) (x y : AdelicGroupPoints F G) :
    placeMatrix σ w (x * y) = placeMatrix σ w x * placeMatrix σ w y
  ```
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.placeMatrix_one.{u} {F : Type u} [Field F]
    [NumberField F] {G : Langlands.GroupScheme (Spec ↧F)} {N : ℕ} (σ : G.MatrixRepresentation (Fin N))
    (w : Langlands.Global.InfinitePlace F) : placeMatrix σ w 1 = 1
  ```
- `placeMatrix_mulVec_mulVec`: `σ_w(x) (σ_w(y) z) = σ_w(x y) z`.
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.placeMatrix_mulVec_mulVec.{u} {F : Type u} [Field F]
    [NumberField F] {G : Langlands.GroupScheme (Spec ↧F)} {N : ℕ} (σ : G.MatrixRepresentation (Fin N))
    (w : Langlands.Global.InfinitePlace F) (x y : AdelicGroupPoints F G) (z : Fin N → ℂ) :
    placeMatrix σ w x *ᵥ placeMatrix σ w y *ᵥ z = placeMatrix σ w (x * y) *ᵥ z
  ```
- `placeMatrix_inv_mulVec`: `σ_w(x⁻¹) (σ_w(x) z) = z`.
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.placeMatrix_inv_mulVec.{u} {F : Type u} [Field F]
    [NumberField F] {G : Langlands.GroupScheme (Spec ↧F)} {N : ℕ} (σ : G.MatrixRepresentation (Fin N))
    (w : Langlands.Global.InfinitePlace F) (x : AdelicGroupPoints F G) (z : Fin N → ℂ) :
    placeMatrix σ w x⁻¹ *ᵥ placeMatrix σ w x *ᵥ z = z
  ```

### Invariant energies

- `IsInvariantEnergy σ w K Q` is a structure in `Prop` on a function `Q : ℂ^N → ℝ` with three
  fields: `pos`, `Q` is positive on nonzero vectors; `smul`, `Q (c • z) = ‖c‖² Q z`;
  `invariant`, `Q (σ_w(k) z) = Q z` for `k ∈ K`.
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.IsInvariantEnergy.{u} {F : Type u} [Field F]
    [NumberField F] {G : Langlands.GroupScheme (Spec ↧F)} {N : ℕ} (σ : G.MatrixRepresentation (Fin N))
    (w : Langlands.Global.InfinitePlace F) (K : Subgroup (AdelicGroupPoints F G))
    (Q : (Fin N → ℂ) → ℝ) : Prop
  ```
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.IsInvariantEnergy.pos.{u} {F : Type u} [Field F]
    [NumberField F] {G : Langlands.GroupScheme (Spec ↧F)} {N : ℕ} {σ : G.MatrixRepresentation (Fin N)}
    {w : Langlands.Global.InfinitePlace F} {K : Subgroup (AdelicGroupPoints F G)}
    {Q : (Fin N → ℂ) → ℝ} (self : IsInvariantEnergy σ w K Q) (z : Fin N → ℂ) : z ≠ 0 → 0 < Q z
  ```
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.IsInvariantEnergy.smul.{u} {F : Type u} [Field F]
    [NumberField F] {G : Langlands.GroupScheme (Spec ↧F)} {N : ℕ} {σ : G.MatrixRepresentation (Fin N)}
    {w : Langlands.Global.InfinitePlace F} {K : Subgroup (AdelicGroupPoints F G)}
    {Q : (Fin N → ℂ) → ℝ} (self : IsInvariantEnergy σ w K Q) (c : ℂ) (z : Fin N → ℂ) :
    Q (c • z) = ‖c‖ ^ 2 * Q z
  ```
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.IsInvariantEnergy.invariant.{u} {F : Type u} [Field F]
    [NumberField F] {G : Langlands.GroupScheme (Spec ↧F)} {N : ℕ} {σ : G.MatrixRepresentation (Fin N)}
    {w : Langlands.Global.InfinitePlace F} {K : Subgroup (AdelicGroupPoints F G)}
    {Q : (Fin N → ℂ) → ℝ} (self : IsInvariantEnergy σ w K Q) (k : AdelicGroupPoints F G) :
    k ∈ K → ∀ (z : Fin N → ℂ), Q (placeMatrix σ w k *ᵥ z) = Q z
  ```

### Characters at the infinite places

- `character_val_fst`, `character_val_snd`: the infinite (finite) component of the idele
  `χ(y)` depends only on the infinite (finite) part of `y`. Both are `characterUnits_naturality`
  for the two projections of `𝔸`.
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.character_val_fst.{u} {F : Type u} [Field F]
    [NumberField F] {P : Langlands.GroupScheme (Spec ↧F)} [IsAffine P.X.left]
    (χ : AlgebraicCharacter F P) (y : AdelicGroupPoints F P) :
    (↑((character F P χ) y)).1 = ↑((characterUnits F P χ ↧(InfiniteAdeleRing F)) ((infinite F P) y))
  ```
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.character_val_snd.{u} {F : Type u} [Field F]
    [NumberField F] {P : Langlands.GroupScheme (Spec ↧F)} [IsAffine P.X.left]
    (χ : AlgebraicCharacter F P) (y : AdelicGroupPoints F P) :
    (↑((character F P χ) y)).2 = ↑((characterUnits F P χ ↧(FiniteAdeleRing (𝓞 F) F)) ((finite F P) y))
  ```
- `characterNorm_eq_prod_placeHom`: if the finite part of `y`, included with trivial infinite
  part, has character norm `1`, then the character norm of `y` is the archimedean product
  `∏_w ‖placeHom w (χ(y))‖^{mult w}`.
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.characterNorm_eq_prod_placeHom.{u} {F : Type u}
    [Field F] [NumberField F] {P : Langlands.GroupScheme (Spec ↧F)} [IsAffine P.X.left]
    (χ : AlgebraicCharacter F P) (y : AdelicGroupPoints F P)
    (hy : (characterNorm F P χ) ((ofFinite F P) ((finite F P) y)) = 1) :
    ↑↑((characterNorm F P χ) y) = ∏ w, ‖(placeHom w) ↑((character F P χ) y)‖ ^ InfinitePlace.mult w
  ```
- `map_ofFinite`: the adelic map of `p` commutes with the inclusions of finite parts.
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.map_ofFinite.{u} {F : Type u} [Field F]
    [NumberField F] {G : Langlands.GroupScheme (Spec ↧F)} [IsAffine G.X.left]
    {P : Langlands.GroupScheme (Spec ↧F)} [IsAffine P.X.left] {p : P ⟶ G}
    (y : FiniteAdelicGroupPoints F P) :
    (AdelicGroupPoints.map F P G p) ((ofFinite F P) y) =
      (ofFinite F G) ((P.affinePointsTarget p ↧(FiniteAdeleRing (𝓞 F) F)) y)
  ```
- `characterNorm_ofFinite_finite_eq_one`: let `q ∈ P(𝔸)` and suppose the finite part of `p(q)`
  equals the finite part of some `k ∈ K`. Then the finite part of `q` has character norm `1`.
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.characterNorm_ofFinite_finite_eq_one.{u} {F : Type u}
    [Field F] [NumberField F] {G : Langlands.GroupScheme (Spec ↧F)} [IsAffine G.X.left]
    {P : Langlands.GroupScheme (Spec ↧F)} [IsAffine P.X.left] {p : P ⟶ G}
    [IsClosedImmersion (Over.Hom.left p.hom.hom)] {K : Subgroup (AdelicGroupPoints F G)}
    (hK : IsIwasawaCompact p K) (χ : AlgebraicCharacter F P) (q : AdelicGroupPoints F P)
    {k : AdelicGroupPoints F G} (hk : k ∈ K)
    (h : (finite F G) ((AdelicGroupPoints.map F P G p) q) = (finite F G) k) :
    (characterNorm F P χ) ((ofFinite F P) ((finite F P) q)) = 1
  ```
- `placeMatrix_map_mulVec`: if `σ(p(q)) e_j = χ(q) e_j` over `𝔸` for all `q`, then
  `σ_w(p(q)) e_j = placeHom w (χ(q)) e_j` at every infinite place.
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.placeMatrix_map_mulVec.{u} {F : Type u} [Field F]
    [NumberField F] {G : Langlands.GroupScheme (Spec ↧F)} {N : ℕ}
    {P : Langlands.GroupScheme (Spec ↧F)} {p : P ⟶ G} {σ : G.MatrixRepresentation (Fin N)} {j : Fin N}
    {χ : AlgebraicCharacter F P} (w : Langlands.Global.InfinitePlace F)
    (ha :
      ∀ (q : AdelicGroupPoints F P),
        ↑((adelicMatrix F G σ) ((AdelicGroupPoints.map F P G p) q)) *ᵥ Pi.single j 1 =
          ↑((character F P χ) q) • Pi.single j 1)
    (q : AdelicGroupPoints F P) :
    placeMatrix σ w ((AdelicGroupPoints.map F P G p) q) *ᵥ Pi.single j 1 =
      (placeHom w) ↑((character F P χ) q) • Pi.single j 1
  ```
- `energy_inv_mulVec`: under the same hypothesis, for an invariant energy `Q` and `k ∈ K`,
  `Q(σ_w((p(q) k)⁻¹) e_j) = ‖placeHom w (χ(q⁻¹))‖² Q(e_j)`.
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.energy_inv_mulVec.{u} {F : Type u} [Field F]
    [NumberField F] {G : Langlands.GroupScheme (Spec ↧F)} {N : ℕ}
    {P : Langlands.GroupScheme (Spec ↧F)} {p : P ⟶ G} {K : Subgroup (AdelicGroupPoints F G)}
    {σ : G.MatrixRepresentation (Fin N)} {j : Fin N} {χ : AlgebraicCharacter F P}
    {w : Langlands.Global.InfinitePlace F} {Q : (Fin N → ℂ) → ℝ} (hQ : IsInvariantEnergy σ w K Q)
    (ha :
      ∀ (q : AdelicGroupPoints F P),
        ↑((adelicMatrix F G σ) ((AdelicGroupPoints.map F P G p) q)) *ᵥ Pi.single j 1 =
          ↑((character F P χ) q) • Pi.single j 1)
    (q : AdelicGroupPoints F P) {k : AdelicGroupPoints F G} (hk : k ∈ K) :
    Q (placeMatrix σ w ((AdelicGroupPoints.map F P G p) q * k)⁻¹ *ᵥ Pi.single j 1) =
      ‖(placeHom w) ↑((character F P χ) q⁻¹)‖ ^ 2 * Q (Pi.single j 1)
  ```
- `placeHom_character_mul`, `norm_placeHom_character_inv_mul`: `placeHom w ∘ χ` is
  multiplicative, and `‖placeHom w (χ(a⁻¹))‖ ‖placeHom w (χ(a))‖ = 1`.
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.placeHom_character_mul.{u} {F : Type u} [Field F]
    [NumberField F] {P : Langlands.GroupScheme (Spec ↧F)} {χ : AlgebraicCharacter F P}
    (w : Langlands.Global.InfinitePlace F) (a b : AdelicGroupPoints F P) :
    (placeHom w) ↑((character F P χ) (a * b)) =
      (placeHom w) ↑((character F P χ) a) * (placeHom w) ↑((character F P χ) b)
  ```
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.norm_placeHom_character_inv_mul.{u} {F : Type u}
    [Field F] [NumberField F] {P : Langlands.GroupScheme (Spec ↧F)} {χ : AlgebraicCharacter F P}
    (w : Langlands.Global.InfinitePlace F) (a : AdelicGroupPoints F P) :
    ‖(placeHom w) ↑((character F P χ) a⁻¹)‖ * ‖(placeHom w) ↑((character F P χ) a)‖ = 1
  ```

### The archimedean formula

- `exp_two_mul_height_sub`: let `χ` be a rational character of `P` with
  `σ(p(q)) e_j = χ(q) e_j` for all `q ∈ P(𝔸)`, and let `Q w` be an invariant energy at every
  infinite place `w`. If `finite x = finite y`, then

  `exp(2 (H_P(y)(χ) − H_P(x)(χ))) = ∏_w (Q_w(σ_w(x⁻¹) e_j) / Q_w(σ_w(y⁻¹) e_j))^{mult w}`.
  ```lean
  Langlands.Global.EisensteinGenericInjectivity.exp_two_mul_height_sub.{u} {F : Type u} [Field F]
    [NumberField F] {G : Langlands.GroupScheme (Spec ↧F)} {N : ℕ} [IsAffine G.X.left]
    {P : Langlands.GroupScheme (Spec ↧F)} [IsAffine P.X.left] {p : P ⟶ G}
    [IsClosedImmersion (Over.Hom.left p.hom.hom)] {K : Subgroup (AdelicGroupPoints F G)}
    {σ : G.MatrixRepresentation (Fin N)} {j : Fin N} (hK : IsIwasawaCompact p K)
    {χ : P.rationalCharacters} {Q : Langlands.Global.InfinitePlace F → (Fin N → ℂ) → ℝ}
    (hQ : ∀ (w : Langlands.Global.InfinitePlace F), IsInvariantEnergy σ w K (Q w))
    (ha :
      ∀ (q : AdelicGroupPoints F P),
        ↑((adelicMatrix F G σ) ((AdelicGroupPoints.map F P G p) q)) *ᵥ Pi.single j 1 =
          ↑((character F P (Additive.toMul χ)) q) • Pi.single j 1)
    (x y : AdelicGroupPoints F G) (hxy : (finite F G) x = (finite F G) y) :
    Real.exp (2 * ((hK.height y) χ - (hK.height x) χ)) =
      ∏ w,
        (Q w (placeMatrix σ w x⁻¹ *ᵥ Pi.single j 1) / Q w (placeMatrix σ w y⁻¹ *ᵥ Pi.single j 1)) ^
          InfinitePlace.mult w
  ```

## Proofs

- `characterNorm_eq_prod_placeHom`. Write `y = ofInfinite(infinite y) · ofFinite(finite y)`. The
  hypothesis removes the finite factor, and the idele norm `IdeleAbsoluteValue.full` of a point
  with trivial finite component is the product over the infinite places
  (`IdeleAbsoluteValue.coe_full`, `character_val_fst`, `character_val_snd`, `norm_placeHom`).
- `characterNorm_ofFinite_finite_eq_one`. The image of `ofFinite(finite q)` under `p` is
  `ofFinite(finite k)` (`map_ofFinite`), which lies in the image of `K` under the continuous
  homomorphism `ofFinite ∘ finite`, a compact subgroup. The Library lemma
  `AdelicGroupPoints.characterLog_eq_zero_of_map_mem` (module `Langlands.Global.AdelicIwasawaHeight`)
  gives `characterLog = 0`, that is, norm one for every character.
- `exp_two_mul_height_sub`. Write `x = p(q_x) k_x` and `y = p(q_y) k_y` with `k_x, k_y ∈ K`
  (`IsIwasawaCompact.exists_eq`) and put `q = q_x⁻¹ q_y`. Then
  `p(q) = k_x x⁻¹ y k_y⁻¹`, so the finite part of `p(q)` is that of `k_x k_y⁻¹ ∈ K`, and
  `characterNorm_ofFinite_finite_eq_one` and `characterNorm_eq_prod_placeHom` express
  `|χ(q)|` as the archimedean product of `‖placeHom w (χ(q))‖^{mult w}`. On the other hand
  `H_P(y)(χ) − H_P(x)(χ) = log |χ(q)|` (`IsIwasawaCompact.height_eq`). At each place,
  `energy_inv_mulVec` gives `Q_w(σ_w(x⁻¹) e_j) = ‖placeHom w χ(q_x⁻¹)‖² Q_w(e_j)` and the same
  for `y`; `Q_w(e_j) > 0` cancels and the quotient is `‖placeHom w (χ(q))‖²`. The compact
  subgroup `K` is only assumed to satisfy `P(𝔸) K = G(𝔸)`; it need not be a product of local
  subgroups.

## Sources

J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer.
Math. Soc. 37 (2024), §2.1, printed p. 190: `H_M : M(𝔸) → 𝔞_P` with
`e^{⟨χ, H_M(m)⟩} = |χ(m)|` for `χ ∈ X^*(M)`, and the map `m_P` extended to `G(𝔸)` through
`G(𝔸) = M(𝔸) U(𝔸) K`. `hK.height` is the corresponding height on `G(𝔸)` for a compact `K` with
`P(𝔸) K = G(𝔸)`. The archimedean formula and the invariant energies are not taken from a
source.
