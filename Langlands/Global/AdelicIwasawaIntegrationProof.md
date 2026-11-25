# Proof of the Iwasawa integration formula on `G(𝔸_F)`

Lean module: `Langlands.Global.AdelicIwasawaIntegrationProof`, namespace
`Langlands.Global.AdelicGroupPoints`.

## Result

`adelicIwasawaIntegration : AdelicIwasawaIntegrationStatement.{u}` proves the published
statement `Langlands.Global.AdelicGroupPoints.AdelicIwasawaIntegrationStatement` exactly, at
the universe level `u` of the number field, with no added hypothesis. For every number field
`F`, connected reductive `G` over `F`, cocharacter `χ` with representing group schemes
`iP : P ⟶ G`, `iM : M ⟶ G`, `iU : U ⟶ G` of `P(χ)`, `Z(χ)` and `U(χ)`, and every compact
subgroup `K ≤ G(𝔸_F)` with `P(𝔸_F) K = G(𝔸_F)`, there is `c > 0` with

`∫_{G(𝔸_F)} f dg = c ∫_K ∫_{M(𝔸_F)} ∫_{U(𝔸_F)} δ_P(m)⁻¹ f(u m k) du dm dk`

for every `f ∈ C_c(G(𝔸_F), ℂ)`. Here `dg`, `dm`, `du` are Mathlib's `Measure.haar`, `dk` is
`compactHaarProbability F G K hK`, and `δ_P(m)` is `parabolicModulus F hP hU` at the image of
`m` in `P(𝔸_F)`, all exactly as in the statement.

The final theorem introduces the data, installs the same instances as the statement
(`hG.isAffineHom`, `hG.smooth`, `isAffine_parabolic`, `isAffine_centralizer`,
`locallyOfFiniteType_centralizer`, `isAffine_unipotent`, `locallyOfFiniteType_unipotent`;
separatedness of `G` follows from `IsAffineHom` by Mathlib's instance) and applies
`adelicIwasawaIntegration_of_isRepresentedBy`. All these instances are propositions, so they
agree with the ones in the statement.

The proof does not use unimodularity of `G(𝔸_F)`, the published `AdelicParabolicModulusStatement`
(still unproved) or any property of reductive groups beyond affineness, smoothness (for local
compactness) and separatedness. Reductivity enters only through these instances.

## The route

The proof has three steps.

1. **Levi coordinates.** `Z(χ)(𝔸_F) × U(χ)(𝔸_F) → P(χ)(𝔸_F)`, `(m, u) ↦ m u`, is a homeomorphism
   onto the image `Q` of `P(𝔸_F)` in `G(𝔸_F)`. Left multiplication by `q ∈ Q` has triangular form
   in these coordinates.
2. **Haar measure on `Q`.** The image of `dm × du` under these coordinates is a left Haar measure
   on `Q`.
3. **Assembly.** The published `CompactFactorization.exists_pos_eq_smul_map_mul_prod` gives
   `dg = c · (q, k) ↦ q k` of (Haar on `Q`) × `dk`. Fubini then reduces the integral to
   `∫_K ∫_M ∫_U f(m u k) du dm dk`. The published `integral_conj_parabolicModulus` turns
   `m u` into `u m` and contributes `δ_P(m)⁻¹`.

## Declarations

### Levi coordinates (section `Levi`)

The adelic points `AdelicGroupPoints F G` are the morphisms `T ⟶ G.X` for the test object
`T = Spec 𝔸_F` over `Spec F`. So the published point-level results of the `Dynamic` library
apply directly to them.

- `mem_range_map_iff_of_isRepresentedBy`: if `i : H ⟶ G` represents a subgroup functor `Φ`, the
  image of `map F H G i` is the subgroup `Φ(T)` of `G(𝔸_F)`. This uses `pointsEquiv`.
- `inv_limit_mul_mem_unipotent`: for separated `G` and `g ∈ P(χ)(T)`, `(lim g)⁻¹ g ∈ U(χ)(T)`.
  It is `g (lim g)⁻¹ ∈ U(χ)(T)` (`Dynamic.mul_inv_limit_mem_unipotent`) conjugated by
  `(lim g)⁻¹ ∈ Z(χ)(T)`, which normalizes `U(χ)(T)` (`Dynamic.centralizer_le_normalizer_unipotent`).
- `limit_centralizer_mul_unipotent`: for `z ∈ Z(χ)(T)` and `x ∈ U(χ)(T)`, `lim (z x) = z`, by
  `HasLimit.mul` and uniqueness of limits (`Dynamic.limit_eq`).
- `isClosedEmbedding_map_parabolic`, `isClosedEmbedding_map_centralizer`,
  `isClosedEmbedding_map_unipotent`: the three adelic inclusions are closed embeddings. They use
  `isClosedEmbedding_map` and the published closedness of represented dynamic subgroups.
- `map_centralizer_mem_range`, `map_unipotent_mem_range`: `M(𝔸_F)` and `U(𝔸_F)` land in `Q`,
  since `Z(χ) ≤ P(χ)` and `U(χ) ≤ P(χ)`.
- `map_centralizerToParabolic`: `iP ∘ (Z(χ) ⟶ P(χ)) = iM` on adelic points, from
  `Dynamic.centralizerToParabolic_comp`.
- `leviProjection : Q →* M(𝔸_F)`: the adelic map of the scheme-level limit homomorphism
  `Dynamic.limitGroupHom hP hM : P ⟶ Z`, composed with the inverse of `rangeEquiv` for `iP`. It
  is continuous (`continuous_leviProjection`). By `Dynamic.limitGroupHom_comp`, its image in
  `G(𝔸_F)` is the dynamic limit of `q` (`map_leviProjection`). This is where continuity of the
  limit on adelic points comes from.
- `inv_map_leviProjection_mul_mem`: `(lim q)⁻¹ q` lies in the image of `U(𝔸_F)`.
- `leviMul (m, u) = m u ∈ Q` and `leviSplit q = (lim q, (lim q)⁻¹ q)`. The second component is
  read back in `U(𝔸_F)` through the inverse of `rangeEquiv` for `iU`.
  `leviSplit_leviMul` uses `limit_centralizer_mul_unipotent` and injectivity of the embeddings.
  `leviMul_leviSplit` is `lim q · (lim q)⁻¹ q = q`. Both maps are continuous
  (`continuous_leviMul`, `continuous_leviSplit`).
- `leviCoordinates : M(𝔸_F) × U(𝔸_F) ≃ₜ Q` packages these maps.
- `leviCorrection q m`, the `U`-coordinate of `q · m`, is continuous in `m`
  (`continuous_leviCorrection`).
- `leviSplit_mul_leviMul`: `q · (m u)` has coordinates `(lim q · m, leviCorrection q m · u)`.
  The first coordinate holds because `leviProjection` is a homomorphism. The second is checked
  after applying the injective map `U(𝔸_F) → G(𝔸_F)`.

### Haar measure on `Q` (section `Measure`)

- `parabolicImageHaar` is the image of `Measure.haar.prod Measure.haar` on
  `M(𝔸_F) × U(𝔸_F)` under `leviCoordinates`.
- `parabolicImageHaar_isHaarMeasure`: this measure is a left Haar measure on `Q`. It is finite
  on compacts and positive on open sets because `leviCoordinates` is a homeomorphism.
  It is left invariant because, by `leviSplit_mul_leviMul`, left multiplication by `q` is the
  skew product `(m, u) ↦ (lim q · m, leviCorrection q m · u)` in coordinates. Both factors are
  left translations, so Mathlib's `MeasurePreserving.skew_product` shows that it preserves
  `dm × du`. The same argument appears in the Library's
  `Aubert.General.IsSemidirectDecomposition.coordinates_isHaarMeasure`, for subgroups with a
  different measurable structure.
- `integral_parabolicImageHaar`: for `f ∈ C_c(G(𝔸_F), ℂ)` and `k ∈ G(𝔸_F)`,
  `∫_Q f(q k) dq = ∫_M ∫_U δ_P(m)⁻¹ f(u m k) du dm`. The proof changes variables through
  `leviCoordinates` (`integral_map`). It then applies Fubini (`integral_prod`). The integrand
  `(m, u) ↦ f(m u k)` is continuous with compact support, since `(m, u) ↦ m u k` is a closed
  embedding (`Q` is closed). For fixed `m`, `integral_conj_parabolicModulus` at
  `p = (m⁻¹ in P(𝔸_F))` applied to `x ↦ f(x m k)` gives
  `∫_U f(m u k) du = δ_P(m⁻¹) ∫_U f(u m k) du`, and `δ_P(m⁻¹) = δ_P(m)⁻¹`.
- `adelicIwasawaIntegration_of_isRepresentedBy` is the formula under explicit instances. `Q` is
  closed (`isClosed_range_map_of_isClosedSubgroup`), and `P(𝔸_F) K = G(𝔸_F)` gives
  `g = q k` for every `g`. `G(𝔸_F)` is second countable, by the published
  `AdelicGroupPoints.secondCountableTopology`. So
  `CompactFactorization.exists_pos_eq_smul_map_mul_prod` applies with the Haar measure
  `parabolicImageHaar` on `Q` and `compactHaarProbability F G K hK` on `K`. It gives `c > 0` with
  `Measure.haar = c • map ((q, k) ↦ q k) (dq × dk)`. Integrability of `(q, k) ↦ f(q k)` follows
  from integrability of `f` for `Measure.haar` and `c ≠ 0`. Fubini (`integral_prod_symm`) gives
  `∫ f dg = c ∫_K ∫_Q f(q k) dq dk`, and `integral_parabolicImageHaar` rewrites the inner
  integral.

## Relation to the sources

The statement is Mœglin–Waldspurger, I.1.13, printed p. 18
(`moeglin-waldspurger-1995-spectral-decomposition`, chapter file
`05.1_pp_1_18_Hypotheses_and_general_notation.pdf`, PDF p. 18), up to the constant `c` and the
generality recorded in `AdelicIwasawaIntegrationStatement.md`. The source states without proof
that `f ↦ ∫_{U_0(𝔸) × M_0 × K} f(u m k) m^{-2ρ_0} dk dm du` is a Haar measure on `G`, and it
states the compatibility formula for standard parabolics. The Lean proof supplies the argument
along the decompositions `G(𝔸_F) = P(𝔸_F) K` and `P = Z(χ) U(χ)`. It does not use the
unimodularity route suggested in the task contract. The published `CompactFactorization`
theorem needs only that `K` is compact, because the modular function of `G(𝔸_F)` is trivial on
the compact subgroup `K`. Getz–Hahn (8.25), printed p. 229
(`getz-hahn-2024-automorphic-representations`), state the local analogue. That source is not
used in the proof.
