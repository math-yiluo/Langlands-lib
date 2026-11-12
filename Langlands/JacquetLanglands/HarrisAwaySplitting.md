# Harris's groups split at the distinguished place

Author: Worker 5.

This pair splits the finite adelic points of Harris's unitary similitude
groups, as topological groups, into the factor at the distinguished place
`w₀ = v^(1)` and a complement. It also identifies the complements of `GJ` and
`GG`. It supplies the splittings `Φ`, `Φ'` and the identification `θ` that the
generic relation `Langlands.JacquetLanglands.IsAwayTransfer` (module
`Langlands.JacquetLanglands.AwayTransfer`) takes as inputs. The Harris transfer
`JL(π_f)` of Harris (1999), §5, is then this relation with the local
Jacquet–Langlands relation at `w₀`, in a later module. Entry declaration:
`Langlands.JacquetLanglands.harrisAwaySplit`.

Everything here is assembled from published isomorphisms of topological groups
in `Langlands.Shimura`. The module adds no new mathematics beyond rearranging
products and composing with given algebra isomorphisms.

## Source

Harris (1999), §4, printed pp. 308–309 (PDF pp. 10–11). `p` splits in the
imaginary quadratic field `𝒦₀`; `v = v^(1)` is a fixed prime of `𝒦` of
residue characteristic `p` with `inv_v(ℬ) = 1/n`; and "`𝒟` and `ℬ` are
isomorphic away from `v` and their complex conjugates". The CM type
"corresponds to a set of primes `Φ_p` of `𝒦` above `p`",
`Φ_p = {v^(j), j = 1, …, t}`, `𝒟_j = 𝒟 ⊗ 𝒦_{v^(j)}`, and Harris
"implicitly identif[ies]

(4.2) `GJ_p ≅ ∏_j (𝒟_j)ˣ × ℚ_pˣ`

as in [H2, Appendix, A.1]". The level of `GG(A_f)` at printed p. 309 is
"defined as above via an identification `GG(A_f^p) ≅ GJ(A_f^p)`".

Harris (1999), §5, printed p. 312 (PDF p. 14) uses these identifications: the
local constituents of `JL(π_f)` and `π_f` "are the same except at `v`".
Grouping all places other than `v` into one complement makes this a statement
about the two factors of the splitting below.

## Correspondence with Harris's notation

As in the published modules `Langlands.Shimura.HarrisSplitPrimeFactors` and
`Langlands.Shimura.HarrisInnerFormLevels`:

- Harris's `𝒦₀` is `F` (a CM field quadratic over `ℚ`), `𝒦` is `K` (totally
  complex, quadratic over the totally real `E`), with `ι : F →+* K`.
- An algebra with involution of the second kind is
  `σ : SecondKindInvolution E K A`. For `GJ` the algebra is `𝒟`, for `GG` it is
  `ℬ`. The group `G` is `σ.rationalInvolution`, with points
  `σ.rationalInvolution.FiniteAdelicPoints` (its `A_f`-points) and
  `σ.rationalInvolution.PrimeToPoints p` (its `A_f^p`-points).
- The prime `p`, `hp : p.Prime`, the place `v` of `ℚ` above `p`, and a
  degree-one place `𝔭 : FinitePlacesAbove F v.1` of `F` with
  `h𝔭 : Function.Bijective (FiniteExtension.completionMap v.1 𝔭.1)`. Harris's
  `Φ_p` is `FinitePlacesAbove K 𝔭.1` (the places `v^(j)`). Harris's
  distinguished place `v = v^(1)` is `w₀ : FinitePlacesAbove K 𝔭.1`, and
  `𝒟_j` is `K_w ⊗[K] A`.

As in those modules, the choice of `𝔭` from the CM type and the choice of
`w₀` are inputs here; they are not derived from Harris's choices.

## Declarations

All declarations are in namespace `Langlands.JacquetLanglands`.

### Continuous multiplicative isomorphisms of products

Mathlib provides these as homeomorphisms and as multiplicative equivalences,
but not as `ContinuousMulEquiv` (`≃ₜ*`). Each is built with
`ContinuousMulEquiv.mk'` from the Mathlib homeomorphism, and multiplicativity
is checked componentwise. The `_apply` lemmas are `rfl`.

- `continuousMulEquivProdCongr e₁ e₂ : M × N ≃ₜ* M' × N'`, `(x, y) ↦ (e₁ x, e₂ y)`.
- `continuousMulEquivProdAssoc M N P : (M × N) × P ≃ₜ* M × (N × P)`.
- `continuousMulEquivPiSplitAt Y i : (Π j, Y j) ≃ₜ* Y i × Π_{j ≠ i} Y j`,
  `x ↦ (x i, (x j)_{j ≠ i})` (from `Homeomorph.piSplitAt`).
- `continuousMulEquivPiCongrRight e : (Π i, Y i) ≃ₜ* Π i, Y' i`, componentwise.

### Unit groups of local factors

`ImaginaryQuadraticSplit.FactorUnits K A S` is the published carrier
`(S ⊗[K] A)ˣ`, with the units topology of the `S`-module topology on
`S ⊗[K] A`.

- `factorUnitsEquiv f`, for an `S`-algebra isomorphism
  `f : S ⊗[K] A ≃ₐ[S] S ⊗[K] B`, is the induced isomorphism
  `FactorUnits K A S ≃ₜ* FactorUnits K B S` (`Units.mapEquiv`). Both directions
  are continuous because `S`-linear maps are continuous for module topologies
  (`IsModuleTopology.continuous_of_linearMap`) and `Units.map` of a continuous
  monoid map is continuous. `factorUnitsEquiv_apply_val`: the underlying
  element is `f x`.
- `factorUnitsMatrixEquiv s`, for a splitting
  `s : S ⊗[K] A ≃ₐ[S] Matrix (Fin n) (Fin n) S`, is the induced isomorphism
  `FactorUnits K A S ≃ₜ* GeneralLinear n S` onto the Library's `GL_n(S)` with
  Mathlib's units topology of the product topology on matrices. Continuity is
  proved the same way, using that the matrix topology is the `S`-module
  topology (`IsModuleTopology` of the product `Fin n → Fin n → S`).
  `factorUnitsMatrixEquiv_apply_val`: the underlying matrix is `s x`.

### Harris's splitting at `w₀`

In the Harris setting above, with `[Module.Finite ℚ A]`:

- `HarrisAwayComplement σ ι p v 𝔭 w₀` is the topological group

      ((Π_{w ∣ 𝔭, w ≠ w₀} (K_w ⊗[K] A)ˣ) × ℚ_vˣ) × G(A_f^p),

  with the `w`-factors `FactorUnits K A K_w`. In Harris's notation this is
  `∏_{j>1} (𝒟_j)ˣ × ℚ_pˣ × GJ(A_f^p)`, everything except the factor at `v`.
- `harrisLocalSplit σ ι p v 𝔭 h𝔭 w₀ : G(ℚ_v) ≃ₜ* (K_{w₀} ⊗[K] A)ˣ ×
  ((Π_{w ≠ w₀} (K_w ⊗[K] A)ˣ) × ℚ_vˣ)` is Harris's (4.2) with the factor at
  `w₀` split off. It composes the published `σ.splitPrimeHomeomorph ι v.1
  (splitPlaceEmbedding v.1 𝔭 h𝔭)` (`G(ℚ_v) ≃ₜ* (ℚ_v ⊗[F] A)ˣ × ℚ_vˣ`) with
  the published `splitPlaceUnitsHomeomorph ι v.1 𝔭 h𝔭`
  (`(ℚ_v ⊗[F] A)ˣ ≃ₜ* Π_{w ∣ 𝔭} (K_w ⊗[K] A)ˣ`), then with
  `continuousMulEquivPiSplitAt` at `w₀` and reassociation.
- `harrisAwaySplit σ ι p hp v 𝔭 h𝔭 w₀ : G(A_f) ≃ₜ* (K_{w₀} ⊗[K] A)ˣ ×
  HarrisAwayComplement σ ι p v 𝔭 w₀` composes the published
  `finiteAdelicPointsSplit p hp.ne_zero` (`G(A_f) ≃ₜ* G(Π_{w ∣ p} ℚ_w) ×
  G(A_f^p)`), the published `dividingPrimePointsEquiv p hp v`
  (`G(Π_{w ∣ p} ℚ_w) ≃ₜ* G(ℚ_v)`), `harrisLocalSplit`, and reassociation.
  - `harrisAwaySplit_apply_fst`: the factor at `w₀` of `g` is the
    `w₀`-component of the published product decomposition
    `σ.splitPlacePoints ι v.1 𝔭 h𝔭` of the local point
    `σ.rationalInvolution.finiteLocalMap v.1 g`. It is proved with the
    published `dividingLocalMap_finiteAdelicPointsSplit`.
  - `harrisAwaySplit_apply_snd_snd`: the `G(A_f^p)`-component of the
    complement is the published prime-to-`p` projection
    `(finiteAdelicPointsSplit p hp.ne_zero g).2` (`rfl`).
- `harrisAwaySplitGL σ ι p hp v 𝔭 h𝔭 w₀ s`, for a splitting
  `s : K_{w₀} ⊗[K] A ≃ₐ[K_{w₀}] M_n(K_{w₀})`, is `harrisAwaySplit` followed
  by `factorUnitsMatrixEquiv s` on the first factor:
  `G(A_f) ≃ₜ* GL_n(K_{w₀}) × HarrisAwayComplement`. This is the splitting for
  `GJ`, whose algebra `𝒟` is split at `v`. Harris's local representation `π_v`
  of `GJ` is a representation of `GL_n(K_v)` (it is assumed supercuspidal on
  printed p. 312). `harrisAwaySplitGL_apply_fst`: the matrix at `w₀` is `s`
  applied to the `w₀`-component of `splitPlacePoints`.

### Identification of the complements

In the Harris setting with two algebras `D` (for `GJ`) and `B` (for `GG`)
over `K`, with involutions `σD` and `σB`:

- `harrisComplementEquiv σB σD ι p v 𝔭 w₀ f e he :
  HarrisAwayComplement σD ι p v 𝔭 w₀ ≃ₜ* HarrisAwayComplement σB ι p v 𝔭 w₀`
  is the product of
  1. `factorUnitsEquiv (f w)` for `K_w`-algebra isomorphisms
     `f w : K_w ⊗[K] D ≃ₐ[K_w] K_w ⊗[K] B` at the places `w ≠ w₀` above `𝔭`
     (Harris: "`𝒟` and `ℬ` are isomorphic away from `v`");
  2. the identity of `ℚ_vˣ`; and
  3. the published `σB.innerFormPrimeToEquiv σD p e he : GJ(A_f^p) ≃ₜ*
     GG(A_f^p)`, induced by an `A_f^p`-algebra isomorphism
     `e : A_f^p ⊗[ℚ] D ≃ A_f^p ⊗[ℚ] B` that intertwines the involutions
     (Harris's identification `GG(A_f^p) ≅ GJ(A_f^p)`, here oriented from `GJ`
     to `GG`).

The isomorphisms `f w`, `e` and `s` are explicit inputs, as Harris fixes such
identifications without naming them. The construction does not require `f w`
to be compatible with the involutions. In (4.2) the group `(K_w ⊗[K] A)ˣ`
at a place `w ∣ 𝔭` is a factor of `G(ℚ_v)` with no involution condition: the
involution exchanges it with the factor at the conjugate place above the other
prime of `F` over `v`, and (4.2) keeps only the factors above `𝔭`.

## Scope

- Only the group-level splittings are constructed. No representation appears
  in this module.
- The existence of the isomorphisms `s`, `f w` and `e` (from Harris's
  hypotheses on the local invariants of `𝒟` and `ℬ`) is not formalized; they
  are parameters.
- `HarrisAwayComplement` groups the places `w ≠ w₀` above `𝔭`, the factor
  `ℚ_vˣ` and `G(A_f^p)` into one group. It does not decompose `G(A_f^p)` into
  local factors, since the Library has no restricted-product decomposition of
  these points.

## Validation

In-place `lean_check` of this module with declaration
`Langlands.JacquetLanglands.harrisAwaySplit` (record
`890ccb8c-3597-474c-9231-59891f5cad2e`): 0 errors, 0 warnings; the
inspection reports a definition using only `propext`, `Classical.choice` and
`Quot.sound`.
