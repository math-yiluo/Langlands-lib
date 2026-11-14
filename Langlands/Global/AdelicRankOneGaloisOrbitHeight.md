# The rank-one orbit-height bound from a twisted split factorization over a Galois splitting field

Author: Worker 17. The hypothesis `hM` of
the core theorem is the body of Worker 5268's Library proposition `HasTwistedOverlapMatching`
(module `Langlands.Global.AdelicGaloisOverlapMatching`), written out inline.

This internal helper module belongs to the proof of the rank-one parabolic rational-orbit
height bound (`Langlands.Global.RepresentationGrowth.RankOneParabolicRationalOrbitHeightBoundStatement`).
It formalizes the adelic part of Springer's proof of the fundamental-set property (F) in
semisimple rank one (T. A. Springer, *Reduction theory over global fields*, 1994, §3.6,
pp. 215–216). Its core theorem derives the target's conclusion,
`HasUniformNormOneRationalOrbitHeightBound F G ρ (Pi.single j 1)`, from Springer's §3.5
factorization over a finite Galois splitting field `L`, given as a hypothesis.

## Springer's argument and the formal version

Springer writes `g ∈ G(A, k)¹` over the splitting field `l` as `g = x t u γ`, with `x` in a
compact set, `t` in the torus with bounded simple roots, `u` in the unipotent radical and
`γ ∈ G(l)`. He distinguishes two cases.

- If all simple roots satisfy `|β(t)| ≥ d`, the element lies in a compact-times-rational
  set over `l`, and the image of `G(A, k)¹` in the quotient is relatively compact (§3.5).
- Otherwise the parabolic `Q = ⋂_s Int(γ⁻¹) P(s.α)` is defined over `k`, conjugate to `P`
  over `k`, and after a rational translation `γ ∈ P(l)`. Then for a `k`-representation `ρ`
  adapted to `P`, with highest weight line `ε`, the height `‖ρ(g)·ε‖` over `l` equals
  `|ω(t)| ‖ρ(x)·ε‖` and is bounded, because the weight `ω` is a nonnegative combination of
  the simple roots. Springer chooses the height on `V(A, l)` so that its restriction to
  `V(A, k)` is the given height.

The formal version follows this outline, with three changes.

1. The bound is proved directly for the orbit height of the line `Pi.single j 1` (the
   target's conclusion), not for membership of `g` in a Siegel set.
2. Springer's Borel subgroup lies in `P`. Here the split torus `i` over `L` is arbitrary,
   so the matched case uses a rational point `m₀ ∈ G(L)` with `m₀ P(ν) m₀⁻¹ ⊆ (P_F)_L`, and
   the conjugated representation `ρ_L ∘ Int(m₀)` (see the companion module
   `Langlands.GroupScheme.Rational.RankOneGaloisParabolicDescent`).
3. Instead of choosing a height over `L` that restricts to the height over `F`, the proof
   uses `orbitHeight_scalarExtensionNormOneMap` (helper module
   `Langlands.Global.AdelicScalarExtensionOrbitHeight`): the height over `L` of the scalar
   extension is the height over `F` raised to the power `[L : F]`.

The statements below are our own formalization (provenance: derived from Springer §3.6).

## Setting and conventions

`F` and `L` are number fields in universe `u` with `[Algebra F L]`, `[FiniteDimensional F L]`
and `[IsGalois F L]`. `G` is a group scheme over `Spec F` with `[IsAffine G.X.left]`,
`[IsAffineHom G.X.hom]` and `[LocallyOfFiniteType G.X.hom]`, and
`G_L = AffineWeil.unitBaseChange F L G` is its base change. Each declaration omits the
instances it does not use. The published map

`scalarExtensionNormOneMap F L G : G(𝔸_F)¹ → G_L(𝔸_L)¹`

is scalar extension of norm-one adelic points, and `rationalSection F L G q` is the
principal adelic point of a rational point `q ∈ G_L(L)`. For a rational point `m` of a group
`H`, `rationalCoeffEquiv K H m` is the same point viewed as a `K`-coefficient point, and
`rational K H` and `rationalNormOne K H` are the principal embeddings into `H(𝔸_K)` and
`H(𝔸_K)¹`.

Over `F`: `iF : TF.toGrp ⟶ G` is a maximal split torus with generic cocharacter `νF`, the
group has rank one (`simpleRelativeRoots iF νF = {αF}`), and `P_F = standardParabolic iF νF ∅`.
The representation `ρ : MatrixRepresentation G (Fin n)` has `P_F` as exact stabilizer of the
coordinate line `j` (`ρ.HasExactCoordinateLineStabilizer P_F j`), as in the target statement.
Over `L`: `i : T.toGrp ⟶ G_L` is a maximal split torus with generic cocharacter `ν`, and
`Δ = simpleRelativeRoots i ν`.

A *factorization* of `g ∈ G(𝔸_F)¹` is an identity

`scalarExtensionNormOneMap F L G g = x · i(t) · P(ν)(p) · rationalSection F L G q`

with `x ∈ C`, `t ∈ T(𝔸_L)` such that `i(t)` has norm one and `|β(t)| ≤ c` for all `β ∈ Δ`
(written with `PositiveRealTorus.normCharacter L T β t`), `p` a norm-one point of the
minimal standard parabolic `Standard.parabolicScheme i ν ∅`, and `q ∈ G_L(L)`. *Matching* of
a family `J : Gal(L/F) → Set (characterLattice T)` with `q` is the inverse-orbit condition
described in the companion module `RankOneGaloisParabolicDescent`.

## Declarations

### `AdelicGroupPoints.constantPoint_base_eq_rationalCoeffEquiv`

The constant point of a rational point `m ∈ H(K)` at the coefficient algebra `K` itself is
`rationalCoeffEquiv K H m`. *Proof.* Extensionality of over-morphisms; the structure map is
the identity (`rationalCoeffEquiv_left`, `simp`).

### `AdelicGroupPoints.map_innerIso_hom`

On adelic points, `map K H H (H.innerIso m).hom y = r · y · r⁻¹`, where
`r = rational K H (rationalCoeffEquiv K H m)`. *Proof.* `map_apply`,
`affinePointsTarget_apply` and `comp_innerIso_hom` reduce the left side to conjugation by
the constant point of `m` at `𝔸_K`, which equals `r` by naturality of constant points
(`constantPoint_naturality`) and the previous lemma.

### `AdelicGroupPoints.rational_rationalCoeffEquiv_map_inv`

For `f : H ⟶ H'` and `x ∈ H(K)`, the inverse of the principal point of `f(x)` is the image
under `map K H H' f` of the inverse principal norm-one point of `x`. *Proof.*
`rationalNormOne_val`, `map_inv`, `rationalCoeffEquiv_map` and naturality of the principal
embedding (`rational_naturality`).

### `AdelicGaloisUnit.affinePointsBaseChangeMulEquiv_rationalCoeffEquiv`

The published comparison `affinePointsBaseChangeMulEquiv F L L G` carries the `L`-point of
`G` obtained from `δ ∈ G(F)` by the coefficient map `F → L` to the rational point
`baseChangeBasePoint (Spec.algebraMap F L) G δ` of `G_L`, written δ_L. *Proof.* Apply the
inverse equivalence (`affinePointsBaseChangeMulEquiv_symm_left`) and compare underlying
morphisms (`baseChangeBasePoint_fst`, `affinePointMap_apply`).

### `AdelicGaloisUnit.scalarExtensionNormOneMap_rationalNormOne`

For `δ ∈ G(F)`, `scalarExtensionNormOneMap F L G` sends the principal norm-one point of `δ` to
the principal norm-one point of `δ_L`. *Proof.* `scalarExtensionNormOneMap_val_eq_tensor` (helper module
`AdelicScalarExtensionOrbitHeight`) describes the map in three steps. The coefficient maps
`𝔸_F → L ⊗_F 𝔸_F` and `F → L → L ⊗_F 𝔸_F` agree on the image of `F`, so the result follows
from naturality of the comparison (`affinePointsBaseChangeMulEquiv_naturality`),
`affinePointMap_comp` and the previous lemma.

### `MatrixRepresentation.preservesCoordinateLine_baseChange_restrict_of_range_le`

If `ρ` has `Φ` as exact stabilizer of the coordinate line `j`, then for every base change `b`
and every homomorphism `f` into the base-changed group with `range f ≤ Φ.baseChange b`, the
restriction of the base-changed representation along `f` preserves the line `j`. *Proof.* A
point of the source maps into `Φ.baseChange b`, that is, its image lies in `Φ`
(`SubgroupFunctor.mem_baseChange`); the stabilizer hypothesis gives the eigenvalue, and
`pointMatrix_restrict`, `pointMatrix_baseChange` identify the matrices.

### `AdelicGaloisUnit.le_max_one_of_pow_le`

For real `x` and `d ≠ 0`, `x ^ d ≤ M` implies `x ≤ max M 1`. *Proof.* If `x ≤ 1` this is
immediate; otherwise `x ≤ x ^ d` (`le_self_pow₀`).

### `AdelicGaloisUnit.scalarExtensionNormOneMap_mul_rationalNormOne_inv`

Scalar extension sends `g · δ⁻¹` (principal norm-one point of `δ ∈ G(F)`) to
`scalarExtensionNormOneMap F L G g · (rationalSection F L G δ_L)⁻¹`. *Proof.* The map is a
homomorphism, and `scalarExtensionNormOneMap_rationalNormOne`.

### `AdelicGaloisUnit.mul_inv_eq_of_mul_inv_eq`

In a group, `s = x a r` and `r d⁻¹ = m⁻¹ y` give `s d⁻¹ = (x m⁻¹)(m a m⁻¹) y`. *Proof.*
Rewriting and `group`.

### `AdelicGaloisUnit.preservesCoordinateLine_innerIso_restrict_of_le_comap`

If `m₀ ∈ G_L(L)` satisfies `Dynamic.parabolic (ν ≫ i) ≤ ((P_F)_L).comap (G_L.innerIso m₀).hom`,
then the representation `ρ_L ∘ Int(m₀)` (`(ρ.baseChange _).restrict (G_L.innerIso m₀).hom`),
restricted to the minimal standard parabolic `Standard.parabolicHom i ν ∅` of `G_L`,
preserves the line `j`. *Proof.* `MatrixRepresentation.restrict_comp` and the previous
line-preservation lemma; the range condition is `hm₀` after
`SubgroupFunctor.range_comp_le_iff`, `Standard.isRepresentedBy_parabolicHom` and
`standardParabolicEndpoints`.

### `AdelicGaloisUnit.exists_orbitHeight_bound_of_matched_of_conjugator`

The matched case with a fixed conjugator. Assume `G` is connected reductive of `F`-rank one,
`ρ` and `j` as above, `G_L` connected reductive with `i`, `ν` as above, and `m₀ ∈ G_L(L)`
with `m₀ P(ν) m₀⁻¹ ⊆ (P_F)_L`. For a compact `C ⊆ G_L(𝔸_L)` and `c`, there is `B > 0` such that
for every `g ∈ G(𝔸_F)¹` with a factorization `(x, t, p, q)` and every family `J` matched with
`q` with `J 1 = Δ \ {α}`, `α ∈ Δ`, there is `q₀ ∈ G(F)` with
`orbitHeight F G ρ (Pi.single j 1) (g · q₀) ≤ B`.

*Proof.* Worker 5253's line bound
`PositiveRealTorus.exists_hasUniformCharacterBound_torusCoordinateLineCharacter_of_minimalStandardParabolic`
(helper module `AdelicMinimalParabolicLineBound`), applied to `ρ_L ∘ Int(m₀)` (whose line is
preserved by the previous lemma), gives a bound `K` on the norm of the line character of
`t` whenever `i(t)` has norm one and `|β(t)| ≤ c`. The Library's
`exists_pos_orbitHeight_bounds_of_isCompact` gives a distortion constant `B₁` for the compact
set `C · {m₀⁻¹}`. Take `B = max (B₁ · K · H₀) 1`, where `H₀` is the height of the line under
`ρ_L ∘ Int(m₀)` at `1`.

Given the data, `exists_rational_mul_eq_of_inverse_orbit_matching` gives `δ ∈ G(F)` and
`π ∈ (P_F)_L(L)` with `δ_L q⁻¹ = π m₀`. Take `q₀ = δ⁻¹`. By `le_max_one_of_pow_le` it suffices
to bound the `[L : F]`-th power of the height; by `orbitHeight_scalarExtensionNormOneMap` this
power is the height over `L` of the scalar extension of `g δ⁻¹`. By the previous lemmas and
`map_innerIso_hom`,

`scalarExtension(g δ⁻¹) = (x m₀⁻¹) · Int(m₀)(i(t) p) · (P_F)_L(π⁻¹)`.

The last factor is a norm-one point of `(P_F)_L`, which preserves the line, so it does not
change the height (`orbitHeight_mul_map_normOne`). The factor `x m₀⁻¹` lies in `C · {m₀⁻¹}`
and changes the height by at most `B₁`. Finally, the height of `Int(m₀)(i(t) p)` for `ρ_L` is
the height of `i(t) p` for `ρ_L ∘ Int(m₀)` (`orbitHeight_restrict`); the norm-one factor `p`
drops out (`orbitHeight_mul_map_normOne`), and `orbitHeight_mul_map_eq_lineCharacterNorm`
writes the remaining height as the line-character norm of `t` (at most `K`) times `H₀`.

### `AdelicGaloisUnit.exists_orbitHeight_bound_of_matched`

The same statement without `m₀`. *Proof.* If some `m₀` with `m₀ P(ν) m₀⁻¹ ⊆ (P_F)_L` exists,
apply the previous theorem. Otherwise no factorization admits a matched family: by
`exists_rational_minimalParabolic_le_comap_of_inverse_orbit_matching`, a matched family
produces such an `m₀` (namely `δ_L q⁻¹`). So `B = 1` works vacuously.

### `AdelicGaloisUnit.exists_orbitHeight_bound_of_unmatched`

The unmatched case. Assume `G_L` is connected reductive with `i` a maximal split torus that is
also a maximal torus (`IsMaximalTorus i`) and `ν` generic. For a compact `C` and `c, d`, there
is `B > 0` such that every `g ∈ G(𝔸_F)¹` with a factorization `(x, t, p, q)` satisfying also
`d < |β(t)|` for all `β ∈ Δ` has a rational translate `g q₀` with orbit height at most `B`.
(No rank-one or stabilizer hypothesis is needed.)

*Proof.* The Library's
`exists_isCompact_normOne_rational_mul_mem_emptyParabolic_rootBox_mul_compact` (for the split
group `G_L`, root-box radius `b = max 1 (max c d⁻¹)` and compact set `C⁻¹`) gives a compact
`K ⊆ G_L(𝔸_L)¹` and, for every norm-one point in `boundedRootParabolicProduct`, a rational
`r` moving it into `K`. The helper `exists_isCompact_rational_mul_mem_of_scalarExtension`
(module `AdelicGaloisSubsetDescent`) descends `K`: it gives a compact `Ω ⊆ G(𝔸_F)¹` such that
whenever a rational translate of the scalar extension of `h ∈ G(𝔸_F)¹` lies in `K`, some
rational translate `q₁ h` lies in `Ω`. `exists_pos_orbitHeight_bounds_of_isCompact` bounds
heights on `Ω⁻¹` by `B₁`, and `B = B₁ · orbitHeight F G ρ (Pi.single j 1) 1`.

Given the data, `q · scalarExtension(g⁻¹) = P(ν)(p⁻¹) · i(t⁻¹) · x⁻¹` (rearranging the
factorization). This lies in `boundedRootParabolicProduct` because `i(t⁻¹)` has norm one and
`t⁻¹` is in the root box by the Library lemma `AdelicGaloisUnit.inv_mem_torusCharacterBox_of_bounds`
(module `Langlands.Global.AdelicSpringerCentralCompactness`): if `d < |β(t)| ≤ c` for all
`β ∈ Δ`, then `t⁻¹ ∈ torusCharacterBox L T Δ (max 1 (max c d⁻¹))`. Hence a rational translate of the scalar
extension of `g⁻¹` lies in `K`, so `q₁ g⁻¹ ∈ Ω` for some `q₁ ∈ G(F)`, and
`g q₁⁻¹ ∈ Ω⁻¹`. Take `q₀ = q₁⁻¹`.

### `AdelicGaloisUnit.hasUniformNormOneRationalOrbitHeightBound_of_twistedOverlapMatching`

**Core theorem.** Assume `G` connected reductive of `F`-rank one with `iF`, `νF`, `αF`, and `ρ`,
`j` with `P_F` the exact stabilizer of line `j`. Assume `G_L` connected reductive, `i` a
maximal split torus and a maximal torus, `ν` generic. Assume `hM`: there are a compact `C`
and `c, d` such that every `g ∈ G(𝔸_F)¹` has a factorization `(x, t, p, q)` with the further
property that for every `α ∈ Δ` with `|α(t)| ≤ d` there is a family `J` with `J σ ⊆ Δ`,
`J 1 = Δ \ {α}`, matched with `q`. Then
`HasUniformNormOneRationalOrbitHeightBound F G ρ (Pi.single j 1)`.

`hM` is exactly `HasTwistedOverlapMatching F L G T i ν` of the Library module
`Langlands.Global.AdelicGaloisOverlapMatching` (Worker 5268); it is stated inline, so this
module does not import that module. The final module
`Langlands.Global.AdelicRankOneOrbitHeightBoundProof` supplies `hM` from the published
proposition, which unfolds definitionally to this body.

*Proof.* Take `B₁` from the unmatched case and `B₂` from the matched case (both with the
`C`, `c`, `d` of `hM`), and `B = max B₁ B₂`. For `g`, take the factorization from `hM`. If all
simple roots satisfy `d < |β(t)|`, the unmatched case applies. Otherwise some `α ∈ Δ` has
`|α(t)| ≤ d` (`push Not`), `hM` gives a matched family `J`, and the matched case applies.

## Scope

The rank-one hypothesis and the stabilizer hypothesis are used only in the matched case. The
module proves no unconditional instance of the target: the factorization hypothesis `hM`
(Springer §3.5) still has to be supplied, for example by Worker 5268's
`SplitGaloisOverlapMatchingStatement` together with the split fundamental-set and overlap
statements and a Galois Borel twisting.
