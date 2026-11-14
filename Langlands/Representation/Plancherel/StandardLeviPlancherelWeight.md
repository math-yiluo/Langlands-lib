# The Plancherel weight on the orbit of a discrete series of a standard Levi

Worker 5. Module `Langlands.Representation.Plancherel.StandardLeviPlancherelWeight`,
namespace `Langlands.Plancherel`.

Waldspurger's wave packets are `f_ψ(g) = ∫_O μ(ω) (E_P^G ψ_ω)(g) dω` (VI.3).
Here `O` is the orbit of a discrete series under the unitary unramified
characters and `μ` is the Plancherel density, used as a function on `O`. In
the Lean development these two ingredients are defined on different groups:

- The weight `plancherelWeight` (module `RationalUnitaryRegularValue`) is a
  function on `Im X(Z_G(ζ ∘ i))`, the unitary unramified characters of the
  centralizer scheme `Z_G(ζ ∘ i)` (`parameterScheme`) of a cocharacter. It is
  defined from a smooth representation of `Z_G(ζ ∘ i)(F)`.
- The wave packets `rationalInducedOrbitWavePacket` (module
  `RationalInducedOrbitWavePacket`) and their decay bound
  `exists_norm_rationalInducedOrbitWavePacket_le_rationalXi_rpow` (module
  `RationalInducedOrbitWavePacketDecay`) take a weight `w : O → ℂ`. Here `O`
  is the orbit of the class of a discrete series `π` of the literal standard
  Levi subgroup `M_I(F)`, a subgroup of `G(F)`. The bound requires `w` to be
  smooth in the circle coordinates `leviRationalUnitaryCoordinates` of
  `Im X(M_I)`.

This module connects the two when `ζ` is a standard cocharacter of `I`. It
defines the Plancherel weight `standardLeviPlancherelWeight : O → ℂ`, proves
that it is smooth in the required coordinates, continuous and nonnegative
where `j_P⁻¹` is, and applies the Library's decay bound to the Plancherel wave
packets. As in module `RationalUnitaryRegularValue`, the weight is defined
under the hypothesis `hreg` that `j_P⁻¹` is regular at every unitary
character. `hreg` is not proved here.

Every result in the module is proved; the module has no Prop-valued target.

## Source

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), 235–333, DOI
10.1017/S1474748003000082, registered as `waldspurger-2003-plancherel`, PDF
SHA256 `4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.

- V.2, printed p.292 / PDF p.58: `μ(ω) = j(ω)⁻¹ ∏_α γ(M_α|M)²` for `ω ∈ O`.
- Lemma V.2.1, printed p.292 / PDF p.58: `μ` is a rational function regular
  on `O`, with `μ(ω) ≥ 0` for `ω ∈ O`.
- VI.3, printed p.302 / PDF p.68: the measure on `O` is the one for which
  `χ ↦ ω ⊗ χ` from `Im X(M)` to `O` locally preserves measures, and
  `f_ψ(g) = ∫_O µ(ω) (E_P^G ψ_ω)(g) dω`.
- Proposition VI.3.1 and its proof, printed p.302–303 / PDF p.68–69:
  `f_ψ ∈ C(G)`. The Library's module `RationalInducedOrbitWavePacketDecay`
  proves a first bound toward it, `|f_ψ(g)| ≤ c Ξ(g) (1 + ‖n_G(g)‖)^{-r}`,
  where `n_G(g)` are the lattice coordinates of the valuation image of `g`.

## Provenance

Derived. Waldspurger's `M` is one Levi subgroup with its orbit `O`, and he
uses `μ` directly as a function on `O`. The Library has two descriptions of a
standard Levi. One is the scheme `Z_G(ζ ∘ i)`, on which `j_P` and `μ` are
built. The other is the subgroup `M_I(F)` of `G(F)`, on which the wave
packets are built. The comparison in this module is internal bookkeeping:

- The Library's `Jacquet.standardLevi_eq_dynamic` (module
  `StandardDynamicConstantTerm`) says that the standard Levi subgroup functor
  of `I` is the dynamic centralizer of `ζ ∘ i` for every standard cocharacter
  `ζ` of `I`. It gives the scheme isomorphism and the identification of
  points used here.
- The descent from `Im X(M)` to `O` uses the Library's description of `O` as
  `Im X(M)` modulo the stabilizer of the class of `π`
  (`discreteSeriesOrbitHomeomorph`, module `DiscreteSeriesOrbitTopology`).
  It also uses the invariance of `plancherelWeight` under unitary self-twists
  of the inducing representation (`plancherelWeight_stabilizer_invariant`,
  module `RationalUnitaryRegularValue`). Waldspurger defines `μ` on `O`
  directly, so this invariance is implicit in his text.
- Smoothness transfers because a pullback of characters is an integer
  monomial map in circle coordinates.

The parabolic used to define `j_P` is the dynamic parabolic `P_G(ζ ∘ i)`. The
wave packets use the standard parabolic `P_I(F)`. This module does not
compare the two parabolics. Only the identification of their Levi subgroups
is used.

## Pullbacks of characters in circle coordinates

Section `MonomialTransfer`, for topological groups `H₁`, `H₂` with families
of norm characters `ν₁`, `ν₂`.

- `isSmoothFiniteTorusFunction_comp_pullback`: let `e₁` be circle coordinates
  on `Im X(H₁)` each of which is the evaluation at a point `g_j` of `H₁`
  (`he₁`). Let `e₂` be circle coordinates on `Im X(H₂)` in which evaluation
  at every point of `H₂` is a Laurent monomial (`HasLaurentUnitaryCoordinates`).
  Let `T : Im X(H₂) → Im X(H₁)` satisfy `(T z)(g) = z(φ g)` for a map
  `φ : H₁ → H₂`. If `f` is smooth in the coordinates `e₁`
  (`IsSmoothFiniteTorusFunction`), then `f ∘ T` is smooth in the coordinates
  `e₂`. Proof: the `j`-th coordinate of `T(e₂⁻¹ y)` is the value of `z` at
  `φ(g_j)`, which is a monomial `∏_k y_k^{n_{jk}}`. So `f ∘ T ∘ e₂⁻¹` is
  `f ∘ e₁⁻¹` composed with the integer torus monomial `finiteTorusMonomial n`.
  The Library's `IsSmoothFiniteTorusFunction.comp_monomial` concludes.

## Canonical circle coordinates are evaluations

Section `CanonicalEvaluation`, for a connected reductive `G` over `F`.

- `exists_rationalCanonicalUnitaryCoordinate_eq_eval`: for each index `j`
  there is `g ∈ G(F)` such that the `j`-th canonical circle coordinate
  (`rationalCanonicalUnitaryUnramifiedCharacterCoordinates`) of every unitary
  unramified character `z` is `z(g)`. Proof: take `g` whose valuation image
  is the `j`-th basis vector `rationalReductiveValuationBasis G hG j`
  (`rationalValuationImageProjection_surjective`), and apply the Library's
  formula `rationalCanonicalUnitaryUnramifiedCharacterCoordinates_symm_apply`.

## Descent to the orbit

Section `OrbitDescent`, for a nonarchimedean group `M`, a normal central
subgroup `C` with Haar measure on `M ⧸ C`, norm characters `νM`, and an
irreducible admissible `π` square integrable modulo `C` (`hsq`). Write `S`
for the stabilizer `discreteSeriesStabilizer` of the class of `π` and `O`
for its orbit `discreteSeriesOrbit`.

- `discreteSeriesOrbitDescend f hf : O → ℂ`, for `f : Im X(M) → ℂ` with
  `hf : f(z s) = f(z)` for `s ∈ S`: the function induced on
  `O ≃ Im X(M) / S` (`discreteSeriesOrbitHomeomorph`).
- `discreteSeriesOrbitDescend_orbitMap`: its value at `π ⊗ z`
  (`discreteSeriesOrbitMap z`) is `f z`.
- `continuous_discreteSeriesOrbitDescend`: it is continuous if `f` is. Proof:
  the orbit map is an open quotient map.
- `nonempty_twistEquiv_of_mem_discreteSeriesStabilizer`: for `s ∈ S` there is
  an equivalence of representations `π ⊗ s ≃ π`.

## Twists of pullbacks

Section `PullbackTwist`.

- `nonempty_twist_pullback_pullback_iso`: for continuous isomorphisms
  `e₂ : H₂ ≃ₜ* H₁`, `e₁ : H₁ ≃ₜ* M`, a smooth representation `B` of `M`, a
  character `ψ` of `M` with an equivalence `B ⊗ ψ ≃ B`, and a character `τ`
  of `H₂` with `τ(h) = ψ(e₁(e₂ h))`, the pullback `B ∘ e₁ ∘ e₂` satisfies
  `(B ∘ e₁ ∘ e₂) ⊗ τ ≅ B ∘ e₁ ∘ e₂`. The same linear equivalence intertwines.

## The standard Levi and the centralizer

Section `Standard`. `G` is connected reductive (`hG`), `i : S → G` a maximal
split torus (`hi`), `ν` generic (`hν`), `I` a set of simple roots, and `ζ` a
standard cocharacter of `I` (`hζ : IsStandardCocharacter i ν (rootSet i ν I) ζ`).
Write `χ = ζ ∘ i`, `M_I = Standard.leviScheme i ν (rootSet i ν I)`, and
`𝐌 = M_I(F)` for the subtype of `G(F)` given by `standardLeviPoints`, in the
form used by the wave-packet modules.

- `standardLeviParameterIso : parameterScheme χ ≅ M_I`: the isomorphism of
  the two schemes, which represent the same subgroup functor of `G`
  (`standardLevi_eq_dynamic`, `isoOfIsRepresentedBy`).
- `standardLeviParameterIso_hom_comp`: it lies over `G`: composed with the
  inclusion `Standard.leviHom` of `M_I` it is the inclusion
  `Dynamic.Affine.centralizerHom χ` of the centralizer.
- `standardLeviDynamicHomeomorph : levi χ ≃ₜ* RationalPointFamily.levi i ν I`:
  the subgroups `Z_G(χ)(F)` and `M_I(F)` of `G(F)` are equal, and this is the
  resulting identification with subspace topologies;
  `standardLeviDynamicHomeomorph_apply_coe` says it is the identity on
  points of `G(F)`.
- `leviRationalPointHomeomorph_map_standardLeviParameterIso`: the point map
  of `standardLeviParameterIso` agrees with this identification.
- `standardLeviCharacterRestrict : Im X(M_I) →ₜ* Im X(Z_G(χ))`, a continuous
  homomorphism. By `standardLeviCharacterRestrict_apply` it sends `z` to
  `z ∘ e`, where `e : Z_G(χ)(F) → M_I(F)` is the identification.
- `isSmoothFiniteTorusFunction_comp_standardLeviCharacterRestrict`: if `f` on
  `Im X(Z_G(χ))` is smooth in the Library's canonical circle coordinates,
  then `y ↦ f(restrict(Φ⁻¹ y))` is smooth, where `Φ` is
  `leviRationalUnitaryCoordinates`. Proof:
  `isSmoothFiniteTorusFunction_comp_pullback`, with the two previous sections
  and the Library's `leviRationalUnitaryCoordinates_hasLaurent`.

## Weights on the orbit of a discrete series of `M_I`

Let `π` be an irreducible admissible representation of `𝐌`, square
integrable modulo a normal central subgroup `C` (`hsq`), and `O` the orbit of
its class under `Im X(M_I)` (with `leviRationalNormCharacters`). Write
`π ∘ e = SmoothRep.pullback (standardLeviDynamicHomeomorph …) π.obj` for the
inducing representation of `Z_G(χ)(F)`.

- `standardLeviCharacterRestrict_mem_stabilizer`: if `s ∈ Im X(M_I)`
  stabilizes the class of `π`, then `s ∘ e` lies in
  `smoothRepUnramifiedTwistStabilizer` of the pullback of `π ∘ e` to the
  points of `parameterScheme χ`. Proof:
  `nonempty_twistEquiv_of_mem_discreteSeriesStabilizer` and
  `nonempty_twist_pullback_pullback_iso`.
- `standardOrbitWeight W hW : O → ℂ`, for `W : Im X(Z_G(χ)) → ℂ` and `hW`
  stating `W(τ z) = W(z)` for every unitary `τ` in that twist stabilizer: the
  function `π ⊗ z ↦ W(z ∘ e)`, by `discreteSeriesOrbitDescend`.
- `standardOrbitWeight_orbitMap`: its value at `π ⊗ z` is `W(z ∘ e)`.
- `isSmoothFiniteTorusFunction_standardOrbitWeight`: if `W` is smooth in the
  canonical circle coordinates of `Im X(Z_G(χ))`, then
  `y ↦ standardOrbitWeight W hW (π ⊗ Φ⁻¹ y)` is smooth. This is the
  hypothesis `hws` of
  `exists_norm_rationalInducedOrbitWavePacket_le_rationalXi_rpow`, in the same form.
- `continuous_standardOrbitWeight`: continuity for continuous `W`.

## The Plancherel weight on the orbit

The section adds the data of `plancherelDensity` for the inducing
representation `A = π ∘ e`. These are `hRefl`, `hCST`, a compact open `K` with
`G(F) = P K = P̄ K` (`hPK`, `hOppK`), continuation data `p`, `q`, nonempty open
sets `DForward`, `DReverse` in the full convergence domains, and a nonempty
open set `D` on which the induced representations are irreducible (`hirr`).
Write `j_P` for `conditionalCanonicalRationalScalar χ … (π ∘ e) p q …` and let
`hreg : RationalFunctionUnitaryRegular (parameterScheme χ) … j_P⁻¹`.

- `standardLeviPlancherelWeight … hreg : O → ℂ`: `standardOrbitWeight` of
  `plancherelWeight … (π ∘ e) … hreg`, well defined by
  `plancherelWeight_stabilizer_invariant`.
- `standardLeviPlancherelWeight_orbitMap`: its value at `π ⊗ z` is
  `plancherelWeight … hreg (z ∘ e)`, that is
  `plancherelDensityConstant · j_P⁻¹(z ∘ e)` by `plancherelWeight_eq`.
- `isSmoothFiniteTorusFunction_standardLeviPlancherelWeight`: smoothness in
  the coordinates `leviRationalUnitaryCoordinates`, in the form of `hws`.
- `continuous_standardLeviPlancherelWeight`: continuity on `O`.
- `standardLeviPlancherelWeight_nonneg`: if `j_P⁻¹` has a nonnegative real
  value at `z ∘ e` (`RationalFunctionNonnegAt`), the weight at `π ⊗ z` is a
  nonnegative real number.
- `standardLeviPlancherelWeight_nonneg_of_forall`: if `j_P⁻¹` has a
  nonnegative real value at every unitary character of `Z_G(χ)`, the weight
  is a nonnegative real number at every point of `O` (Lemma V.2.1, first
  item). Proof: the orbit map is surjective.

## Decay of the Plancherel wave packets

- `exists_norm_standardLeviPlancherelWavePacket_le_rationalXi_rpow`: take a
  compact open `Kw` of `G(F)` with Iwasawa decompositions for the minimal
  parabolic (`hPKw`) and in `M_I(F)` (`hM`). Assume the stabilizer of the
  class of `π` is finite. Take a finite left invariant measure `ρ` on
  `Im X(M_I)`, the coefficient bound `hcoeff` on `π`, and a section
  `s ∈ rationalInducedSmoothOrbitSections`. Then for every real `r` there is
  `c > 0` such that the wave packet
  `rationalInducedOrbitWavePacket … ρ (standardLeviPlancherelWeight … hreg) s`
  satisfies `|f(g)| ≤ c · Ξ(g) · (1 + ‖n_G(g)‖)^{-r}` for all `g ∈ G(F)`.
  Proof: the Library's
  `exists_norm_rationalInducedOrbitWavePacket_le_rationalXi_rpow` with
  `w = standardLeviPlancherelWeight … hreg` and `hws` from
  `isSmoothFiniteTorusFunction_standardLeviPlancherelWeight`. The subgroup
  `Kw` of the wave packet is independent of the subgroup `K` used to define
  `j_P`.

## Not proved here

- `hreg`, the regularity of `j_P⁻¹` at every unitary character (in
  Waldspurger, from IV.3 (5) and (6)).
- Nonnegativity of `j_P⁻¹` at every unitary character, the hypothesis of
  `standardLeviPlancherelWeight_nonneg_of_forall`.
- The comparison of the parabolics `P_G(ζ ∘ i)` and `P_I(F)`, and the
  identification of the Library's `j_P` and `rankOneGammaProduct` with
  Waldspurger's `j` and `γ(M_α|M)`.
- The remaining parts of Proposition VI.3.1: `f_ψ ∈ C(G)` and the continuity
  of `ψ ↦ f_ψ`.
