# The spaces `𝔞_P` and `𝔞_P^*` of standard parabolic subgroups

Module `Langlands.Global.ArthurParabolicSpaces`, namespace
`Langlands.Global.ArthurParabolicSpaces`. Its subject is the comparison of
`𝔞_P` with `RealCharacterDual F P` and of `𝔞_P^*` with `RealCharacterParameter F P`. The
comparison itself is stated in `Langlands.Global.ArthurParabolicSpacesStatement`.

## Sources

J. Arthur, *An introduction to the trace formula* (2005), in the volume registered as
`arthur-ellwood-kottwitz-2005-harmonic-analysis-shimura` (PDF page = printed page + 12):

- §4, p.22: `𝔞_P = 𝔞_{M_P} = Hom(X(M_P)_ℚ, ℝ)` for a standard parabolic subgroup `P = M_P N_P`;
- §5, p.24, (5.1): `𝔞_P^* = X(M_P)_ℚ ⊗ ℝ ≅ X(A_P)_ℚ ⊗ ℝ`, and for `P_1 ⊆ P_2` the restriction maps
  giving `𝔞_{P_2}^* ↪ 𝔞_{P_1}^*` and the dual surjection `𝔞_{P_1} → 𝔞_{P_2}`;
- §5, p.26: `𝔞_P = {H ∈ 𝔞_0 : α(H) = 0, α ∈ Δ_0^P}`.

## Objects

The data are a field `F` (a number field in the applications), a group scheme `G` over `Spec F`
with `IsAffineHom G.X.hom`, a homomorphism `i : T.toGrp ⟶ G` from a commutative group scheme (the
maximal split torus `A_0` in the applications), a cocharacter `ν` and a set `S` of characters
(`Δ_0^P = S`). The standard parabolic subgroup is the published closed representative
`Standard.parabolicScheme i ν S` (module `StandardRepresentability`).

- `torusToParabolic F i ν S : T ⟶ P_S`: the factorization of `i` through the representative,
  from the published inclusions `range i ≤ torusCentralizer i ≤ standardLevi i ν S ≤
  standardParabolic i ν S`; `torusToParabolic_comp` says that it composes with the inclusion of
  `P_S` to `i`.
- `restrictToTorus F i ν S : RealCharacterParameter F P_S →ₗ[ℝ] Vstar T`: restriction of real
  rational characters along `torusToParabolic`, `X(P_S) ⊗ ℝ → X(T) ⊗ ℝ`. With
  `RealCharacterParameter F P = X(P) ⊗ ℝ` (module `AdelicComplexParameters`) and
  `Vstar T = 𝔞_0^*`, this is Arthur's embedding `𝔞_P^* ↪ 𝔞_0^*`: characters of `P` are characters
  of `M_P`, and the restriction to `T ⊇ A_P` realizes (5.1).
- `toCharacterDual F i ν S : V T →ₗ[ℝ] RealCharacterDual F P_S`, `H ↦ (χ ↦ ⟨χ|_T, H⟩)`: the map
  `𝔞_0 → 𝔞_P = Hom(X(P), ℝ)`, the target of the published Iwasawa height
  `IsIwasawaCompact.height`. `toCharacterDual_apply` unfolds it.
- `realParameterPairing_toCharacterDual`: `⟨μ, toCharacterDual H⟩ = ⟨restrictToTorus μ, H⟩` for
  `μ ∈ X(P) ⊗ ℝ` and `H ∈ V T`, with the published `realParameterPairing`. So the two maps are
  transposes of each other.

No `NumberField` assumption is needed for these definitions.

## Provenance

The maps are Arthur's restriction maps (source), built from the published factorization,
character restriction and pairing; the transpose lemma is proved.
