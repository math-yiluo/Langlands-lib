# Representations of the absolute Weil group and weak association

Worker 8 authored this definition unit for task
`6c50b2fd-cb4a-47b3-8f5d-d464916d69fb`. All declarations lie in the namespace
`Langlands.ClassField.Global.WeilMapSystem`. For the projective limit `W_F = S.WeilGroup` of a
supplied transitive system `S` of Weil maps (module
`Langlands.ClassField.Global.AbsoluteWeilGroup`), the module defines:

- inflation of representations of `W_{K/F}` to `W_F`;
- local components of representations of `W_F` along local-to-global Weil maps
  `W_{F_v} → W_F` (module `Langlands.ClassField.Global.AbsoluteLocalWeilMap`);
- weak association of representations of `W_F` with unramified spectral systems and with
  actual cuspidal classes, in the sense of Henniart 2000, §2.2.

These are the absolute counterparts of the published relative notions in
`Langlands.Automorphic.Unramified.RelativeWeilAssociation`. The comparison between the two
is proved under an explicit hypothesis that local-to-global Weil maps exist. No local
map, representation or spectrum is constructed.

## Setting

A class family `c`, a number field `F : Type u`, a field `Ω : Type u` with
`[Algebra F Ω]`, `h : FundamentalClass.Restriction c` and `S : WeilMapSystem c F Ω h`.
Layers are `K : FiniteGaloisIntermediateField F Ω`. Representations are the published
`FiniteRepresentation.{0, u, uV} ℂ G`: finite-dimensional complex representations on a
carrier in an independent universe `uV`. `IsContinuous` refers to the usual topology on
endomorphisms. On `W_{K/F}` it uses the Krull-topology convention of the relative
association module.

## Declarations

### Inflation

- `S.continuous_levelHom_krull K`: the projection `S.levelHom K : W_F → W_{K/F}` is
  continuous for the Krull topology on `Gal(K/F)`. This follows from `continuous_levelHom`
  and the published bridge `RelativeWeilGroup.continuous_krull_of_relativeGalois`.
- `S.inflate K A`, for `A : FiniteRepresentation ℂ (RelativeWeilGroup c F K)`, is
  `FiniteRepresentation.restrict (S.levelHom K) A`, on the same carrier.
  `inflate_representation`: `(S.inflate K A).representation x = A.representation
  (S.toLevel K x)`. `rank_inflate`: the rank is unchanged.
- `isContinuous_inflate`: inflation preserves continuity (published
  `FiniteRepresentation.isContinuous_restrict`).
- `isUnitary_inflate`: inflation preserves unitarizability. The same invariant inner
  product works.
- `subrepresentationCompOrderIso ρ f hf`: for a surjective monoid homomorphism `f` and a
  complex representation `ρ`, the subrepresentations of `ρ` and of `ρ.comp f` correspond as
  ordered sets. Both consist of the same submodules.
- `isIrreducible_inflate`: if `S.toLevel K` is surjective, inflation preserves
  irreducibility. Mathlib's irreducibility means that the subrepresentations form a simple
  order. Surjectivity of `S.toLevel K` is a hypothesis here. It is not proved for the
  projective limit (see `AbsoluteWeilGroup.md`).

### Local components and matching

Let `v : FinitePlace F` and `θ : W_{F_v} →ₜ* S.WeilGroup`.

- `S.localComponent A θ` is `FiniteRepresentation.restrict θ A`, the representation
  `A ∘ θ` of the actual local Weil group on the carrier of `A`
  (`localComponent_representation`). It is continuous when `A` is
  (`localComponent_isContinuous`).
- `S.localEulerPolynomial A θ` is `LocalFactor.eulerPolynomial` of `A(θ Fr)`, that is
  `det(1 - X A(θ Fr))`, where `Fr` is the published geometric Frobenius lift
  `Weil.Local.localGeometricFrobenius (padicField v)`.
- `S.IsUnramifiedMatchAt A v P` is the conjunction of two conditions. First, some `θ` with
  `S.IsLocalWeilMap v θ` exists. Second, every such `θ` makes `A ∘ θ` unramified for the
  published inertia subgroup `Weil.Local.localInertia (padicField v)` and satisfies
  `S.localEulerPolynomial A θ = P`.

### Weak association

- `S.IsWeaklyAssociated A s`, for a published spectral system
  `s : SpectralSystem (FinitePlace F) n`, states that `A` is continuous, that
  `A.rank = n`, and that on one cofinite set of finite places `v`, `s` is defined at `v`
  (`v ∉ s.exceptional`) and `S.IsUnramifiedMatchAt A v (s.eulerPolynomial v _)` holds.
- `S.IsWeaklyAssociatedClass A π`, under `[CompactSpace (AdeleQuotient F)]`, for an actual
  full cuspidal class `π : Automorphic.CuspidalOperatorRealization.IsoClass F r` of
  `GL_{r+1}` over `F`, states that some spectral system `s` with
  `IsoClass.HasSpectralSystem π s` is weakly associated with `A`.

### Invariance under equivalence

For an equivalence `φ : FiniteRepresentation.Equiv A B`, possibly between carriers in
different universes:

- `representation_eq_conj_of_equiv`: `B(x) = φ ∘ A(x) ∘ φ⁻¹`;
- `isContinuous_of_equiv`, `localEulerPolynomial_eq_of_equiv`,
  `localComponent_isUnramified_of_equiv`;
- `IsUnramifiedMatchAt.of_equiv`, `IsWeaklyAssociated.of_equiv` and
  `IsWeaklyAssociatedClass.of_equiv`.

The proofs are those of the published relative module, written for `W_F`.

### Comparison with the relative notions

Let `A` be a representation of `W_{K/F}`.

- `eulerPolynomial_representation_conj`: `det(1 - X A(x⁻¹ y x)) = det(1 - X A(y))`. The
  proof uses the linear equivalence with components `A(x⁻¹)` and `A(x)`, and the published
  `LocalFactor.eulerPolynomial_conj`.
- `isUnramifiedMatchAt_inflate`: suppose `A` satisfies the published relative
  `RelativeWeilGroup.IsUnramifiedMatchAt A v P` and some local-to-global Weil map at `v`
  exists. Then `S.IsUnramifiedMatchAt (S.inflate K A) v P` holds. Given `θ`,
  `IsLocalWeilMap.exists_level` writes `S.toLevel K ∘ θ` as `x⁻¹ ι x` for a local-to-relative
  Weil map `ι` at some place `w` above `v`. The relative condition at `w` applies to `ι`, and
  unramifiedness and Euler polynomials are invariant under conjugation.
- `isWeaklyAssociated_inflate`: relative weak association of `A` with `s`, together with
  the existence of local-to-global Weil maps at all but finitely many finite places, gives
  weak association of `S.inflate K A` with `s`.
- `isWeaklyAssociatedClass_inflate`: the same for cuspidal classes.

## Source correspondence

- G. Henniart, *Une preuve simple des conjectures de Langlands pour GL(n) sur un corps
  p-adique*, Invent. Math. 139 (2000), 439–455, literature ID `henniart-2000-simple-proof`,
  SHA256 `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`. The PDF page is
  the printed page minus 438. §2.1, printed p.444 (PDF p.6): `W_F` is the Weil group of
  `\bar{ℚ}` over `F`. §2.2, printed p.444 (PDF p.6): a continuous complex representation `S`
  of degree `n` of `W_F` and an automorphic representation `Π` of `GL_n(𝔸_F)` are
  *associated* if `L(S_v, s) = L(Π_v, s)` for almost every finite place `v` at which the
  local components `S_v` and `Π_v` are unramified. §2.4, printed p.445 (PDF p.7), applies
  this to irreducible `S` and cuspidal `Π`.
- J. Tate, *Number theoretic background*, Proc. Sympos. Pure Math. 33, Part II (1979),
  literature ID `tate-1979-number-theoretic-background`, SHA256
  `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`. §2.1, printed p.9
  (PDF p.18): every representation of `W_F` factors through some `W_{E/F}`, because
  `W_F = proj lim W_{E/F}` and `GL(V)` has no small subgroups. The restriction
  `V ↦ V_v` along `θ_v` of (1.6.1) depends only on `v`.

### Derived formulation

The relative module lists the choices shared with this one. These are: Euler polynomials
in place of `L`-functions; one cofinite set of places; geometric normalizations; the
explicit continuity and rank conditions; and the restriction to actual full cuspidal
classes. They are not repeated here. The choices specific to the absolute group are these.

1. **Supplied system.** `W_F` is the projective limit of a supplied `WeilMapSystem`, not
   a group constructed from arithmetic alone (see `AbsoluteWeilGroup.md`).
2. **Local components.** Henniart's `S_v` is the restriction along `W_{F_v} → W_F`. That
   map is determined up to conjugation (Tate (1.6.1)). Here matching is required for every
   map satisfying `IsLocalWeilMap`. No uniqueness theorem is used, and the result does not
   depend on any choice. As in the relative module, the existence of one such map is a
   conjunct, so matching is never vacuous.
3. **Inflation and factorization.** Tate's §2.1 shows that representations of `W_F`
   factor through some `W_{E/F}`. Inflation is the converse construction. The factorization
   theorem is not proved here.

## Scope and remaining obligations

These results are neither proved nor assumed here:

- that every continuous representation of `S.WeilGroup` is an inflation from some layer
  (Tate §2.1);
- surjectivity of `S.toLevel K`, which `isIrreducible_inflate` takes as a hypothesis;
- existence of local-to-global Weil maps, which the comparison theorems take as a
  hypothesis;
- the converse comparison, from absolute to relative matching. It needs every
  local-to-relative Weil map to lift, up to conjugation, to a local-to-global one;
- existence or uniqueness of associated classes or representations, strong multiplicity
  one and Chebotarev-type uniqueness, and the consequences of Henniart §2.2–2.4.
