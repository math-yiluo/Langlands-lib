# Surjectivity of `N(k)/Z(k) → N(U)/Z(U)` from rational structure statements

This module is a conditional deduction. It proves no structural theorem about reductive
groups. Each structural input is an explicit premise. Four premises are the published
propositions `GenericMinimalParabolicStatement`, `MinimalParabolicConjugacyStatement`,
`MinimalParabolicSplitTorusConjugacyStatement` and `GenericCentralizerStatement`. The other
two are explicit hypotheses `hself` and `hrig`, described below.

Notation: `k` is a field, `G` is a group scheme over `Spec k` with `IsConnectedReductive G`,
and `i : T ⟶ G` is a maximal split torus. `N(U)` and `Z(U)` are the published
`(torusNormalizer i).carrier U` and `(torusCentralizer i).carrier U` over a test scheme
`U`. `N(k)` is `normalizerPoints i`. For a cocharacter `χ : 𝔾_m ⟶ G`, `P(χ)`, `Z(χ)` and
`U(χ)` are the published dynamic subgroup functors `Dynamic.parabolic`,
`Dynamic.centralizer` and `Dynamic.unipotent`.

## Main results

`relativeWeylGroupRestrict_surjective_of_rigid` proves that
`relativeWeylGroupRestrict i U : N(k)/Z(k) → N(U)/Z(U)` is surjective for any test scheme
`U`, given the six premises:

- `hgen : GenericMinimalParabolicStatement`: `P(ν ≫ i)` is a minimal parabolic for
  every generic cocharacter `ν` of `T`.
- `hconj : MinimalParabolicConjugacyStatement`: two minimal parabolics are conjugate by a
  rational point.
- `htorus : MinimalParabolicSplitTorusConjugacyStatement`: two maximal split tori inside a
  minimal parabolic `P` are conjugate by a rational point of `P`.
- `hcent : GenericCentralizerStatement`: `Z(ν ≫ i) = torusCentralizer i` for generic `ν`.
- `hself`: every parabolic subgroup `j : P ⟶ G` of this `G` satisfies
  `(SubgroupFunctor.range j).normalizer = SubgroupFunctor.range j`. This is the body of
  `Langlands.GroupScheme.ParabolicSelfNormalizerStatement` (module
  `Langlands.GroupScheme.Rational.ParabolicNormalizerStatement`; Conrad, *Reductive group
  schemes*, Corollary 5.2.8). That statement was not yet in the Library at this module's
  base, so its body appears here verbatim at `k` and `G`. A proof `h` of the statement
  gives `hself` as `fun P j hj => h k G hG P j hj`.
- `hrig` (rigidity on `U`): every `g ∈ N(U)` acts on `T` through one automorphism
  `σ : T ≅ T`. That is, for every `V`, `a : V ⟶ U` and `t : V ⟶ T.X`,
  `(a ≫ g) * i(t) * (a ≫ g)⁻¹ = i(σ(t))`. This premise is where connectedness of `U`
  enters: for connected `U` it is the rigidity of split tori, which this module does not
  prove. No other premise mentions `U`.

The theorem has no other hypotheses on `U`. It holds even for empty or disconnected `U`
whenever `hrig` holds there.

`exists_inv_mul_mem_torusCentralizer` is the pointwise form. Given the same five structural
premises, a point `g ∈ N(U)` and an automorphism `σ` as in `hrig` for this `g`, it gives
`n ∈ N(k)` with `(n|_U)⁻¹ * g ∈ Z(U)`, where `n|_U` is `G.constantPoint n U`. The main
theorem applies this to a representative `g` of a class in `N(U)/Z(U)`. Then
`QuotientGroup.eq` gives `relativeWeylGroupRestrict i U (mk n) = mk g`.

## Proof of `exists_inv_mul_mem_torusCentralizer`

1. **A cocharacter `ν` with `ν` and `ν ≫ σ` both generic.** The set
   `r = relativeRoots i ∪ {σ ≫ α | α ∈ relativeRoots i}` is finite
   (`IsSplitTorus.finite_relativeRoots`). It does not contain `0`: relative roots are
   nonzero, and `σ ≫ α = 0` forces `α = 0` since `σ` is an isomorphism.
   `IsSplitTorus.exists_pairings_ne_zero` gives a cocharacter `ν` pairing nontrivially with
   every element of `r`. Then `ν` is generic, and so is `ν ≫ σ`, because
   `⟨α, ν ≫ σ⟩ = ⟨σ ≫ α, ν⟩` (`latticePairing_apply`).
2. **Two minimal parabolics.** `hgen` and `isMinimalParabolicFunctor_iff_exists` give
   minimal parabolic subgroups `j : P ⟶ G` and `j' : P' ⟶ G` with ranges `P(ν ≫ i)` and
   `P((ν ≫ σ) ≫ i)`.
3. **A rational normalizing point conjugating them** (`exists_normalizingPoint_comap_eq`).
   `hconj` gives a rational `h` and `e : P ≅ P'` with `j ≫ Int(h) = e ≫ j'`. The torus
   factors through `P` (`Dynamic.parabolicTorusFactor`), so `i ≫ Int(h)` and `i` are two
   maximal split tori of `G` inside `P'` (`IsMaximalSplitTorus.comp_iso`). `htorus` gives a
   rational `p` of `P'` and `ε : T ≅ T` conjugating the first into the second. For
   `n = j'(p) * h`, `innerIso_mul_hom` and `innerIso_hom_comp` give
   `i ≫ Int(n) = ε ≫ i`, so `n ∈ N(k)`. They also give `j ≫ Int(n) = (e ≫ Int_P'(p)) ≫ j'`.
   By `range_eq_comap_of_comp_eq`, a point `x` lies in `P(ν ≫ i)` exactly when
   `n x n⁻¹` lies in `P((ν ≫ σ) ≫ i)`.
4. **`g` conjugates `ν ≫ i` into `(ν ≫ σ) ≫ i`.** This is the rigidity identity for `g` at
   the torus points `t = ν(s)`, recorded as `ConjugatesCocharacter`.
5. **`m = (n|_U)⁻¹ * g` normalizes `P(ν ≫ i)`, so it lies in `P(ν ≫ i)`.** Normalization
   is `constantPoint_inv_mul_mem_normalizer`, applied to steps 3 and 4. Membership follows
   from `hself` for `j`, rewriting `P(ν ≫ i)` as the range of `j`.
6. **`m` lies in `Z(U)`.** `m ∈ N(U)`, since `n|_U` and `g` lie in `N(U)`
   (`normalizerPointsRestrict`). The range of `i` lies in `Z(ν ≫ i)` (`range_le_torusCentralizer`,
   `torusCentralizer_le_dynamicCentralizer`). `hcent` gives `Z(ν ≫ i) ≤ torusCentralizer i`.
   Then `mem_torusCentralizer_of_mem_parabolic` gives `m ∈ Z(U)`. `G` is separated because
   it is affine over `Spec k`.

## Helper results

- `ConjugatesCocharacter h χ χ'` (definition): for a point `h : U ⟶ G.X` and cocharacters
  `χ χ' : 𝔾_m ⟶ G` over any base, `(a ≫ h) * χ(s) * (a ≫ h)⁻¹ = χ'(s)` for every
  `a : V ⟶ U` and every point `s : V ⟶ 𝔾_m`. It is the condition `h χ h⁻¹ = χ'` over `U`,
  tested on all refinements.
- `ConjugatesCocharacter.inv`: `h⁻¹` conjugates `χ'` into `χ`.
- `ConjugatesCocharacter.conj_mem_parabolic`: such an `h` conjugates `P(χ)` into `P(χ')`
  after every refinement `a : V ⟶ U`. Take an orbit extension `e` of `x` over
  `V × 𝔸¹`, and let `h̃` be `a ≫ h` pulled back to `V × 𝔸¹`. Then `h̃ e h̃⁻¹` is an orbit
  extension of `(a ≫ h) x (a ≫ h)⁻¹`, by the conjugation identity at `V × 𝔾_m`.
- `constantPoint_inv_mul_mem_normalizer`: suppose a rational `n` satisfies
  `P(χ) = P(χ').comap Int(n)` and `g` conjugates `χ` into `χ'`. Then `(n|_U)⁻¹ * g`
  normalizes `P(χ)` over `U`. Both conjugation directions use the previous two lemmas.
- `mem_torusCentralizer_of_mem_parabolic`: over any base with `G` separated, assume the
  range of `i` lies in `Z(χ)` and `Z(χ) ≤ torusCentralizer i`. Then every
  `m ∈ N(U) ∩ P(χ)(U)` lies in `Z(U)`. Its limit `l` (`Dynamic.exists_hasLimit`) lies in
  `Z(χ)` (`HasLimit.mem_centralizer`), hence in `Z(U)`, and `u = m l⁻¹` lies in `U(χ)`
  and in `N(U)`. Fix a torus point `t` and write `τ = i(t)`. The commutator `u τ u⁻¹ τ⁻¹`
  is `τ' τ⁻¹` for another torus point `τ'`, so it lies in `Z(χ)`. It also lies in `U(χ)`,
  because `U(χ)` is normalized by `P(χ)` (`Dynamic.conj_mem_unipotent`). Hence it is `1`
  (`Dynamic.eq_one_of_mem_centralizer_of_mem_unipotent`, using uniqueness of limits
  `HasLimit.unique`). So `u ∈ Z(U)` and `m = u l ∈ Z(U)`.
- `innerIso_hom_comp`: `Int_P(p) ≫ j = j ≫ Int_G(j(p))` for a homomorphism `j : P ⟶ G` and
  a rational point `p` of `P`.
- `range_eq_comap_of_comp_eq`: if `j ≫ φ = E ≫ j'` with `φ : G ≅ G` and `E : P ≅ P'`,
  then `range j = (range j').comap φ`.
- `exists_normalizingPoint_comap_eq`: step 3 above, for any two cocharacters `χ, χ'` of
  `T` whose dynamic parabolics are represented by minimal parabolic subgroups.

## Provenance

`ConjugatesCocharacter` and all results here are internal. The route recombines steps of
Borel–Tits, *Groupes réductifs*, Théorème 5.3 and its proof (printed pp.96–97, PDF
pp.43–44):

- On p.96, rational conjugacy of minimal parabolics (their 4.13) gives `x ∈ G_k` carrying
  one minimal parabolic `P` to another, `P'`. Multiplying `x` by a rational point of
  `R_u(P')`, by conjugacy of Levi subgroups (their 4.7), makes it normalize `𝒵(S)`, hence
  `S`. Here this is step 3, which uses conjugacy of maximal split tori inside `P'`
  (`htorus`) instead of Levi conjugacy.
- On p.97, an element of `𝒩(S)` normalizing the minimal parabolic `P` lies in `P`,
  because `P` is its own normalizer (their 4.3). Moreover `𝒩(S) ∩ P = 𝒵(S)`. These are
  steps 5 and 6. Step 6 replaces their Levi decomposition and solvable-group argument with
  the dynamic decomposition `P(χ) = Z(χ) U(χ)`, `Z(χ) ∩ U(χ) = 1`, already proved in the
  Library.

Borel–Tits apply these facts to `k`-points. Here the point `g` lies over an arbitrary test
scheme `U`, and genericity of `ν ≫ σ` comes from choosing `ν` off finitely many walls.
The hypothesis `hself` is Conrad's Corollary 5.2.8 (*Reductive group schemes*, printed
pp.155–156): the normalizer functor of a parabolic subgroup is that subgroup.

The Milne errata entry for p.549 (`milne-2017-algebraic-groups-errata-2026-11-02`) concerns
the claim that the relative roots form a root system. Nothing here uses root-system axioms;
only finiteness of the relative roots and genericity are used. The entry for p.545 requires
the parabolics in 25.6(b), 25.24 and 25.27 to be minimal, and `S` to be maximal split in
`P` in 25.27. The conjugacy premises used here already assume minimal parabolics and
maximal split tori.

This module does not prove any of the six premises, injectivity of the restriction, or the
bijectivity target `RelativeWeylGroupRestrictStatement`.

The inner-conjugation compatibility `innerIso_hom_comp` is reused from
`Rational.BruhatCoveringReduction`.
