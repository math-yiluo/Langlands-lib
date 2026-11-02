# Dynamic subgroup functors attached to a cocharacter

This module defines the dynamic subgroup functors `P_G(λ)`, `Z_G(λ)` and `U_G(λ)` of a
cocharacter `λ : 𝔾_{m,S} ⟶ G`, for a group scheme `G` over an arbitrary base scheme `S`. They
are defined by actual orbit extension from `𝔾_m` to `𝔸¹` on every scheme `T` over `S`, so
non-affine and non-reduced tests are included.

## Sources

- Conrad, *Reductive group schemes* (2014): Definition 4.1.6 and Theorem 4.1.7 (PDF
  pp. 112–113), together with the paragraph before Definition 4.1.6 (p. 112) on limits of orbit
  maps. Conrad notes on p. 114 that these constructions work over any base scheme `S`.
- Conrad–Gabber–Prasad, *Pseudo-reductive groups*, 2nd ed. (2015): §2.1, Example 2.1.1
  (printed pp. 45–47), Lemma 2.1.4 and Lemma 2.1.5 (printed pp. 49–50).

A *1-parameter subgroup* (cocharacter) of `G` is a homomorphism `λ : 𝔾_m → G`. Following the
Library convention, it is a morphism `(Gm S).toGrp ⟶ G` of group objects in `Over S`, where
`Gm S` is the Library multiplicative group. Conrad (Def. 4.1.6) allows `ker λ ≠ 1` and
`λ = 1`, and so does this module. The `𝔾_m`-action is conjugation `t.g = λ(t) g λ(t)⁻¹`. This is
the case to which Conrad's Theorem 4.1.7 reduces abstract actions, via `G ⋊ 𝔾_m`.

## The affine line

- `AffineLine.scheme S` is the affine line `𝔸¹_S`, Mathlib's `𝔸(PUnit; S)` with its structure
  morphism, as an object of `Over S`. `AffineLine.coord S` is its standard coordinate.
- `AffineLine.homEquiv T` identifies morphisms `T ⟶ 𝔸¹_S` over `S` with global functions
  `Γ(T, ⊤)`, by pulling back the coordinate. The inverse uses `AffineSpace.homOfVector`.
  `homEquiv_comp` gives its naturality, and `hom_ext` gives extensionality.
- `AffineLine.unitInclusion S : 𝔾_{m,S} ⟶ 𝔸¹_S` corresponds to the universal unit of `𝔾_m`.
  By `homEquiv_comp_unitInclusion`, on `T`-points it sends a unit `u ∈ Γ(T,O_T)ˣ` to its
  underlying function `u`. This is the standard open immersion `𝔾_m ⊆ 𝔸¹`. The module does not
  state that it is an open immersion.
- `AffineLine.zeroSection S : S ⟶ 𝔸¹_S` is the zero function. By `homEquiv_comp_zeroSection`,
  every point that factors through it is the zero function.

## Orbit maps, extensions and limits

Fix a cocharacter `λ` (written `χ` in Lean) and a test scheme `T` over `S`. Products are fibre
products over `S` (the cartesian monoidal structure of `Over S`).

- `Dynamic.orbit χ g : T ×_S 𝔾_{m,S} ⟶ G` is the orbit map of a point `g : T ⟶ G`. It is the
  point `(x, t) ↦ λ(t) g(x) λ(t)⁻¹`, defined by the group law of `G` on points over
  `T ×_S 𝔾_{m,S}`. This is the `T`-morphism `𝔾_{m,T} → G_T`, `t ↦ t.g`, in Conrad's text,
  written as a morphism over `S`. `orbit_one`, `orbit_mul` and `orbit_inv` show that
  `g ↦ orbit χ g` is a group homomorphism. `whiskerRight_orbit` gives naturality in `T`.
- `Dynamic.IsOrbitExtension χ g e`: the morphism `e : T ×_S 𝔸¹_S ⟶ G` restricts along
  `T ×_S 𝔾_{m,S} ⊆ T ×_S 𝔸¹_S` (`T ◁ unitInclusion`) to the orbit map of `g`. This is Conrad's
  extension of the orbit map to a `T`-map `𝔸¹_T → G_T`. Extensions of the orbit maps of `1`,
  `g h` and `g⁻¹` are given by `1`, `e e'` and `e⁻¹` (`IsOrbitExtension.one`, `.mul`, `.inv`).
  Extensions restrict along morphisms of tests (`IsOrbitExtension.whiskerRight`).
- `Dynamic.evalZero e : T ⟶ G` is the value of `e` along the zero section
  `T ⟶ T ×_S 𝔸¹_S`. It is multiplicative and natural (`evalZero_mul`, `evalZero_one`,
  `evalZero_inv`, `evalZero_whiskerRight`), and `evalZero_fst` evaluates constant maps.
- `Dynamic.HasLimit χ g l`: some orbit extension `e` of `g` has `evalZero e = l`. This is
  "`lim_{t→0} t.g` exists and equals `l`".

**Uniqueness.** Conrad and CGP note that an extension is unique when `G` is separated, because
`T ×_S 𝔾_m` is schematically dense in `T ×_S 𝔸¹` for every `T`. This module does not prove
uniqueness. It defines existence of an extension, and `HasLimit` asks for *some* extension with
the given zero value. For separated `G` (in particular affine `G`, as in Conrad's Theorem 4.1.7),
these existential definitions are exactly Conrad's. For non-separated `G` they are the
existential versions.

## The dynamic subgroup functors

All three are `SubgroupFunctor G` (see `Langlands.GroupScheme.SubgroupFunctor`) on all schemes
`T` over `S`.

- `Dynamic.parabolic χ`, written `P_G(λ)`: its `T`-points are the `g : T ⟶ G` whose orbit map
  has an extension `T ×_S 𝔸¹_S ⟶ G` (`mem_parabolic`). This is Conrad's
  `P_G(λ)(k') = {g ∈ G(k') | lim_{t→0} λ(t,g) exists}` and CGP Lemma 2.1.4 / p. 46.
- `Dynamic.centralizer χ`, written `Z_G(λ)`: its `T`-points are the `g` whose orbit map is the
  constant map `(x, t) ↦ g(x)` (`mem_centralizer`). Since the orbit map is defined using the
  universal point of `T ×_S 𝔾_m`, this says that `g_{T'}` commutes with `λ(t)` for every
  `T' → T` and every `t ∈ 𝔾_m(T')`. This is Conrad's "subfunctor of points of `G` that commute
  with the `𝔾_m`-action", and CGP Lemma 2.1.5's description of the centralizer of `λ`. CGP proves
  that for affine `G` this equals `P_G(λ) ∩ P_G(-λ)`. That equality is a theorem and is not used
  as the definition here.
- `Dynamic.unipotent χ`, written `U_G(λ)`: its `T`-points are the `g` with `HasLimit χ g 1`,
  that is, an orbit extension with value `1` at zero (`mem_unipotent`). This is Conrad's
  `U_G(λ)(k') = {g ∈ P_G(λ)(k') | lim_{t→0} λ(t,g) = 1}`.

Each subgroup structure comes from `IsOrbitExtension.one/.mul/.inv` together with the
corresponding properties of `evalZero` and `orbit`. Restriction stability comes from
`IsOrbitExtension.whiskerRight`, `evalZero_whiskerRight` and `whiskerRight_orbit`.

## Elementary comparisons

- `unipotent_le_parabolic`: `U_G(λ) ≤ P_G(λ)`.
- `hasLimit_of_mem_centralizer`: a centralizing point has the constant extension
  `T ×_S 𝔸¹_S → T → G`, and its limit is the point itself.
- `centralizer_le_parabolic`: `Z_G(λ) ≤ P_G(λ)`.

The module proves no representability, closedness, semidirect product decomposition or base
change of these functors. Those are the contents of Conrad's Theorem 4.1.7 and of later
statements.
