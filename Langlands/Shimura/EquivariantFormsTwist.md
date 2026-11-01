# Twisted equivariant functions and functions on double-quotient level spaces

Author: Worker 61. Built on the published
`Langlands.Shimura.EquivariantForms` (Worker 61: `forms`),
`Langlands.Shimura.EquivariantFormsHecke` (Worker 61: `levelTransport`,
`levelPresheaf`, `heckeOperator` and its formula `heckeOperator_apply_coe`)
and Worker 57's published `Langlands.Shimura.Levels` (`CompactOpenLevel`
and its category of transporter arrows, `heckeLevel`, the double-quotient
level spaces `LevelSpace`, `LevelSpace.translate`, `LevelSpace.tower`), and
on Mathlib's `Representation.IsTrivial`.

The module compares two forms of the functional equations of equivariant
functions on a group. The forms of `Langlands.Shimura.EquivariantForms` are
left invariant and twisted on the right by the level; the twisted forms
defined here are twisted on the left by the representation and right
invariant under the level. For a representation of the whole group the two
are identified by multiplying with the representation, and this
identification turns the level transport of
`Langlands.Shimura.EquivariantFormsHecke` into plain right translation. For
trivial coefficients, forms are the functions on Worker 57's double-quotient
level spaces with a one-point `X`, naturally in the level. Everything is
generic in the groups, levels and coefficients.

## Conventions

`R` is a commutative ring, `Γ` and `G` are groups and `ι : Γ →* G` is a
group homomorphism. Elements of subgroups are coerced to `G` silently below.
For a subgroup `K` of `G` and a representation `ρ` of `K` on an `R`-module
`V`, `forms ι K ρ` is the submodule of functions `f : G → V` with
`f (ι γ * g) = f g` and `f (g * k) = ρ k⁻¹ (f g)`. For a representation `ρ`
of `G`, `ρ.comp K.subtype` is its restriction to `K`. The groups and the
carrier `V : Type t` have independent universes.

## Twisted forms and the twist

`ρ : Representation R G V` is a representation of all of `G`.

- `twistedForms ι K ρ : Submodule R (G → V)`: the functions `f : G → V`
  with `f (ι γ * g) = ρ (ι γ) (f g)` for all `γ : Γ`, `g : G` and
  `f (g * k) = f g` for all `g : G`, `k : K`. Both conditions are linear in
  `f`. `mem_twistedForms` unfolds membership.
- `twistEquiv ι K ρ`: the `R`-linear equivalence from
  `forms ι K (ρ.comp K.subtype)` to `twistedForms ι K ρ` sending `F` to
  `g ↦ ρ g (F g)` (`twistEquiv_apply_coe`), with inverse
  `f ↦ (g ↦ ρ g⁻¹ (f g))` (`twistEquiv_symm_apply_coe`). The equations
  match: `ρ (ι γ * g) (F (ι γ * g)) = ρ (ι γ) (ρ g (F g))` by left
  invariance of `F`, and
  `ρ (g * k) (F (g * k)) = ρ (g * k) (ρ k⁻¹ (F g)) = ρ g (F g)`; the
  inverse is checked in the same way, and the two maps are mutually inverse
  because `ρ g⁻¹ ∘ ρ g` and `ρ g ∘ ρ g⁻¹` are the identity.

## Right translation and the presheaf of twisted forms

For subgroups `K`, `L` of `G`:

- `twistedTranslate ι ρ g hg`, for `g : G` with
  `hg : g⁻¹ * k * g ∈ L` for all `k ∈ K`: the linear map from
  `twistedForms ι L ρ` to `twistedForms ι K ρ` sending `f` to
  `x ↦ f (x * g)` (`twistedTranslate_apply_coe`). Left equivariance is
  unchanged, and right invariance under `k ∈ K` follows from
  `x * k * g = x * g * (g⁻¹ * k * g)` and right invariance of `f` under `L`.

Now `G` is a topological group (`TopologicalSpace G`), and a compact open
level `K : CompactOpenLevel G` carries the restriction of `ρ` to
`K.subgroup`. An arrow `a : K ⟶ L` of Worker 57's category of levels is a
group element `a.element` with `a.element⁻¹ * k * a.element ∈ L` for all
`k ∈ K` (`a.respects`); composition multiplies the elements.

- `twistEquiv_levelTransport`: for an arrow `a : K ⟶ L` and a form `F` of
  level `L`, `twistEquiv` of `levelTransport R ι ρ a F` (the form
  `x ↦ ρ a.element (F (x * a.element))` of level `K`) is the right translate
  `twistedTranslate ι ρ a.element a.respects` of `twistEquiv F`; pointwise
  this is `ρ x (ρ a.element (F (x * a.element))) =
  ρ (x * a.element) (F (x * a.element))`.
- `twistedLevelPresheaf R ι ρ : (CompactOpenLevel G)ᵒᵖ ⥤ ModuleCat.{max uG t} R`:
  a level `K` goes to `twistedForms ι K.subgroup ρ` and an arrow `a` to
  `twistedTranslate` along `a.element`
  (`twistedLevelPresheaf_map_apply_coe`). The functor laws are
  `f (x * 1) = f x` and `f (x * (a.element * b.element)) =
  f (x * a.element * b.element)`.
- `levelPresheafTwistIso : levelPresheaf R ι ρ ≅ twistedLevelPresheaf R ι ρ`:
  the natural isomorphism with components `twistEquiv`, whose naturality is
  `twistEquiv_levelTransport`.

## Hecke operators under the twist

`G` is a topological group with `IsTopologicalGroup G`. For compact open
levels `K`, `L` and `g : G`, `heckeOperator R ι ρ K L g` of
`Langlands.Shimura.EquivariantFormsHecke` maps forms of level `L` to forms
of level `K` by `x ↦ ∑ ρ (k * g) (F (x * k * g))`, summed over Mathlib's
representatives `k = q.out` of the cosets `q` of `K ∩ g L g⁻¹`
(`CompactOpenLevel.heckeLevel K L g`) in `K`.

- `twistEquiv_heckeOperator`: for any `Fintype` instance on these cosets,
  `twistEquiv` of `heckeOperator R ι ρ K L g F` at `x` is
  `∑ q, (twistEquiv F) (x * q.out * g)`: under the twist the Hecke operator
  has the untwisted formula, since
  `ρ x (ρ (k * g) (F (x * k * g))) = ρ (x * k * g) (F (x * k * g))`.

## Functions on level spaces

For a type `X` with an action `MulAction Γ X`, Worker 57's
`LevelSpace (X := X) ι K` is the quotient of `X × G` by
`(x, g) ~ (γ • x, ι γ * g * k)` for `γ : Γ`, `k ∈ K`, and for a level arrow
`a : K ⟶ L`, `LevelSpace.translate a.element a.respects` is the map
`[(x, g)] ↦ [(x, g * a.element)]` from the level space of `K` to that of
`L`.

- `levelSpaceFunctions R ι X V : (CompactOpenLevel G)ᵒᵖ ⥤ ModuleCat.{max uG uX t} R`:
  a level `K` goes to the `R`-module of all functions
  `LevelSpace (X := X) ι K.subgroup → V` (pointwise operations), and an
  arrow `a : K ⟶ L` to pullback along `LevelSpace.translate`
  (`levelSpaceFunctions_map_apply`). The functor laws are Worker 57's
  `LevelSpace.translate_one` and `LevelSpace.translate_comp`.
  `levelSpaceFunctions_map_apply_tower` restates the maps as pullback along
  the continuous maps `(LevelSpace.tower).map a` of Worker 57's tower of
  level spaces (`TopologicalSpace X`, `ContinuousMul G`), whose underlying
  functions are `LevelSpace.translate`. No continuity is imposed on the
  functions.
- An instance: the restriction `ρ.comp f` of a trivial representation `ρ`
  (`Representation.IsTrivial`) along any group homomorphism `f` is trivial.
- `levelSpaceEquiv ι K ρ`, for a representation `ρ` of `K` with
  `ρ.IsTrivial`: the `R`-linear equivalence from `forms ι K ρ` to the
  functions `LevelSpace (X := Unit) ι K → V`. For trivial `ρ`, a form `f`
  satisfies `f (ι γ * g * k) = f g`, so it is constant on the classes of
  `((), g)`, and the equivalence sends `f` to the function
  `[((), g)] ↦ f g` (`levelSpaceEquiv_mk`); the inverse sends `φ` to
  `g ↦ φ [((), g)]` (`levelSpaceEquiv_symm_apply_coe`).
- `levelSpaceEquiv_levelTransport`: for a trivial representation `ρ` of
  `G`, an arrow `a : K ⟶ L` and a form `F` of level `L`, `levelSpaceEquiv`
  of `levelTransport R ι ρ a F` is `levelSpaceEquiv F` composed with
  `LevelSpace.translate a.element a.respects`, since `ρ a.element` is the
  identity.
- `levelPresheafTrivialIso : levelPresheaf R ι ρ ≅ levelSpaceFunctions R ι Unit V`,
  for a trivial representation `ρ` of `G`: the natural isomorphism with
  components `levelSpaceEquiv`, whose naturality is
  `levelSpaceEquiv_levelTransport`.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), §3, printed p.306 (one-based PDF page 8):
"Let `K ⊂ GJ(𝔸^f)` be an open compact subgroup,
`_K S(GJ) = GJ(ℚ)\GJ(𝔸)/GJ_∞ × K`." Printed p.307 (one-based PDF page 9),
read in the rendered scanned page: "For any `L`-algebra `L'`, we let (3.2)
`𝒜_f(GJ, ρ, K)(L') = {f : GJ(𝔸^f)/K → W(L') | f(γ·g) = ρ(γ)f(g),
g ∈ GJ(𝔸), γ ∈ GJ(ℚ)}`; If `L'` is an `L_ℓ` algebra, we define (3.3)
`𝒜_ℓ(GJ, ρ, K)(L') = {f : _{K^ℓ}S(GJ) → W(L'_ℓ) | f(gk) =
ρ(k_ℓ)^{-1} f(g), g ∈ GJ(𝔸), k ∈ K ∩ GJ_ℓ}`." Further: "Similarly, for any
`L_ℓ`-algebra `L'` we have an isomorphism (3.5)
`res_ℓ : 𝒜_ℓ(GJ, ρ, K)(L') ⥲ 𝒜_f(GJ, ρ, K)(L')`, given by
`f ↦ {g ↦ ρ(g_ℓ)^{-1} · f(g), g ∈ GJ(𝔸^f)}`. Letting `K` vary, it is clear
that these isomorphisms commute with the action of the prime-to-`ℓ` finite
adeles of `GJ`. When `ρ` is the trivial one-dimensional representation, we
write `𝒜_0(GJ, K)` in place of `𝒜_0(GJ, ρ, K)`, and likewise for the other
spaces defined above."

How the module relates to this passage (an explanation, not formalized):

- Take `G = GJ(𝔸^f)`, `ι` the diagonal inclusion of `GJ(ℚ)`, and `ρ` the
  representation of `GJ(𝔸^f)` on `W(L'_ℓ)` inflated along the projection to
  `GJ(ℚ_ℓ)`, so that `ρ g = ρ(g_ℓ)` and `ρ (ι γ) = ρ(γ)` for `γ ∈ GJ(ℚ)`.
  Then `twistedForms ι K ρ` has the functional equations of (3.2): `f` is a
  function on `GJ(𝔸^f)/K` with `f(γ·g) = ρ(γ) f(g)`. The forms of
  `Langlands.Shimura.EquivariantForms` for the restriction of `ρ` to `K`
  have those of (3.3) (see `Langlands/Shimura/EquivariantForms.md` for that
  specialization, there with `G = GJ(𝔸)`; on functions right invariant
  under `GJ_∞` the two choices of `G` agree via
  `GJ(𝔸) = GJ_∞ × GJ(𝔸^f)`, which is not formalized).
- `twistEquiv` is the isomorphism (3.5) with Harris's exponent reversed:
  its inverse `f ↦ (g ↦ ρ g⁻¹ (f g))` is Harris's printed formula
  `f ↦ {g ↦ ρ(g_ℓ)^{-1} · f(g)}`, and it is this formula that maps
  functions with the equations of (3.2) to functions with those of (3.3),
  while `twistEquiv`, with `ρ(g_ℓ)`, maps (3.3) to (3.2). With the
  functional equations as printed, Harris's formula applied to an element
  of (3.3) satisfies neither equation of (3.2) in general, so we read the
  printed exponent as a slip in the direction of the map. The modules are
  isomorphic in either direction, and nothing else depends on this
  reading.
- `levelPresheafTwistIso` is our generic counterpart of Harris's sentence
  that the isomorphisms (3.5) commute with the action of the prime-to-`ℓ`
  finite adeles as `K` varies: under the twist, `levelTransport` along any
  level arrow, including arrows whose element has an `ℓ`-component, is
  right translation of twisted forms. For a prime-to-`ℓ` element `g`,
  `ρ g` is the identity in the specialization above, so `levelTransport` is
  also right translation, and the naturality square is Harris's
  commutation. Harris does not write the action out; we take right
  translation along the transporter arrows of `CompactOpenLevel`.
- `twistEquiv_heckeOperator` is the formula of the Hecke operator of
  `Langlands.Shimura.EquivariantFormsHecke` on the side of (3.2). Hecke
  operators are not defined in Harris 1999; this lemma is ours.
- `levelSpaceEquiv` and `levelPresheafTrivialIso` treat Harris's trivial
  representation case: for trivial `ρ`, the spaces (3.2) and (3.3) both
  consist of the functions on `GJ(ℚ)\GJ(𝔸^f)/K`, which is the level space
  `LevelSpace (X := Unit) ι K`, the quotient of `Unit × GJ(𝔸^f)` by
  `GJ(ℚ)` and `K`. Harris writes `_K S(GJ) = GJ(ℚ)\GJ(𝔸)/GJ_∞ × K`; its
  identification with this level space uses `GJ(𝔸) = GJ_∞ × GJ(𝔸^f)` and
  is not formalized. Harris's functions are "taken to be continuous"
  (printed p.306); for open `K` every function on the discrete quotient
  `GJ(ℚ)\GJ(𝔸^f)/K` qualifies, and `levelSpaceFunctions` imposes no
  continuity in any case.
- `twistedForms`, `twistedTranslate`, `twistedLevelPresheaf`,
  `levelSpaceFunctions` and the triviality instance are internal
  constructions of standard objects (equivariant functions and functions on
  double cosets with right translation). All Lean statements and proofs are
  ours, derived from Mathlib and the published modules named above.

Worker 13 (first executor of task 23471a9e) reported no overlap with this
module.

## Scope

The module does not define Harris's groups, adelic points, `_K S(GJ)` as a
limit, `ℓ`-adic coefficient systems or continuity conditions, and it does
not construct the inflation of an algebraic representation from the
`ℓ`-component; the specialization above is an explanation. It does not
compare `levelSpaceFunctions` with sheaf cohomology of the level spaces or
with locally constant functions, and it constructs no cohomology. As in
`Langlands.Shimura.EquivariantFormsHecke`, the arrows of
`CompactOpenLevel G` are represented elements, and the presheaves are
functors on that category.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are Mathlib and the published modules named above, pinned to
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
