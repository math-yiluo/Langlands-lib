# Level maps and Hecke operators on equivariant functions

Author: Worker 61. Built on the published
`Langlands.Shimura.EquivariantForms` (Worker 61: `forms`,
`levelQuotientAction`) and Worker 57's published `Langlands.Shimura.Levels`
(`CompactOpenLevel`, its category of transporter arrows, `heckeLevel`,
`heckeRight`), and on Mathlib's subgroup quotients, indices and sums.

The module relates the modules `forms ι K ρ` of
`Langlands.Shimura.EquivariantForms` for different levels `K`: restriction to
a smaller level, the trace back up along a subgroup of finite index,
transport along a group element, the presheaf of forms on the category of
compact open levels, and the Hecke operator of a double coset. Everything is
generic in the groups, levels and coefficients; nothing is specialized to
Harris's groups.

## Conventions

`R` is a commutative ring, `Γ` and `G` are groups and `ι : Γ →* G` is a
group homomorphism. For a subgroup `K` of `G` and a representation `ρ` of `K`
on an `R`-module `V`, `forms ι K ρ` is the submodule of functions
`f : G → V` with `f (ι γ * g) = f g` and `f (g * k) = ρ k⁻¹ (f g)`.
Elements of subgroups are coerced to `G` silently below. For `hle : K' ≤ K`,
`ρ.comp (Subgroup.inclusion hle)` is the restriction of `ρ` to `K'`, and
`K ⧸ K'.subgroupOf K` is the set of left cosets `k K'` of `K'` in `K`.

## Restriction and trace

`hle : K' ≤ K` are subgroups of `G` and `ρ` is a representation of `K`.

- `restrict ι ρ hle`: the inclusion of `forms ι K ρ` into the forms of level
  `K'` for the restricted representation, keeping the underlying function
  (`restrict_apply_coe`).
- `translateTwist ι ρ hle k`, for `k : K`: the linear map sending a form `f`
  of level `K'` to the function `g ↦ ρ k (f (g * k))`
  (`translateTwist_apply`). `translateTwist_mul` shows that it does not
  change when `k` is replaced by `k * m` with `m ∈ K'`: by the `K'`-equation
  `ρ (k * m) (f (g * k * m)) = ρ (k * m) (ρ m⁻¹ (f (g * k))) = ρ k (f (g * k))`.
- `cosetTwist ι ρ hle q`, for a coset `q : K ⧸ K'.subgroupOf K`: the map
  `translateTwist ι ρ hle k` for any representative `k` of `q`
  (`cosetTwist_mk`). Each `cosetTwist q f` is left invariant under `ι Γ`
  (`cosetTwist_left`), and right translation by `k₀ : K` moves it to the
  coset `k₀ • q`: `cosetTwist q f (g * k₀) = ρ k₀⁻¹ (cosetTwist (k₀ • q) f g)`
  (`cosetTwist_right`).
- `trace ι ρ hle`, assuming `Finite (K ⧸ K'.subgroupOf K)`: the linear map
  from forms of level `K'` (restricted representation) to `forms ι K ρ`
  given by the sum of `cosetTwist q f` over all cosets `q`. The sum is a form
  of level `K`: left invariance holds termwise, and right translation by
  `k₀` permutes the terms by `q ↦ k₀ • q` and applies `ρ k₀⁻¹`. The finite
  set of cosets is enumerated by `Fintype.ofFinite`, and `trace_apply_coe`
  restates the formula `(trace f) g = ∑ q, cosetTwist q f g` for any
  `Fintype` instance on the cosets (all such instances are equal).
  `trace_apply_coe_out` writes it with Mathlib's chosen representatives
  `q.out`: `(trace f) g = ∑ q, ρ q.out (f (g * q.out))`.
- `trace_restrict`: `trace ι ρ hle (restrict ι ρ hle f)` is
  `(K'.subgroupOf K).index • f`, since each term
  `ρ k (f (g * k)) = ρ k (ρ k⁻¹ (f g))` equals `f g`.
- `restrict_trace`: if `K'.subgroupOf K` is normal in `K`, restricting
  `trace f` to level `K'` gives the sum of the translates of `f` under the
  representation `levelQuotientAction ι ρ hle` of `K ⧸ K'.subgroupOf K`
  from `Langlands.Shimura.EquivariantForms`, whose action on `f` is
  `g ↦ ρ k (f (g * k))` for a representative `k`.

## Transport

`ρ`, `σ` and `τ` are representations of subgroups `K`, `L` and `M` of `G` on
`V`, `W` and `U`.

- `transport ι ρ σ g hg φ hφ`, for `g : G` with `hg : g⁻¹ * k * g ∈ L` for
  all `k ∈ K`, and a linear map `φ : W →ₗ[R] V` with
  `hφ : φ (σ (g⁻¹ * k * g) w) = ρ k (φ w)` for all `k : K` and `w : W`: the
  linear map from `forms ι L σ` to `forms ι K ρ` sending `f` to
  `x ↦ φ (f (x * g))` (`transport_apply_coe`). Left invariance is unchanged,
  and for `k : K` one writes `x * k * g = x * g * (g⁻¹ * k * g)` and uses the
  `L`-equation of `f` at `g⁻¹ * k⁻¹ * g` followed by `hφ`.
- `transport_comp`: transport along `h` (from `M` to `L`, intertwiner `ψ`)
  followed by transport along `g` (from `L` to `K`, intertwiner `φ`) is
  transport along `g * h` with intertwiner `φ ∘ₗ ψ`. The conditions for the
  composite are separate hypotheses `hgh` and `hφψ`, so that the lemma
  applies to any proofs of them.
- `restrict_eq_transport`: for `K ≤ L`, restriction is transport along `1`
  with the identity map.

## The presheaf of forms on compact open levels

`G` is now a topological group (`TopologicalSpace G`; the presheaf needs no
continuity of the multiplication), `ρ : Representation R G V` is a
representation of all of `G` with `V : Type t`, and a compact open level
`K : CompactOpenLevel G` carries the representation `ρ` restricted to
`K.subgroup`. An arrow `a : K ⟶ L` of Worker 57's category of levels is a
group element `a.element` with `a.element⁻¹ * k * a.element ∈ L` for all
`k ∈ K` (`a.respects`); identities are `1` and the composite of `a` and `b`
has element `a.element * b.element`.

- `levelTransport R ι ρ a`: transport along `a.element` with intertwiner
  `ρ a.element`, from the forms of level `L` to the forms of level `K`:
  `f ↦ (x ↦ ρ a.element (f (x * a.element)))` (`levelTransport_apply_coe`).
  The intertwining condition is
  `ρ a.element (ρ (a.element⁻¹ * k * a.element) w) = ρ k (ρ a.element w)`.
- `levelPresheaf R ι ρ : (CompactOpenLevel G)ᵒᵖ ⥤ ModuleCat.{max uG t} R`:
  a level `K` goes to the forms of level `K.subgroup` for the restriction of
  `ρ`, an arrow to `levelTransport`
  (`levelPresheaf_map_apply_coe`). The identity law holds since `ρ 1` is the
  identity. For arrows `a : K ⟶ L` and `b : L ⟶ M`, applying
  `levelTransport` along `b` and then along `a` gives
  `x ↦ ρ a.element (ρ b.element (f (x * a.element * b.element)))`, which is
  `levelTransport` along the composite, with element
  `a.element * b.element`.

## Hecke operators

`G` is a topological group with `IsTopologicalGroup G`. For compact open
levels `K`, `L` and `g : G`, Worker 57's `CompactOpenLevel.heckeLevel K L g`
is the compact open level `K ∩ g L g⁻¹`, and
`CompactOpenLevel.heckeRight K L g` is its arrow to `L` with element `g`.

- An instance `Finite (K.subgroup ⧸ K'.subgroup.subgroupOf K.subgroup)` for
  compact open levels `K` and `K'`: `K ∩ K'` is an open subgroup of the
  compact group `K`, so it has finitely many cosets in `K` (Mathlib's
  `Subgroup.quotient_finite_of_isOpen`).
- `heckeLevel_le`: `K ∩ g L g⁻¹ ≤ K`. `heckeLevel_conj_mem`: for `k` in
  `K ∩ g L g⁻¹`, `g⁻¹ * k * g ∈ L` (the condition `respects` of
  `heckeRight`).
- `hecke ι K L g ρ σ φ hφ`, for representations `ρ` of `K` and `σ` of `L`
  and a linear map `φ : W →ₗ[R] V` intertwining `σ` conjugated by `g` with
  `ρ` on `K ∩ g L g⁻¹`: transport from `forms ι L σ` along `g` to the forms
  of level `K ∩ g L g⁻¹`, followed by the trace to `forms ι K ρ`.
  `hecke_apply_coe`: `(hecke f) x = ∑ q, ρ q.out (φ (f (x * q.out * g)))`,
  summed over the cosets `q` of `K ∩ g L g⁻¹` in `K`.
- `heckeOperator R ι ρ K L g`, for a representation `ρ` of `G`: `hecke` with
  the restrictions of `ρ` to `K` and `L` and the intertwiner `ρ g`, a linear
  map from the forms of level `L` to the forms of level `K`.
  `heckeOperator_apply_coe` gives the formula
  `([K g L] f) x = ∑ q, ρ (q.out * g) (f (x * q.out * g))`, and
  `heckeOperator_eq` (by definition) writes it as `levelTransport` along
  `heckeRight K L g` followed by `trace` along `heckeLevel_le K L g`, that
  is, pullback along the second leg of the Hecke correspondence of
  `Langlands.Shimura.Levels` and trace along the first.

For trivial `ρ` the formula is the classical
`([K g L] f) x = ∑_{h ∈ K g L / L} f (x * h)`: the map `k ↦ k * g * L`
identifies the cosets of `K ∩ g L g⁻¹` in `K` with the cosets of `L` in
`K g L`. This identification is an explanation and is not formalized.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), §3, printed p.307 (one-based PDF page 9),
read in the rendered scanned page: "(3.2) `𝒜_f(GJ, ρ, K)(L') = {f :
GJ(𝔸^f)/K → W(L') | f(γ·g) = ρ(γ)f(g), g ∈ GJ(𝔸), γ ∈ GJ(ℚ)}`" and
"(3.3) `𝒜_ℓ(GJ, ρ, K)(L') = {f : _{K^ℓ}S(GJ) → W(L'_ℓ) | f(gk) =
ρ(k_ℓ)^{-1} f(g), g ∈ GJ(𝔸), k ∈ K ∩ GJ_ℓ}`", followed by "(3.5)
`res_ℓ : 𝒜_ℓ(GJ, ρ, K)(L') ⥲ 𝒜_f(GJ, ρ, K)(L')`, given by
`f ↦ {g ↦ ρ(g_ℓ)^{-1} · f(g), g ∈ GJ(𝔸^f)}`. Letting `K` vary, it is clear
that these isomorphisms commute with the action of the prime-to-`ℓ` finite
adeles of `GJ`."

How the module relates to this passage (an explanation, not formalized):

- The specialization of `forms` to Harris's spaces (3.3), with `G = GJ(𝔸)`,
  `ι` the inclusion of `GJ(ℚ)` and `ρ` inflated from the `ℓ`-component, is
  explained in `Langlands/Shimura/EquivariantForms.md`. For such `ρ`, the
  element `ρ g` is the identity for every prime-to-`ℓ` finite adele `g`, so
  `levelTransport` along an arrow with element `g` is plain right
  translation `f ↦ (x ↦ f (x * g))` between levels. This is the action of
  the prime-to-`ℓ` finite adeles on the tower of spaces (3.3) as `K` varies
  to which Harris's sentence refers; Harris does not write the action out,
  and we take right translation.
- For a general `g` (including an `ℓ`-component), `levelTransport` twists
  by `ρ g`. This twist matches right translation under the comparison of
  (3.3) with (3.2): for `F` satisfying the equations of (3.3), the function
  `f(g) = ρ(g_ℓ) F(g)` is right invariant under `K` and satisfies
  `f(γ g) = ρ(γ) f(g)` as in (3.2), and the right translate `g ↦ f(g h)`
  corresponds to `g ↦ ρ(g_ℓ)^{-1} f(g h) = ρ(h_ℓ) F(g h)`, which is
  `levelTransport` along `h`. Harris's printed formula for `res_ℓ` uses
  `ρ(g_ℓ)^{-1}`; with the functional equations as printed, the map from
  (3.3) to (3.2) is the twist by `ρ(g_ℓ)`, and the printed formula gives the
  inverse map from (3.2) to (3.3). Nothing here depends on that direction.
  This computation, and any comparison with `𝒜_f`, is not formalized.
- `restrict`, `trace`, `transport`, `levelPresheaf`, `hecke` and
  `heckeOperator` are standard constructions on functions on double cosets
  (restriction and corestriction along finite-index subgroups, and the
  double-coset Hecke operator `[K g L]` written as pullback along one leg of
  the Hecke correspondence followed by the trace along the other). Harris
  1999 defines no Hecke operators on these spaces and no traces between
  levels: a search of the text layer of the scanned PDF finds "Hecke" only
  in "Hecke character" (one-based PDF pages 2 and 16). These definitions and
  all statements and proofs are ours, derived from Mathlib and the published
  modules named above. The
  Hecke operator uses the span `heckeLevel`/`heckeRight` of
  `Langlands.Shimura.Levels`, whose `heckeLeft` is the inclusion arrow
  along which the trace is taken.

Worker 13 (first executor of task 23471a9e) reported no overlap with this
module.

## Scope

The module does not define Harris's groups, adelic points, `_K S(GJ)`,
`ℓ`-adic coefficient systems or continuity conditions; it does not compare
the forms of different levels with Harris's `𝒜_f`, form a Hecke algebra or
prove relations between Hecke operators (such as composition of double
cosets), and it constructs no cohomology. The arrows of
`CompactOpenLevel G` are represented elements: distinct arrows between the
same levels may give different transports, and `levelPresheaf` is a functor
on that category, not on a category of levels with arrows taken modulo the
target level.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are Mathlib and the published modules named above, pinned to
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
