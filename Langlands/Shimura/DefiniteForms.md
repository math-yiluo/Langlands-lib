# Harris's spaces of automorphic forms on the similitude group of an algebra with involution

Author: Worker 61. Built on the published
`Langlands.Shimura.EquivariantForms` (Worker 61: `forms`),
`Langlands.Shimura.EquivariantFormsHecke` (Worker 61: `levelTransport`,
`levelPresheaf`, `heckeOperator`),
`Langlands.Shimura.EquivariantFormsTwist` (Worker 61: `twistedForms`,
`twistEquiv`, `twistEquiv_heckeOperator`), and on Worker 57's published
`Langlands.Shimura.Unitary.Adelic` (`Points`, `FiniteAdelicPoints`,
`finiteAdelicDiagonal`, `finiteLocalMap`, `diagonalPoints`),
`Langlands.Shimura.Coefficients.Algebraic` (`AlgebraicRepresentation`,
`rationalAction`, `finiteAdelicVia`, `finiteAdelicVia_diagonal`) and
`Langlands.Shimura.Levels` (`CompactOpenLevel`, `heckeLevel`).

The module specializes the generic equivariant forms of
`Langlands.Shimura.EquivariantForms` and `Langlands.Shimura.EquivariantFormsTwist`
to Worker 57's actual similitude group of an algebra with involution, its
finite adelic points and its algebraic coefficient representations. The
result is the spaces (3.2) and (3.3) of Harris 1999 and the isomorphism (3.5)
between them, as presheaves on compact open levels with Hecke operators. No
new groups, levels or coefficients are defined.

## Conventions

`A` is a `ℚ`-algebra (`[Ring A] [Algebra ℚ A]`) and
`σ : AlgebraInvolution ℚ A` is an involution. Worker 57's
`σ.similitudes` is its group of rational similitudes (Harris's `GJ(ℚ)`).
`σ.Points S` is the group of similitudes of `S ⊗[ℚ] A` for a commutative
`ℚ`-algebra `S`. `σ.FiniteAdelicPoints = σ.Points (FiniteAdeles ℚ)` is the
finite adelic group (Harris's `GJ(𝔸^f)`), with the topology Worker 57
transports from the finite adeles. `σ.finiteAdelicDiagonal` is the diagonal
embedding of the rational points into it. For a finite place `ℓ` of `ℚ`,
`σ.finiteLocalMap ℓ` (which needs `[Module.Finite ℚ A]`) is the continuous
homomorphism `g ↦ g_ℓ` to the points over the completion `ℚ_ℓ`.

`L` is a field with `[Algebra ℚ L]`, `W` is an `L`-vector space, and
`ρ : (σ.baseChange L).AlgebraicRepresentation W` is an algebraic
representation of the similitude group over `L`. In Worker 57's
functor-of-points form it is an action `ρ.act S` of the points over every
commutative `L`-algebra `S` in the universe of `L` on `S ⊗[L] W`, natural in
`S`. Its restriction to the rational points over `L` is
`ρ.rationalAction : (σ.baseChange L).similitudes →* (W ≃ₗ[L] W)`. For an
`L`-algebra `S`, we write `W(S)` for `S ⊗[L] W`. Elements of subgroups are
coerced silently below.

## The space (3.2)

`S` is a commutative ring with `[Algebra L S]`, in any universe.

- `rationalRep σ ρ S : Representation S σ.similitudes (S ⊗[L] W)`: the
  action `γ ↦ ρ(γ)` of the rational similitudes on `W(S)`. It is the scalar
  extension from `L` to `S` (`Module.End.baseChangeHom`) of
  `ρ.rationalAction` composed with the diagonal map
  `σ.diagonalPoints L : σ.similitudes →* σ.Points L`, where `σ.Points L` is
  by definition `(σ.baseChange L).similitudes` (`rationalRep_apply`).
- `finiteForms σ ρ S K`, for any subgroup `K` of `σ.FiniteAdelicPoints`:
  the `S`-submodule of functions `f : σ.FiniteAdelicPoints → S ⊗[L] W` with
  `f (finiteAdelicDiagonal γ * g) = rationalRep σ ρ S γ (f g)` for all
  rational `γ` and all `g`, and `f (g * k) = f g` for all `g` and `k ∈ K`
  (`mem_finiteForms`). Both conditions are linear in `f`. The generic
  `twistedForms` of `Langlands.Shimura.EquivariantFormsTwist` has the same
  shape, but its left equation evaluates a representation of the whole
  group at `finiteAdelicDiagonal γ`. Since `rationalRep` is a representation
  of the rational group only, the conditions are written out here; for
  `ellAdicRep` the two submodules coincide (`twistedForms_eq_finiteForms`
  below).
- `finiteTranslate σ ρ S g hg`, for subgroups `K`, `K'` and `g` with
  `hg : g⁻¹ * k * g ∈ K'` for all `k ∈ K`: the `S`-linear map
  `finiteForms σ ρ S K' → finiteForms σ ρ S K`, `f ↦ (x ↦ f (x * g))`
  (`finiteTranslate_apply_coe`). Left equivariance is unchanged, and right
  invariance follows from `x * k * g = x * g * (g⁻¹ * k * g)`.
- `finiteFormsPresheaf σ ρ S : (CompactOpenLevel σ.FiniteAdelicPoints)ᵒᵖ ⥤ ModuleCat S`:
  a compact open level `K` goes to `finiteForms σ ρ S K.subgroup`, and an
  arrow `a : K ⟶ K'` of Worker 57's category of levels (an element
  `a.element` with `a.element⁻¹ * k * a.element ∈ K'` for all `k ∈ K`) goes to
  `finiteTranslate` along `a.element`
  (`finiteFormsPresheaf_map_apply_coe`). The functor laws are
  `f (x * 1) = f x` and `f (x * (a * b)) = f (x * a * b)`.
- `finiteForms_isLocallyConstant`: if `K` is open and
  `f ∈ finiteForms σ ρ S K`, then `f` is locally constant, since it is
  constant on each open coset `x K` (the preimage of `K` under
  `y ↦ x⁻¹ * y`). Here `[Module.Finite ℚ A]` is assumed, because the proof
  uses continuity of multiplication, which comes from Worker 57's
  topological group instance on the adelic points (stated under that
  hypothesis).

## The space (3.3) and the isomorphism (3.5)

Now `[Module.Finite ℚ A]`, `ℓ : FinitePlace ℚ` is a finite place, and `S` is
a commutative ring in the universe of `L` with `[Algebra ℚ S]`,
`[Algebra L S]` and a `ℚ`-algebra map `φ : FiniteCompletion ℚ ℓ →ₐ[ℚ] S`.
Since a ring has at most one `ℚ`-algebra structure, the two structures are
compatible on `ℚ`, and these data amount to an algebra over
`L_ℓ = L ⊗_ℚ ℚ_ℓ` (an explanation; this equivalence is not formalized). The
universe restriction comes from `ρ.act`, which is given on algebras in the
universe of `L`.

- `ellAdicRep σ ρ ℓ φ : Representation S σ.FiniteAdelicPoints (S ⊗[L] W)`:
  the action `g ↦ ρ(g_ℓ)` through the `ℓ`-component. It is Worker 57's
  `ρ.finiteAdelicVia ℓ φ`, which sends `g` to `ρ.act S` of the image of
  `σ.finiteLocalMap ℓ g` under `φ` (`ellAdicRep_apply`).
- `ellAdicRep_diagonal`: on rational points the `ℓ`-adic action is the
  rational one, `ellAdicRep σ ρ ℓ φ (finiteAdelicDiagonal γ) = rationalRep σ ρ S γ`
  (Worker 57's `finiteAdelicVia_diagonal`).
- `ellAdicRep_eq_one`: an element `g` with `σ.finiteLocalMap ℓ g = 1` acts
  as the identity.
- `ellAdicForms σ ρ ℓ φ K` (an abbreviation): the generic
  `forms σ.finiteAdelicDiagonal K ((ellAdicRep σ ρ ℓ φ).comp K.subtype)`,
  that is, the functions `f : σ.FiniteAdelicPoints → S ⊗[L] W` with
  `f (finiteAdelicDiagonal γ * g) = f g` and
  `f (g * k) = ρ.finiteAdelicVia ℓ φ k⁻¹ (f g)` for `k ∈ K`
  (`mem_ellAdicForms`).
- `ellAdicForms_mul_of_local_eq_one`: if `f ∈ ellAdicForms σ ρ ℓ φ K` and
  `k ∈ K` has trivial `ℓ`-component, then `f (g * k) = f g`
  (`ellAdicRep_eq_one` applied to `k⁻¹`).
- `twistedForms_eq_finiteForms`: the generic
  `twistedForms σ.finiteAdelicDiagonal K (ellAdicRep σ ρ ℓ φ)` equals
  `finiteForms σ ρ S K`, because on rational points `ellAdicRep` is
  `rationalRep` (`ellAdicRep_diagonal`).
- `resEll σ ρ ℓ φ K : ellAdicForms σ ρ ℓ φ K ≃ₗ[S] finiteForms σ ρ S K`:
  the generic `twistEquiv` for `ellAdicRep`, followed by the identification
  `twistedForms_eq_finiteForms`. It sends `f` to `g ↦ ρ(g_ℓ) (f g)`
  (`resEll_apply_coe`), and its inverse sends `f` to
  `g ↦ ρ((g⁻¹)_ℓ) (f g) = ρ(g_ℓ)⁻¹ (f g)` (`resEll_symm_apply_coe`).
- `levelTransport_of_local_eq_one`: along a level arrow `a` whose element
  has trivial `ℓ`-component, the generic `levelTransport` of
  `Langlands.Shimura.EquivariantFormsHecke` (the map
  `f ↦ (x ↦ ρ(a_ℓ) (f (x * a)))`) is plain right translation
  `f ↦ (x ↦ f (x * a))`.
- `resEllIso σ ρ ℓ φ : levelPresheaf S σ.finiteAdelicDiagonal (ellAdicRep σ ρ ℓ φ) ≅ finiteFormsPresheaf σ ρ S`:
  the natural isomorphism with components `resEll` at all compact open
  levels (`resEllIso_hom_app_apply_coe`). Its naturality is the pointwise
  identity `ρ(x_ℓ) (ρ(a_ℓ) (f (x * a))) = ρ((x * a)_ℓ) (f (x * a))`, by
  multiplicativity of `ρ.finiteAdelicVia ℓ φ`.
- `resEll_heckeOperator`: for compact open levels `K`, `K'`, an element `g`
  and any `Fintype` instance on the cosets of `K ∩ g K' g⁻¹`
  (`CompactOpenLevel.heckeLevel K K' g`) in `K`, `resEll` of the generic
  `heckeOperator S σ.finiteAdelicDiagonal (ellAdicRep σ ρ ℓ φ) K K' g f` at
  `x` is `∑ q, (resEll f) (x * q.out * g)`. So under `res_ℓ` the Hecke
  operator has the untwisted formula on the side of (3.2). This is the
  generic `twistEquiv_heckeOperator`.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), §3 "The totally definite case". The
passages below were read in the rendered scanned pages.

Printed p.306 (one-based PDF page 8): "Let `K ⊂ GJ(𝔸^f)` be an open
compact subgroup, `_K S(GJ) = GJ(ℚ)\GJ(𝔸)/GJ_∞ × K`. More generally, if
`U ⊂ GJ(𝔸^f)` is any closed subgroup, we let
`_U S(GJ) = lim_{K ⊃ U} _K S(GJ)`, the limit over open compact subgroups
`K` containing `U`. Let `(ρ, W)` denote a finite-dimensional algebraic
representation of `GJ`, rational over the number field `L = L(ρ)`. For any
place `v` of `ℚ` we use the same letter `ρ` to designate the representation
of `GJ_v` on `W(L_v)`, where we write `L_v = L ⊗_ℚ ℚ_v`. We define certain
spaces of functions on `GJ(𝔸)`. In what follows, `K` is as above, `ℓ` is a
finite prime in `ℚ`, `K^ℓ = K ∩ GJ^ℓ`, and all functions are taken to be
continuous."

Printed p.307 (one-based PDF page 9): "For any `L`-algebra `L'`, we let
(3.2) `𝒜_f(GJ, ρ, K)(L') = {f : GJ(𝔸^f)/K → W(L') | f(γ·g) = ρ(γ)f(g),
g ∈ GJ(𝔸), γ ∈ GJ(ℚ)}`; If `L'` is an `L_ℓ` algebra, we define (3.3)
`𝒜_ℓ(GJ, ρ, K)(L') = {f : _{K^ℓ}S(GJ) → W(L'_ℓ) | f(gk) =
ρ(k_ℓ)^{-1} f(g), g ∈ GJ(𝔸), k ∈ K ∩ GJ_ℓ}`. Here the standing continuity
hypothesis needs to be specified. We assume `f ∈ 𝒜_ℓ(GJ, ρ, K)(L')` to be
locally constant on `GJ(𝔸^{f,ℓ})`; continuity of `f` in `G_ℓ` is guaranteed
by the functional equation." Further: "Similarly, for any `L_ℓ`-algebra
`L'` we have an isomorphism (3.5)
`res_ℓ : 𝒜_ℓ(GJ, ρ, K)(L') ⥲ 𝒜_f(GJ, ρ, K)(L')`, given by
`f ↦ {g ↦ ρ(g_ℓ)^{-1} · f(g), g ∈ GJ(𝔸^f)}`. Letting `K` vary, it is clear
that these isomorphisms commute with the action of the prime-to-`ℓ` finite
adeles of `GJ`."

How the module relates to this passage (an explanation, not formalized):

- Groups. Harris's `GJ = GU(𝒥, *)` is the similitude group of a central
  simple algebra `𝒥` with an involution of the second kind (§1, printed
  p.301, one-based PDF page 3), and §3 is titled "The totally definite
  case". We take Worker 57's similitude
  group of an arbitrary involution `σ` of a `ℚ`-algebra, finite-dimensional
  from (3.3) on. Definiteness is used by Harris for the archimedean space
  (3.1) and for the finiteness of `_K S(GJ)` (our reading). None of the
  definitions or lemmas here needs it. Harris's functions on `GJ(𝔸)` right invariant
  under `GJ_∞` are functions on `GJ(𝔸^f)` via `GJ(𝔸) = GJ_∞ × GJ(𝔸^f)`, and
  we work on `σ.FiniteAdelicPoints` directly; this decomposition is not
  formalized.
- Coefficients. Harris's `L` is the number field `L(ρ)`; we allow any field
  `L` with `[Algebra ℚ L]`. Harris's `W(L')` is `L' ⊗_L W`, and his `ρ(γ)` on
  it is `rationalRep`. For (3.3), Harris's `ρ` on `W(L_ℓ)` (and on `W(L')`
  for an `L_ℓ`-algebra `L'`) evaluated at `k_ℓ` is Worker 57's
  `ρ.finiteAdelicVia ℓ φ k`. For `S = L ⊗_ℚ ℚ_ℓ` and `φ` the inclusion of
  `ℚ_ℓ`, this is Worker 57's `ρ.harrisLocal ℓ` evaluated at the
  `ℓ`-component. We read Harris's printed target `W(L'_ℓ)` in (3.3) as
  `W(L')`, since `L'` is already an `L_ℓ`-algebra.
- (3.2). `finiteForms` has exactly the functional equations of (3.2): `f` is
  right `K`-invariant (a function on `GJ(𝔸^f)/K`) and `f(γ·g) = ρ(γ) f(g)`.
  Harris's functions are continuous. For open `K`, every element of
  `finiteForms` is locally constant (`finiteForms_isLocallyConstant`), hence
  continuous for any topology on `W(L')`, so imposing no continuity loses
  nothing.
- (3.3). Harris's functions live on `_{K^ℓ}S(GJ)`. They are left invariant
  under `GJ(ℚ)` and right invariant under the prime-to-`ℓ` part `K^ℓ`, and
  satisfy `f(gk) = ρ(k_ℓ)^{-1} f(g)` for `k ∈ K ∩ GJ_ℓ`. Directly after (3.5)
  Harris assumes `K = K^ℓ × K_ℓ`. For such `K`, our single condition
  `f (g * k) = ρ(k_ℓ)⁻¹ (f g)` for all `k ∈ K` is equivalent to his pair of
  conditions, since `ρ(k_ℓ) = 1` for `k ∈ K^ℓ`
  (`ellAdicForms_mul_of_local_eq_one`) and every `k ∈ K` is such a product.
  For general `K` our condition is the natural extension. The product
  decomposition of `K` is not formalized. As for continuity, for open `K^ℓ`
  right `K^ℓ`-invariance already makes `f` locally constant in the
  prime-to-`ℓ` variable. Continuity in `GJ_ℓ` is the statement Harris says
  follows from the functional equation; `W(S)` carries no topology here,
  and we impose no condition.
- (3.5). `resEll` is Harris's `res_ℓ`, with the printed exponent reversed,
  as explained in `Langlands/Shimura/EquivariantFormsTwist.md` for the
  generic `twistEquiv`. Harris's printed formula
  `f ↦ {g ↦ ρ(g_ℓ)^{-1} · f(g)}` is our inverse map
  (`resEll_symm_apply_coe`). It maps functions with the equations of (3.2) to
  functions with those of (3.3), while `resEll`, with `ρ(g_ℓ)`, maps (3.3) to
  (3.2). As printed, Harris's formula applied to an element of (3.3) does
  not satisfy the equations of (3.2) in general, so we read the exponent as
  a slip in the direction of the map. The spaces are isomorphic either way.
- "Letting `K` vary, … commute with the action of the prime-to-`ℓ` finite
  adeles." `resEllIso` makes `res_ℓ` natural along all arrows of
  `CompactOpenLevel`, for right translation on (3.2) and the transport
  `f ↦ (x ↦ ρ(a_ℓ) (f (x * a)))` on (3.3).
  `levelTransport_of_local_eq_one` shows that this transport is plain right
  translation for prime-to-`ℓ` elements `a`, so the naturality square is
  Harris's commutation with the prime-to-`ℓ` adelic action. Harris does not
  write the action out; we take right translation along the transporter
  arrows of `CompactOpenLevel`.
- `resEll_heckeOperator` is ours. Hecke operators are not defined in Harris
  1999.
- `rationalRep`, `finiteForms`, `finiteTranslate`, `finiteFormsPresheaf`,
  `ellAdicRep`, `ellAdicForms` and `resEll` are internal specializations of
  the published generic constructions named above to Worker 57's groups and
  coefficients. All Lean statements and proofs are ours, derived from
  Mathlib and the published modules named above.

## Scope

The module covers (3.2), (3.3) and (3.5) only. It does not define the
archimedean space (3.1) or `res`, does not prove Harris's base change
isomorphism (3.4) `𝒜_f(L') = 𝒜_f(L) ⊗_L L'` (which needs finiteness of the
double quotients), and does not treat (3.6) onwards (lattices, `ℓ`-adic
coefficient modules, (3.8)). It does not construct `_K S(GJ)` as a space or
limit, decompose levels as `K^ℓ × K_ℓ`, or impose continuity conditions. The
arrows of `CompactOpenLevel` are represented elements, and the presheaves are
functors on that category.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are Mathlib and the published modules named above, pinned to
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
