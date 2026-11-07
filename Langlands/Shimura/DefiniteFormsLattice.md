# Lattice-valued forms on definite similitude groups

Author: Worker 61. Built on the published
`Langlands.Shimura.DefiniteFormsDoubleCoset` (Worker 61: `localLevel`,
`localLevelMap`, `ellModuleForms`, `localRep`),
`Langlands.Shimura.DefiniteForms` (Worker 61: `ellAdicForms`),
`Langlands.Shimura.EquivariantFormsDoubleCoset` (Worker 61:
`DoubleCosets`, `doubleCosetStabilizer`, `apply_mem_invariants`,
`doubleCosetEquiv`, `doubleCosetEquiv_apply_coe`) and
`Langlands.Shimura.EquivariantForms` (Worker 61: `forms`), and on Worker
57's similitude groups (`AlgebraInvolution.FiniteAdelicPoints`,
`finiteAdelicDiagonal`) and algebraic coefficients
(`AlgebraicRepresentation`). From Mathlib it uses localizations of rings
and modules (`IsLocalization`, `IsLocalization.mem_span_iff`,
`IsLocalizedModule`, `IsLocalizedModule.exist_integer_multiples_of_finite`,
`IsLocalizedModule.isBaseChange`), base change (`IsBaseChange.equiv`,
`IsBaseChange.equiv_tmul`), tensor products, finitely generated submodules
(`Submodule.FG`), spans (`Submodule.span`), restriction of linear maps
(`LinearMap.restrict`) and representations (`Representation.comp`,
`Representation.invariants`, `Representation.trivial`).

The module proves Harris's comparison between forms with values in a
`K_ℓ`-stable lattice and forms with values in `L_ℓ`-vector spaces:
`𝒜_ℓ(GJ, 𝓛_W, K) ⊗_𝒪 L_ℓ ≅ 𝒜_ℓ(GJ, ρ, K)(L_ℓ)`. It does so for an
arbitrary localization `S` of a commutative ring `O` in place of
`L_ℓ ⊃ 𝒪`, assuming finitely many double cosets
`GJ(ℚ) \ GJ(𝔸^f) / K`. A first, generic section shows that forming forms
commutes with localization when there are finitely many double cosets.

## Conventions

As in the published `DefiniteFormsDoubleCoset.md`:
`σ : AlgebraInvolution ℚ A` is an involution of a finite-dimensional
`ℚ`-algebra `A`, and `σ.FiniteAdelicPoints` is the group of finite adelic
points of its similitude group (Harris's `GJ(𝔸^f)`), with the rational
points embedded by `σ.finiteAdelicDiagonal`. `ℓ` is a finite place of `ℚ`,
`K` is a subgroup of `σ.FiniteAdelicPoints`, `localLevel σ ℓ K` (Harris's
`K_ℓ`) is the image of `K` under the `ℓ`-component map, and
`localLevelMap σ ℓ K : K →* localLevel σ ℓ K` is `k ↦ k_ℓ`. Generically,
`ι : Γ →* G` is a group homomorphism and `K` a subgroup of `G`;
`forms ι K ρ` consists of the functions `f : G → V` with
`f (ι γ * g) = f g` and `f (g * k) = ρ k⁻¹ (f g)`; `DoubleCosets ι K` is
the double coset space `ι(Γ) \ G / K`, `x.out` is Mathlib's chosen
representative of a class `x`, and `doubleCosetEquiv` is the published
restriction of forms to these representatives. For a representation `ρ'`
of `localLevel σ ℓ K`, `ellModuleForms σ ℓ K ρ'` is
`forms σ.finiteAdelicDiagonal K (ρ'.comp (localLevelMap σ ℓ K))`, Harris's
(3.7). `ρ : (σ.baseChange L).AlgebraicRepresentation W` is an algebraic
representation on an `L`-vector space `W`, `S` is a commutative `L`-algebra
with a `ℚ`-algebra map `φ : ℚ_ℓ → S`, `W(S)` is `S ⊗[L] W`,
`localRep σ ℓ ρ φ K` is the action `k_ℓ ↦ ρ(k_ℓ)` of `K_ℓ` on `W(S)`, and
`ellAdicForms σ ρ ℓ φ K` is Harris's `𝒜_ℓ(GJ, ρ, K)(S)` (3.3); it is by
definition `ellModuleForms σ ℓ K (localRep σ ℓ ρ φ K)` (published
`ellAdicForms_eq_ellModuleForms`). Elements of subgroups and submodules are
coerced silently below.

## Generic section: forms and localization

Namespace `Langlands.Shimura.EquivariantForms`. Here `O` and `S` are
commutative rings, `S` an `O`-algebra which is the localization of `O` at a
submonoid `M` (`[IsLocalization M S]`), `W` an `S`-module (with the induced
`O`-module structure, `[IsScalarTower O S W]`) with a representation `ρ` of
`K` over `S`, `V` an `O`-module with a representation `ρL` of `K` over `O`,
and `j : V →ₗ[O] W` with `j (ρL k v) = ρ k (j v)` (`hj`).

- `scalarFormsMap ι K ρ ρL j hj : forms ι K ρL →ₗ[O] forms ι K ρ`, the
  map `f ↦ j ∘ f` (`scalarFormsMap_apply_coe`, true by definition). The
  functional equations are preserved since `j` is linear and
  `K`-equivariant.
- `isLocalizedModule_scalarFormsMap`: if `ι(Γ) \ G / K` is finite
  (`[Finite (DoubleCosets ι K)]`), `j` is a localization at `M`
  (`[IsLocalizedModule M j]`) and `j` is injective, then
  `scalarFormsMap ι K ρ ρL j hj` is a localization at `M`
  (`IsLocalizedModule M _`). Proof: elements of `M` act invertibly on the
  `S`-module `forms ι K ρ` since they map to units of `S`. Given a form
  `F` for `ρ`, its finitely many values `F x.out` at the representatives
  of the double cosets have a common denominator: there is `s ∈ M` with
  `s • F x.out = j (v x)` for some `v x ∈ V` (Mathlib's
  `IsLocalizedModule.exist_integer_multiples_of_finite`). Since `F x.out`
  is invariant under the stabilizer `doubleCosetStabilizer ι K x.out`
  (published `apply_mem_invariants`) and `j` is injective and equivariant,
  so is `v x`; hence `v` is a family of invariant vectors and, by the
  published `doubleCosetEquiv` for `ρL`, the restriction of a form `f` for
  `ρL`. Then `j ∘ f` and `s • F` agree at every representative, so they are
  equal by the published `doubleCosetEquiv` for `ρ`. Finally, `j ∘ f₁ =
  j ∘ f₂` forces `f₁ = f₂` as `j` is injective.
- `formsBaseChangeEquiv M ι K ρ ρL j hj hinj :
  S ⊗[O] forms ι K ρL ≃ₗ[S] forms ι K ρ` under the same hypotheses: the
  equivalence of Mathlib's `IsBaseChange.equiv` for the base change
  property `IsLocalizedModule.isBaseChange` of the localization
  `scalarFormsMap`. `formsBaseChangeEquiv_tmul`: it sends `s ⊗ f` to
  `g ↦ s • j (f g)`.

## Harris's setting

Namespace `Langlands.Shimura.DefiniteForms`, with `ρ`, `S`, `φ` and `K` as
in the conventions and a commutative ring `O` with `[Algebra O S]`.

- `IsStableLattice σ ℓ ρ φ K 𝓛` (a structure in `Prop`) for an
  `O`-submodule `𝓛` of `W(S) = S ⊗[L] W`: `𝓛` is finitely generated over
  `O` (`fg`), spans `W(S)` over `S` (`span_eq_top`) and is stable under
  `localRep σ ℓ ρ φ K k` for every `k ∈ K_ℓ` (`mem`). This is Harris's
  "`K_ℓ`-stable `𝒪`-lattice `𝓛_W`".
- `latticeRep h : Representation O (localLevel σ ℓ K) 𝓛` for
  `h : IsStableLattice σ ℓ ρ φ K 𝓛`: the restriction of `localRep` to `𝓛`
  (`latticeRep_apply_coe`, true by definition). Thus
  `ellModuleForms σ ℓ K (latticeRep h)` is Harris's `𝒜_ℓ(GJ, 𝓛_W, K)`
  (3.7).
- From here on `S` is the localization of `O` at a submonoid `M`
  (`[IsLocalization M S]`). `IsStableLattice.isLocalizedModule M h`: the
  inclusion `𝓛.subtype : 𝓛 → W(S)` is a localization at `M`. Proof:
  elements of `M` act invertibly on `W(S)`; every `x ∈ W(S)` lies in the
  `S`-span of `𝓛`, hence (Mathlib's `IsLocalization.mem_span_iff`)
  `x = (1/z) • y` with `y` in the `O`-span of `𝓛`, which is `𝓛`, and
  `z ∈ M`; the inclusion is injective. Only `span_eq_top` is used; the
  finiteness `fg` is part of the notion of a lattice but not needed here.
- With finitely many double cosets
  (`[Finite (DoubleCosets σ.finiteAdelicDiagonal K)]`):
  `latticeFormsEquiv M h :
  S ⊗[O] ellModuleForms σ ℓ K (latticeRep h) ≃ₗ[S] ellAdicForms σ ρ ℓ φ K`,
  the generic `formsBaseChangeEquiv` for `j = 𝓛.subtype` and the
  representations `latticeRep h` and `localRep σ ℓ ρ φ K` composed with
  `localLevelMap σ ℓ K`. This is Harris's isomorphism
  `𝒜_ℓ(GJ, 𝓛_W, K) ⊗_𝒪 L_ℓ ≅ 𝒜_ℓ(GJ, ρ, K)(L_ℓ)`.
  `latticeFormsEquiv_tmul`: it sends `s ⊗ f` to `g ↦ s • f g`.
- `trivialLatticeFormsEquiv σ ℓ K M hinj`: for `S` the localization of `O`
  at `M`, the algebra map `O → S` injective (`hinj`) and finitely many
  double cosets, an `S`-linear equivalence from
  `S ⊗[O] ellModuleForms σ ℓ K (Representation.trivial O (localLevel σ ℓ K) O)`
  to `ellModuleForms σ ℓ K (Representation.trivial S (localLevel σ ℓ K) S)`:
  the generic `formsBaseChangeEquiv` for `j = Algebra.linearMap O S`, which
  is a localization at `M` since `S` is. This is Harris's trivial case
  `𝒜_ℓ(GJ, 𝒪, K) ⊗_𝒪 L_ℓ ≅ 𝒜_ℓ(GJ, K)(L_ℓ)`.
  `trivialLatticeFormsEquiv_tmul`: it sends `s ⊗ f` to
  `g ↦ s * algebraMap O S (f g)`.

## Provenance and interpretation

Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39-2 (1999), §3 "The totally definite case". Worker 61
read the rendered scanned pages. Printed p.307 (one-based PDF page 9), after
(3.6): "Let `𝒪` denote the ring of integers of `L_ℓ`, and let `𝓛_W` be a
`K_ℓ`-stable `𝒪`-lattice in `W(L)`. Then we can define". Printed p.308
(one-based PDF page 10): "(3.7) `𝒜_ℓ(GJ, 𝓛_W, K) = {f : _{K^ℓ}S(GJ) → 𝓛_W |
f(gk) = ρ(k_ℓ)^{-1} f(g), g ∈ GJ(𝔸), k ∈ K ∩ G_ℓ}`, with the continuity
hypothesis as above. Then there is a natural isomorphism
`𝒜_ℓ(GJ, 𝓛w, K) ⊗_𝒪 L_ℓ ≅ 𝒜_ℓ(GJ, ρ, K)(L_ℓ)`. When `ρ` is trivial, we take
the lattice `𝒪 ⊂ L_ℓ` and write `𝒜_ℓ(GJ, 𝒪, K)`." Further, (3.9):
"`GJ(ℚ)\GJ(𝔸)/K_∞ · K = ⋃_{j=1}^N GJ(ℚ) · K_∞ · K^ℓ γ_j K_ℓ`". The readings
of (3.3) and (3.7) and of `K_ℓ` are those of the published
`DefiniteForms.md` and `DefiniteFormsDoubleCoset.md`.

How the module relates to Harris (an explanation, not formalized):

- Rings. Harris's `L_ℓ` and its ring of integers `𝒪` become a commutative
  ring `O` and its localization `S` at a submonoid `M`. For Harris's rings
  `L_ℓ` is the localization of `𝒪` at the powers of `ℓ` (for `L_ℓ` a finite
  extension of `ℚ_ℓ` or a finite product of such), so his setting is the
  case `O = 𝒪`, `S = L_ℓ`, `M = {ℓ^n}`; this identification is not
  formalized. As in the published (3.3), `S` is an `L`-algebra with
  `φ : ℚ_ℓ → S`; nothing requires `S` to be complete or `φ` to be
  compatible with `O`.
- The lattice. Harris writes "`𝒪`-lattice in `W(L)`". An `𝒪`-lattice lives
  in an `L_ℓ`-vector space, `K_ℓ` acts on `W(L_ℓ)` and not on `W(L)`, and
  the isomorphism compares with `W(L_ℓ)`-valued forms, so we read `W(L_ℓ)`,
  that is `W(S) = S ⊗[L] W`. Harris does not define "lattice"; we take a
  finitely generated `O`-submodule spanning `W(S)` over `S`. Over a
  discrete valuation ring `𝒪` such a submodule is free with an `𝒪`-basis
  that is an `L_ℓ`-basis of `W(L_ℓ)`, the usual notion; this is not
  formalized. `K_ℓ`-stability is stability under `ρ(k_ℓ)` for
  `k_ℓ ∈ K_ℓ`, and the action on `𝓛_W` is the restriction of `ρ`.
- The isomorphism. Harris does not write out his "natural isomorphism";
  we take `s ⊗ f ↦ s • f`, the evident map, and write the base change as
  `S ⊗[O] _` (Mathlib's convention) rather than `_ ⊗_𝒪 L_ℓ`. Naturality is
  not formalized.
- Finiteness. Harris writes the double coset space as a union of `N`
  double cosets in (3.9); for his definite group and open compact `K` this
  finiteness is a theorem, not proved here. We assume
  `[Finite (DoubleCosets σ.finiteAdelicDiagonal K)]` explicitly; the proof
  uses it to find a common denominator for the values of a form at the
  representatives.
- Continuity. Harris's continuity hypothesis is not imposed, as in the
  published (3.3) and (3.7).
- Trivial case. Harris's `𝒜_ℓ(GJ, 𝒪, K)` is (3.7) for the lattice `𝒪` with
  trivial action, `ellModuleForms` for the trivial representation of
  `K_ℓ` on `O`; by Harris's convention for trivial `ρ`, the right-hand side
  `𝒜_ℓ(GJ, K)(L_ℓ)` consists of the `L_ℓ`-valued forms with trivial
  action, which we write as `ellModuleForms` for the trivial representation
  on `S` (rather than as `ellAdicForms` for a trivial algebraic
  representation). The injectivity of `O → S` (true for `𝒪 ⊂ L_ℓ`) is an
  explicit hypothesis.
- Proof route. Harris gives no proof. Ours reduces to the published
  restriction to double coset representatives (`doubleCosetEquiv`) and
  Mathlib's characterization of base change along a localization.
- `scalarFormsMap`, `isLocalizedModule_scalarFormsMap`,
  `formsBaseChangeEquiv`, `latticeRep` and
  `IsStableLattice.isLocalizedModule` are internal constructions not
  printed in Harris 1999. All definitions, statements and proofs are ours,
  derived from Mathlib and the published modules named above.

## Scope

The module inherits the scope of the published `DefiniteFormsDoubleCoset`:
levels are not decomposed as products `K^ℓ × K_ℓ`, `K_ℓ` is the image of
`K` in the `ℓ`-adic points, and there are no openness, compactness or
continuity conditions. It does not prove the finiteness of the double coset
space, does not construct lattices, does not compare forms for different
lattices, does not treat reduction modulo `ℓ^m` or limits in `m`, and
constructs no cohomology.

Source registration: Harris 1999,
`harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`, SHA-256
`525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.

Dependencies are Mathlib and the published modules named above, pinned to
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
