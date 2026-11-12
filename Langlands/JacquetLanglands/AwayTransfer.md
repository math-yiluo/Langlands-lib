# Transfer away from a distinguished factor

This pair defines the representation-theoretic relation behind Harris's
transfer `JL(π_f)`: two representations of two groups agree away from one
distinguished local factor, and their constituents at that factor are related
by a given local relation. The module is generic. It knows nothing about
Harris's groups `GJ`, `GG` or about the Jacquet–Langlands correspondence; the
Harris specialization supplies the splittings and the local relation in a
separate module. Entry declaration: `Langlands.JacquetLanglands.IsAwayTransfer`.

## Definitions

Throughout, `G, G', L, L', H, H'` are groups with topologies. The topologies
enter only through the splittings, which are continuous group isomorphisms
(Mathlib's `ContinuousMulEquiv`, notation `≃ₜ*`). Representations are Mathlib
`Representation ℂ _ _` on complex vector spaces, with no topology on the spaces
and no smoothness, admissibility or irreducibility imposed here; a consumer
adds those conditions explicitly.

- `splitTensor Φ π σ`, for `Φ : G ≃ₜ* L × H` and representations `π` of `L` on
  `X` and `σ` of `H` on `Y`, is the representation of `G` on `X ⊗[ℂ] Y`

      g ↦ π((Φ g).1) ⊗ σ((Φ g).2),

  that is, the external tensor product `π ⊠ σ` of `L × H` pulled back along `Φ`.
  The external tensor product is built exactly as in the Library's
  `Langlands.FlathTwoFactorStatement`:
  `Representation.tprod (π.comp (MonoidHom.fst L H)) (σ.comp (MonoidHom.snd L H))`.
  The pullback is composition with the underlying group homomorphism of `Φ`.
  `splitTensor_apply_tmul` records the action on pure tensors (proved by `rfl`).

- `IsAwayTransfer Φ Φ' θ R ρ ρ'` takes splittings `Φ : G ≃ₜ* L × H`,
  `Φ' : G' ≃ₜ* L' × H'`, an identification `θ : H ≃ₜ* H'` of the complements,
  a local relation

      R : ∀ X X' : ModuleCat.{u} ℂ, Representation ℂ L X → Representation ℂ L' X' → Prop,

  and representations `ρ` of `G` on `V` and `ρ'` of `G'` on `V'`, where `V` and
  `V'` are complex vector spaces in the universe `u`. It holds when there exist
  complex vector spaces `X, X', Y` in the universe `u` (packaged as objects of
  `ModuleCat.{u} ℂ`), representations `π` of `L` on `X`, `π'` of `L'` on `X'`
  and `σ` of `H` on `Y` with

  1. `R X X' π π'`;
  2. an equivariant linear isomorphism `ρ ≅ splitTensor Φ π σ`
     (Mathlib's `Representation.Equiv`); and
  3. an equivariant linear isomorphism
     `ρ' ≅ splitTensor Φ' π' (σ ∘ θ⁻¹)`.

  Thus `ρ` and `ρ'` have the same complement constituent `σ`, read on `H'`
  through `θ`, and distinguished constituents related by `R`. The
  isomorphisms are genuine data inside `Nonempty`; no equality of carriers is
  required.

The universe of the constituents equals the universe of `ρ` and `ρ'`. This
matches the Library's Flath existence clause
(`AdmissibleProductFactorizationStatement`), which produces the two factors of
an admissible irreducible representation of a product in `ModuleCat.{uV} ℂ` for
the universe `uV` of the given space. So, whenever that statement is available,
the factors it produces are admissible witnesses for `IsAwayTransfer`.

## Lemmas

- `isAwayTransfer_splitTensor` (nonvacuity): for every `π`, `π'`, `σ` with
  `R X X' π π'`, the pair `splitTensor Φ π σ` and
  `splitTensor Φ' π' (σ ∘ θ⁻¹)` is related, witnessed by identity
  isomorphisms. Hence the relation is satisfiable exactly when `R` is.
- `IsAwayTransfer.of_equiv_left`, `IsAwayTransfer.of_equiv_right`: the relation
  depends only on the isomorphism classes of `ρ` and `ρ'` (the carriers of the
  two isomorphic representations may differ).
- `IsAwayTransfer.mono`: the relation is monotone in `R`.

All proofs are term-level packing and unpacking of the existential.

## Source and provenance

The definition is a derived formalization device, not a definition printed in
a source. It formalizes the transfer condition of

M. Harris, *Galois properties of cohomological automorphic forms on GL(n)*,
J. Math. Kyoto Univ. 39 (1999), §5, printed p.312 (one-based PDF page 14);
literature ID `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`:

> Let π be a representation of GJ, and let π_v be its constituent at the chosen
> place v, as in [H1, H2]; π_v is a representation of GL(n, 𝒦_v). Suppose π_v
> is supercuspidal. Let JL(π_f) be the corresponding irreducible admissible
> representation of GG(A_f); the local constituents of JL(π_f) and π_f are the
> same except at v, where they correspond by the local Jacquet-Langlands
> correspondence [DKV, R], also denoted JL(•).

Harris's condition is placewise: the local constituents agree at every finite
place other than `v`. The definition here instead groups all those places into
one complement `H` and asks for a common constituent of that complement. In
Harris's setting, (4.2) on printed p.309 identifies `GJ_p` with
`Π_j (𝒟_{v^(j)})ˣ × ℚ_pˣ`, the factor at `v = v^(1)` being `GL(n, 𝒦_v)`; the
complement is then `Π_{j>1} (𝒟_{v^(j)})ˣ × ℚ_pˣ × GJ(A_f^p)`. The two are equivalent for
irreducible admissible representations, by the following standard facts; they
are stated here to explain the choice and are not used or asserted by this
module:

- Flath's two-factor theorem (Library `FlathTwoFactorStatement`): an
  irreducible admissible representation of `L × H` is `π ⊠ σ` with `π`, `σ`
  irreducible admissible, unique up to isomorphism of each factor. So
  "constituent at the distinguished factor" and "complement constituent" are
  well defined up to isomorphism, and condition 2 or 3 above pins them down.
- Flath's restricted tensor product theorem for the complement: the
  complement constituent is determined up to isomorphism by its local
  constituents at the places it contains. Then "same complement constituent"
  is "same local constituents at every place other than `v`".

The Library does not yet decompose Harris's prime-to-`p` group into a
restricted product over places, so the placewise reading is recorded as a
later obligation of the Harris specialization and of Flath's restricted
tensor statements; the two-factor formulation used here needs neither.

Harris fixes identifications of `GJ` and `GG` away from `v` (§4, printed
pp.308–309: `𝒟` and `ℬ` are assumed isomorphic away from `v` and its complex
conjugate, and `K(m)^p` is defined "via an identification
`GG(A_f^p) ≅ GJ(A_f^p)`"). The parameter `θ` is that identification; the
module takes it as an explicit input rather than choosing one, and the
relation is stated for the given `θ`.

## Dependencies and validation

Project import: `Langlands.Representation.Smooth.Definitions` (published).
Mathlib supplies `Representation`, `Representation.tprod`, `Representation.Equiv`,
`ModuleCat`, `ContinuousMulEquiv` and `MonoidHom.fst`/`snd`. Environment
`bb168ec3-1031-46d9-816b-5c2ed7bbe1a6` (Lean 4.34.0, Mathlib commit
`5ed2965256430c3649e86755f9576b54eca72435`).

`lean_check` `01d40e1d-453c-480e-9f39-3c3ee6ccb955` of the module in place: 0 errors, 0 warnings. Inspection of
`Langlands.JacquetLanglands.IsAwayTransfer` reports `statement_returns_prop: true`,
level parameters `u uG uG' uL uL' uH uH'`, axioms `propext`, `Classical.choice`,
`Quot.sound` only.
