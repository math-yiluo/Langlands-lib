# Proof: Renard III.3.2, smooth global sections

Worker 140 wrote this proof for Task 5597. The entry theorem is
`Langlands.Sheaf.Renard.HomogeneousSmoothGlobalProof.smoothGlobalAlphaBeta :
HomogeneousSectionStatements.SmoothGlobalAlphaBetaStatement`. It proves that published
statement from `Langlands/Sheaf/Renard/HomogeneousSectionStatements.lean`, and the
statement is not modified. The hypotheses are kept as stated: `G : Type` is a topological
group with `SigmaCompactSpace G` and `Langlands.Topology.IsLocallyProfinite G`, and `H` is
a closed subgroup. The base is the published `LeftQuotient H`, acted on by
`homogeneousAction` (`g • quotientMap H k = quotientMap H (k * g⁻¹)`), with origin
`o = origin H = quotientMap H 1`.

Every `F : SmoothActionSheaf G (LeftQuotient H)` gets an intertwining map
`beta F` from `smoothInduced H (stalkRepresentation H F.obj)` to
`Langlands.smoothPart (globalRepresentation F.obj)`. The proof shows the following about it:
- `beta F` is a left and a right inverse of the published `alphaSmoothGlobal H F.obj`;
- it satisfies the displayed germ formula
  `Γgerm (g • o) (beta F f) = stalkPull(g⁻¹, g • o, o) (eval f g⁻¹)`;
- it is natural for every morphism `u : F ⟶ F'` of smooth action sheaves, in the exact
  form of the statement.

`SigmaCompactSpace G` is part of the statement, but the proof never uses it. The
locally profinite and closed-subgroup hypotheses are used once, through the published
`quotient_isLocallyProfinite H hG hH`.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, registered as `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. The relevant
passage is III.3.2, printed p.85 / PDF p.91, and PDF p.91 was read for this proof. The
source says that the smooth part of the representation of `G` on `F(H\G)` is isomorphic to
`Ind_H^G(τ, E)`, where `(τ, E)` is the `H`-representation on the fibre at `o`. It writes
the compact-section isomorphism as
`α : φ ↦ [g ↦ (γ_g · φ)(o)]` with inverse `β : f ↦ [H g⁻¹ = γ_g(o) ↦ γ_g(f(g⁻¹))]`. For the
smooth-global case it says only "by analogous formulas". For naturality it says "On
vérifie sans difficulté". The source gives no further argument, so the Lean proof below is
its own: it proves that the published literal alpha is bijective and takes beta to be the
inverse.

## Implemented proof

The file has two sections, then the entry theorem.

### General action-sheaf lemmas

These hold for any `X` with a `G`-action and any `F : ActionSheaf G X`.

- `stalkPull_congr`: `Godement.stalkPull F g x y h` depends only on the label `g`. If two
  labels are equal, the transports are equal, whatever the proofs of `g • x = y` are.
- `germ_global_action`: `Γgerm x (globalRepresentation F k s)` equals
  `stalkPull(k⁻¹, x, y)(Γgerm y s)` whenever `k⁻¹ • x = y`. This is the published
  `Godement.germ_stalkPull_arrow` applied to `ActionOpens.sectionArrow k`, which has label
  `k⁻¹`.
- `global_ext`: global sections that have the same germ at every point are equal. This is
  Mathlib's `TopCat.Presheaf.section_ext` for the underlying sheaf on `⊤`.
- `exists_global_of_local`: let `v x` be one stalk element for each point `x`. Suppose
  every `x` has an open `U ∋ x` and a section `t` on `U` whose germ at each `y ∈ U` is
  `v y`. Then some global section has germ `v x` at every `x`. The proof chooses `U x` and
  `t x` for each point. Compatibility on overlaps follows from `section_ext` and
  `germ_res_apply`. Mathlib's `TopCat.Sheaf.existsUnique_gluing'` then glues the sections
  to a section on `⊤`.

### The homogeneous base

- `exists_smul_eq_origin`: for every `x` there is `a` with `a • x = o`. Write
  `x = quotientMap H k` and take `a = k`.
- `mem_of_smul_origin`: if `h • o = o` then `h ∈ H`. This is `Quotient.exact` together
  with `QuotientGroup.rightRel_apply`.
- `germ_eq_stalkPull_alpha` is the key germ formula. Let `s` be any global section and
  suppose `a • y = o`. Then `Γgerm y s = stalkPull(a, y, o)(alphaFunction H F s a)`. The
  proof writes `s = a⁻¹ • (a • s)` using `Representation.inv_self_apply` and applies
  `germ_global_action` with `k = a⁻¹`. It then replaces the label `a⁻¹⁻¹` by `a`.
- `alphaFunction_injective`: if two global sections have the same literal function
  `alphaFunction`, they are equal. For each point `y`, choose `a` with `a • y = o`. The
  germ formula then gives equal germs at `y`, and `global_ext` finishes.
- `germAt f a y h` is `stalkPull(a, y, o)(eval f a)`, for `f` in `SmoothFunctions` and
  `h : a • y = o`. Lemma `germAt_eq` shows that it does not depend on `a`. Suppose also
  `b • y = o`. Then `p = b * a⁻¹` fixes `o`, so `p ∈ H` by `mem_of_smul_origin`. The
  covariance of `f` (its membership in `coindV`) gives
  `f b = f (p * a) = stalkRepresentation p (f a)`. The published `fixedStalkAction`
  defines this action as `stalkPull(p⁻¹, o, o)`. `Godement.stalkPull_mul` then gives
  `stalkPull(b, y, o) ∘ stalkPull(p⁻¹, o, o) = stalkPull(p⁻¹ * b, y, o)`, and
  `p⁻¹ * b = a`.
- `germFamily f y` is `germAt` at the point `y`, for one element chosen with
  `exists_smul_eq_origin`. Lemma `germFamily_eq` says that by `germAt_eq` any element
  `a` with `a • y = o` computes it.
- `germFamily_local`: every point `x` has a neighbourhood on which the germ family comes
  from one global section. The proof first fixes `a` with `a • x = o`. Since the quotient is
  locally profinite, the published `CompactGerms.germ_surjective` gives a compact
  section `σ` with `Γgerm x σ = germFamily f x`.
  - Renard smoothness of `F` (`IsSmoothAction F`, smoothness of `compactRepresentation`)
    gives an open subgroup `K'` that fixes `σ`.
  - Smoothness of `f` gives an open subgroup `K` that fixes `f` under right translation.
  - Put `L = K ⊓ K'` and `x = quotientMap H c`. Take `U = quotientMap H '' (c · L)`, which
    is open by `leftQuotient_isOpenQuotientMap` and `isOpenMap_mul_left`.

  Every point of `U` has the form `y = m • x` with `m ∈ L`. For such `y`:
  - `(a * m⁻¹) • y = o`, so `germFamily f y = stalkPull(a * m⁻¹, y, o)(f (a * m⁻¹))`;
  - `f (a * m⁻¹) = f a` because `m⁻¹ ∈ K`;
  - `stalkPull(a * m⁻¹, y, o) = stalkPull(m⁻¹, y, x) ∘ stalkPull(a, x, o)` by
    `stalkPull_mul`.

  Hence `germFamily f y = stalkPull(m⁻¹, y, x)(Γgerm x σ)`. By `germ_global_action` this
  equals `Γgerm y (m • σ)`, which is `Γgerm y σ` because `m ∈ K'`.
- `exists_global_germFamily`: the germ family glues to a global section `s`. Apply
  `exists_global_of_local` to the restrictions of the local sections `σ` to `U`.
- `alphaFunction_of_germs`: if `s` has germ family `germFamily f`, then
  `alphaFunction H F s g = eval f g` for all `g`. By `germ_global_action`,
  `alphaFunction s g = stalkPull(g⁻¹, o, g⁻¹ • o)(Γgerm (g⁻¹ • o) s)`. Substituting
  `germFamily_eq` at the element `g` turns this into
  `stalkPull(g⁻¹, o, g⁻¹ • o)(stalkPull(g, g⁻¹ • o, o)(f g))`. By `stalkPull_mul`,
  `g * g⁻¹ = 1` and `stalkPull_one`, that is `f g`.
- `alphaSmoothGlobal_bijective`: `alphaSmoothGlobal H F.obj` is bijective. Injectivity
  holds because evaluation of `alphaSmoothGlobal` is `alphaFunction`, by the published
  `alphaSmoothGlobal_apply`, and `alphaFunction_injective` applies. For surjectivity, take
  the glued section `s` of a smooth induced function `f`. It is a smooth vector: if `K`
  fixes `f`, then for `k ∈ K` we have
  `alphaFunction (k • s) g = alphaFunction s (g * k) = f (g * k) = f g = alphaFunction s g`
  (using `global_mul`), so `k • s = s` by `alphaFunction_injective`. Then `⟨s, _⟩` maps
  to `f` by `alphaFunction_of_germs`.
- `beta hX F` is
  `((alphaSmoothGlobal H F.obj).ofBijective _).symm.toIntertwiningMap`. It uses Mathlib's
  `Representation.IntertwiningMap.ofBijective` and `Representation.Equiv.symm`, so it is
  complex-linear and `G`-equivariant. Lemmas `alpha_beta` and `beta_alpha` are the two
  inverse laws, `LinearEquiv.apply_symm_apply` and `LinearEquiv.symm_apply_apply`.

### Entry theorem

`smoothGlobalAlphaBeta` introduces the data and sets
`hX := quotient_isLocallyProfinite H hG hH`. It supplies `beta H hX` together with the
following proofs:

- the inverse laws `beta_alpha` and `alpha_beta`;
- the germ formula: rewrite with `germ_eq_stalkPull_alpha` at `a = g⁻¹` and `y = g • o`
  (proof `inv_smul_smul g o`), then `alphaFunction (beta f) g⁻¹ = eval f g⁻¹` by
  `alpha_beta`;
- naturality: by injectivity of `alphaSmoothGlobal H F'.obj`, it suffices to compare
  images. The published `alphaSmoothGlobal_naturality H u.hom` and `alpha_beta` for `F`
  and `F'` show that both images equal `smoothInducedMap H (...) f`.

The proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.
