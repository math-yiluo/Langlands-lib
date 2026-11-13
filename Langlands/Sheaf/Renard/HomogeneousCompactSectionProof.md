# Proof: Renard III.3.2, compact-section alpha and beta

Worker 139 implemented this proof for Task 5596. The entry theorem is
`Langlands.Sheaf.Renard.HomogeneousCompactSectionProof.compactAlphaBeta :
CompactAlphaBetaStatement`. It proves the published statement
`Langlands.Sheaf.Renard.HomogeneousSectionStatements.CompactAlphaBetaStatement`
from `Langlands/Sheaf/Renard/HomogeneousSectionStatements.lean` without changing it.

The hypotheses are those of the statement:

- `G` is a topological group with `[SigmaCompactSpace G]` and
  `Langlands.Topology.IsLocallyProfinite G`.
- `H` is a closed subgroup of `G`.
- The base is the published left quotient `LeftQuotient H`, with the inverse right
  action `homogeneousAction`, so `g • Hk = H k g⁻¹`.
- The origin is `o = origin H = quotientMap H 1`.

For every `F : SmoothActionSheaf G (LeftQuotient H)` the proof constructs an
intertwining map
`beta F : compactInduced H (stalkRepresentation H F.obj) → compactRepresentation F.obj`.
It then proves:

- both inverse laws against the published `alphaCompact H F`;
- the displayed germ formula
  `Γgerm (g • o) (beta F f) = stalkPull g⁻¹ (g • o) o (eval f g⁻¹)`;
- naturality for every morphism `u : F ⟶ F'`, with the published
  `CompactSections.map u.hom` and
  `compactInducedMap H ((fixedStalkFunctor …).map u.hom).hom`.

The `SigmaCompactSpace G` hypothesis is kept in the statement but the proof never
uses it. Renard needs countability at infinity to identify an abstract transitive
`G`-space with `H\G` (Corollary II.3.3). Here the base is already the literal
quotient `LeftQuotient H`, so that step does not arise. The proof uses the
locally profinite hypothesis on `G` and the closedness of `H`, through
`quotient_isLocallyProfinite H hG hH`, which makes `H\G` Hausdorff with a compact
open neighbourhood basis.

## Source

David Renard, *Représentations des groupes réductifs p-adiques*, French version
dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`. The relevant
passage is III.3.2, printed p.85 / PDF p.91, with the hypotheses on printed p.84 /
PDF p.90. Both pages were read for this proof.

Renard gives `α : F_c(H\G) → ind_H^G(τ, E)` by `φ ↦ [g ↦ (γ_g · φ)(o)]`. He gives
the inverse `β : f ↦ [Hg⁻¹ = γ_g(o) ↦ γ_g(f(g⁻¹))]`, and says the isomorphisms are
natural and easily checked. The Lean proof shows that the published `alpha` is
bijective and defines `beta` as its inverse. It then derives Renard's displayed
formula for `beta` as a theorem, `germ_beta`. In the Library's conventions
Renard's `γ_g` applied to an element of the stalk at `o` is the stalk transport
`Godement.stalkPull F g⁻¹ (g • o) o`. That is the right side of the statement's
germ formula.

## Implemented proof

All declarations are in `HomogeneousCompactSectionProof.lean`.

### General helpers

- `exists_global_of_locally_germ`: let `F` be a Mathlib sheaf of complex vector
  spaces on a space `X`, and let `σ x` be an element of the stalk at `x` for each
  `x`. Suppose every point has an open neighbourhood `V` and a global section `u`
  with `Γgerm y u = σ y` for all `y ∈ V`. Then some global section `s` has
  `Γgerm x s = σ x` for every `x`. The proof restricts each `u` to its `V`. These
  restrictions are compatible because on overlaps both sides have the germs `σ`
  (`TopCat.Presheaf.section_ext`). It then glues them with
  `TopCat.Sheaf.existsUnique_gluing'`.
- `stalkPull_comp_apply`, `stalkPull_cancel` and `stalkPull_label` give the
  composition law of the published `Godement.stalkPull_mul` in applied form, for
  any label `c` with `b * a = c`. They also give its cancellation case `b * a = 1`,
  and the fact that equal labels give equal transports.
- `germ_global`: the germ at `x` of `globalRepresentation F k s` is
  `stalkPull F k⁻¹ x y` of the germ of `s` at `y = k⁻¹ • x`. This is
  `Godement.germ_stalkPull_arrow` applied to `ActionOpens.sectionArrow k`, whose
  label is `k⁻¹`. `germ_global_inv` is the same formula for the operator `k⁻¹`,
  with label `k`.

### Homogeneous base

- `mem_of_smul_origin`: an `h` with `h • o = o` lies in `H`. This uses
  `Quotient.exact` and `QuotientGroup.rightRel_apply`.
- `smul_self` and `out_smul`: `a • quotientMap H a = o` for every `a`. In
  particular this holds for the representative `Quotient.out x` of a coset `x`.
- `eval_covariant`: for `h ∈ H` and `f` a compact induced function,
  `eval f (h * g)` is `stalkPull h⁻¹ o o (eval f g)`. This is the covariance of
  `f`, and the coefficient action `stalkRepresentation H F.obj` is by definition
  this stalk transport (`fixedStalkAction_apply`).
- `betaGerm H F f x := stalkPull (x.out) x o (eval f x.out)` is the displayed
  germ, computed with a chosen representative. `betaGerm_eq` shows that any `g`
  with `g • x = o` gives the same value `stalkPull g x o (eval f g)`. Indeed
  `g * x.out⁻¹` fixes `o`, so it lies in `H`. Covariance then rewrites
  `eval f g`, and `stalkPull_comp_apply` gives the result, because
  `(g * x.out⁻¹)⁻¹ * g = x.out`.

### Injectivity of alpha

`alphaCompact_injective`: suppose `alphaCompact H F s = 0`. For every `g`, the
value `alphaFunction H F.obj s g` is then zero (`alphaCompact_apply` is `rfl`). By
the published `alphaFunction_ne_zero_iff`, the germ of `s` at `quotientMap H g` is
zero. Every coset is `quotientMap H (Quotient.out x)`, so all germs of `s` vanish,
and `TopCat.Presheaf.section_ext` on the underlying sheaf `underlying F.obj` gives
`s = 0`.

### Surjectivity of alpha

`alphaCompact_surjective hG hH`: let `f` be a compact induced function. We glue the
germ family `betaGerm H F f` with `exists_global_of_locally_germ`. The local
representatives come from the following argument at a coset `x = quotientMap H a`.

1. `CompactGerms.germ_surjective` gives a compactly supported global section `t`
   with germ `eval f a` at `o`. It applies to the sheaf `underlying F.obj` on the
   locally profinite quotient.
2. Put `u₀ = compactRepresentation F.obj a⁻¹ t`. The published smoothness
   condition of `SmoothActionSheaf` (`F.property`, smoothness of the whole
   compact-section representation) gives an open subgroup `K` fixing `u₀`.
   Smoothness of `f` gives an open subgroup `K'` with `f(y * k) = f(y)` for
   `k ∈ K'`. Let `L = K ⊓ K'`.
3. The neighbourhood is `V = quotientMap H '' (a · L)`. It is open because left
   multiplication is open and `leftQuotient_isOpenQuotientMap` makes the
   projection open, and it contains `x`.
4. Take a point `quotientMap H (a * l)` with `l ∈ L`, and let `b = a * l`, so
   `b • (Hb) = o`. Since `l⁻¹ ∈ K`, we get `u₀ = globalRepresentation (a * l)⁻¹ t`
   (`global_mul`, `mul_inv_rev`). By `germ_global_inv`, the germ of `u₀` there is
   `stalkPull b _ o (eval f a)`. Since `l ∈ K'`, this equals
   `stalkPull b _ o (eval f b)`, which is `betaGerm` there by `betaGerm_eq`.

The glued global section `s` satisfies `alphaFunction H F.obj s g = eval f g` for
every `g`. Indeed `germ_global` writes the left side as
`stalkPull g⁻¹ o (g⁻¹ • o)` applied to `betaGerm f (g⁻¹ • o)`. By `betaGerm_eq` this
germ is `stalkPull g (g⁻¹ • o) o (eval f g)`, and `stalkPull_cancel` removes the
two transports. Finally `s` has compact support. By the published
`quotientSupport_alphaFunction`, its support equals
`quotientSupport H (alphaFunction s) = quotientSupport H (eval f)`, which is
compact because `f` is a compact induced function. So `⟨s, _⟩` is a compact section
with `alphaCompact H F ⟨s, _⟩ = f`.

### Beta, the inverse laws and the germ formula

- `beta H F hG hH` is the inverse of
  `LinearEquiv.ofBijective (alphaCompact H F).toLinearMap ⟨injective, surjective⟩`.
  Its equivariance is Mathlib's `LinearEquiv.isIntertwining_symm_isIntertwining`
  applied to the intertwining property of `alphaCompact`. Thus `beta F f` is an
  actual original compactly supported global section.
- `beta_alphaCompact` and `alphaCompact_beta` are the two inverse laws,
  `symm_apply_apply` and `apply_symm_apply`.
- `germ_beta`: by `alphaCompact_beta`,
  `eval f g⁻¹ = alphaFunction (beta f) g⁻¹`. By `germ_global_inv` with operator
  `g⁻¹`, this is `stalkPull g o (g • o)` of the germ of `beta f` at `g • o`.
  Applying `stalkPull g⁻¹ (g • o) o` and `stalkPull_cancel` gives the statement's
  displayed formula.

### Naturality and the entry theorem

`compactAlphaBeta` introduces the statement's data and supplies
`fun F => beta H F hG hH` with the three laws above. For naturality we compare
both sides on `f`. It suffices to compare them after the injective
`alphaCompact H F'`. On the right, `alphaCompact_beta` for `F'` leaves
`compactInducedMap … f`. On the left, the published `alphaCompact_naturality H u`
turns `alphaCompact H F' (CompactSections.map u.hom (beta F f))` into
`compactInducedMap … (alphaCompact H F (beta F f))`, which is
`compactInducedMap … f` by `alphaCompact_beta` for `F`.

The development uses only the axioms `propext`, `Classical.choice` and
`Quot.sound`.
