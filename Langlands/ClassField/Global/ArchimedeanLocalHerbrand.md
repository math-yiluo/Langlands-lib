# Herbrand quotients of the archimedean local unit groups

Let `E` be a number field and `F` a field with `Algebra F E`. Fix an infinite place `w` of `E`.
Let `D_w ⊆ Aut(E/F)` be its stabilizer, `MulAction.stabilizer (E ≃ₐ[F] E) w`. The Library's
`infiniteLocalRepresentation F w` is the local coefficient module `E_wˣ`: the units of the
completion `w.Completion`, written additively, with `D_w` acting through the idèle action. This
module proves:

- `H¹(D_w, E_wˣ) = 0`;
- `|H²(D_w, E_wˣ)| = |D_w|`;
- hence `HasHerbrandQuotient (infiniteLocalRepresentation F w) |D_w|`.

Both cohomology groups are Mathlib's ordinary `groupCohomology`. No hypothesis beyond
`[Field F] [Field E] [NumberField E] [Algebra F E]` is needed. In particular `E/F` need not be
Galois or finite. The group `D_w` always has order `1` or `2`, so it is cyclic.

This is infrastructure for the first fundamental inequality in global class field theory
(task fb66219f): it is the archimedean factor of the per-place Herbrand computation.
Combining it over places is not part of this module.

All declarations are in the namespace `Langlands.ClassField.Global`. The module imports
`Langlands.ClassField.Global.IdeleArchimedean`, for the local action, and
`Langlands.Cohomology.HerbrandQuotient`. The latter supplies `HasHerbrandQuotient`,
`hasHerbrandQuotient_natCast_iff`, `Subquotient`, and the identifications for a generator `g`
of a finite cyclic group:

- `nonempty_linearEquiv_one`: `H¹ ≅ ker N ⧸ range (ρ(g) - 1)`;
- `nonempty_linearEquiv_two`: `H² ≅ ker (ρ(g) - 1) ⧸ range N`.

## Mathematical content and source

Milne, *Class Field Theory* v4.03, Chapter VII, Corollary 2.6 and the proof of Proposition 2.7,
printed p.206 (PDF p.215), gives `H¹(G_v, L_wˣ) = 0` (Hilbert 90) for every place. The local
invariant map gives `|H²(G_v, L_wˣ)| = n_v = [L_w : K_v]`. Hence `h(G_v, L_wˣ) = n_v`. For an
infinite place the local extension is `ℝ/ℝ`, `ℂ/ℂ` or `ℂ/ℝ`, so these facts reduce to elementary
statements about `ℝˣ` and `ℂˣ`. The Lean proof proves those statements directly.

**The structure of `D_w`.** Mathlib's `InfinitePlace.mem_stabilizer_mk_iff` shows that an
element `d` of `D_w` is either `1` or a complex conjugation of `w`: `w.embedding ∘ d` is the
complex conjugate of `w.embedding`. Two conjugations of `w` are equal (`IsConj.ext`). So either
`D_w` is trivial, or `D_w = {1, c}`. In the second case `c` is nontrivial, and
`ComplexEmbedding.isConj_ne_one_iff` shows that `w` is complex.

**The complex value.** Write `v(a) ∈ ℂ` for the image of `a ∈ E_wˣ` under the canonical
embedding `E_w → ℂ` (`infiniteLocalValue`). It turns addition in the additive module into
multiplication, and it is injective. At a complex place it is onto `ℂˣ`. The Library's
`extensionEmbedding_ideleInfiniteCoordinate_of_isConj` shows that a conjugation `c` acts by
`v(ρ(c) a) = conj (v a)`.

**Case `D_w = {1, c}`.** Take `g = c`. The norm is `N a = a + ρ(c) a`, so `v(N a) = |v a|²`.
Also `v((ρ(c) - 1) a) = conj (v a) / v a`.

1. **`H¹ = 0`.** If `N a = 0` then `|v a| = 1`. Choose `t` with `t² = conj (v a)`, so
   `|t| = 1` and `conj t = t⁻¹`. Then `conj t / t = t⁻² = (conj (v a))⁻¹ = v a`. For the element
   `b` with `v b = t`, this gives `(ρ(c) - 1) b = a`. So `ker N ⧸ range (ρ(c) - 1) = 0`.
2. **`|H²| = 2`.** An element `a` with `(ρ(c) - 1) a = 0` has real value `v a`. A positive real
   value `r` is a norm: `r = v(N b)` with `v b = √r`. So the class of `a` is `0` if `v a > 0`.
   If `v a < 0`, the class equals the class of the element `m` with `v m = -1`. The class of `m`
   is nonzero, because `-1` is not of the form `|z|²`. So `ker (ρ(c) - 1) ⧸ range N` has exactly
   the two elements `0` and `[m]`, and `|D_w| = 2`.

**Case `D_w` trivial.** Take `g = 1`. Then `N` is the identity and `ρ(1) - 1 = 0`. Both
subquotients `ker N ⧸ range 0` and `ker 0 ⧸ range N` are trivial, so `H¹ = H² = 0` and
`|H²| = 1 = |D_w|`.

Provenance: derived. The statement is the archimedean case of Milne's local computation
`h(G_v, L_wˣ) = n_v`, for the stabilizer `D_w` in `Aut(E/F)`. The proof is the direct
computation above, not the invariant map. Internal: `infiniteLocalValue` and its lemmas, and the
two subquotient lemmas in the section `Generic`. The local module and the conjugation formula
come from the Library's `Langlands.ClassField.Global.IdeleArchimedean`.

## Conventions and scope

- `F E : Type u`. The coefficient ring is `NormalizedTwoCocycle.CoefficientScalars.{u}`, as for
  `infiniteLocalRepresentation`.
- `|D_w|` is `Nat.card (MulAction.stabilizer (E ≃ₐ[F] E) w)`, which is `1` or `2`
  (`InfinitePlace.nat_card_stabilizer_eq_one_or_two`).
- `H²(D_w, E_wˣ)` corresponds to the Tate group `Ĥ⁰` used by Milne, since `D_w` is cyclic.
  `HasHerbrandQuotient` records this convention.

## Declarations

### `Generic` (any commutative ring `k` and group `G`)

- `subsingleton_subquotient_of_forall`: `Subquotient φ ψ = ker φ ⧸ range ψ` is a subsingleton
  when every `x` with `φ x = 0` lies in `range ψ`.
- `subsingleton_groupCohomology_of_subsingleton`: for a trivial group `G` and any `A : Rep k G`,
  `groupCohomology A 1` and `groupCohomology A 2` are subsingletons.

### `Value` (any field `E`)

- `infiniteLocalValue w : Additive (w.Completion)ˣ → ℂ` (def): `a ↦ extensionEmbedding w a`,
  the complex value of the unit `a`.
- `infiniteLocalValue_add`, `infiniteLocalValue_zero`, `infiniteLocalValue_sub`: it maps `+`,
  `0` and `-` to `*`, `1` and `/`.
- `infiniteLocalValue_ne_zero`: its values are nonzero.
- `infiniteLocalValue_injective`: it is injective.
- `exists_infiniteLocalValue_eq`: at a complex place every nonzero `z : ℂ` is a value.

### `Local` (`[Field F] [Field E] [NumberField E] [Algebra F E]`)

- `eq_one_or_isConj_of_mem_stabilizer`: an element of `D_w` is `1` or a complex conjugation of
  `w.embedding`. This does not need `NumberField E`.
- `infiniteLocalValue_ρ_of_isConj`: for a conjugation `c` of `w`,
  `infiniteLocalValue w ((infiniteLocalRepresentation F w).ρ c a) = conj (infiniteLocalValue w a)`.
- `infiniteLocal_cohomology_of_isConj`: if `w` has a conjugation `c ≠ 1`, then `H¹` is a
  subsingleton and `Nat.card H² = Nat.card D_w`.
- `infiniteLocal_cohomology F w`: for every infinite place `w`, `H¹(D_w, E_wˣ)` is a
  subsingleton and `Nat.card H²(D_w, E_wˣ) = Nat.card D_w`.
- `subsingleton_groupCohomology_one_infiniteLocalRepresentation F w`:
  `Subsingleton (groupCohomology (infiniteLocalRepresentation F w) 1)`.
- `natCard_groupCohomology_two_infiniteLocalRepresentation F w`:
  `Nat.card (groupCohomology (infiniteLocalRepresentation F w) 2) =
  Nat.card (MulAction.stabilizer (E ≃ₐ[F] E) w)`.
- `hasHerbrandQuotient_infiniteLocalRepresentation F w`:
  `HasHerbrandQuotient (infiniteLocalRepresentation F w)
  (Nat.card (MulAction.stabilizer (E ≃ₐ[F] E) w))`. So `H¹` and `H²` are finite, and
  `|H²| = |D_w| · |H¹|`.
