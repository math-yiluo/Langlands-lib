# Deligne's modified local constant `ε₀`

Worker 33 wrote this module for task `e534647a`. It adds Deligne's modified
local constant `ε₀` to the coverage map of that task. The main declaration is
`Langlands.LocalFactor.EpsilonZeroStatement`. It is a proposition only. No
local-constant system, presentation or Frobenius is constructed or chosen, and
nothing is assumed as an axiom. The module defines `ε₀` from a supplied system
(Deligne (5.1)) and proves two small lemmas: `ε₀` does not depend on the
supplied Frobenius lift.

## Objects

Everything except `ε₀` itself comes from the published Library:

- `CommonClosure`: a p-adic field `F`, the finite intermediate extensions
  `E : Extension F` in its algebraic closure, their Weil subgroups `W_E`
  (`weilSubgroup F E`), the continuous exact virtual groups `Virtual F E`,
  additive characters `ψ`, Haar measures `μ` with their rescaling
  `scaleHaar`, the trace character `traceCharacter F E L h ψ = ψ ∘ Tr_{L/E}`,
  virtual induction `induce`, the actual induced representation
  `inducedRepresentation`, the supplied reciprocity components
  `reciprocityUnits` and the Weil-group character `weilCharacter F e E χ` of a
  field character `χ`.
- `NonabelianSystem`: an assignment `ε_E(x, ψ, μ)` on virtual classes, with
  the system property `IsSystem F e ε` for a reciprocity family `e`.
- `CommonClosureSpectral`: `conditionalDeligneValue x s = ε_E(x ⊗ ω_s, ψ, μ)`.
  Here `ω_s` is `character F E s`, `w ↦ q_F^(-s · deg w)`, with `deg` the
  degree over `F` and `q_F = baseCardinality F` the residue cardinality of `F`.
- `CommonClosureWeilDeligne`: the inertia subgroup `inertia F E` (the kernel of
  the degree map of `W_E`), the residue cardinality
  `q_E = residueCardinality F E` of `E`, and the supplied geometric Frobenius
  elements `GeometricFrobenius F E`, elements `Φ ∈ W_E` of norm `q_E^(-1)`.
- `FiniteRepresentation`: the actual inertia invariants `invariants`, twists
  by a character `twist`, tensor products `tensor`, short exact sequences
  `IsShortExact`, and the dimension `rank`.
- `ConductorExponent` (published with `ConductorExponentStatement`): the bottom
  field `base F`, finite-inertia presentations `Presentation F A` of a
  representation of `W_F = weilSubgroup F (base F)`, and `additiveConductor F ψ`,
  Tate's integer `n(ψ)`. A presentation `P` with surjectivity `hsurj` of the
  actual restriction map has a rational Swan conductor
  `P.swanConductor hsurj`. In the Library the Artin conductor is the
  codimension of the inertia invariants plus this Swan conductor
  (`Ramification.Padic.artinConductorOfQuotient_eq_tame_add_swan`).

## Definitions

All of these live in the namespace `Langlands.LocalFactor.EpsilonZero`. Here
`A` is a finite-dimensional complex representation of `W_E`.

- `inertiaInvariants F E A` is the subrepresentation `V^I` of vectors fixed by
  `inertia F E`.
- `invariantDeterminant F E A Φ s` is
  `det(q_E^(-s) · (-Φ) | V^I)`, with `q_E^(-s) = exp(-s log q_E)`.
- `genuineClass F E A hA` is the exact virtual class of a continuous `A`.
- `value F e ε hε E ψ μ A hA Φ s` is
  `conditionalDeligneValue (genuineClass A) s · invariantDeterminant A Φ s`.

`value` is `ε₀(V ⊗ ω_s, ψ, μ)`. Deligne (5.1) defines `ε₀` for a
representation `V` by `ε(V, ψ, dx) = ε₀(V, ψ, dx) · det(-F | V^I)^(-1)`, where
`F` is a geometric Frobenius. So `ε₀(V) = ε(V) · det(-F | V^I)`. Apply this to
`V ⊗ ω_s`. Its inertia invariants are `V^I ⊗ ω_s`, because `ω_s` is trivial on
inertia. A geometric Frobenius `Φ` over `E` has degree `f(E/F)` over `F`, so
`ω_s(Φ) = q_F^(-s · f) = q_E^(-s)`. Hence `Φ` acts on `(V ⊗ ω_s)^I` as
`q_E^(-s) Φ` acts on `V^I`, which gives the second factor of `value`. At
`s = 0`, `value` is `ε₀(V, ψ, μ)` itself.

Two lemmas are proved:

- `invariantDeterminant_eq_of_frobenius`: two geometric Frobenius elements
  differ by an element of inertia (`frobenius_coset`), which acts trivially on
  `V^I`. So the determinant does not depend on `Φ`.
- `value_eq_of_frobenius`: hence `value` does not depend on `Φ` either.

`ε₀` is defined only for genuine continuous representations. Deligne (5.2)
says that `ε` and `ε₀` are additive in `V` and therefore make sense for virtual
`V`. Additivity of `ε₀` is the first clause below; the virtual extension is not
defined here.

## The statement

`EpsilonZeroStatement` says that for every prime `p` and every p-adic field
`F`, seven clauses hold. In each clause the data include a reciprocity family
`e`, an assignment `ε` with `IsSystem F e ε`, and a geometric Frobenius `Φ` at
the field where `value` is evaluated. Write `ε₀(V, ψ, μ, s)` for `value` with
these data and drop arguments that do not change. All representations are
genuine and continuous.

1. `AdditivityStatement` (Deligne (5.2)): for a short exact sequence
   `0 → A → B → C → 0` of representations of `W_E` (`IsShortExact f g`) and
   every `s`, `ε₀(B, s) = ε₀(A, s) · ε₀(C, s)`.
2. `HaarScalingStatement` (Deligne (5.3)): for every real `c > 0` and every
   `s`, `ε₀(A, ψ, c · μ, s) = c^(dim A) · ε₀(A, ψ, μ, s)`.
3. `AdditiveCharacterScalingStatement` (Deligne (5.4)): let `a ∈ E^×` and
   `w ∈ W_E` with `reciprocityUnits F e E w = a`. Then for every `s`,
   `ε₀(A, ψ(a ·), μ, s) = det A(w) · ω_s(w)^(dim A) · ‖a‖^(-dim A) · ε₀(A, ψ, μ, s)`,
   with `‖·‖` the normalized absolute value of `E`. The factor
   `det A(w) · ω_s(w)^(dim A)` is `det(A ⊗ ω_s)(w)`.
4. `SpectralSwanStatement` (Deligne (5.5.2), second formula), at the base
   field: for every presentation `P` of `A` with `hsurj`, and every `s`,
   `ε₀(A, s) = ε₀(A, 0) · q^(-(sw + dim A · (n + 1)) · s)`. Here
   `sw = P.swanConductor hsurj`, `n = n(ψ)`, `q = q_F`, and the power is the
   complex power of the positive real `q`.
5. `UnramifiedCharacterSwanStatement` (Deligne (5.5.1), second formula), at the
   base field: let `χ` be a field character of `F` that is trivial on every
   unit of valuation one, let `m ∈ ℤ` satisfy `m = sw + dim A · (n + 1)` in
   `ℚ`, and let `c ∈ F^×` have valuation `m` (`discreteValuation c = exp(-m)`).
   Then for every `s`, `ε₀(A ⊗ χ, s) = χ(c) · ε₀(A, s)`. Here `A ⊗ χ` is the
   twist of `A` by the Weil-group character `weilCharacter F e (base F) χ`.
6. `UnramifiedTensorSwanStatement` (Deligne (5.5.3), second formula), at the
   base field: let `W` be a representation of `W_F` on which every element of
   `inertia F (base F)` acts trivially, and let `m` be as in clause 5. Then for
   every `s`, `ε₀(A ⊗ W, s) = det W(Φ)^m · ε₀(A, s)^(dim W)`, with the same `Φ`
   in `det W(Φ)` and in `ε₀`.
7. `InductionStatement` (Deligne (5.6.2) for `ε₀`): let `E ⊆ L` be nested
   finite extensions in the common closure, `ψ` an additive character of `E`,
   `μ_E` and `μ_L` Haar measures of `E` and `L`, `A` a representation of `W_L`
   of any dimension, and `Φ_E`, `Φ_L` geometric Frobenius elements over `E`
   and `L`. Put `ψ_L = ψ ∘ Tr_{L/E}` and
   `λ = ε_E(Ind 1_L, ψ, μ_E) / ε_L(1_L, ψ_L, μ_L)`, computed with the system `ε`
   on virtual classes. Then for every `s`,
   `ε₀_E(Ind A, ψ, μ_E, s) = λ^(dim A) · ε₀_L(A, ψ_L, μ_L, s)`.

### Design choices

- **Frobenius as an argument.** `value` takes a supplied geometric Frobenius
  rather than choosing one. The proved lemma `value_eq_of_frobenius` shows that
  the choice does not matter, so each clause has the same content for every
  `Φ`.
- **Spectral variable everywhere.** Every clause holds at every `s ∈ ℂ`, not
  only at `s = 0`. Deligne writes (5.2)–(5.4) and (5.6.2) at `s = 0`. The
  versions at `s` follow by applying them to `V ⊗ ω_s`, using that `ω_s` is
  trivial on inertia, has `dim 1`, commutes with direct sums, tensor products
  and induction, and that `det(V ⊗ ω_s)(w) = det V(w) · ω_s(w)^(dim V)`.
- **The base field for the Swan clauses.** Clauses 4–6 are stated at the bottom
  field `base F`, exactly as in `ConductorExponentStatement`, for the same
  reason: the Library's finite-inertia presentations are defined only for
  representations of the local Weil group of `F`. Since `F` is arbitrary, they
  cover every p-adic field. Clauses 1–3 and 7 need no conductor and hold over
  every `E`.
- **Every presentation; rational Swan conductor.** As in
  `ConductorExponentStatement`, clauses 4–6 hold at every presentation whose
  restriction map is surjective, given as an explicit hypothesis. The Swan
  conductor is rational in the Library. Clause 4 uses a complex power, and
  clauses 5 and 6 quantify over an integer `m` equal to `sw + dim A · (n + 1)`
  in `ℚ`. Such an `m` exists by the Hasse–Arf integrality of the Swan
  conductor, which is not asserted here.
- **Residue cardinalities.** Clause 4 uses `q = baseCardinality F`, matching
  `ω_s`. The determinant factor in `value` at the base field uses
  `residueCardinality F (base F)`, the residue cardinality from the canonical
  data of the subfield `⊥`. These are different Lean terms for the same
  number. This module does not prove that they are equal.
- **The same `λ` for `ε₀`.** Clause 7 uses the constant `λ` of `ε`, as Deligne
  states. This needs no new constant because the determinant factor is
  compatible with induction (see below).
- **Twist in clause 5.** Clause 5 twists the genuine representation `A` by
  `χ ∘ e`, while `ConductorExponentStatement` tensors virtual classes with the
  character class of `χ`. The exact classes agree; the genuine twist is needed
  here because `ε₀` is defined on genuine representations.

### Why the clauses hold

This is recorded only to explain the hypotheses and is not part of the
statement. Write `D(V, s) = det(-q^(-s) Φ | V^I)`, so `ε₀(V, s) = ε(V, s) D(V, s)`.

- Clauses 1–3 and 7 hold for `ε` by Deligne (5.2)–(5.4) and (5.6.2), applied
  to `V ⊗ ω_s`. For clause 1, inertia acts on a continuous representation
  through a finite quotient, so `V ↦ V^I` is exact and `D` is multiplicative.
  `D` depends neither on `μ` nor on `ψ`, which gives clauses 2 and 3.
- For clause 7, put `f = f(L/E)`. Mackey's formula gives
  `(Ind V)^(I_E) ≅ Ind_{fℤ}^{ℤ} V^(I_L)` as representations of
  `W_E / I_E ≅ ℤ`, where `Φ_E^f` acts on `V^(I_L)` as a geometric Frobenius
  `Φ_L` of `L`. The operator `Φ_E` is a block cyclic matrix with `f` blocks,
  so `det(-t Φ_E | (Ind V)^(I_E)) = det(-t^f Φ_L | V^(I_L))`. With `t = q_E^(-s)`
  and `q_E^f = q_L`, the factors `D` on both sides agree. Also `ω_s` of `E`
  restricts to `ω_s` of `L`, so `(Ind V) ⊗ ω_s = Ind(V ⊗ ω_s)`.
- For clause 4, write `a` for the Artin conductor, so
  `a = sw + dim V - dim V^I`. Tate (3.4.5), stated as clause 1 of
  `ConductorExponentStatement`, gives `ε(V, s) = ε(V, 0) q^(-(a + n dim V) s)`.
  Also `D(V, s) = q^(-s dim V^I) D(V, 0)`. The exponents add up to
  `sw + dim V (n + 1)`.
- For clause 6, let `Φ` have eigenvalues `α_i` on `V^I` and `β_j` on `W`. Then
  `(V ⊗ W)^I = V^I ⊗ W` and
  `det(-Φ | V^I ⊗ W) = det(-Φ | V^I)^(dim W) · det W(Φ)^(dim V^I)`. Multiply by
  Tate (3.4.6), `ε(V ⊗ W) = ε(V)^(dim W) det W(Φ)^(a + n dim V)`. The exponent
  of `det W(Φ)` is again `sw + dim V (n + 1)`.
- Clause 5 is clause 6 for the line `W` on which `W_F` acts by `χ ∘ e`.
  `NormalizedReciprocity` in `IsSystem` sends `Φ` to an element of valuation
  one, so `det W(Φ)^m = χ(e(Φ))^m = χ(c)`.

### Consequences not stated

- `ε₀` of virtual classes, by multiplicative extension, and the consequences
  that need it: independence of `dx` in degree 0 (Deligne (5.3)) and
  inductivity in degree 0 (Deligne (5.6.1) for `ε₀`). Both follow from
  clauses 1, 2 and 7.
- Deligne's first formulas in (5.5.1)–(5.5.3), for `ε`. They are clauses 1–3
  of `ConductorExponentStatement`.
- The abelian formulas for `ε₀` (Deligne (3.4.3.3)–(3.4.3.5)), in particular
  the formula of `ε₀(χ)` as an integral over a single shell. They concern the
  rank-one values `PadicAbelian.epsilonAt` rather than a nonabelian system.

## Sources

`deligne-1973-local-constants`, SHA-256
`b03f483c4eeca79b75e34b88f41406fe4c9e16ba621480ce859697c93e8d5844`:
P. Deligne, *Les constantes des équations fonctionnelles des fonctions L*,
LNM 349 (1973). The PDF page is the printed page minus 500.

- §5.1–(5.5.2), printed p.548 (PDF p.48): the definition (5.1)
  `ε(V, ψ, dx) = ε₀(V, ψ, dx) det(-F, V^I)^(-1)`; (5.2), `ε` and `ε₀` are
  additive in `V`, hence make sense for virtual `V`; (5.3),
  `ε(V, ψ, a dx) = a^(dim V) ε(V, ψ, dx)`, and the same for `ε₀`; (5.4),
  `ε(V, ψ(ax), dx) = det(V)(a) ‖a‖^(-dim V) ε(V, ψ, dx)`, and the same for
  `ε₀`; (5.5.1), for `χ` an unramified quasi-character,
  `ε₀(Vχ, ψ, dx) = χ(π^(dim V + sw(V) + dim V · n(ψ))) ε₀(V, ψ, dx)`; the
  notation `ε(V, ψ, dx, s) = ε(V ω_s, ψ, dx)`, the same for `ε₀`; and the
  first formula of (5.5.2).
- printed p.549 (PDF p.49): the second formula of (5.5.2),
  `ε₀(V, ψ, dx, s) = ε₀(V, ψ, dx) q^(-(sw(V) + dim V (n(ψ) + 1)) s)`; (5.5.3),
  for `W` unramified,
  `ε₀(V ⊗ W, ψ, dx) = det W(π^(sw(V) + dim V (n(ψ) + 1))) ε₀(V, ψ, dx)^(dim W)`;
  (5.6.1) and (5.6.2), `ε(V_K, ψ, dx_K) = λ(L/K, ψ, dx_L, dx_K)^(dim V_L) ·
  ε(V_L, ψ ∘ Tr_{L/K}, dx_L)` for `V_K` induced from `V_L` of any dimension,
  followed by "La même formule vaut pour `ε₀`". Taking `V_L = 1` gives
  `λ = ε(Ind 1, ψ, dx_K) / ε(1, ψ ∘ Tr, dx_L)`.
- §3.4, printed p.527 (PDF p.27): `n(ψ)`, the Artin conductor `a(χ)` and the
  Swan conductor `sw(χ)` of a character.

`tate-1979-number-theoretic-background`, SHA-256
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`:
J. Tate, *Number theoretic background*, Corvallis Part II (1979), (3.4.5) and
(3.4.6), printed p.15 (PDF p.24), used in the explanation above.
