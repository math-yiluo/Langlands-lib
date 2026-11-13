# Open pieces of invertible modules on a projective flat family, by Hilbert polynomials and vanishing of higher cohomology

Authors: Worker 5705.

Worker 5705 wrote the Lean file and this description for task
`07219dde-fd87-48cf-83be-db16cbb3707c` (Task 5705), after reading
pp.27–31 of Kleiman's survey (Theorem 4.8, its proof and Lemma 4.9). The
proposition isolates the open decomposition of the Picard functor used in that
proof: the subfunctors `P^φ` (fixed Hilbert polynomial of `L⁻¹`) and
`P^φ_m` (vanishing higher cohomology of `L(n)` for `n ≥ m`), described
through explicit opens of each base, together with the cohomological facts
that the proof extracts from them. One condition is added to Kleiman's pieces
(`H⁰(X_t, L_t(m)) ≠ 0`); the reason is explained under *Source and
derivation*.

No proof is asserted here.

## Statement

The module defines one declaration,
`Langlands.AlgebraicGeometry.Picard.PicardHilbertPolynomialPiecesStatement`,
with the single universe parameter `u`. It is a proposition (`def … : Prop`).

### Hypotheses

It quantifies over a noetherian commutative ring `A : Type u`, with
`S = Spec (CommRingCat.of A)`, a scheme `X`, a morphism `f : X ⟶ S` and a
module `𝓛X : X.Modules`, and assumes

- `f` is proper (Mathlib's `IsProper`), flat (`Flat`) and geometrically
  integral (`GeometricallyIntegral`: for every field `K` and every
  `Spec K ⟶ S` the fibre product `X ×_S Spec K` is integral);
- `Scheme.Modules.IsInvertible 𝓛X` and
  `Scheme.Modules.ClosedImmersionBySections 𝓛X f` (FLT-port definitions:
  `𝓛X` is invertible, and finitely many of its global sections define a
  closed immersion of `X` into a finite projective space over `A`). These are
  exactly the hypotheses on `(f, 𝓛X)` of the divisor-scheme statement
  `Langlands.AlgebraicGeometry.Picard.RelativeEffectiveDivisorHilbertPiecesStatement`
  (a companion statement of Task 5705, staged by Worker 22); `𝓛X` plays the
  role of Kleiman's `O_X(1)`.

### Notation

For a scheme `T` and `s : T ⟶ S` write `X_T = pullback f s` with projections
`pullback.fst f s : X_T ⟶ X` and `pullback.snd f s : X_T ⟶ T`. For a module
`L` on `X_T` and `m : ℕ` write

```lean
L(m) := Nat.rec (motive := fun _ => (pullback f s).Modules) L
  (fun _ M => M ⊗ (Scheme.Modules.pullback (pullback.fst f s)).obj 𝓛X) m
```

that is, `L ⊗ 𝓛X_T ⊗ ⋯ ⊗ 𝓛X_T` with `m` factors of the pullback of `𝓛X`,
bracketed to the left. The tensor product `⊗` and the unit `𝟙_` in this
declaration elaborate to the monoidal structure of the FLT port on module
sheaves (`AlgebraicGeometry.Scheme.Modules.monoidalCategory`), as in the
divisor-scheme statement. (The transitive imports also contain the Library's
`Langlands.Scheme.Modules.tensorMonoidalCategory`; it is not the instance
selected here.)

For a point `t : T` write `X_t = pullback (pullback.snd f s) (T.fromSpecResidueField t)`
for the fibre of `X_T` over `Spec κ(t)` and `M_t` for the pullback of a module
`M` on `X_T` along the projection `X_t ⟶ X_T`; `Hⁱ(X_t, M_t)` is the Library's
derived-functor cohomology
`Modules.DerivedSections.relativeCohomology (pullback.snd (pullback.snd f s) (T.fromSpecResidueField t)) i`,
a `κ(t)`-module.

### Conclusion

There exist a type `κ : Type`, polynomials `θ : κ → ℕ → Polynomial ℚ`, and a
function `U` assigning to every scheme `T : Scheme.{u}`, every
`s : T ⟶ S`, every module `L` on `X_T`, every `c : κ` and every `m : ℕ` an
open subset `U T s L c m : T.Opens`, with the following five properties.
In all of them `T` (and `T'`) are locally noetherian (Mathlib's
`IsLocallyNoetherian`) and `L` is invertible (`Scheme.Modules.IsInvertible`);
nothing is asserted about other `T` or `L`.

1. **Invariance under twists from the base.** If `L, L'` on `X_T` and `N` on
   `T` are invertible and `L ≅ L' ⊗ (pullback.snd f s)^* N`, then
   `U T s L c m = U T s L' c m` for all `c, m`. So `U` depends only on the
   class of `L` in `Pic(X_T)/Pic(T)`.
2. **Base change.** For locally noetherian `T, T'`, every `s : T ⟶ S`, every
   morphism `h : T' ⟶ T` and every invertible `L` on `X_T`,
   `U T' (h ≫ s) (h_X^* L) c m = h ⁻¹ᵁ U T s L c m`, where
   `h_X = pullback.map f (h ≫ s) f s (𝟙 X) h (𝟙 _) _ _ : X_{T'} ⟶ X_T`.
3. **Shape of the decomposition.** For every invertible `L` on `X_T`:
   - `U T s L c m ≤ U T s L c (m + 1)` for all `c, m` (increasing in `m`);
   - `U T s L c m` and `U T s L c' m'` are disjoint whenever `c ≠ c'`, for
     all `m, m'`;
   - the opens `U T s L c m`, over all `c : κ` and `m : ℕ`, cover `T`
     (`⨆ c m, U T s L c m = ⊤`).
4. **Cohomology on a piece.** If `U T s L c m = ⊤`, then for every point `t`
   of `T`, `H¹(X_t, L(m)_t)` is zero and `H⁰(X_t, L(m)_t)` is not zero
   (`IsZero` and `¬ IsZero` in `ModuleCat`).
5. **Hilbert polynomials of the divisors.** Let `B : Type u` be a noetherian
   commutative ring, `s : Spec B ⟶ S`, `L` invertible on `X_B` with
   `U (Spec B) s L c m = ⊤`. Let `I` be an actual ideal sheaf of `X_B` that is a
   relative effective Cartier ideal over `Spec B`
   (`IsRelativeEffectiveCartierIdeal (pullback.snd f s) I`), and suppose
   `O(I) ≅ L(m) ⊗ (pullback.snd f s)^* N` for some invertible `N` on `Spec B`,
   where `O(I)` is the Library's `EffectiveCartierDivisor.lineBundle`. Then
   for every algebraically closed field `k : Type u` and every ring map
   `sk : B →+* k` there is `n₀` such that for all `n ≥ n₀`
   ```lean
   ((Scheme.Modules.geomFibreH0Finrank (I.subschemeι ≫ pullback.snd f s)
       (Nat.rec (motive := fun _ => I.subscheme.Modules) (𝟙_ I.subscheme.Modules)
         (fun _ M => M ⊗ (Scheme.Modules.pullback
           (I.subschemeι ≫ pullback.fst f s)).obj 𝓛X) n) k sk : ℕ) : ℚ)
     = (θ c m).eval n
   ```
   that is, `dim_k H⁰(E_k, O_E(n)) = θ c m (n)` for large `n`, where `E` is
   the closed subscheme of `I` and `E_k` its fibre over `Spec k`. This is,
   verbatim, the condition by which
   `RelativeEffectiveDivisorHilbertPiecesStatement` characterises its open
   piece `U θ` of the divisor scheme, with `θ = θ c m`.

## Source and derivation

The source is S. L. Kleiman, *The Picard scheme*, arXiv math/0504020v1
(2005), registered original `kleiman-2005-picard-scheme-arxiv-math0504020v1`,
proof of Theorem 4.8 (pp.28–30). The intended witness is `κ = ℚ[n] × ℚ[n]`,
`c = (φ, ψ)`, and `U T s L (φ, ψ) m` the set of points `t` such that

- `χ(X_t, L_t⁻¹(n)) = φ(n)` for all `n` (Kleiman's (4.8.1), p.28);
- `χ(X_t, O_{X_t}(n)) = ψ(n)` for all `n` (p.30: Kleiman makes `ψ` constant by
  passing to an open and closed part of `S`; here `ψ` is recorded in the
  index instead);
- `Hⁱ(X_t, L_t(n)) = 0` for all `i ≥ 1` and `n ≥ m` (Kleiman's (4.8.3),
  p.29, defining `P^φ_m`);
- `H⁰(X_t, L_t(m)) ≠ 0` (added; see below),

with `θ (φ, ψ) m (n) = ψ(n) − φ(n − m)`. Each property is then Kleiman's:

- Property 1: the conditions involve only the fibres `L_t`, and pullbacks of
  invertible modules on `T` are trivial on fibres (`P` is defined from
  invertible sheaves modulo `Pic(T)`, Definition 2.2).
- Property 2: cohomology commutes with the flat base change from `κ(t)` to
  `κ(t')` (p.28 for (4.8.1), p.29 for (4.8.3)).
- Property 3: openness of each condition is Kleiman's: (4.8.1) by
  EGA III 7.9.11 (p.28), (4.8.3) by Serre's theorem (p.29); the pieces are
  disjoint for distinct `φ` (p.29, "the `T'^φ` are disjoint and cover `T'`")
  and increase with `m` and cover (p.29, "as `m` varies … a nested sequence of
  open subschemes of `T`, whose union is `T`").
- Property 4: (4.8.3) at `i = 1`, `n = m`; Kleiman uses this on p.30 to make
  `Q` locally free.
- Property 5: on p.30 Kleiman sets `θ(n) := ψ(n) − φ₀(n)` and observes that
  `Z = P^{φ₀}_0 ×_P Div_{X/S}` lies in `Hilb^θ_{X/S}`. With
  `O(E) ≅ L(m) ⊗ N`, the exact sequence `0 → O(−E) → O → O_E → 0` on a
  geometric fibre gives `χ(O_{E_k}(n)) = ψ(n) − φ(n − m)`, which equals
  `dim H⁰(E_k, O_{E_k}(n))` for `n ≫ 0` by Serre vanishing. Kleiman twists by
  `m` first, via `L ↦ L(m)`, `P^φ_m ≅ P^{φ₀}_0` (pp.29–30); here the twist is
  built into `L(m)` instead of into the functor.

  **Sign correction.** Kleiman prints `φ₀(n) = φ(m + n)` for this twist. With
  his convention (4.8.1) that `φ` is the Hilbert polynomial of `L⁻¹`, this
  sign is wrong: `(L(m))⁻¹(n) = L⁻¹(n − m)`, so the map `L ↦ L(m)` gives
  `φ₀(n) = φ(n − m)`. That is the formula used above, which yields
  `θ(n) = ψ(n) − φ(n − m)`. Check: for `X = ℙ¹`, `L = O` and `m = 1`,
  `φ(n) = n + 1`; the inverse of `L(1) = O(1)` has polynomial `n = φ(n − 1)`,
  whereas `φ(n + 1) = n + 2`. A hyperplane `E` (a point) has
  `O(E) ≅ L(1)` and Hilbert polynomial `1 = ψ(n) − φ(n − 1)` with
  `ψ(n) = n + 1`, while the printed sign would give `−1`.

The added condition `H⁰(X_t, L_t(m)) ≠ 0` corrects a gap. On p.30 Kleiman
deduces from Theorem 3.13 that `T' ×_{P^{φ₀}_0} Z` is the smooth scheme
`P(Q)` and concludes that `Z → P^{φ₀}_0` is a surjection of étale sheaves.
This needs `P(Q) → T'` to be surjective, that is `H⁰(X_t, L_t) ≠ 0` at every
point. That does not follow from (4.8.3) alone: for `X = ℙ¹` over a field and
`L = O(−1)`, all `Hⁱ(L(n))` with `i ≥ 1`, `n ≥ 0` vanish, yet
`H⁰(L) = 0` and `P(Q)` is empty. With the added condition the pieces remain
open and increasing: on the locus where (4.8.3) holds, `h⁰(L_t(m)) = χ(L_t(m))`
is locally constant; and multiplying a nonzero section of `L_t(m)` by a
section of `O(1)` that does not vanish identically on the integral fibre
`X_t` gives a nonzero section of `L_t(m + 1)`. They still cover, since
`L_t(n)` is generated by global sections for `n ≫ 0`. This is a derived
correction of Kleiman's argument, not a statement found in the source.

## Conventions and scope

- The pieces are given by opens of each locally noetherian base rather than
  as subfunctors of the Picard sheaf; together with properties 1 and 2 they
  define open subfunctors of the Picard sheaf on locally noetherian tests
  (by Kleiman's p.28 argument). The intended consumer is the assembly of
  Kleiman's Theorem 4.8(2) in Task 5705, together with the companion
  statements of that task on the divisor scheme (property 5 is phrased for
  it) and on linear systems, `ProperFlatIntegralLinearSystemStatement`
  (property 4 uses its fibre-cohomology form). These are
  descriptions of intended use only; this module imports neither.
- `κ`, `θ` and `U` are existential: the proposition fixes no particular
  formula for the pieces, only the five properties.
- Twists are by `m : ℕ` only; this suffices because the pieces increase with
  `m` and cover.
- Property 5 is asserted only over noetherian affine bases `Spec B`, the
  affine opens of a locally noetherian scheme.
