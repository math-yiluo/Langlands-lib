# V 5 at the Galois-fixed points from the wall invariance of `m(u)` (KP Corollary 9.4.10)

Author: Worker 91.

Lean module: `Langlands.Geometry.Building.UnramifiedFixedOppositeReduction`.

This module proves that `UnramifiedFixedWallInvarianceStatement` (module of the same name)
implies the published `UnramifiedFixedOppositeStatement` (module
`UnramifiedFixedLocusStatement`). The latter is axiom V 5 of KP Definition 6.1.2 for the
restricted families at the Galois-fixed points of an unramified apartment. Neither
proposition is proved here.

## Declarations

| Lean name | Kind | Content |
| --- | --- | --- |
| `exists_eval_eq_of_ne_zero` | theorem | A nonzero character `a` of a split torus `S` takes every real value `r` on `V(S)`. |
| `unramifiedFixedOpposite_core` | theorem | V 5 at one fixed point `x`, from the wall invariance for the same data (hypothesis `hW`), with explicit binders and instances. |
| `unramifiedFixedWallInvariance_apply` | theorem | `UnramifiedFixedWallInvarianceStatement` specialized to given data, with explicit binders. |
| `UnramifiedFixedOppositeReductionStatement` | `def … : Prop` | The implication `UnramifiedFixedWallInvarianceStatement.{u} → UnramifiedFixedOppositeStatement.{u}`. |
| `unramifiedFixedOpposite_of_wallInvariance` | theorem | Proof of that implication. |
| `unramifiedFixedOppositeReduction` | theorem | The same, stated as `UnramifiedFixedOppositeReductionStatement.{u}`. |

The statement `UnramifiedFixedOppositeReductionStatement` only names the implication. Both
sides are published or staged statements; neither is asserted.

## Notation

The data are those of `UnramifiedFixedOppositeStatement`: `K = inertiaFixedField F`, the
maximal split torus `iS : S → G`, the torus `T` with `f : S → T` and `iT_K` maximal split in
`G_K`, opposite factor pairs `hE` for `iT_K`, and the apartment class `D` of `(G_K, T_K)`.
For `y : D.Apartment` write `φ y` for the torus-then-field restriction
`torusFieldRestrictedRootFunctionFamily … (D.isRootDatumValuation_of_mem y.mem) f_K`, a
root-function family for `(G, S)`. "Fixed" means fixed by
`RootFunctionFamily.galoisAction F K T G σ` for every `σ : K ≃ₐ[F] K`. `V(S)` is the real
cocharacter space and `eval S a` the evaluation of a character `a` on it. For a root-function
family `ψ`:

- `(v +ᵥ ψ) b e = ψ b e + eval S b v` (`RootFunctionFamily.vadd_apply`);
- `(n • ψ) b e = ψ (n⁻¹ · b) (n⁻¹ e n)` for `n ∈ N(F)` (`RootFunctionFamily.smul_apply`);
- `n • (v +ᵥ ψ) = (n • v) +ᵥ (n • ψ)` (`RootFunctionFamily.smul_vadd`);
- `eval S a (n • v) = eval S (n⁻¹ · a) v` (`eval_normalizer_smul`).

## Implemented proof

### `exists_eval_eq_of_ne_zero`

By the published `IsSplitTorus.exists_pairing_eq_pos` there are an integer `d > 0` and a
cocharacter `ζ` with `⟨a, ζ⟩ = d`. Then `v = (r / d) ⊗ ζ` has `eval S a v = (r / d) · d = r`
(`eval_tmul`).

### `unramifiedFixedOpposite_core`

Fix a fixed point `x`, a relative root `a`, `g ∈ U_a(F)` with `g ≠ 1`, and
`g', g'' ∈ U_{-a}(F)` with `m = g' g g'' ∈ N(F)`. We show `φ x (-a) g' + φ x a g = 0`.

1. **Fixed translates.** For `v : V(S)`, put `y = descentCocharacterMap v +ᵥ x`. It lies in
   `D.Apartment` (`D.vadd_mem`). It is fixed by the published
   `RootFunctionFamily.galoisAction_vadd` and `galoisCocharacterAction_descentCocharacterMap`.
   Its restriction is `φ y = v +ᵥ φ x` by the published
   `torusFieldRestrictedRootFunctionFamily_descent_vadd`. This is the argument of
   `unramifiedValuationDescent_core` (module `UnramifiedValuationDescentReduction`).
2. **Finite values.** For a relative root `b` and `e ∈ U_b(F)` with `e ≠ 1`, the value
   `φ y b e` is a real number. Otherwise it would be `⊤`, and the published
   `torusFieldRestrictedRootFunctionFamily_eq_top_iff` would force `e = 1`.
3. **The reflection.** `(g', g'')` is an opposite factor pair of `g`
   (`RelativeRoot.IsOppositeFactorPair`). The published `IsOppositeFactorPair.weylAction_eq_neg`
   gives `m · a = -a`, hence `m⁻¹ · a = -a` and `m · (-a) = a`.
   `IsOppositeFactorPair.factors_ne_one` gives `g' ≠ 1`.
   `neg_mem_relativeRoots_of_weylAction_eq_neg` shows that `-a` is a relative root.
4. **The same `m` for `g'`.** Put `q = m g'' m⁻¹`. It lies in `U_{-(-a)}(F) = U_a(F)`, by the
   published `conj_mem_rootGroupPoints` and `m · (-a) = a`. Also `g ∈ U_{-(-a)}(F)`. A direct
   group computation gives `q g' g = m`, because `m⁻¹ g' g = g''⁻¹`. So `(q, g)` is an opposite
   factor pair of `g' ∈ U_{-a}(F)` with the same product `m` (KP Remark 2.11.18:
   `m(u) = m(u')`).
5. **Two wall points.** Let `r = φ x a g` and `r' = φ x (-a) g'` (real by step 2).
   - Choose `v` with `eval S a v = -r` and the fixed point `z` with `φ z = v +ᵥ φ x`. Then
     `φ z a g = r + (-r) = 0`, and the hypothesis `hW` gives `m • φ z = φ z`.
   - Choose `v'` with `eval S (-a) v' = -r'` and the fixed point `z'` with
     `φ z' = v' +ᵥ φ x`. Then `φ z' (-a) g' = 0`. The hypothesis `hW`, applied to the root
     `-a`, the point `g'` and the pair `(q, g)`, gives `m • φ z' = φ z'` (after identifying the
     normalizer point `⟨q g' g, _⟩` with `m` by `Subtype.ext`).
6. **Comparison.** `φ z' = (v' - v) +ᵥ φ z` (`vadd_vadd`). By `smul_vadd` and `m • φ z = φ z`,
   the second invariance becomes `(m • (v' - v)) +ᵥ φ z = (v' - v) +ᵥ φ z`. Evaluate both sides
   at `(a, g)`. Since `φ z a g = 0`, this gives `eval S a (m • (v' - v)) = eval S a (v' - v)`.
   The left side is `eval S (m⁻¹ · a) (v' - v) = -eval S a (v' - v)` (`eval_normalizer_smul`,
   `eval_neg_char`). Hence `eval S a (v' - v) = 0`, i.e. `eval S a v' = eval S a v = -r`.
   Since `eval S (-a) v' = -r'`, also `eval S a v' = r'`. So `r' = -r`, and
   `φ x (-a) g' + φ x a g = r' + r = 0`.

### `unramifiedFixedOpposite_of_wallInvariance`

The target unfolds to the binders of `UnramifiedFixedOppositeStatement`. As in the published
`unramifiedValuationDescent_of_fixedLocus`, the proof introduces them and installs the instances
`IsAffineHom G.X.hom`, `Smooth G.X.hom` and the two monomorphism instances that the statement
creates with `letI`/`haveI`. It then applies `unramifiedFixedOpposite_core`, with `hW` supplied
by `unramifiedFixedWallInvariance_apply`. The two `_apply`-style theorems and the final theorem
use `maxHeartbeats 8000000` for elaboration, as in `UnramifiedValuationDescentReduction`.

The proof uses neither Levi transport nor any building of `G_K`. Only the wall invariance at
two fixed points is used.

## Provenance

Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach* (2023), registered as
`kaletha-prasad-2023-bruhat-tits-new-approach` (SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`):

- Corollary 9.4.10 and its proof, printed p. 350 / PDF p. 381. KP deduce
  `ψ^{u'}_{-a} = -ψ^u_a` from the last assertion of Proposition 9.4.9 and
  `m(u) = m(u') = m(u'')`.
- Remark 2.11.18, printed p. 136 / PDF p. 167, for `m(u) = m(u')` and the formula
  `m(u) = (m(u) u'' m(u)⁻¹) u' u`. Step 4 uses this formula.
- Definition 6.1.2, axiom V 5, printed p. 199 / PDF p. 230.

The Lean proof follows KP's argument on the side of the restricted families. The wall of `g` and
the wall of `g'` are both fixed by `m`. Since `m` reverses `a`, the two walls coincide, and
that is V 5. The KP version uses the apartment `A(S)`; here translates along `V(S)` stand in
for its points.
