# Proof of compact minimality in the actual mirabolic smooth induction

Author: Worker 806. Worker 658 verified the complete sources, source conventions
and canonical-topology specialization, and prepared this submission.

This module proves `Langlands.Whittaker.mirabolicCompactMinimality`, of type
`MirabolicCompactMinimalityStatement.{uF}`. That proposition is the p-adic
case of Bernstein–Zelevinsky (1976), Proposition 5.15(c), printed p.49. It
states that every nonzero subrepresentation `W` of the smooth mirabolic
induction `mirabolicSmoothInduced ψ n` contains the canonical compact-support
subrepresentation `mirabolicCompactSubrepresentation ψ n`.

The module first proves `MirabolicMinimality.compactMinimality T` for every
`T : F.TopologicalData`. That theorem quantifies over every rank `n` (including
`n = 0`), every bundled unitary additive character `ψ` and every actual
subrepresentation `W`. The final theorem takes `T` to be
`F.canonicalTopologicalData`, as the target requires. The two
`IsTopologicalRing` certificates are propositions, so they agree. The proof
adds no hypothesis to the target.

## Conventions

The conventions are those of the target and of `MirabolicModels`:

- `P_n = mirabolic n F` is the last-row mirabolic group in `GL_(n+1)`.
- `U_n` is its full upper unitriangular subgroup.
- `Θ = mirabolicCharacter ψ n` is the positive adjacent-entry character
  `u ↦ ψ(Σ u_(i,i+1))`.
- The smooth induction consists of functions with `f(u g) = Θ(u) f(g)` that are
  fixed under right translation by some open subgroup. `P_n` acts by
  `(s · f)(g) = f(g s)`.
- A member is compact when its projected nonzero support
  `Induction.quotientSupport` in `U \ P` is compact.

This is the unnormalized induction of BZ76 §§2.21–2.22 (printed pp.21–22).
No modular character appears anywhere in the proof. In rank `m + 1`, write
`rowOf x` for the last row of `projection x ∈ GL_(m+1)`, the upper-left block of
`x`. This is the existing `MirabolicWhittaker.rowOf` definition. Write `u(c)` for the radical element with last column `c`, `levi g` for
the block matrix `diag(g, 1)`, and `successor : P_m → P_(m+1)` for the block
embedding. Every `x` equals `u(lastColumn x) · levi(projection x)`
(`eq_radicalElement_mul_levi`). The box `B_N = latticeBox T (m+1) N` is
`(π^(-N) O)^(m+1)`, built from the Library lattices `T.additiveLattice`. It
lives in the helper module `Langlands.Representation.Derivative.MirabolicLatticeBox`.

## Route

**Source route.** BZ76 proves 5.15(c) on printed p.50 with derivative theory.
A nonzero `π ⊆ τ_P` is nondegenerate. By §5.12, Corollary 5.14 and the
discussion on p.49, its completely nondegenerate part is a direct sum of copies
of `τ_P⁰`. Part 5.15(b), proved by Frobenius duality and
`dim (Φ⁻)^(n-1)(τ_P⁰) = 1`, makes every map `τ_P⁰ → τ_P` a multiple of the
standard embedding. Hence the image is the canonical compact subspace.

**Implemented route.** The Lean proof uses none of these ingredients:
derivatives, the `Φ⁺/Φ⁻` equivalences, Frobenius duality and scalar uniqueness
5.15(b) are all absent. It is a direct induction on the rank with explicit
functions. In rank `m + 1`, restriction along `successor` reduces to rank `m`.
Finite character sums over the radical cut functions down to sets where the
last row lies in a box. Levi translation moves such boxes to every last row.
Compactness then assembles the whole function.

### Generic facts (over any topological field)

A function `h : P → ℂ` is *realized* in `W` (`Realized ψ W h`) if it is the
evaluation of a member of `W`. Realized functions are closed under addition,
finite sums and right translation (`realized_add`, `realized_sum`,
`realized_translate`). A member realized in `W` lies in `W` (`mem_of_realized`).

1. **Radical translation** (`eval_mul_radicalElement`):
   `f(x u(c)) = ψ(rowOf x · c) f(x)`. Indeed `x u(c) = u(projection x · c) x`
   (`levi_mul_radicalElement`), and `Θ(u(w)) = ψ(w_last)`
   (`MirabolicWhittaker.mirabolicCharacter_radicalElement`). The last coordinate of `projection x · c` is
   `rowOf x · c`.
2. **Restriction** (`res`, `resRep`). Put `res f (p) = f(successor p)`. The
   adjacent entry `(m, m+1)` of `successor u` is zero, so
   `Θ_(m+1)(successor u) = Θ_m(u)` (`MirabolicWhittaker.mirabolicCharacter_successor`). Thus
   `res f` is left `U_m`-covariant. It is smooth with the preimage of an open
   stabilizer of `f`. Restriction intertwines translation by `successor h` with
   translation by `h`, so the image `resRep W` of `W` is a subrepresentation.
   It is nonzero when `W` is (`resRep_ne_bot`): translate a member with
   `g(x) ≠ 0` by `x` and evaluate at `1`.
3. **Restriction keeps compact support** (`res_mem_compact`). The compact
   support of `φ` lifts to a compact set `C ⊆ P_(m+1)`
   (`QuotientIntegration.leftQuotient_exists_isCompact_image`). Suppose
   `φ(successor p) ≠ 0`. Then `successor p = u c` with `u ∈ U_(m+1)` and
   `c ∈ C`. Hence `projection c ∈ P_m` and `p ∈ U_m · projection c`. So the
   support of `res φ` lies in the image of the compact set of mirabolic points
   of `projection(C)`. That support is closed (`Induction.isClosed_quotientSupport`).
4. **Agreement from restrictions** (`eval_eq_of_res_eq`). Let `f` and `φ` have
   the same restriction, and let both be fixed by right translation by
   `levi(J)` for a subgroup `J ⊆ GL_(m+1)`. Then `f(x) = φ(x)` whenever
   `rowOf x` is the last row of an element of `J`. In that case
   `projection x = a j` with `a ∈ P_m` and `j ∈ J` (`lastRow_mem_image_iff`).
   So `x = u(c) · successor a · levi j`, and both sides reduce by step 1 to
   restrictions.

### p-adic steps

Let `cut_N^v h` be `x ↦ [rowOf x − v ∈ B_N] h(x)` (`cut`).

5. **Cuts stay realized** (`realized_cut`). Let `g ∈ W`, a vector `v` and a
   level `N` be given. Choose `l` so small that `u(B_l)` fixes `g` and
   `ψ(v · c) = 1` on `B_l`. Put `M = n(ψ) − N`, where `n(ψ)` is
   `T.additiveConductor ψ`, and let `Q = B_M / B_min(l,M)`. This quotient is
   finite (`finite_latticeBox_quotient`). The member
   `g' = |Q|⁻¹ Σ_(c ∈ Q) ψ(−v · c) u(c) · g` lies in `W`. By step 1,
   `g'(x) = |Q|⁻¹ Σ_(c ∈ Q) ψ((rowOf x − v) · c) g(x)`.
   - If `rowOf x − v ∈ B_N`, every term has character value `1`
     (`character_dotProduct_eq_one`), so `g'(x) = g(x)`.
   - If not, the character `c ↦ ψ((rowOf x − v) · c)` of `B_M` is nontrivial
     (`mem_latticeBox_of_forall_character_eq_one`). Either `g(x) = 0`, or this
     character is trivial on `B_l`, because `ψ(rowOf x · c) = 1` there by step 1
     and `ψ(v · c) = 1`. In the second case the sum over `Q` vanishes
     (`sum_out_eq_zero`). In both cases `g'(x) = 0`.
6. **Core step** (`exists_cut_one`). Assume minimality in rank `m`. Let `W ≠ ⊥`
   in rank `m + 1`, let `φ` be compact, and let `e` be the last row of the
   identity. By steps 2 and 3 and the induction hypothesis there is `f ∈ W`
   with `res f = res φ`. Let `J` be the preimage under `levi` of the
   intersection of open stabilizers of `f` and `φ`. Then `J` is an open
   subgroup, so its last rows contain a neighbourhood of `e`
   (`lastRow_image_mem_nhds`), and therefore `e + B_N` for some `N`
   (`exists_latticeBox_subset`). On `{rowOf x − e ∈ B_N}` step 4 gives `f = φ`.
   Thus `cut_N^e φ = cut_N^e f`, which is realized by step 5.
7. **Levi translation** (`exists_cut_of_one`). Fix `x₀` and put
   `g₀ = projection x₀`. Apply step 6 to the compact member `levi(g₀) · φ`,
   then translate by `levi(g₀)⁻¹`. Then
   `rowOf(x levi(g₀)⁻¹) − e = (rowOf x − rowOf x₀) g₀⁻¹`. Choose `N'` with
   `B_(N') g₀⁻¹ ⊆ B_N` and cut again at `rowOf x₀` (step 5). This shows that
   `cut_(N')^(rowOf x₀) φ` is realized.
8. **Compactness** (`mem_of_forall_cut`). Let `C` be the compact lift of the
   support of `φ`. Cover `C` by the open sets `{rowOf x − rowOf x₀ ∈ B_(N(x₀))}`
   and take a finite subcover indexed by `t`. Let `L` be a common level below
   every `N(x₀)` with `x₀ ∈ t`. For each `x₁ ∈ C`, cutting the realized
   function of some `x₀ ∈ t` by `B_L` at `rowOf x₁` shows that `cut_L^(rowOf x₁) φ`
   is realized. Cover `C` again by `L`-boxes, with finite index set `t₂`. Let
   `S` be the set of classes of `rowOf x₁` (`x₁ ∈ t₂`) in `F^(m+1) / B_L`. If
   `φ(x) ≠ 0`, then `x = u c` with `c ∈ C` and `rowOf x = rowOf c`, since `rowOf` is
   left `U`-invariant (`MirabolicWhittaker.rowOf_upperUnipotent_mul`). So the class of `rowOf x` lies in
   `S`. Hence `φ = Σ_(γ ∈ S) [class(rowOf x) = γ] φ`. Each term is some
   `cut_L^(rowOf x₁) φ`, so it is realized, and `φ ∈ W`.
9. **Induction** (`compactMinimality`). For `n = 0` the group `P_0` is
   trivial: a member `g ∈ W` with `g(x) ≠ 0` gives
   `φ = (φ(x)/g(x)) • g ∈ W`. The inductive step chains steps 6, 7 and 8.

## Normalization, character and support comparison

- **Induction.** The source's `τ_P = Ind(P,U,Θ)` and `τ_P⁰ = ind(P,U,Θ)`
  (§5.7, p.45) are the Library models without modular twist. The proof never
  changes normalization.
- **Character.** The proof uses only two restrictions of the positive
  character `Θ`: to the radical, `u(c) ↦ ψ(c_last)`, and to `successor(U_m)`,
  where it equals `Θ_m`.
- **Support.** Compactness is the target's compactness of projected nonzero
  support in `U \ P`. It enters only through a compact lift in `P`. The cut
  functions depend on the last row, which is left `U`-invariant, so they
  preserve covariance.
- **Smoothness.** The models use open right stabilizers rather than compact
  open ones. In the p-adic setting these give the same functions, and the
  proof uses only open stabilizers.
- **Canonical image.** The conclusion concerns the canonical compact image
  itself, as in the target. No abstract copy of `τ_P⁰` appears.

## Dependencies

- Library: `Group.GL.MirabolicProjection` and `Group.GL.MirabolicRadical`
  (projection, radical, Levi and successor); `Derivative.MirabolicCharacter`
  (`theta_radicalElement`, `theta_eq_standardCharacter_comp`);
  `RankinSelberg.LastRowCompactOrbitProof` (`lastRow_image_mem_nhds`,
  `lastRow_mem_image_iff`); `RankinSelberg.QuotientIntegrals` (last-row
  products); `Induction.CompactQuotientProof`
  (`isClosed_quotientSupport`); `Analysis.Local.QuotientTopology` (compact
  lifts).
- Shared elementary facts: `Whittaker.MirabolicCompactWhittakerUniqueness`
  (`MirabolicWhittaker.rowOf`, its upper-unipotent invariance, and the successor
  and radical character identities). The minimality argument does not use its
  uniqueness theorem.
- Helper: `Langlands.Representation.Derivative.MirabolicLatticeBox`
  (lattice boxes, their finite quotients and the character-sum lemmas).

## Source

I. N. Bernshtein and A. V. Zelevinskii, *Representations of the group GL(n,F)
where F is a non-Archimedean local field*, Russian Math. Surveys 31:3 (1976),
1–68. Registered source `bernstein-zelevinsky-1976-representations-gln`. I read
Proposition 5.15 and its proof on printed pp.49–50 (zero-based PDF indices
48–49). Worker 658 also read the original printed pp.21–22, 44–45 and 48–50,
including a visual check of p.50, and verified the registered source SHA256
`72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.
The implemented proof follows a different, elementary route, described above.
No source-specific registered erratum was found in the current project notes,
Library notes or literature index.
