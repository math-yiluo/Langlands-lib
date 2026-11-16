# Proof of `RealPrincipalSeriesSubquotientStatement` (Harish-Chandra's subquotient theorem for `GL_n(ℝ)`)

Module: `Langlands.Representation.Archimedean.RealPrincipalSeriesSubquotientProof`.

Main theorem:
`Langlands.Archimedean.realPrincipalSeriesSubquotient :
Langlands.Archimedean.RealPrincipalSeriesSubquotientStatement.{uV}`. The theorem uses only the
axioms `propext`, `Classical.choice` and `Quot.sound`.

## What is proved

`RealPrincipalSeriesSubquotientStatement` is in the Library module
`Langlands.Representation.Archimedean.RealJacquetSubquotientReduction`. Let `V` be an irreducible
admissible `(𝔤𝔩_n(ℝ), O(n))`-module, given as `ρ`, `π` with `IsRealGKModule n ρ π`,
`IsIrreducibleGKModule ρ π` and `IsAdmissibleGKModule ρ`. Then there are:

- a list `cs` of `n` characters of `GL_1(ℝ)`;
- a subspace `W` of the `O(n)`-finite functions of the principal series
  `realStandardModule n (cs.map RealBlock.character)`;
- a surjective linear map `T : W → V` with `IsRealSubquotientMap n ρ π W T`.

`IsRealSubquotientMap` says that `W` is stable under right translation by `O(n)` and under right
derivatives, and that `T` intertwines these with `ρ` and `π`. So `V ≅ W / ker T` is a
subquotient of a principal series.

## Provenance

The proof follows Lepowsky's algebraic proof (J. Lepowsky, *Algebraic results on representations
of semisimple Lie groups*, Trans. Amer. Math. Soc. 176 (1973), 1–44; Library source
`lepowsky-1973-algebraic-results-semisimple-lie-groups`). It uses the presentation in N. R.
Wallach, *Real Reductive Groups I* (1988), §3.5, Theorem 3.5.6 and its proof in 3.5.2–3.5.11
(source `wallach-1988-real-reductive-groups-i`). The objects match as follows:

- `Hom_K(V_γ, V)` is the space `gkIntertwiners ρ d τ` of `K`-intertwiners from a matrix
  representation `τ`.
- Wallach's algebra `U(𝔤)^K` acting on `Hom_K(V_γ, V)` (with `U(𝔤)I_γ` acting by `0`) becomes the
  algebra `Bsub τ` of `K`-invariant matrices over `U(𝔤)`, acting through `act`.
- Wallach's projection `p_γ` and its evaluation on principal series become the polynomial matrix
  `ĉ = chat τ`.

The implemented proof differs from Wallach's in three places. None of them needs the
Harish-Chandra isomorphism or PBW linear independence.

1. **Projection and central elements.** Wallach defines `p` with the PBW decomposition
   `U(𝔤) = U(𝔞) ⊗ U(𝔨) ⊕ 𝔫U(𝔤)` and computes `p_γ(z)` for central `z` with the Harish-Chandra
   homomorphism (3.5.6–3.5.8). Here the polynomial representatives `Q` are built by induction on
   word length. They are made unique by separating with all principal series and Frobenius
   reciprocity. Central elements are scalar polynomials by a Jacquet-module argument on `U(𝔤)`
   itself (`RealSubquotientProjection`).
2. **Injectivity (Wallach Lemma 3.5.9)** is proved with the Library's symbol calculus, ordered
   spanning, and the spectral theorem for real symmetric matrices (`RealSubquotientSymbol`).
3. **Nilpotency (Wallach 3.5.10).** Wallach uses `q(Z(𝔤)) = U(𝔥)^W`. Here Gelfand's elements
   `tr(E^l)` are used: their polynomials have top parts the power sums, so `ℂ[a]` is finite over
   them and the fibre is finite. A determinant trick and the Nullstellensatz complete the step
   (`RealSubquotientFinite`). The final step (Wallach 3.5.11 with Proposition 3.5.4) is replaced
   by a reduction to one principal series and a graph argument (`RealSubquotientAverage`,
   `RealSubquotientMain`).

## Helper modules

The proof uses seven helper modules, submitted with it. Each has its own Markdown file.

- `RealSubquotientEval`: principal series `PS a e`, upper triangular derivatives at `1`,
  `IsTypeDerivative`, sign functionals, and Frobenius reciprocity
  (`exists_frobenius_intertwiner`).
- `RealSubquotientProjection`: symbols, polynomial representatives `Q`, the action `act`, `InB`,
  `chat`, and central elements (`exists_Q_central`).
- `RealSubquotientSymbol`: Claim B (`mem_of_symbol_vanish`), the descent, and injectivity
  (`act_eq_zero_of_chat_eq_zero`).
- `RealSubquotientFinite`: Gelfand elements `Cgel`, `xiPoly`, `Bsub`, finiteness
  (`mem_spanBox`, `finite_fibre`), the determinant trick, and nilpotency
  (`exists_pow_act_eq_zero`).
- `RealSubquotientAverage`: Haar averaging (`avg`, `act_avg`, `avg_mem_Bsub`), simplicity
  (`exists_act_eq_of_irreducible`), and reduction to one principal series
  (`exists_single_kill`).
- `RealSubquotientKType`: a `K`-type as matrix data (`exists_ktype`).
- `RealSubquotientMain`: killing `T₀` (`act_T0_eq_zero_of_kill`) and the graph argument
  (`exists_subquotient_of_kill`).

## Declarations of this module

- `RealSubquotient.act_sum_right`: `b · ∑ᵣ Tᵣ = ∑ᵣ b · Tᵣ`.
- `RealSubquotient.exists_spanning_intertwiners`: if `gkIntertwiners ρ d τ` is
  finite-dimensional, it is spanned by finitely many intertwiners `ω₁, …, ω_m`, taken from a
  basis.
- `realPrincipalSeriesSubquotient`: the main theorem.

## The proof of `realPrincipalSeriesSubquotient`

Let `V` be irreducible and admissible.

1. **A `K`-type.** `exists_ktype` gives `d > 0`, a continuous `τ : O(n) →* Mat_d(ℂ)` with
   derivative `D`, and a nonzero `K`-intertwiner `T₀ : ℂ^d → V`.
2. **Infinitesimal character.** The Library's
   `InfinitesimalCharacter.realGKModuleInfinitesimalCharacter` says that central elements act on
   `V` by scalars. Let `λ_l` be the scalar of the Gelfand element `Cgel n l`.
3. **Finite fibre.** Let `ξ_l = xiPoly τ (Cgel n l)`. By `xiPoly_Cgel_top`, `ξ_l` has degree
   `≤ l` with top part the power sum `p_l`. So `finite_fibre` makes the fibre
   `Z = {a : ξ_l(a) = λ_l for all l}` finite.
4. **Finitely many principal-series intertwiners.** For each pair `s = (a, e)`, the space
   `gkIntertwiners (realStandardRep n (psList a e)) d τ` is finite-dimensional. This is the
   Library's `realStandardAdmissible` applied to the continuous `τ`. `exists_spanning_intertwiners`
   chooses spanning families `ω_{s,1}, …, ω_{s,m(s)}`. The finite index set `F` consists of the
   `(s, r)` with `a ∈ Z`, any sign vector `e`, and `r ≤ m(s)`.
5. **Killing.** Let `b ∈ Bsub τ` kill every `ω_i`, `i ∈ F`. Then `b` kills every
   `K`-intertwiner into `PS a e` for `a ∈ Z`, because these are combinations of the `ω_{(a,e),r}`
   (`act_sum_right`, `act_smul_right`). So `b · T₀ = 0` by `act_T0_eq_zero_of_kill`.
6. **Cyclicity of `T₀`.** If `b · T₀ ≠ 0` for `b ∈ Bsub τ`, then
   `exists_act_eq_of_irreducible` gives a matrix `c` with `c · (b · T₀) = T₀`. Its average
   `avg τ c` is `K`-invariant with the same property (`act_avg`, `avg_mem_Bsub`).
7. **One principal series.** `exists_single_kill` gives one `((a, e), r) ∈ F` and
   `c ∈ Bsub τ` such that every `b ∈ Bsub τ` killing `S₀ := c · ω_{(a,e),r}` kills `T₀`. `S₀` is
   a `K`-intertwiner into `PS a e` by `act_mem`. The Library's
   `InfinitesimalCharacter.rho_mul_envelopingAction` gives the compatibility of `ρ` with
   `envelopingAction` that `act_mem` needs.
8. **Graph argument.** `exists_subquotient_of_kill` gives `W ≤ PS a e` and a surjective
   `T : W → V` with `IsRealSubquotientMap n ρ π W T`.
9. **Conclusion.** Take `cs = List.ofFn (RealJacquetFrobenius.chars a e)`. It has length `n`,
   and `cs.map RealBlock.character = psList a e`, so `PS a e` is the `O(n)`-finite part of
   `realStandardModule n (cs.map RealBlock.character)`.

## Implementation note

Lean does not synthesize the `AddCommGroup` instance on the subtype
`gkIntertwiners (realStandardRep n ds) d τ` for these submodule-valued modules. So
`Module.finBasis` cannot be applied there directly. `exists_spanning_intertwiners` is therefore
stated for an arbitrary module, where the instance is local, and then applied to the principal
series.
