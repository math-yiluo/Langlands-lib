# The constant-term formula for adelic Eisenstein series (proof)

Module `Langlands.Global.AdelicEisensteinConstantTermProof`. It proves

`Langlands.Global.eisensteinConstantTerm : EisensteinConstantTermStatement.{u}`,

the statement of module `Langlands.Global.AdelicEisensteinConstantTermStatement`, with all its
hypotheses and its universe `u`. This is Bernstein–Lapid Lemma 6.10, formula (6.17), and
Mœglin–Waldspurger II.1.7. Fix the data of the statement:

- a parabolic `P` with Levi `M`, a split component `A` and an Iwasawa compact `K`;
- an automorphic function `φ` for `U(𝔸)M(F)`;
- a parabolic `Q = M_Q V`;
- representatives `w_i` of `Q(F) \ G(F) / P(F)`, with the parabolics `P'_i` and `Q'_i` of the
  geometric lemma.

The statement then gives `R` such that, for every `R`-regular `λ` and every `g ∈ G(𝔸)`, three
conclusions hold. The intertwining integrands are integrable. Their integrals are summable over
`Q'_i(F) \ Q(F)`. The constant term of `E(φ, λ)` along `V` at `g` is the sum over `i` and over
`Q'_i(F) \ Q(F)` of the intertwining integrals of the constant term of `φ` along `U'_i`, with
the restricted parameter, at `γ g`.

## The proof

The theorem is one application of three Library results:

- `Langlands.Global.eisensteinConstantTerm_of_convergence_of_unfolding` (module
  `Langlands.Global.EisensteinConstantTerm.Reduction`) proves `EisensteinConstantTermStatement`
  from `EisensteinAbsoluteConvergenceStatement` and `GeometricLemmaUnfoldingStatement`;
- `Langlands.Global.eisensteinAbsoluteConvergence` (module
  `Langlands.Global.AdelicEisensteinConvergenceProof`) proves
  `EisensteinAbsoluteConvergenceStatement`;
- `Langlands.Global.geometricLemmaUnfolding` (module
  `Langlands.Global.EisensteinConstantTerm.GeometricLemmaUnfoldingProof`) proves
  `GeometricLemmaUnfoldingStatement`.

All three are used at the universe `u` of the target, and no hypothesis of the target is
dropped. The Lean proof is the term
`eisensteinConstantTerm_of_convergence_of_unfolding eisensteinAbsoluteConvergence
geometricLemmaUnfolding`.

## The mathematics behind the three results

The reduction follows the proof of BL Lemma 6.10:

1. `R` is the constant of absolute convergence for `φ`. For `R`-regular `λ`, the Eisenstein
   series of `φ_λ = φ · m_P^λ` converges absolutely, uniformly for the argument in a compact
   set. Since `V(F) \ V(𝔸)` is compact, this bound holds on all of `V(𝔸) g`.
2. The double cosets `Q(F) w_i P(F)` partition `G(F)`. Each `P(F) \ P(F) w_i⁻¹ Q(F)` is in
   bijection with `(Q(F) ∩ w_i P(F) w_i⁻¹) \ Q(F)`. Integrating over `V(F) \ V(𝔸)` and
   exchanging sum and integral, which the bound permits, gives a sum over `i` and over
   `Q'_i(F) \ Q(F)` of integrals over `(V ∩ w_i P w_i⁻¹)(F) \ V(𝔸)`.
3. `geometricLemmaUnfolding` identifies each such integral with the integral of the constant
   term of `φ_λ` along `U'_i` over `(V'_i(F) ∩ w_i U'_i(𝔸) w_i⁻¹) \ V'_i(𝔸)`, the quotient on
   which the Library's `intertwiningMeasure` lives. It is proved from the dynamic description
   of the parabolics `P'_i` and `Q'_i` and from the semidirect decompositions of their
   unipotent radicals.
4. The twists match: `m_{P'_i}^{λ ∘ f_i} = m_P^λ`, since `K` is Iwasawa for both `P` and
   `P'_i`. The factor `m_P^λ` is left `U'_i(𝔸)`-invariant and comes out of the constant term
   along `U'_i`.

Integrability and summability (conclusions 1 and 2) come from the same computation for `|φ_λ|`.
The Markdown pages of the three modules above describe their proofs in detail.

## Sources

- J. Bernstein and E. Lapid, *On the meromorphic continuation of Eisenstein series*, J. Amer.
  Math. Soc. 37 (2024), registered as `bernstein-lapid-2024-meromorphic-continuation-eisenstein`:
  Lemma 6.10, formula (6.17), and its proof, journal pp. 208–209 (PDF pages 22–23); the Bruhat
  decomposition, §6.7, journal pp. 206–207.
- C. Mœglin and J.-L. Waldspurger, *Spectral decomposition and Eisenstein series* (1995),
  registered as `moeglin-waldspurger-1995-spectral-decomposition`: II.1.7, printed pp. 91–93.
  BL describe their Lemma 6.10 as a straightforward generalization of this computation, without
  cuspidality.
