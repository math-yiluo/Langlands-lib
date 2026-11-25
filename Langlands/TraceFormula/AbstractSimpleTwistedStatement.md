# The abstract simple twisted trace formula

`Langlands.TraceFormula.AbstractSimpleTwistedTraceFormulaStatement` is a proposition
definition. It supplies no proof. The statement is proved by
`abstractSimpleTwistedTraceFormula` (module `Langlands.TraceFormula.AbstractSimpleTwistedProof`).

It is the geometric side of the simple twisted trace formula for a general locally compact
group, a discrete subgroup and a continuous automorphism. It says that the trace of
`R(f) ∘ I_θ` on `L²(Γ \ G)` is a finite sum of volumes times twisted orbital integrals. It
contains no spectral side and no adelic group. Those belong to the later specialization to
`GL_n` over a global field.

## Setting

The statement quantifies over:

- a group `G` (universe `uG`) that is a Hausdorff, locally compact, second-countable
  topological group with its Borel σ-algebra;
- a measure `μG` on `G` that is a left Haar measure and is also right invariant, so `G` is
  unimodular;
- a subgroup `Γ` whose subspace topology is discrete, and a measure `ν` on the coset space
  `Γ \ G`. Here `Γ \ G` is the Library's `QuotientIntegration.LeftQuotient Γ`, the space of
  cosets `Γ * g`, with any Borel σ-algebra placed on it. The measure `ν` is compatible with
  `μG` and the counting measure on `Γ`, in the sense of the Library's predicate
  `QuotientIntegration.IsCompatible Γ μG Measure.count ν`
  (`Langlands/Analysis/Local/QuotientMeasure.lean`). Its fields say that `ν` is nonzero,
  regular and invariant under every right translation `rightTranslate Γ g`, and that for
  every continuous compactly supported `h : G → ℂ` the average
  `Γ g ↦ ∫ γ, h(γ g) d(count)` (`quotientAverage`) is `ν`-integrable with
  `∫_{Γ \ G} (∫ γ, h(γ g) d(count)) dν = ∫_G h dμG`. The inner integral is the Bochner
  integral for the counting measure on `Γ`;
- a topological group automorphism `θ : G ≃ₜ* G` with `θ x ∈ Γ ↔ x ∈ Γ` for every `x`, which
  preserves `μG`, and whose induced homeomorphism `θ̄` of `Γ \ G`
  (`QuotientIntegration.quotientAutomorphism Γ θ hθΓ`) has an inverse that preserves `ν`;
- a homomorphism `π : G →* (Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν)` with isometric values and the
  measurability needed by `Langlands.Analysis.integratedIsometricAction`, such that
  `π g φ` is represented `ν`-almost everywhere by `q ↦ φ(q g)` (the Library's
  `rightTranslate Γ g`). So `π` is the right regular representation. It is supplied with its
  defining property, as in the Library's
  `CompactQuotientConvolutionTraceClassStatement`;
- a continuous compactly supported function `f : C_c(G, ℂ)`.

Write `R(f) = integratedIsometricAction μG π … f …`, the operator `φ ↦ ∫_G f(g) π(g) φ dμG(g)`,
and `I_θ = twistOperator Γ θ hθΓ ν hθν`, the operator `φ ↦ φ ∘ θ̄⁻¹` of the module
`Langlands.TraceFormula.TwistedOrbital`.

## Hypotheses

1. `R(f) ∘ I_θ` is trace class (`Langlands.Analysis.OperatorIdeals.IsTraceClass`).
2. The support condition: there is a compact set `C ⊆ G` such that every `x ∈ G` with
   `f(x⁻¹ γ θ(x)) ≠ 0` for some `γ ∈ Γ` is `g y` with `g ∈ Γ` and `y ∈ C`,

   `∃ C : Set G, IsCompact C ∧ ∀ x : G, ∀ γ ∈ Γ, f (x⁻¹ * γ * θ x) ≠ 0 → ∃ g ∈ Γ, ∃ y ∈ C, x = g * y`.

   So the function `x ↦ Σ_{γ ∈ Γ} |f(x⁻¹ γ θ(x))|` on `Γ \ G` vanishes outside the image of the
   compact set `C`. The condition holds for every `f` when `Γ \ G` is compact:
   `Langlands.TraceFormula.exists_isCompact_twistedSupport_of_compactSpace` (module
   `Langlands.TraceFormula.TwistedGeometricUnfolding`) gives such a `C` for every function on `G`.
3. A natural number `n` and representatives `r : Fin n → Γ` are given. They are pairwise not
   `Γ`-`θ`-conjugate: `IsTwistedConjugate Γ θ (r i) (r j)` implies `i = j`.
4. They cover every relevant class: if `γ ∈ Γ` and `f(x⁻¹ γ θ(x)) ≠ 0` for some `x ∈ G`, then
   `γ` is `Γ`-`θ`-conjugate to some `r i`. Equivalently, every `Γ`-`θ`-conjugacy class in `Γ`
   whose `G`-`θ`-conjugacy class meets the set `{f ≠ 0}` is represented. Extra
   representatives whose classes miss `{f ≠ 0}` are allowed. Their orbital integrals vanish,
   so they contribute zero.
5. For each `i`, write `C_i = twistedCentralizer θ (r i)` (the `θ`-centralizer
   `{x | x⁻¹ r_i θ(x) = r_i}`) and `Γ_i = Γ ∩ C_i` (as `Γ.subgroupOf C_i`). The data are:
   - a measure `μC i` on `C_i` that is right invariant, finite on compact sets and positive
     on nonempty open sets;
   - a measure `νC i` on `C_i \ G` compatible with `μG` and `μC i`
     (`IsCompatible C_i μG (μC i) (νC i)`);
   - a measure `νΓC i` on `Γ_i \ C_i` compatible with `μC i` and the counting measure on
     `Γ_i` (`IsCompatible (Γ.subgroupOf C_i) (μC i) Measure.count (νΓC i)`).
   Here `C_i \ G` and `Γ_i \ C_i` are again `LeftQuotient`s with Borel σ-algebras, and
   `IsCompatible` has the same fields as for `ν` above.
   These measures are hypotheses, not constructions: the statement does not assert that they
   exist. If for some `i` no such measures exist, the hypotheses cannot all hold and the
   statement says nothing about those data.
6. Each `Γ_i \ C_i` has finite volume: `νΓC i univ ≠ ⊤`.
7. Each twisted orbital integral converges absolutely: the function
   `C_i x ↦ f(x⁻¹ r_i θ(x))` on `C_i \ G` (`twistedOrbitFunction θ (r i) f`) is
   `νC i`-integrable.

## Conclusion

```
operatorTrace (R(f) ∘ I_θ) =
  ∑ i, ((νΓC i univ).toReal : ℂ) * twistedOrbitalIntegral θ (r i) (νC i) f
```

that is, `tr(R(f) ∘ I_θ) = Σ_i vol(Γ_i \ C_i) · TO_{r_i}(f)` with
`TO_{r_i}(f) = ∫_{C_i \ G} f(x⁻¹ r_i θ(x)) d(νC i)`. Here `operatorTrace` is the Library's trace
(`Langlands/Analysis/OperatorTrace.lean`). On trace-class operators it is the absolutely
convergent diagonal sum in every Hilbert basis (`operatorTraceBasis`).

The volumes and orbital integrals are taken for the supplied measures. The compatibility
conditions tie them together: the formula is unchanged if `μC i` is scaled by `c > 0` and
`νC i`, `νΓC i` are scaled by `c⁻¹` and `c`.

## Source and provenance

- Getz–Hahn, *An introduction to automorphic representations* (2024), registered
  `getz-hahn-2024-automorphic-representations`, §18.5, printed pp. 486–488 (in the PDF,
  page = printed + 7 in Chapter 18). Here `θ` is a finite-order automorphism of a reductive
  group `G` over a number field `F` (printed p. 486). Equations (18.31)–(18.33) (printed
  p. 487) define the `θ`-centralizer `C^θ_γ = {g | g⁻¹ γ θ(g) = γ}`, the twisted orbital
  integral `TO_γ(f)` over `(A^θ_G \ C^θ_γ(A_F)) \ (A_G \ G(A_F))`, where
  `A^θ_G = {a ∈ A_G | θ(a) = a}`, the volume `τ(C^θ_γ)` of `A^θ_G C^θ_γ(F) \ C^θ_γ(A_F)`,
  and `I_θ φ = φ ∘ θ⁻¹`. The kernel of `R(f) ∘ I_θ` is `K_f(g, θ(h))`, where
  `K_f(x, y) = Σ_{γ ∈ G(F)} f(x⁻¹ γ y)`. Corollary 18.5.1 (printed p. 488) is the simple
  twisted trace formula `Σ_π tr(π(f) ∘ I_θ) = Σ_{[γ]} τ(C^θ_γ) TO_γ(f)`, equation (18.36).
  On p. 488 Getz–Hahn cite Brislawn 1991, Corollary 3.2, for the trace of the trace-class
  operator (18.34).
- Getz–Hahn, Theorem 18.2.5 (printed p. 479), the simple relative trace formula for a
  subgroup `H ≤ G × G` and a character `χ`. Its proof (printed pp. 481–482) integrates the
  kernel `K_f(h₁, h₂) χ⁻¹(h₁, h₂)` over the relative quotient `A_{G,H} H(F) \ H(A_F)`,
  (18.19), and unfolds this integral into a sum over classes of volumes times relative
  orbital integrals, (18.20). It justifies the unfolding by the absolute convergence (18.21).
  Each integral in (18.21) converges absolutely by Proposition 18.2.4 (printed p. 478). The
  finiteness of the contributing classes has two steps (printed p. 482). Theorem 17.7.10
  (printed p. 461) shows that within each geometric class only finitely many relative
  classes can contribute. Lemma 18.2.6 (printed p. 479) shows that only finitely many
  geometric classes can contribute. Corollary 18.5.1 is the case where `H` is the twisted
  diagonal `{(g, θ(g))}` and `χ` is trivial. Then the relative classes are the
  `G(F)`-`θ`-conjugacy classes, and (18.19) is the integral of `K_f(g, θ(g))` over the
  diagonal copy of `[G] = A_G G(F) \ G(A_F)`.
- Deligne–Kazhdan–Vignéras 1984, Appendix A.1 (registered
  `bdkv-1984-representations-local-field`, printed pp. 41–44, PDF pp. 45–48), for the
  untwisted case and with a central character. A.1.a (printed pp. 41–42): `G` is a connected
  reductive group over a global field `F` with centre `Z`, `G* = Z \ G`, and `ω` is a
  unitary character of `Z(F) \ Z(A)`. The representation `ρ` is right translation on
  `L²(G(F) \ G(A), ω)`. Its functions transform by `ω` under `Z(A)` and are square
  integrable over `G*(F) \ G*(A)`. For `f = ∏ f_v` transforming by `ω⁻¹` under the centre,
  `ρ(f dg) = ∫_{G*(A)} f(g) ρ(g) dg` is an integral operator on `G*(F) \ G*(A)` with
  kernel `K_f(x, y) = Σ_{γ ∈ G*(F)} f(x⁻¹ γ y)`. A.1.b (printed p. 43): for supercuspidal
  `f`, `ρ(f dg)` is trace class, `K_f` is integrable along the diagonal, and
  `trace ρ(f dg) = ∫_{G*(F) \ G*(A)} Σ_{γ ∈ G*(F)} f(x⁻¹ γ x) dx`. It then assumes that the
  support of `f` meets no `G(A)`-conjugacy class of an element of `G(F)` that is not
  elliptic regular. On printed p. 44 it exchanges sum and integral and groups the `γ` into
  conjugacy classes in `G*(F)`, which gives the simple formula A.1.c:
  `trace ρ(f dg) = Σ_{γ} ∫_{Z*_γ(F) \ G*(A)} f(x⁻¹ γ x) dx
  = Σ_{γ} [Z*_γ(F) : Z_γ(F)]⁻¹ vol(Z_γ(F) Z(A) \ Z_γ(A)) ∫_{Z_γ(A) \ G(A)} f(x⁻¹ γ x) dx`.
  Here `Z_γ` is the centralizer of `γ` in `G` and `Z*_γ` its centralizer in `G*`. A.1.d
  (printed p. 44) gives local hypotheses under which the formula holds.

  The present statement with `θ = id` has the same kernel shape `Σ_γ f(x⁻¹ γ y)`, the same
  orbital integrand `f(x⁻¹ γ x)` and the same shape "volume times orbital integral". It has
  no central character, and its centralizers and volumes are those of the supplied group.
  Transporting it to the central-character setting of A.1, with the starred groups and the
  index `[Z*_γ(F) : Z_γ(F)]⁻¹`, is a separate comparison and is not claimed here.

No source prints this abstract statement. It is derived content: the geometric half of the
argument of Getz–Hahn Theorem 18.2.5 and Corollary 18.5.1, abstracted from
`A_G \ G(A_F)` and `G(F)` to a unimodular group `G` and a discrete subgroup `Γ`. The source
hypotheses are replaced by explicit hypotheses here:

- Getz–Hahn assume that `R(f)` has cuspidal image, so that it is trace class by Theorem
  9.1.2 (Gelfand–Piatetski-Shapiro, printed p. 241). Here trace class is hypothesis 1.
- They assume that every element of `G(F)` that is `θ`-conjugate under `G(A_F)` to the
  support of `f` is `θ`-elliptic (finite volume `τ(C^θ_γ)`) and `θ`-semisimple (closed
  orbit). With the compactness of the support, the source uses this to show that only
  finitely many classes contribute (printed p. 482: Lemma 18.2.6 for the geometric classes
  and Theorem 17.7.10 for the `G(F)`-classes within each geometric class), that their
  volumes are finite, and that their orbital integrals converge absolutely (Proposition
  18.2.4). Here these facts are hypotheses 3–4, 6 and 7.
- Deligne–Kazhdan–Vignéras (printed p. 44) derive from their assumption on the support of `f`
  that `x ↦ Σ_γ |f(x⁻¹ γ x)|` has compact support modulo `Z(A) G(F)`, which allows them to
  exchange sum and integral. Here the corresponding property for `θ`-conjugation is
  hypothesis 2.
- Getz–Hahn fix Haar measures on `G(A_F)` and on the centralizers and use the induced
  quotient measures. Here the measures `μG`, `ν`, `μC i`, `νC i`, `νΓC i` are supplied,
  tied together by the `IsCompatible` hypotheses and hypothesis 5.

The following outline of a proof is explanation only; the module proves nothing, and the
outline is not part of the statement. Since `θ` preserves `Γ` and `θ̄⁻¹` preserves `ν`, the operator
`R(f) ∘ I_θ` has kernel `K(x, y) = Σ_{γ ∈ Γ} f(x⁻¹ γ θ(y))` (`twistedKernel Γ θ f` in
`Langlands.TraceFormula.TwistedOrbital`; the computation is on the page of
`AbstractTwistedKernelDiagonalTraceStatement`). The trace is then `∫_{Γ \ G} K(x, x) dν`: this
is the separate statement `Langlands.TraceFormula.AbstractTwistedKernelDiagonalTraceStatement`
(module `Langlands.TraceFormula.AbstractTwistedKernelDiagonalTraceStatement`), an instance of
Brislawn's Corollary 3.2, which the Library states as
`Langlands.Analysis.OperatorIdeals.TraceClassContinuousKernelDiagonalStatement` (module
`Langlands.Analysis.TraceClassKernelDiagonalStatement`; not imported here). Grouping the `γ`
by `Γ`-`θ`-conjugacy class, the class of `r_i` is parametrized by `Γ_i \ Γ`, and the sum over
it unfolds to `∫_{Γ_i \ G} f(x⁻¹ r_i θ(x))`. Hypothesis 2 bounds `x ↦ Σ_γ |f(x⁻¹ γ θ(x))|` on
`Γ \ G` by a constant times the indicator of a compact set, which makes the sum over `Γ` and the
integral over `Γ \ G` absolutely convergent and justifies the exchange. Integration in stages
over `Γ_i \ C_i` and `C_i \ G`, with the finite volumes of hypothesis 6, gives
`vol(Γ_i \ C_i) · TO_{r_i}(f)`; the integrability of hypothesis 7 is then a consequence.

The geometric half of this outline is proved in `Langlands.TraceFormula.TwistedGeometricSide`:
`abstractSimpleTwistedTraceFormula_of_trace_eq_integral` gives the conclusion from the hypotheses
and the identity `tr(R(f) ∘ I_θ) = ∫_{Γ \ G} K(x, x) dν`, and
`abstractSimpleTwistedTraceFormula_of_kernelDiagonalTrace` derives this statement from
`AbstractTwistedKernelDiagonalTraceStatement`. The analytic half is proved as well:
`abstractTwistedKernelDiagonalTrace` (module
`Langlands.TraceFormula.AbstractTwistedKernelDiagonalTraceProof`) proves
`AbstractTwistedKernelDiagonalTraceStatement` from
`Langlands.Analysis.OperatorIdeals.traceClassContinuousKernelDiagonal` (module
`Langlands.Analysis.TraceClassKernelDiagonalProof`), and `abstractSimpleTwistedTraceFormula` is
`abstractSimpleTwistedTraceFormula_of_kernelDiagonalTrace` applied to it.

Three hypotheses of the statement are not used by this proof: `MeasurePreserving θ μG μG` (neither
half uses it; the kernel identity uses that `θ̄⁻¹` preserves `ν`), the positivity of `μC i` on
nonempty open sets (`∀ i, (μC i).IsOpenPosMeasure`), and hypothesis 7, the integrability of the
twisted orbit functions, which the geometric side proves. The right invariance of `μG` is used
only by the geometric side, to obtain compatible measures on `(Γ ∩ C_i) \ G`.

## Relation to the specialization

In Getz–Hahn's setting the supplied group is `A_G \ G(A_F)`, `Γ` is the image of `G(F)`,
and the automorphism is the one induced by `θ`. It is well defined because `θ` is an
automorphism of `G` over `F` and so preserves `A_G`. In this setting the abstract
centralizers are the groups used in (18.32), by the following argument. Let `G(A_F)¹` be the
norm-one subgroup (2.19) (Getz–Hahn, printed p. 68, PDF p. 85). Since `F` is a number
field, `G(A_F)` is the direct product `A_G × G(A_F)¹` by Lemma 2.6.2 (printed p. 69, PDF
p. 86). The group `G(F)` lies in `G(A_F)¹` by the product formula, and `θ` preserves
`G(A_F)¹` because it permutes the characters in (2.19). Let `γ ∈ G(F)`, and let `g = a x`
with `a ∈ A_G` and `x ∈ G(A_F)¹`. Then `g⁻¹ γ θ(g) = a⁻¹ θ(a) · x⁻¹ γ θ(x)`. So if
`g⁻¹ γ θ(g) ∈ A_G γ`, then `x⁻¹ γ θ(x) γ⁻¹` lies in `A_G ∩ G(A_F)¹ = 1`, and
`x ∈ C^θ_γ(A_F)`. Hence the `θ`-centralizer of the image of `γ` in `A_G \ G(A_F)` is the
image of `C^θ_γ(A_F)`. It is isomorphic to `A^θ_G \ C^θ_γ(A_F)`, since
`A_G ∩ C^θ_γ(A_F) = A^θ_G`. For `g = δ ∈ G(F)` one has `a = 1`, so the same argument shows
that the intersection of this centralizer with `Γ` is the image of `C^θ_γ(F)`. So, for
`r_i` the image of `γ`, the abstract quotients `Γ_i \ C_i` and `C_i \ G` correspond
canonically to `A^θ_G C^θ_γ(F) \ C^θ_γ(A_F)` and `(A^θ_G \ C^θ_γ(A_F)) \ (A_G \ G(A_F))`,
the domains of `τ(C^θ_γ)` and `TO_γ(f)`.

This identification of groups is explanation only. Matching the measures with Getz–Hahn's
`τ(C^θ_γ) TO_γ(f)` and deriving hypotheses 1–7 from Getz–Hahn's assumptions are part of the
`GL_n` specialization and are not claimed here. This statement claims only what is written
above.
