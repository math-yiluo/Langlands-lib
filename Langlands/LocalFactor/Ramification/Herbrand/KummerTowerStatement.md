# Kummer-step and Kummer-tower ramification statements

The Lean module
`Langlands.LocalFactor.Ramification.Herbrand.KummerTowerStatement`, in namespace
`Langlands.Ramification.Kummer`, supplies five supporting definitions and six
proposition definitions. It proves none of the six ramification statements.
Each statement is universe-polymorphic in `u` and quantifies over every prime
`p`, with `[Fact p.Prime]`, and every `F : PadicField.{u} p`.

## Existing objects and conventions

Write `Ω = AlgebraicClosure F.Carrier`, `G_F` for
`Field.absoluteGaloisGroup F.Carrier`, and
`e = F.canonicalTopologicalData.ramificationIndex`. A uniformizer `ϖ` satisfies
`F.canonicalTopologicalData.ord ϖ = 1`. This is the existing normalized additive
order, whose value at zero is zero. The absolute ramification index and order
are those of `Langlands.LocalField.Normalization.Definitions`.

The notation `G_F^v` in this document means the existing
`Langlands.Ramification.Padic.absoluteUpperRamificationGroup F v`, with Serre's
upper numbering, including `v = -1`. A finite subextension is the Library's
`Langlands.LocalClassField.FiniteIntermediateExtension F.Carrier`. For such an
`E`, write `G_E = E.field.fixingSubgroup`, as a subgroup of `G_F`, and
`ψ_{E/F} = Langlands.Ramification.HerbrandBridge.relativeHerbrandPsi E`.
The latter is defined even when `E/F` is not Galois: it is
`φ_{M/E} ∘ ψ_{M/F}` in the Galois closure `M` of `E`, as in
`Herbrand.SubextensionProof`. This is the inverse of Serre's relative function
in *Local Fields*, IV §3, Remark 2, printed p. 75.

Because `G_F^v` is normal, the subgroup supremum `G_E ⊔ G_F^v` has underlying
set equal to the product `G_E · G_F^v`. Thus the supremum equals `⊤` exactly
when this product is all of `G_F`; for finite `E/F`, this says that `G_F^v`
acts transitively on the `F`-embeddings of `E` into `Ω`. The same product
interpretation applies to the fixing subgroup of the infinite union.

No assumption that `F` contains the `p`-th roots of unity is made. In particular,
the degree-`p` step need not be Galois. There is no second definition here of
upper groups, finite intermediate extensions, normalized order or the relative
Herbrand function.

## Supporting definitions

These are internal constructions implementing the fields and numerical bound
in the two operator notes cited below.

- `adjoinFiniteIntermediate F α` packages the actual simple intermediate field
  `F⟮α⟯` inside `Ω`. Its finiteness certificate is
  `IntermediateField.adjoin.finiteDimensional`, applied to the integrality of
  `α` in the algebraic closure.
- `kummerBreak F` is the real number `b = p e / (p - 1)`. The casts precede the
  subtraction and division, so these are real operations.
- `IsKummerRootSystem F ϖ πs` is precisely the conjunction that `ϖ` is a
  uniformizer, `πs 0 = algebraMap F.Carrier Ω ϖ`, and
  `πs (n + 1) ^ p = πs n` for every natural number `n`. Thus the roots are
  compatible and `πs n` is a `p^n`-th root of `ϖ`.
- `kummerStage F πs n` is `adjoinFiniteIntermediate F (πs n)`, the finite
  field `K_n = F(πs n)`.
- `kummerTower F πs` is the intermediate-field supremum
  `⨆ n, (kummerStage F πs n).field`. Under `IsKummerRootSystem` the stages
  increase, so this is their union `L`. The stage and supremum constructions
  are defined for arbitrary `πs`; compatibility is a hypothesis of the
  ramification statements.

## The six statements

1. **`KummerStepUpperSupStatement.{u}`.** For every uniformizer `ϖ` and every
   `α : Ω` with `α ^ p = algebraMap F.Carrier Ω ϖ`, put `E = F(α)`. Then
   `G_E ⊔ G_F^v = ⊤` for each real `v` with `-1 ≤ v ≤ b`. This is the
   transitivity assertion for the single Kummer step in the plan note,
   Remark 4.1(i), and the first step of the proof of the route note's
   Corollary `cor:kummer`. Wintenberger 1.1.1 and 1.3.1 supply the
   embedding-ramification convention and elementary-extension criterion.

2. **`KummerStepHerbrandPsiStatement.{u}`.** For the same `ϖ`, `α` and `E`,
   both clauses hold:
   `ψ_{E/F}(x) = x` for `-1 ≤ x ≤ b`, and
   `ψ_{E/F}(x) = p x - p e` for `b ≤ x`.
   Both clauses include `b`, where the formulas agree. This is the step formula
   in the proof of the route note's Lemma `lem:tower`. That source passage
   assumes the roots of unity for its cyclic-step application; the present
   statement uses the relative function for the possibly non-Galois step.
   Its broader scope comes from the embedding computation of the plan note's
   Remark 4.1(i), Wintenberger 1.1.1 and 1.3.1, and the relative-function
   convention of Serre IV §3, Remark 2.

3. **`HerbrandPsiTruncationStatement.{u}`.** For every finite intermediate
   extension `E/F` and every real `μ`, if `G_E ⊔ G_F^μ = ⊤`, then
   `ψ_{E/F}(x) = x` for every real `x` satisfying `-1 ≤ x ≤ μ`.
   This states the Herbrand-function clause of the route note's Lemma
   `lem:trunc` in absolute Galois group vocabulary. The route note phrases
   it for totally ramified `E/F`, `μ > 0`, and `0 ≤ x ≤ μ`. Here total
   ramification on the positive range is forced by the supremum hypothesis;
   the interval `[-1, 0]` uses the standard identity convention for the
   relative functions (Wintenberger 1.1.1–1.2.1). No separate total
   ramification or positivity hypothesis is imposed. For `μ < -1` the
   conclusion has an empty interval.

4. **`KummerTowerUpperSupStatement.{u}`.** For every `ϖ` and `πs` satisfying
   `IsKummerRootSystem F ϖ πs`, every natural `n`, and every real `v` with
   `-1 ≤ v ≤ b`, one has `G_{K_n} ⊔ G_F^v = ⊤`.
   Stage zero is included. This is the finite-stage transitivity assertion
   of the route note's Corollary `cor:kummer` and the plan note's
   Remark 4.1(i), with the common interval including `[-1, 0]`.

5. **`KummerTowerHerbrandPsiStatement.{u}`.** With the same root-system
   hypothesis, every natural `n` and every real `x` with `-1 ≤ x ≤ b`
   satisfy `ψ_{K_n/F}(x) = x`.
   This is the finite-stage consequence of the route note's truncation lemma
   and Kummer corollary; the common identity range is also recorded in the
   plan note's Remark 4.1(i).

6. **`KummerTowerLimitUpperSupStatement.{u}`.** With the same root-system
   hypothesis, let `L = kummerTower F πs`. For every real `v` with
   `-1 ≤ v ≤ b`, the fixing subgroup of `L` satisfies
   `G_L ⊔ G_F^v = ⊤`.
   This is the infinite-tower product assertion in the final display of
   part (i) of the plan note's Remark 4.1. Wintenberger 1.4.1–1.4.2
   provide the broader elementary-tower context.

## Dependencies for later proofs

The intended dependency route is recorded here; no implication is proved in
this module. Statement 4 uses statement 1 at each successive base field
`K_n`, together with the existing Herbrand subgroup comparison and the
identity supplied by truncation. The step over `K_n` has the larger break
`p^{n+1} e / (p - 1)`, which contains the common interval through `b`.
Statement 5 follows from statements 3 and 4. Statement 6 follows from
statement 4 by compactness: the closed subgroups `G_{K_n}` decrease to
`G_L`, and the existing absolute upper group `G_F^v` is closed.
Statement 2 separately specifies the full step function needed by the
route note's tower argument, including its second linear branch.

These propositions do not state arithmetic profiniteness, construct a field
of norms or assert its Galois-group comparison. Those are separate inputs
for later work on the close-fields statement E1a.

## Sources and reading locations

- Operator, *Formalizing the large external inputs of the local Langlands
  correspondence for GL_n* (16 November 2026), registered
  `operator-external-inputs-plan-2026-11-16`, source
  `/home/taskhub/pilot/literature/Operator note - Formalizing the large external inputs of the local Langlands correspondence for GL_n (16 November 2026)/external-inputs-plan.tex`.
  Remark 4.1 (`rem:fon`), part (i), lines 586–603, gives the compatible-root
  tower, embedding ramification values, elementary levels and common
  transitivity and identity interval. Lines 613–618 describe the missing
  Kummer-step lemma.
- Operator, *Numerical local Langlands for GL_n, counts on the two sides
  and the recommended route* (16 November 2026), registered
  `operator-numerical-llc-route-2026-11-16`, source
  `/home/taskhub/pilot/literature/Operator note - Numerical local Langlands for GL_n, counts on the two sides and the recommended route (16 November 2026)/numerical-LLC-route.tex`.
  Lemma `lem:trunc` and Corollary `cor:kummer`, lines 876–897;
  Lemma `lem:tower`, especially its step computation, lines 1196–1207.
- Jean-Pierre Wintenberger, *Le corps des normes de certaines extensions
  infinies de corps locaux; applications*, Annales scientifiques de l'École
  Normale Supérieure, series 4, 16 (1983), 59–89; registered
  `wintenberger-1983-field-of-norms`. Read 1.1.1, printed pp. 61–62
  (PDF pp. 4–5), for embedding ramification and relative functions;
  1.2.1, printed p. 62, for the integral formula and negative-index convention;
  1.3.1, printed p. 64 (PDF p. 7), for the elementary-extension criterion;
  and 1.4.1–1.4.2, printed pp. 64–65 (PDF pp. 7–8), for elementary towers.
  Original:
  `/home/taskhub/central-library/Wintenberger--Le corps des normes de certaines extensions infinies de corps locaux ; applications--1983.pdf`.
- Jean-Pierre Serre, *Local Fields*, GTM 67, Springer (1979); registered
  `serre-1979-local-fields`. IV §3, Remark 2, printed p. 75 (PDF p. 82),
  defines the relative function for a subextension of a finite Galois
  extension. Original:
  `/home/taskhub/central-library/Serre--Local Fields--1979.pdf`.
