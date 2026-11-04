# Signed class formula from exactness before the terminal degree

Module `Langlands.Representation.Aubert.General.SharpClassFormulaReduction`,
namespace `Langlands.Aubert.General.SharpClassFormula`.

Implementation and documentation: Worker 1511 (task
`13e2abdc-2be7-4191-b74b-9eae99a56fcc`). The complex, its terminal cokernel and
the target are Workers 194 and 379's constructions; this module only proves a
reduction about them.

## Scope

This is a generic, conditional reduction of the body of
`Langlands.Aubert.General.SharpClassFormulaTarget`, Aubert's class formula
`D_G[E] = (-1)^{|I|} [E#]` in the actual finite-length Grothendieck group
(Corollaire 3.9 (a), 1995, printed p. 2189). It works over arbitrary families
`P M U : Finset ι → Subgroup G` with the same variables as the target (`h`,
`hclosed`, `hδ`, `hP : Monotone P`, `hU : Antitone U`, `hfl`). It takes two
inputs as explicit hypotheses of its main theorem. This module does not prove
either of them:

* `hexact : StandardComplex.IsExactBeforeTerminal P M U h hclosed hδ hP hU E I`:
  exactness of the actual complex at every degree strictly before the terminal
  degree `terminalDegree I = |S| - |I|`. This is the conclusion of the corrected
  Théorème 3.6.
* `hvan : ∀ K, K.card < I.card → Subsingleton (r_K E)`: the actual normalized
  Jacquet module of `E` vanishes at every standard subset with fewer than `|I|`
  roots.

The theorem does not assume that `E` lies in `Alg({I})`. Membership is needed
only to obtain `hexact` and `hvan`. For `E` in `Alg({I})`, `hvan` is the expected
consequence of `SupportCategoryJacquetVanishingTarget` together with the fact
that associated standard subsets have equal cardinality. This module neither
proves nor uses that consequence. The module therefore does not prove
`SharpClassFormulaTarget` or its rational specialization
`RationalSharpClassFormulaStatement`. Those still need proofs of the two inputs.

## Provenance

This is internal, derived content. It formalizes the Euler-characteristic step
that the Markdown of `SharpConsequenceStatements` describes for
`SharpClassFormulaTarget`:
`(-1)^{|S|-|I|} [E#] = ∑_J (-1)^{|S|-|J|} [E_J] = (-1)^{|S|} D_G([E])`.
That step is in turn Aubert's derivation of Corollaire 3.9 (a) from the corrected
Théorème 3.6. The proof uses only published Library declarations:

* `SmoothRep.FiniteExactEuler.signed_descending_class` and
  `FiniteExactEuler.terminal` (Euler characteristic of a finite exact sequence
  with terminal cokernel);
* `Aubert.FiniteProduct.finiteLength` and `Aubert.FiniteProduct.class_eq_sum`
  (class of a finite product);
* `inductionJacquet_hasFiniteLength`, `inductionK0_ofRepresentation`,
  `alternatingOperator_ofRepresentation` (the actual operator `D_G` on classes);
* `SmoothRep.IrreducibleGrothendieckProof.ofRepresentation_eq_zero_of_subsingleton`
  and `ofRepresentation_eq_of_equiv`;
* the complex `StandardComplex.degreeObject`, `Complex.degreeMorphism`,
  `Complex.terminalObject`, `StandardComplex.sharpObject` and the predicate
  `StandardComplex.IsExactBeforeTerminal`.

No literature assertion beyond this algebraic bookkeeping is used or claimed.
The proof uses no Langlands classification, no character independence and no
geometric lemma. It uses no adjunction beyond what the imported definitions of
`D_G` and the complex already contain.

## Declarations

* `degree_hasFiniteLength`: each homogeneous degree
  `StandardComplex.degreeObject … E k` has finite length when `E` does. It is a
  finite product of the finite-length coordinates `i_{S∖s} r_{S∖s} E`
  (`FiniteProduct.finiteLength`).
* `degree_class`: the class of degree `k` is the sum, over removed-root sets
  `s` with `|s| = k`, of the classes of `i_{S∖s} r_{S∖s} E`. The proof
  reindexes the product by `Fin` and applies `FiniteProduct.class_eq_sum`.
* `term_vanish`: if `r_J E` is a subsingleton then the class of `i_J r_J E` is
  zero. The proof writes this class as `inductionK0` of the zero class.
* `degreeFL`, `degreeMap`: the degrees as finite-length objects and the signed
  differentials as morphisms (`Complex.degreeMorphism` for the removed-root
  families).
* `terminal_class`: the terminal cokernel
  `FiniteExactEuler.terminal (degreeFL …) (degreeMap …) k` of the finite
  sequence and the actual terminal cokernel `Complex.terminalObject … E k` have
  the same class. At `k = 0` the equivalence is the quotient by `⊥`. At `k + 1`
  both are the same quotient by the range of the previous differential, and the
  equivalence is the identity.
* `alternatingOperator_degree_sum`:
  `D_G[E] = Σ_{i ≤ |S|} (-1)^{|S|-i} [degree i]`. The proof starts from
  `alternatingOperator_ofRepresentation`, then reindexes `J ↦ S ∖ J` with
  `Function.Involutive.toPerm`, groups by cardinality
  (`Finset.sum_fiberwise_of_maps_to`, `Finset.sum_subtype`), uses
  `|S ∖ s| = |S| - |s|`, and finishes with `degree_class`.
* `degree_class_eq_zero`: under `hvan`, the class of every degree
  `i > terminalDegree I` is zero, since each coordinate has
  `|S ∖ s| = |S| - i < |I|`.
* `class_formula_of_exact`: under `hexact` and `hvan`,
  `alternatingOperator … (ofRepresentation E hE) = (-1)^{|I|} • ofRepresentation (sharpObject … E I) hE'`.
  This is the body of `SharpClassFormulaTarget` for this `E` and `I`. The proof
  applies `FiniteExactEuler.signed_descending_class`, whose conclusion is
  `(-1)^{n-(m+1)} • Σ_{i ≤ m} (-1)^{n-(i+1)} [C i] = [terminal C d m]`, with
  `m = terminalDegree I = |S| - |I|` and `n = |S| + 1`. Injectivity at the
  start is `hexact 0`, since `boundary 0 = ⊥`. Exactness at `i + 1` is
  `hexact (i + 1)`, since `boundary (i + 1)` is the range of `d i`. The proof
  then identifies the terminal term by `terminal_class` and simplifies the
  outer sign exponent `n - (m + 1) = |S| + 1 - (m + 1) = |I|`; the inner
  exponents become `n - (i + 1) = |S| - i`. It uses
  `(-1)^{|I|}·(-1)^{|I|} = 1` and `alternatingOperator_degree_sum`, and it
  drops the degrees above `m` by `degree_class_eq_zero`.

## Universes

`ι : Type uI`, `G : Type uG`, and `E : SmoothRep.{0, uG, max uI uG uV} ℂ G`,
with the functors at the carrier universe `max uI uV` used by the target. All
universes are independent.
