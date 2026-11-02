# Finite-length and irreducible consequences of the corrected Theorem 3.6

Implementation and documentation: Worker 379 (task
`0a1bd7fb-66c2-4dcc-a3c8-6619f6fa10b4`, the complex-and-targets unit of the
general Aubert program `46df6a68-5db4-4428-8044-05151d6ce1f6`). The complex and
its terminal cokernel are Worker 194's constructions; this module only states
targets about them.

This module states, as separate proposition targets, Aubert's Corollaire 3.9
(1995, printed p. 2189), its finite-length specialization for the support
categories `Alg({I})` of the 1996 erratum, and the finite-length and support
assertions these need. Nothing here is proved.

## Data

All targets are `Prop`-valued definitions in namespace `Langlands.Aubert.General`
of the data of Worker 194's standard complex and of `SupportCategory`:

* `ι` with `[LinearOrder ι] [Fintype ι]` (the simple roots `S`, ordered to fix
  the exterior signs of the complex), and `G` locally compact nonarchimedean;
* `P M U : Finset ι → Subgroup G` with the standard-index convention
  (`L_I = M I`), `h : ∀ J, IsSemidirectDecomposition (P J) (M J) (U J)`,
  `hclosed : ∀ J, IsClosed (U J)`, `hδ : ∀ J, IsUnimodularModulus (U J) (hclosed J)`,
  `hP : Monotone P` and `hU : Antitone U`;
* `hM : ∀ I, IsClosed (M I)` and the Levi-in-Levi decompositions `hL`, as in
  `SupportCategoryStatements`;
* the association relation `IsAssociate`.

Representations `E` have carriers in `Type (max uI uG uV)`. Worker 194's
`StandardComplex.sharpObject` sends carriers in `Type (max uG uV')` to carriers in
`Type (max uI uG uV')`; it is used here at `uV' = max uI uV`, so `E`, `E#` and
`(E#)#` all lie in `SmoothRep.{0, uG, max uI uG uV} ℂ G`, and their classes lie
in one exact Grothendieck group.

`E#` denotes `StandardComplex.sharpObject P M U h hclosed hδ hP hU E I`: the
actual cokernel of the differential into the degree `|S| - |I|` of the normalized
smooth complex `E_J = i_J r_J E` (Aubert's (3.5)/(3.7); erratum p. 4690,
"`E#` = coker `d_{|I|}`"). It depends on `I` only through `|I|`.

`D_G` is Worker 23's `alternatingOperator P M U h hclosed hfl`, the unadjusted
operator `∑_{I ⊆ S} (-1)^{|I|} i_I ∘ r_I` of Aubert's Définition 1.5 on
`SmoothRep.FiniteLengthGrothendieckGroup` (the exact finite-length Grothendieck
group). It needs the finite-length hypotheses
`hfl : ∀ J, ParabolicFiniteLength (h J) (hclosed J)`, which every target using
`D_G` takes as a quantified argument.

## Targets

### `SharpFiniteLengthTarget`

For every `I` and every finite-length `E`, `E#` has finite length
(`SmoothRep.HasFiniteLength`). This is the finite-length obligation for `E#` that
Corollaire 3.9 (a) needs before `[E#]` makes sense. It is stated for every
finite-length `E`, not only for members of `Alg({I})`: `E#` is a quotient of a
finite direct sum of the `i_J r_J E`, which have finite length when `E` does
(Renard VI.6.2 and VI.6.4, the conjuncts of `ParabolicFiniteLength`).

### `SharpClassFormulaTarget`

For every `hfl`, every `I`, every `E ∈ Alg({I})` and finite-length proofs
`hE` for `E` and `hE'` for `E#`:
`D_G([E]) = (-1)^{|I|} • [E#]`.

Source: Corollaire 3.9 (a), p. 2189, "(-1)^{|I|}[E#] = D_G([E])", stated there for
`E ∈ 𝔈(I)`. The target is its finite-length specialization of the corrected
Theorem 3.6: it asks the formula for every finite-length member of `Alg({I})`, as
the task requires. It follows from three facts: exactness of the complex before
the terminal degree (Worker 194's corrected Theorem 3.6 target), vanishing of the
terms `E_J` with `|J| < |I|` (`SupportCategoryJacquetVanishingTarget`), and
additivity of classes along exact sequences. Then the Euler characteristic gives
`(-1)^{|S|-|I|} [E#] = ∑_J (-1)^{|S|-|J|} [E_J] = (-1)^{|S|} D_G([E])`. Membership
of `𝔈(I)` in `Alg({I})` (`IsInCuspidalSeries.isInSupportCategory`, given
`IsAssociate I I 1`, which holds for the intended relations) recovers Aubert's
case. Aubert's own proof of (b) already applies (a) to the reducible induced
representation `i^G_{L_I}(σ)`, so it uses the formula beyond `𝔈(I)`.

### `SharpSupportRetentionTarget`

For every `I` and every smooth `E ∈ Alg({I})`, `E# ∈ Alg({I})`. `E#` is a
quotient of a finite direct sum of the `i_J r_J E`, so this follows from
`SupportCategoryInductionJacquetTarget` and the closure of `Alg({I})` under
quotients and extensions. It is the retention of the support type that iterating
`#` needs.

### `SharpIrreducibleTarget`

Corollaire 3.9 (b), p. 2189: for `E ∈ 𝔈(I)`, `E#` is irreducible. Aubert writes
"si `E` est irréductible, `E#` est aussi un G-module irréductible"; members of
`𝔈(I)` are irreducible by Notation 1.6. `SmoothRep.IsIrreducible` includes
`E# ≠ 0`, so this is the actual nonzero irreducibility the task asks for.

### `SharpCuspidalSeriesTarget`

For `E ∈ 𝔈(I)` there are `I'` and `n` with `IsAssociate I I' n`,
`M I' = n (M I) n⁻¹` and `E# ∈ 𝔈(I')`. This is the retention of the cuspidal
series used in Aubert's proof of (c), which applies (a) and (b) to `E#`. It follows
from `SharpSupportRetentionTarget`, (b) and the definition of `Alg({I})`, given
that conjugation by `n` preserves cuspidality.

### `SharpInvolutionTarget`

Corollaire 3.9 (c), p. 2189: for `E ∈ 𝔈(I)`, there is an isomorphism of smooth
representations `(E#)# ≅ E`, where both cokernels are taken with the same `I`,
that is at degree `|S| - |I|`. Since `E# ∈ 𝔈(I')` with `L_{I'}` conjugate to
`L_I`, `|I'| = |I|` and this is Aubert's `(E#)#`. The conclusion is a
categorical isomorphism `≅` in `SmoothRep`, an actual equivariant linear
isomorphism, not an equality of Grothendieck classes. Aubert derives it from the
involutivity of `D_G` (Théorème 1.7 (3)), the class formula (a) for `E` and for
`E#`, irreducibility (b), and the fact that irreducible representations with the
same class are isomorphic.

## Prerequisites recorded elsewhere

The extension of the class formula from one support type to every finite-length
representation uses, besides `SharpClassFormulaTarget` and
`SharpFiniteLengthTarget`:

* `SupportCategoryDecompositionTarget` (support decomposition, Renard VI.7.2);
* `SupportCategoryJacquetVanishingTarget` and the other support targets of
  `SupportCategoryStatements`;
* termwise finite length `ParabolicFiniteLength` (Worker 23's named hypothesis,
  Renard VI.6.2, VI.6.4) and its consequence
  `inductionJacquet_hasFiniteLength`;
* Worker 194's corrected Theorem 3.6 exactness target
  `Langlands.Aubert.General.CorrectedTheorem36Statement` (module
  `Aubert.General.CorrectedTheorem36`) and the terminal-cokernel constructions of
  `Aubert.General.StandardComplex`.

The proof of Corollaire 3.9 also needs Aubert's Théorème 1.7 (involutivity of
`D_G` and its compatibility with induction), whose general targets belong to the
sibling task `e3d69272`.

## Faithfulness and scope

* All representations are arbitrary smooth representations unless finite length
  is an explicit hypothesis; no admissibility is assumed.
* `E ∈ 𝔈(I)` is `IsInCuspidalSeries`, which includes irreducibility.
* Through `SupportCategory` the module imports `Category.ConstituentDichotomy`,
  which imports the `GL_n` module `Classification.SupercuspidalSupport`. This is a
  module import only: the predicates and targets here use no classification
  theorem and assume none. A proof route for these targets must still record any
  classification it uses, transitively. Aubert's own proof of Corollaire 3.9 uses
  Théorème 1.7 and the corrected Théorème 3.6.
* The targets are meant for the standard families of the rational points of a
  connected reductive group over a nonarchimedean local field, with no
  restriction to split, quasisplit, characteristic-zero or positive-rank groups.
  For arbitrary families of the stated shape they can be false.

## Declarations

* `SharpFiniteLengthTarget`
* `SharpClassFormulaTarget`
* `SharpSupportRetentionTarget`
* `SharpIrreducibleTarget`
* `SharpCuspidalSeriesTarget`
* `SharpInvolutionTarget`

Each returns `Prop`. Lean includes a section variable only where it is used:
`SharpFiniteLengthTarget` takes `P M U h hclosed hδ hP hU`;
`SharpIrreducibleTarget` and `SharpInvolutionTarget` also take `hM hL`; the other
three also take `IsAssociate`.

## Sources

* A.-M. Aubert, Trans. AMS 347 (1995), Définition 1.5 and Notation 1.6
  (p. 2181), (3.5) and Théorème 3.6 (p. 2187), Corollaire 3.9 and its proof
  (p. 2189).
* A.-M. Aubert, *Erratum*, Trans. AMS 348 (1996), p. 4687 (`Alg({I})` and the
  corrected theorem) and p. 4690 (`E#` as the cokernel of `d_{|I|}`).
* D. Renard, *Représentations des groupes réductifs p-adiques* (2026 version),
  VI.6.2 and VI.6.4 (finite length), VI.7.2 (Bernstein decomposition).
