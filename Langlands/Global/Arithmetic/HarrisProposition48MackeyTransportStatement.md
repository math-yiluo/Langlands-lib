# Mackey constituents, child transport and induced parameters in Proposition 4.8

Module `Langlands.Global.Arithmetic.HarrisProposition48MackeyTransportStatement`.
Statements only (Prop-valued definitions); nothing is proved here.

## Sources

- Harris (1998), *The local Langlands conjecture for GL(n) over a p-adic
  field, n < p*, Invent. Math. 134, 177–210 (registered source
  `harris-1998-local-langlands`), Proposition 4.8 and its proof, printed
  pp.202–203 (`math_9611226v1.tex` lines 1566–1664). The parts used are:
  - lines 1574–1613: the induction over a tower inside the normal closure `L`
    of `E'/E`. The Mackey constituents of the restriction of `Ind_{E'/E} ξ`
    to an intermediate field `E_i` are indexed by double cosets (line 1579),
    and the constituent of `a` is induced from `a(ξ) ∘ N` on `a(E') · E_i`;
  - lines 1630–1645: `Π_{t-1}` over the prime cyclic step `E_{t-1}/E` is
    `Gal(E_{t-1}/E)`-invariant by strong multiplicity one;
  - lines 1646–1663: the prime orbit. If there are `q = [E_{t-1} : E]` double
    cosets, they form a principal homogeneous space under `Gal(E_{t-1}/E)`,
    and `Π_{t-1} = Π(e,t-1) ⊞ α(Π(e,t-1)) ⊞ ⋯ ⊞ α^{q-1}(Π(e,t-1))`;
  - lines 1663–1664: "It is thus clear that `Π` is a weak automorphic
    induction of `ξ`".
- Plan note `operator-external-inputs-plan-2026-11-16`
  (`external-inputs-plan.tex`), Section 4.8: Remark 4.2 (lines 859–894),
  including the fibres of `A_{i-1} → A_i` (line 860) and
  `α Π(b,i-1) = Π(αb,i-1)` (line 881); the induction (line 899); the prime
  branch (line 908); the infinity type (lines 910–912).
- The design of the exact-stabilizer branches
  (`HarrisProposition48ExactStabilizerParameterData`):
  solutions carry the complex-place parameters of the representation induced
  from `ξ`, in the vocabulary and normalization of the archimedean bridge.
  Regularity of the induced class comes from these parameters.
- Arthur–Clozel, *Simple algebras, base change, and the advanced theory of the
  trace formula*, Chapter III: weak induction is a relation between unramified
  components at almost all places, and induction is transitive in towers.

All statements are derived interfaces of the Library's Proposition 4.8
vocabulary: `Proposition48Problem`, `conjugateField`, `MackeyIndex`,
`mackeyField`, `mackeyCharacter` and `IsPrimeCyclicStep`
(`Langlands/Global/Arithmetic/HarrisProposition48InductionData.lean`), and
`IsMackeyConstituent`, `IsInducedComplexPlaceParameter` and
`HasInducedComplexPlaceParameters`
(`Langlands/Global/Arithmetic/HarrisProposition48ExactStabilizerParameterData.lean`).
Each is stated in the form the reductions of the exact-stabilizer branches
use. For each statement, the source entry says which passage uses the fact
without stating it.

Notation: `Q` is a problem with fields `E ⊆ E' ⊆ L` and Hecke character
`ξ` of `E'`, `G = Gal(L/E)`, `D` an intermediate field of `L/E`,
`Q.conjugateField a = a(E')`, `Q.mackeyField D a = D ⊔ a(E') = D · a(E')`,
and `Q.mackeyCharacter D a = a(ξ) ∘ N_{D·a(E')/a(E')}`.

## Statements

### `Proposition48MackeyFibreStatement.{uF}`

- Hypotheses: `IsNormalClosure Q.E Q.E' Q.L`; `Q.IsPrimeCyclicStep D` (`D/E` is
  Galois and cyclic of prime degree); and
  `Nat.card (Q.MackeyIndex D) = Module.finrank Q.E D` (there are `[D : E]`
  double cosets `Gal(L/D) \ G / Gal(L/E')`).
- Conclusion: `D ≤ Q.conjugateField 1` (that is, `D ⊆ E'` inside `L`), and for
  all `a b ∈ G`,
  `DoubleCoset.mk D.fixingSubgroup (Q.conjugateField 1).fixingSubgroup a =
  DoubleCoset.mk … b` if and only if `∀ x ∈ D, a x = b x`.
- Why: `L/E` is Galois. `H = Gal(L/D)` is normal of index `[D : E]`, and let
  `K = Gal(L/E')`. Since `H` is normal, `H a K = a H K`, so the double cosets
  are the cosets of `HK` and there are `[G : HK]` of them. The count `[G : H]`
  forces `HK = H`, so `K ≤ H`, so `D ⊆ E'` by the Galois correspondence. Then
  `H a K = a H`, and `a H = b H` if and only if `a` and `b` agree on `D`.
- Source: Harris, lines 1647–1649 ("If `A_{t-1}` has `q` elements then it
  is a principal homogeneous space under `Gal(E_{t-1}/E)`"); plan note line
  860.

### `Proposition48MackeyConstituentGaloisConjugateStatement.{uF, uV}`

- Hypotheses: `a, τ ∈ G` and `σ ∈ Gal(D/E)` with
  `∀ x : D, (σ x : L) = τ x` (`τ` restricts to `σ`); `r : ℕ`; a cuspidal class
  `c` over `D` of rank index `r`; and `Q.IsMackeyConstituent D a c`, that is,
  `c` is a weak automorphic induction of `Q.mackeyCharacter D a`.
- Conclusion: `Q.IsMackeyConstituent D (τ * a) (IsoClass.galoisConj σ c)`.
- Why: `galoisConj σ c = arithmeticComap σ.symm c` is the transport of `c`
  along `σ`. Since `τ` restricts to `σ` on `D` and `τ(a(E')) = (τa)(E')`, `τ`
  maps `D · a(E')` onto `D · (τa)(E')`. It carries `a(ξ) = ξ ∘ a⁻¹`
  (`conjugateCharacter`) to `(τa)(ξ) = ξ ∘ (τa)⁻¹` (`AlgEquiv` multiplication
  is composition), and it commutes with the norms. So `τ` carries the Mackey
  character of `a` to that of `τ * a`. Weak automorphic induction is preserved
  when both sides are transported along compatible field isomorphisms, here
  `σ` on `D` and `τ` on `D · a(E')`.
- Source: Harris, lines 1646–1655. The constituents `α^j(Π(e,t-1))` are the
  solutions for the double cosets `α^j e`. Plan note line 881 has the same
  identity as `α Π(b,i-1) = Π(αb,i-1)`.

### `Proposition48MackeyChildTransportStatement.{uF, uV}`

- Hypotheses: a double coset representative `a ∈ G`, a problem `R`, and ring
  isomorphisms `e : R.E ≃+* D` and `e' : R.E' ≃+* Q.mackeyField D a` such that
  - they are compatible: `(e' (algebraMap R.E R.E' x) : L) = (e x : L)`;
  - they identify the characters:
    `R.ξ = (Q.mackeyCharacter D a).comp (ideleClassEquiv e')`.

  These are the witnesses `e`, `e'` of `IsMackeyChild Q D a R` together with
  its second and fifth clauses, so they are available for every child.
  `IsAuxiliaryMackeyChild` is `IsMackeyChild` of the paddings, which change
  only the place datum and the local character and keep the fields and `ξ`.
  The statement then quantifies over `r : ℕ` and a cuspidal realization `S`
  over `R.E` of rank index `r`.
- Conclusion: the pullback `S.arithmeticComap e.symm` over `D`
  1. is a Mackey constituent of `a` when `S.isoClass` is a weak automorphic
     induction of `R.ξ`;
  2. when `R.HasInducedComplexPlaceParameters S.isoClass`, has at every complex
     place `u` of `D` a parameter list `ds`
     (`IsoClass.HasComplexPlaceParameter u ds`) that is, up to order, the
     Langlands sum `complexPlaceLanglandsSum u en (fun w => [dχ w])`, taken
     over an enumeration `en` of the places of `D · a(E')` above `u`, of
     actual parameters `dχ w` of the Mackey character. This is the `D`-level
     form of `IsInducedComplexPlaceParameter`, with `D · a(E')/D` in place of
     `E'/E`.
- Why: the pullback along `e.symm` transports weak automorphic induction
  along the compatible pair `(e, e')`. It transports complex places and their
  parameters too. `complexPlaceParameterTransport` makes the comparison
  independent of the embedding chosen at each place, so the induced lists of
  `R` at the place of `R.E` corresponding to `u` become induced lists over `D`
  at `u`.
- Source: Harris, lines 1583–1597 and 1630–1633. The solution `Π(a,t-1)` of
  the child problem `(E_{t-1}, a(E') · E_{t-1}, a(ξ) ∘ N)` is used directly
  as a constituent over `E_{t-1}`. The Library's children are abstract
  problems linked to the parent by isomorphisms, so the identification needs
  this transport. The parameters follow the design of
  `HarrisProposition48ExactStabilizerParameterData`.

The other transported properties used by the branches (unitary central
character, supercuspidal components at corresponding places, conjugate
self-duality) are general and are stated in
`Langlands.Automorphic.CuspidalArithmeticTransportStatement`.

### `Proposition48PrimeInducedParameterStagesStatement.{uF}`

- Hypotheses: `D ≤ Q.conjugateField 1`; a complex place `v` of `E`; an
  enumeration `en : Fin d ≃ InfinitePlacesAbove D v`; and for each place `w`
  of `D` above `v` a list `ds w` that is, up to order, the Langlands sum
  `complexPlaceLanglandsSum (complexPlaceAbove v w) en' (fun u => [dχ u])`,
  over some enumeration `en'` of the places of `D · E'` (`Q.mackeyField D 1`)
  above `w`, of actual parameters `dχ u` of the Mackey character of `1`.
- Conclusion:
  `Q.IsInducedComplexPlaceParameter v (complexPlaceLanglandsSum v en ds)`.
- Why: as `D ⊆ E'`, `D · E'` is the copy `Q.conjugateField 1` of `E'`, and the
  Mackey character of `1` is `ξ` read on this copy (the norm of a trivial
  extension is the identity). The places of `E'` above `v` are the disjoint
  union over `w` of the places above `w`. Reading a list at `u` in the
  coordinates of `w` and then in those of `v` is the same as reading it in the
  coordinates of `v`: `complexPlaceParameterTransport` conjugates exactly when
  the restricted embedding differs, and two conjugations cancel. `List.Perm`
  is preserved by `map` and `flatten`.
- Source: the design of `HarrisProposition48ExactStabilizerParameterData`
  (solutions carry the parameters of `Ind ξ`); plan note
  lines 908–912. Harris has no counterpart, because he does not track the
  infinity type through the induction (his Remark, lines 1615–1628).

### `Proposition48PrimeInductionStagesStatement.{uF, uV}`

- Hypotheses: `D ≤ Q.conjugateField 1`; `r m : ℕ`; a cuspidal class `c` over
  `E` and a cuspidal class `d` over `D`;
  `IsoClass.IsWeakInductionOf c d` (`c` is a weak induction of `d`); and
  `Q.IsMackeyConstituent D 1 d`.
- Conclusion: `c.IsWeakAutomorphicInductionOf Q.ξ`.
- Why: at almost all places `v` of `E`, the unramified component of `c` is the
  induction of the components of `d` at the places of `D` above `v`. Each of
  those is the induction of the components of the Mackey character of `1`,
  which is `ξ` (as above). Induction is transitive. The two relations each
  come with spectral systems of `d`, possibly from different presentations. A
  proof has to check that these agree at almost all places, which is
  unramified uniqueness of local components.
- Source: Harris, lines 1663–1664 ("It is thus clear that `Π` is a weak
  automorphic induction of `ξ`"); Arthur–Clozel, Chapter III (transitivity).

### `Proposition48InducedParameterRegularAlgebraicStatement.{uF}`

- Hypotheses: the archimedean bridge
  `CuspidalComplexParameterBridgeTCStatement.{0}` (module
  `CuspidalComplexParameterBridgeStatement`);
  for a problem `Q`, `IsAlgebraicAfterTwist (finrank Q.E Q.E' - 1) Q.ξ`,
  `IsRelativelyRegular Q.E Q.ξ` and `IsConjugateInverse Q.ξ`; and a cuspidal
  class `c` over `E` with `Q.HasInducedComplexPlaceParameters c`. No other
  clause of validity is assumed.
- Conclusion: `c.IsRegularAlgebraic`.
- Why: let `n = [E' : E]`. At each complex place `v` of `E` (all are complex,
  `E` being CM), the induced list has one entry per place of `E'` above `v`,
  so `n` entries. The length clause of `HasComplexPlaceParameter` makes the
  rank of `c` equal to `n`, so no rank hypothesis is needed. Conjugate
  inversion makes the exponent of each entry `0`, so
  `zExponent = weight/2 = -zBarExponent`. Algebraicity after the twist of
  parity `n - 1` makes `weight ≡ n - 1 (mod 2)`, so both exponents lie in
  `(n - 1)/2 + ℤ`. Relative regularity makes the weights of the different
  places of `E'` above `v` distinct after `complexPlaceParameterTransport`
  (which changes the sign of the weight exactly when it conjugates). So the
  `z`-exponents are distinct and, by `zBarExponent = -zExponent`, so are the
  `z̄`-exponents. Each induced list is therefore
  `ComplexPlaceParameter.IsClozelRegularAlgebraic n`, and the bridge gives a
  regular algebraic infinitesimal character for a representative.
- Source: plan note lines 910–912 (the infinity type); in the design of the
  branches, regularity of the induced class comes from B7(2) and the children's
  parameters.

### `WeakInductionConjugateInverseSelfDualStatement.{uV, uE, uE'}` and its TC form

- Hypotheses: spectral rigidity, `CuspidalSpectralRigidityStatement.{uE, uV}`
  (for the TC form, `CuspidalSpectralRigidityTCStatement.{uE, uV}`); CM fields
  `E : Type uE`, `E' : Type uE'` with `[Algebra E E']` and
  `CompactSpace (AdeleQuotient E)`; a Hecke character `ξ` of `E'` with
  `IsConjugateInverse ξ` (`ξ = ξ⁻¹ ∘ c`); `r : ℕ`; and a cuspidal class `c`
  over `E` with `c.IsWeakAutomorphicInductionOf ξ`.
- Conclusion: `c.IsConjugateSelfDual`.
- Why: the CM involution of `E'` restricts to that of `E`, because both induce
  complex conjugation under every complex embedding. So the conjugate
  contragredient of `Ind ξ` is `Ind (ξ⁻¹ ∘ c) = Ind ξ`. The conjugate
  contragredient of `c` therefore has, at almost all places, the unramified
  components induced from `ξ`, the same as `c`. Rigidity (strong
  multiplicity one) identifies the two cuspidal classes. A proof needs, beyond
  the rigidity premise, the conjugate contragredient of `c` as a cuspidal
  class with its spectral system (`Langlands/Automorphic/Contragredient.lean`,
  `Langlands/Automorphic/CuspidalConjugateRealization.lean`), and the
  conversion of the identification into the pairing of `IsConjugateSelfDual`.
  The conclusion holds unconditionally, by the theorem of Jacquet and Shalika.
  The premise names the Library statement such a proof would use.
- Source: conjugate self-duality is part of the conclusion of Harris's
  Proposition 4.8 (the hypothesis `ξ = ξ⁻¹ ∘ c`, `math_9611226v1.tex` lines
  1558–1559). His proof of the prime orbit (lines 1646–1664) does not argue it
  separately. This is a derived interface.

## Universes

`uF` is the universe of the local field in `Proposition48Problem`, `uV` the
carrier universe of spectral presentations. The number fields of a problem
are in `Type`. The last two statements have independent field universes `uE`
and `uE'`.

## Consumers

- `HarrisProposition48ExactStabilizerPrimeBranchReductionStatement`: the reduction of
  `Proposition48ExactStabilizerPrimeBranchStatement` and its TC form uses all
  eight statements. The route: the trivial double coset's child is moved to
  `D` (child transport). By the Galois conjugation and fibre statements, the
  moved constituent is not stable under any nontrivial element of
  `Gal(D/E)`. Weak induction in stages and the parameter stages give the
  weak induction of `ξ` and the induced parameters. The regular-algebraicity
  statement and conjugate self-duality finish the argument.
- The exact-stabilizer singleton branch
  (`Proposition48ExactStabilizerSingletonBranchStatement` in
  `HarrisProposition48ExactStabilizerBranchStatement`, and its restricted form in
  `HarrisProposition48ExactStabilizerRestrictedDescentStatement`): its proof route uses
  the child transport (with any double coset `a`), the regular-algebraicity statement
  and conjugate self-duality.
- The general-position prime branch reduction
  (`HarrisProposition48PrimeBranchReductionStatement`) has the transport of children to `D`, Galois
  invariance, Mackey's formula and conjugate self-duality among its
  obligations. It can reuse the child transport, the Galois conjugation of
  Mackey constituents, weak induction in stages and conjugate self-duality.
