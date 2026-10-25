# Vanishing of the first idele-class cohomology

Module `Langlands.ClassField.Global.H1VanishingProof`. Main theorem:
`Langlands.ClassField.Global.ideleClassH1Vanishing : FundamentalClass.IdeleClassH1Vanishing.{u}`,
which proves the published statement
`Langlands.ClassField.Global.FundamentalClass.IdeleClassH1Vanishing.{u}` from
`Langlands.ClassField.Global.FundamentalClassStatement`. For every finite Galois extension
`E/F` of number fields in `Type u`, the actual group
`H¹(Gal(E/F), C_E) = relativeIdeleClassCohomology F E 1` is a subsingleton.

**Structure.** The module first proves the target from hypotheses, in
`H1VanishingProof.ideleClassH1Vanishing_of`. It takes four published child propositions, all at
the common universe `.{u, u}`:

- `hA : IdeleClassGaloisDescent` (module `IdeleClassGaloisDescentStatement`): for `E/K`
  Galois, `ideleClassInclusion : C_K → C_E` is injective and its range is exactly the
  `Gal(E/K)`-fixed classes.
- `hC : IdeleClassNormGaloisProduct`: `ideleClassInclusion (N_{E/K} y)` is the product of
  the Galois conjugates `σ y`.
- `hD : CyclicIdeleClassHerbrandQuotient` (first inequality): for cyclic `E/K`, `H¹` and
  `H²` are finite and `|H²| = [E : K] · |H¹|`.
- `hE : IdeleClassSecondInequality` (module
  `Langlands.Global.AdelicFunctoriality.IdeleClassSecondInequalityStatement`): the index of
  the norm range `N_{E/K} C_E` in `C_K` divides `[E : K]`.

It also takes a fifth hypothesis, the published generic group-cohomology statement
`hP : Langlands.Cohomology.PrimeSectionH1Vanishing.{u}` (module
`Langlands.Cohomology.PrimeSectionH1Statement`). For a finite group `G` and any
representation `A`, it says that `H¹(G, A) = 0` follows once `H¹(H/N, A^N) = 0` for every
subgroup `H ≤ G` and every normal subgroup `N ⊴ H` of prime index. No hypothesis restates
the target.

All five inputs have published proofs, which the module imports and plugs in one at a time:

- `hC`: `Langlands.ClassField.Global.ideleClassNormGaloisProduct` (module
  `IdeleClassNormGaloisProductProof`);
- `hP`: `Langlands.Cohomology.primeSectionH1Vanishing` (module
  `Langlands.Cohomology.PrimeSectionH1Proof`);
- `hA`: `Langlands.ClassField.Global.ideleClassGaloisDescent` (module
  `IdeleClassGaloisDescentProof`);
- `hD`: `Langlands.ClassField.Global.cyclicIdeleClassHerbrandQuotient` (module
  `CyclicIdeleClassHerbrandAssembly`);
- `hE`: `Langlands.Global.AdelicFunctoriality.ideleClassSecondInequality` (module
  `Langlands.Global.AdelicFunctoriality.IdeleClassSecondInequalityProof`).

The final theorem `ideleClassH1Vanishing` has no hypotheses.

## Route

The proof follows Milne, *Class Field Theory* v4.03, Chapter VII, Theorem 5.1(b) and
Lemmas 5.2–5.4 (printed pp. 212–213, PDF pp. 221–222): first the cyclic case from the two
inequalities, then a reduction to sections `H/N` of prime order. Milne reduces to `p`-groups
by Sylow restriction and then inducts along normal subgroups of index `p` with the
inflation–restriction sequence. Here that group theory is the hypothesis `hP`
(`PrimeSectionH1Vanishing`). The arithmetic input it needs is that
`H¹(H/N, C_E^N) = 0` whenever `N ⊴ H ≤ Gal(E/F)` has prime index. This is proved by
identifying `C_E^N` with `C_M` for `M` the fixed field of `N`, at the level of cocycles.

## Declarations

### `subsingleton_H1_of_isCyclic`

For cyclic `Gal(E/F)` and all four hypotheses: `H¹ = 0`. By `hD`,
`|H²| = [E:F] · |H¹|`. The published proof
`Langlands.ClassField.Global.cyclicH2NormIndexComparison hA hC F E` (module
`CyclicH2NormIndexComparisonProof`) gives that `|H²|` divides `[C_F : N_{E/F} C_E]`; by `hE`
this index divides `[E:F]`. Cancelling the positive degree `[E:F]` gives
`|H¹| ∣ 1`. Since `H¹` is finite, it is a subsingleton.

### `exists_coboundary_of_prime_card`

Let `E/K` be Galois and `M` an intermediate field with `M/K` Galois of prime degree. Let
`f : Gal(E/K) → C_E` be a multiplicative 1-cocycle,
`f(στ) = f(σ) · σ(f(τ))`, with `f = 1` on `Gal(E/M)`. Then `f` is a coboundary:
`f(σ) = σ(c)/c` for some `c : C_E`. The proof proceeds as follows.

1. The cocycle identity gives `f(σn) = f(σ)` for `n ∈ Gal(E/M)`. Since `Gal(E/M)` is normal,
   `n(f(σ)) = f(σ)` for every such `n`. So every value is fixed by `Gal(E/M)`, after
   transporting the action through `relativeIdeleClassAut_restrictScalars`
   (module `CocycleRestriction`).
2. By `hA` for `E/M`, each value is `ideleClassInclusion (g₀ σ)` for a unique `g₀ σ : C_M`.
   The function is constant on the fibres of `restrictNormalHom M`, so it descends along a
   chosen section `lift` of `Gal(E/K) → Gal(M/K)`.
3. `ideleClassInclusion_relativeIdeleClassAut` (module `CohomologyMaps`) and injectivity
   from `hA` show that `τ ↦ g₀(lift τ)` is a 1-cocycle of `Gal(M/K)` in `C_M`.
4. `Gal(M/K)` has prime order, hence it is cyclic. By `subsingleton_H1_of_isCyclic` its
   additive cocycle class vanishes (`H1π_eq_zero_iff`), giving `d` with
   `g₀(lift τ) = τ(c)/c`. Pushing `c` into `C_E` and using step 3 gives the required
   coboundary.

### `exists_coboundary_of_prime_index`

This is the same statement with `M` replaced by a normal subgroup `N ⊴ Gal(E/K)` of prime
index. Take `M = fixedField N`. Then `M/K` is Galois, `|Gal(M/K)| = [Gal(E/K) : N]` by
`IsGalois.normalAutEquivQuotient`, and `fixingSubgroup (fixedField N) = N`.

### `subsingleton_H1_quotientToInvariants`

For `H ≤ Gal(E/F)` and `N ⊴ H` of prime index,
`H¹(H/N, (Res_H C_E)^N) = 0`, with `(Res_H C_E)^N` Mathlib's
`Rep.quotientToInvariants`. Let `K' = fixedField H`. The isomorphism
`e : Gal(E/K') ≃* H` composes `fixingSubgroupEquiv` with `fixingSubgroup_fixedField`, and
it acts as `restrictScalars`. Let `N'` be the preimage of `N`; it is normal of the same prime
index. A cocycle `z` on `H/N` gives a multiplicative cocycle `f(σ) = z(e(σ) N)` on
`Gal(E/K')` that is trivial on `N'`. By the previous lemma, `f(σ) = σ(c)/c`. Then `c` is
`N`-invariant, because `f = 1` on `N'`, and the coboundary of `c` in the `N`-invariants is
`z`. Hence `[z] = 0`.

### `ideleClassH1Vanishing_of`

`hP` applied to `relativeIdeleClassRepresentation F E` and to the previous lemma gives `Subsingleton (relativeIdeleClassCohomology F E 1)` for every Galois
`E/F`, which is the target proposition.

### `ideleClassH1Vanishing_of_descent`

This is `ideleClassH1Vanishing_of` with `hC := ideleClassNormGaloisProduct` (at `.{u, u}`) and
`hP := Langlands.Cohomology.primeSectionH1Vanishing`. Its remaining hypotheses are `hA`, `hD`
and `hE`, and its conclusion is `FundamentalClass.IdeleClassH1Vanishing.{u}`.

### `ideleClassH1Vanishing_of_inequalities`

This is `ideleClassH1Vanishing_of_descent` with `hA := ideleClassGaloisDescent.{u, u}`. Its
remaining hypotheses are `hD` (cyclic Herbrand quotient) and `hE` (second inequality), and its
conclusion is `FundamentalClass.IdeleClassH1Vanishing.{u}`.

### `ideleClassH1Vanishing_of_secondInequality`

This is `ideleClassH1Vanishing_of_inequalities` with
`hD := cyclicIdeleClassHerbrandQuotient.{u, u}`. Its only remaining hypothesis is `hE` (second
inequality), and its conclusion is `FundamentalClass.IdeleClassH1Vanishing.{u}`.

### `ideleClassH1Vanishing`

This is `ideleClassH1Vanishing_of_secondInequality` applied to the published proof
`Langlands.Global.AdelicFunctoriality.ideleClassSecondInequality.{u, u}`. It has no hypotheses.
Its type is exactly `FundamentalClass.IdeleClassH1Vanishing.{u}`: for every finite Galois
extension `E/F` of number fields in `Type u`,
`Subsingleton (relativeIdeleClassCohomology F E 1)`.

## Checks

`ideleClassH1Vanishing` has the single universe parameter `u` and is not applied at any
fixed universe: it proves `FundamentalClass.IdeleClassH1Vanishing.{u}` for an arbitrary `u`.
The published inputs are used at `.{u, u}`, which is their instance for fields in one
universe. The theorem depends only on the standard axioms `propext`, `Classical.choice` and
`Quot.sound` (development check 7bab8202, Library 91e7eebd). It uses no `sorry` and no new
axioms.

## Sources

- J. S. Milne, *Class Field Theory* v4.03 (2020), `milne-2020-class-field-theory`, Chapter VII:
  Theorem 4.3 (printed p. 211, PDF p. 220), Theorem 5.1 and Lemmas 5.2–5.4 (printed
  pp. 212–213, PDF pp. 221–222).
- E. Artin and J. Tate, *Class Field Theory* (2009), `artin-tate-2009-class-field-theory`:
  Chapter V §1 Theorem 1 (first inequality), Chapter VI §1 (second inequality), and
  Chapter XIV §2 Lemma 1 (printed pp. 147–148) for the group-theoretic reduction.

The Lean route is at the level of explicit cocycles. It uses no corestriction for idele
classes and no inflation–restriction sequence for `C_E` itself. Those appear only in
proofs of the generic statement `PrimeSectionH1Vanishing`.
