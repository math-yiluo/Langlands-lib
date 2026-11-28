# Pairs of Henniart candidates compatible with a cyclic base change

The module `Langlands.Correspondence.HenniartCandidatePairBaseChangeStatement` has two
definitions in `Langlands.Henniart.Numerical` and two proposition definitions in
`Langlands.Henniart`. It contains no theorems and proves neither proposition. It imports
`Langlands.Correspondence.HenniartCandidateBaseChangeFiniteImageReductionStatement`.

## Notation

- `S : Numerical.CyclicPrimeStep.{uK} p` is a Galois extension \(M/L\) of \(p\)-adic
  fields whose Galois group `S.Gal` has prime order. Here \(L=\) `S.base`, \(M=\) `S.top`,
  and `S.embedding : L →ₐ[ℚ_p] M`.
- `Ch : Numerical.CyclicBaseChangeMap.{uK, uV} S` is a function. For each `k : ℕ` it sends
  a supercuspidal class `π` of `GL_{k+1}(L)` to a multiset `Ch k π` of pairs `⟨j, ρ⟩`, where
  `ρ` is a supercuspidal class of `GL_{j+1}(M)`.
- Over a \(p\)-adic field `K`, `PadicSupercuspidal.Lattice K` is the free abelian group on
  the supercuspidal classes of all `GL_n(K)`, each tagged with its rank `n : ℕ+`.
  `PadicSupercuspidal.UnitaryLattice K` is the free abelian group on the unitary
  supercuspidal classes. `LocalWeil.UnitaryLattice K` is the free abelian group on the
  unitary irreducible classes of the Weil group \(W_K\), and `LocalWeil.Lattice K` is the
  free abelian group on all its irreducible classes. Each `includeUnitary` includes a
  unitary lattice into the corresponding full lattice. `generator b` is the basis element
  of the class `b`.
- `LocalWeil.unitaryFiniteFactoringSupported K q` is the span of the unitary irreducible
  classes of \(W_K\) that factor through `q` composed with the projection of \(W_K\) to the
  absolute Galois group. Here `q : Field.absoluteGaloisGroup K.Carrier →* Q` is any group
  homomorphism to a finite group, and it need not be continuous or surjective.
- `LocalWeil.realizeExact K` sends a virtual class of \(W_K\) into the exact Grothendieck
  group of continuous finite-dimensional complex representations of \(W_K\).
  `Weil.Local.extensionWeilMap S.base S.top S.embedding : W_M →ₜ* W_L` is the map of Weil
  groups induced by `S.embedding`. `ExactGrothendieckGroup.continuousRestrict` along it
  restricts from \(W_L\) to \(W_M\) on these groups.
- `StableMap.IsCandidate K q Φ` is a predicate on an isomorphism `Φ : W ≃ₗ[ℤ] A`, where `W`
  is a sublattice of `LocalWeil.UnitaryLattice K` and `A` is a sublattice of
  `PadicSupercuspidal.UnitaryLattice K`. It says that `W` contains
  `unitaryFiniteFactoringSupported K q` and that `Φ` has the properties of Henniart's
  candidates (`LatticeMap.HenniartProperties`; Henniart 2000, §§3.8 and 4.1).

## Definitions

### `Numerical.cyclicBaseChangeLatticeMap.{uK, uV} S Ch`

This is the `ℤ`-linear map

```text
PadicSupercuspidal.Lattice.{uK, uV} S.base →ₗ[ℤ] PadicSupercuspidal.Lattice.{uK, uV} S.top
```

defined on the basis as follows. Let `π` be a supercuspidal class of `GL_n(L)`. The map
sends the basis element of `π` to the sum, with multiplicities, of the basis elements of
the classes `ρ` of rank `j + 1` for `⟨j, ρ⟩ ∈ Ch (n - 1) π`. It is the additive extension
of `Ch` from classes to lattices. In Lean, the rank `n` is written `(n - 1).succPNat` with
`n - 1 = n.natPred`. The class is moved to that rank by `Extension.rankCast` along
`PNat.succPNat_natPred`.

### `Numerical.IsCandidatePairBaseChangeCompatible.{uK, uW, uV, uQ} S Ch q Φ_L Φ_M`

Let `q : Field.absoluteGaloisGroup S.base.Carrier →* Q` be a homomorphism to a finite
group `Q : Type uQ`. Let `Φ_L : W_L ≃ₗ[ℤ] A_L` and `Φ_M : W_M ≃ₗ[ℤ] A_M` be isomorphisms of
sublattices. Here `W_L` and `W_M` are sublattices of `LocalWeil.UnitaryLattice.{uK, uW}` of
\(L\) and \(M\), and `A_L` and `A_M` are sublattices of
`PadicSupercuspidal.UnitaryLattice.{uK, uV}` of \(L\) and \(M\). The predicate says the
following. For every `x : W_L` whose value lies in `unitaryFiniteFactoringSupported S.base q`,
there is `x' : W_M` with

```text
ExactGrothendieckGroup.continuousRestrict (Weil.Local.extensionWeilMap S.base S.top S.embedding)
    (LocalWeil.realizeExact S.base (LocalWeil.includeUnitary S.base x)) =
  LocalWeil.realizeExact S.top (LocalWeil.includeUnitary S.top x')
∧ cyclicBaseChangeLatticeMap S Ch (PadicSupercuspidal.includeUnitary S.base (Φ_L x)) =
  PadicSupercuspidal.includeUnitary S.top (Φ_M x')
```

The first equation says that the restriction of `x` to \(W_M\) is `x'` in the exact
Grothendieck group of \(W_M\). In particular, the restriction lies in the domain of
`Φ_M`. The second says that `Ch` sends `Φ_L x` to `Φ_M x'`. In short, this is
\(\mathrm{Ch}\circ\Phi_L=\Phi_M\circ\mathrm{Res}^{W_L}_{W_M}\) on the virtual unitary
classes of \(W_L\) that factor through `q`. The predicate does not require `Φ_L` or
`Φ_M` to be candidates.

## Propositions

### `CertifiedCandidatePairCompatibilityStatement.{uK, uW, uV}`

Take a prime `p`, a step `S` and a map `Ch` with two properties. First, `Ch` is a weak
cyclic base change (`Numerical.IsWeakCyclicBaseChange S Ch`). Second, for every
`σ : S.Gal` with `σ ≠ 1`, `Ch` is certified by σ-lifts on supercuspidal classes
(`BaseChange.IsSigmaLiftOnSupercuspidals S.embedding Ch σ`). Let
`q_L : Field.absoluteGaloisGroup S.base.Carrier →* Q_L` and
`q_M : Field.absoluteGaloisGroup S.top.Carrier →* Q_M` be homomorphisms to finite groups
`Q_L Q_M : Type uK`. The proposition asserts that there exist isomorphisms `Φ_L` over \(L\)
and `Φ_M` over \(M\) such that:

- `Φ_L` is a candidate at `q_L`: `StableMap.IsCandidate.{uK, uW, uV, uW, uK} S.base q_L Φ_L`;
- `Φ_M` is a candidate at `q_M`: `StableMap.IsCandidate.{uK, uW, uV, uW, uK} S.top q_M Φ_M`;
- `IsCandidatePairBaseChangeCompatible S Ch q_L Φ_L Φ_M` holds.

### `CandidatePairFiniteImageReductionStatement.{uK, uW, uV}`

This is the implication

```text
CertifiedCandidatePairCompatibilityStatement.{uK, uW, uV} →
  CandidateFiniteImageBaseChangeCompatibilityReductionStatement.{uK, uW, uV}
```

The conclusion says the following. Assume candidate existence,
`CandidateExistenceStatement.{uK, uW, uV, uW, uK}`. Then every weak cyclic base change
that is certified by σ-lifts for every `σ ≠ 1` satisfies (CI1) on the classes of finite
image (`Numerical.IsCandidateBaseChangeCompatibleOnFiniteImage`).

### Universes

- `uK` is the universe of the \(p\)-adic fields, `uW` that of the Weil representation
  carriers, and `uV` that of the supercuspidal representation carriers. These are the
  levels of `CandidateFiniteImageBaseChangeCompatibilityReductionStatement`.
- `uQ` is free in `IsCandidatePairBaseChangeCompatible` because the predicate involves
  only the one quotient `q`.
- `CertifiedCandidatePairCompatibilityStatement` takes the quotients `Q_L` and `Q_M` in
  `Type uK`. This is the universe of the quotients in `StableMap.IsStableImage` and
  `StableMap.IsFiniteFactoring`, so the stable-image quotients used in the reduction are
  admissible.
- Both candidate predicates are taken at `IsCandidate.{uK, uW, uV, uW, uK}`, the levels of
  `CandidateExistenceStatement.{uK, uW, uV, uW, uK}` in the target of the reduction. The
  fourth level is the universe of the local-constant-system assignments in the factor
  conditions of `LatticeMap.HenniartProperties`. It is `uW`, as in
  `StableExistsAt.{uK, uW, uV, uW}`. The fifth level is the universe of the quotient,
  `uK`.

## Mathematical origin

Neither proposition is a published result. §6.5 of the numerical correspondence route
note discusses input (I4), the hypothesis (CI). Its source (b) says that if Henniart's
candidates over the various fields are compatible with cyclic base change of prime
degree, they provide (CI). It also says that this compatibility is not stated in
Henniart (2000). The note expects it to follow from the construction by the usual global
argument, and marks this as an assessment rather than a published statement.
`CertifiedCandidatePairCompatibilityStatement` isolates the global part of that
argument: for compatible pairs of candidates at arbitrary finite quotients, `Ch` matches
the restriction of Weil classes. `CandidatePairFiniteImageReductionStatement` is the
local deduction from it of (CI1) for the rank extensions of the stable images
(`Extension.rankExtension`, Henniart 2000, §§4.1–4.4) on classes of finite image.

## Intended proof of `CandidatePairFiniteImageReductionStatement` (local)

Assume the pair statement and candidate existence. Fix `p`, `S` and a certified weak
cyclic base change `Ch`. Take `k`, `hL : StableExistsAt S.base k.succPNat`, a class `σ` with
a unitary witness `b₀` of finite factoring, a multiset `m` with
`IsRestrictionDecomposition S σ m`, and `hm`.

1. **The class over `L`.** By `hL`, `b₀` has a stable image `y_σ`.
   `StableMap.IsStableImage.exists_quotient` gives a finite quotient `q_σ` with
   `generator b₀ ∈ unitaryFiniteFactoringSupported S.base q_σ`. It also shows that every
   candidate at a refinement of `q_σ` sends `generator b₀` to `y_σ`.
   `StableMap.IsStableImage.exists_generator` gives `y_σ = generator π₀` with `π₀` of rank
   `k + 1`. The trivial twist is a stable decomposition of `σ`. Twist independence follows
   from `Extension.unramifiedTwistIndependence_of_reciprocity`, candidate existence and
   `LocalClassField.commonClosureReciprocityExistence`. With it,
   `Extension.rankExtensionBasis_eq` identifies `Extension.rankExtension S.base hL σ` with
   `π₀`.
2. **The constituents over `M`.** The restriction of a unitary class of finite image to
   \(W_M\) is a direct sum of unitary classes of finite image. So each `τ ∈ m` is unitary,
   and it factors through a finite quotient of the absolute Galois group of \(M\). By
   `hm`, `τ` has a stable image `y_τ = generator ρ_τ` at a quotient `q_τ`. As in step 1,
   `Extension.rankExtension S.top (hm τ _) τ.2` is `ρ_τ`.
3. **A pair of candidates.** Apply the pair statement with `q_L = q_σ` and with `q_M` the
   product of the `q_τ`, a finite group in `Type uK`. Each projection composed with `q_M`
   is `q_τ`. So `IsStableImage.exists_quotient` gives `Φ_M (generator τ) = y_τ`, the
   argument of `StableMap.IsCandidate.comp` and `StableMap.exists_common_candidate`. It
   also gives `Φ_L (generator b₀) = y_σ`.
4. **Restriction.** The compatibility at `x = generator b₀` gives `x'`. Its exact class
   equals the restriction of the exact class of `σ`. The restriction identity of
   `IsRestrictionDecomposition` is stated with `Weil.Local.extensionRestrictClass` and
   `FiniteRepresentation.directSumClass`. The proof must carry this identity into the
   exact Grothendieck group, where it says that the restriction of `σ` is the sum of the
   classes `τ ∈ m`. This module does not contain that comparison. Since `realizeExact` is
   injective on unitary lattices (`Weil.realizeExact_includeUnitary_injective`),
   `x' = Σ_{τ ∈ m} generator τ`.
5. **Coefficients.** By linearity of `Φ_M`, the second equation of the compatibility
   becomes `cyclicBaseChangeLatticeMap S Ch (generator π₀) = Σ_{τ ∈ m} generator ρ_τ`. The
   left side is the sum of the basis elements of `Ch k π₀`. Distinct multisets of basis
   elements have distinct sums, and `j ↦ j.succPNat` is injective. So comparing
   coefficients gives the multiset identity of (CI1):

   ```text
   Ch k (Extension.rankExtension S.base hL σ) =
     m.pmap (fun τ h => ⟨τ.1, Extension.rankExtension S.top h τ.2⟩) hm
   ```

The hypotheses of the pair statement are among those of the reduction's target, so the
reduction assumes nothing else.

## Intended proof of `CertifiedCandidatePairCompatibilityStatement` (global)

1. **Globalization.** Only finitely many irreducible classes factor through `q_L` or
   `q_M`, and each has finite image. Choose a finite Galois extension \(K'/L\)
   containing \(M\) such that every class of \(W_L\) factoring through `q_L` factors
   through \(\mathrm{Gal}(K'/L)\), and every class of \(W_M\) factoring through `q_M`
   factors through \(\mathrm{Gal}(K'/M)\). Globalize it as in Henniart (2000),
   §3.1 (Théorème) and §3.3: take a Galois extension \(F'/F\) of number fields and a
   place \(v\) of \(F\) with full decomposition group, whose completion is \(K'/L\). Let
   \(E\subset F'\) be the fixed field of \(\mathrm{Gal}(K'/M)\). Then \(E/F\) is cyclic
   of degree \([M:L]\), with one place \(w\) above \(v\) and completion \(M\).
2. **Candidates.** Henniart's construction (Henniart 2000, §§3.4–3.8) produces `Φ_L` over
   \(F\) and `Φ_M` over \(E\). It uses Brauer combinations of monomial representations and
   the automorphic representations attached to them by Harris (1998), Proposition 4.8.
3. **Base change.** Global cyclic base change (Arthur–Clozel 1989, III, Theorem 4.2) and
   strong multiplicity one take the automorphic data over \(F\) to the data attached to
   the restricted Galois data over \(E\). The external-inputs plan names the cyclic
   transfer inputs B1–B3 and the rigidity input C2 for this step.
4. **The place above `v`.** The local identity at \(w\) is Arthur–Clozel III, Theorem
   5.1, for the certified map `Ch`. In the Library, clause N′ of the proposition
   definition `Automorphic.Unramified.CyclicStrongBaseChangeSupportStatement` has this
   form. Its hypothesis is σ-lift certification for every `σ ≠ 1`, and it compares the
   actual supercuspidal supports at \(v\) and \(w\) through `sF.bind Ch`. Extending this
   additively over the Brauer combinations gives
   \(\mathrm{Ch}\circ\Phi_L=\Phi_M\circ\mathrm{Res}\) on the classes factoring through
   `q_L`.

## Sources

- *The numerical local Langlands correspondence for GL_n* (16 November 2026),
  `operator-numerical-llc-route-2026-11-16`, `numerical-LLC-route.tex`, §6.5 (lines
  1150–1174), source (b) at lines 1164–1167, ending "[Assessment; this is not a published
  statement ...]".
- *Formalizing the large external inputs of the local Langlands correspondence for GL_n*
  (16 November 2026), `operator-external-inputs-plan-2026-11-16`,
  `external-inputs-plan.tex`, interfaces B1–B3 and C2 and §4.6.
- Guy Henniart, *Une preuve simple des conjectures de Langlands pour GL(n) sur un corps
  p-adique*, Invent. Math. 139 (2000), `henniart-2000-simple-proof`, §3 (printed
  pp. 448–451) and §§4.1–4.4.
- Michael Harris, *The local Langlands conjecture for GL(n) over a p-adic field, n < p*,
  Invent. Math. 134 (1998), `harris-1998-local-langlands`, Proposition 4.8.
- James Arthur and Laurent Clozel, *Simple Algebras, Base Change, and the Advanced Theory
  of the Trace Formula*, Annals of Math. Studies 120 (1989),
  `arthur-clozel-1989-base-change`, Chapter III, Theorem 4.2 (printed pp. 202–203) and
  Theorem 5.1 (pp. 212–213).
