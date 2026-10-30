# Local factors of weakly associated pairs

Worker 35 authored this statement unit for task
`91266440-3276-48dc-ab77-8d1c1fa386e8`. All declarations lie in the namespace
`Langlands.ClassField.Global.RelativeWeilGroup`. Worker 1058 corrected the
description of its existence claims for the 2026-10-29 documentation audit;
the Lean file is unchanged.

The module states Henniart's Théorème 2.3, Corollaire 2.3, Théorème 2.4 and
Corollaire 2.4 (Henniart 2000, §§2.3–2.4) as four `Prop`-valued definitions,
with their conjunction `AssociatedFactorStatement`.
Each concerns a representation `S` of the relative Weil group
`W_{E/F} = RelativeWeilGroup c F E` that is weakly associated with an actual
cuspidal class of `GL_{r+1}` over the number field `F`. The finite-place
components are compared through the published local gamma, L and epsilon
factors. Nothing is proved. No representation, cuspidal class, local map,
additive character, local-constant system, measure or factor is constructed,
and no existence proposition is proved in this module. The stated
propositions do contain existence claims, made conditionally on their
hypotheses. Each local matching predicate asserts that a `ψ`-self-dual
measure exists and, for every such measure, that a common gamma factor,
L-polynomial or epsilon factor exists (`IsPairGammaMatch`, `IsPairLMatch`,
`IsPairEpsilonMatch`). `AssociatedSupercuspidalInductionStatement` asserts
that a block shape and unitarizable supercuspidal factors exist whose
normalized parabolic induction is equivalent to the local component. These
existence claims are stated here and not proved.

## Objects

- **Fields, class family and Weil group.** Number fields `F E : Type u` with
  `[Algebra F E]` and `[IsGalois F E]`, a class family
  `c : FundamentalClass.ClassFamily.{u}`, and the published relative Weil
  group `RelativeWeilGroup c F E`. Every statement assumes
  `IsArithmeticClassFamily c`; see below.
- **Weil-side representations.** `S S' : FiniteRepresentation.{0, u, uV} ℂ
  (RelativeWeilGroup c F E)` are finite-dimensional complex representations
  with carriers in one universe `uV`.
- **Cuspidal classes.** Under the explicit assumption
  `[CompactSpace (AdeleQuotient F)]`, which the published automorphic-form
  constructions require, `T : Automorphic.CuspidalOperatorRealization F r` is
  an actual irreducible cuspidal realization of `GL_{r+1}` over `F`, and
  `T.isoClass` is its class. The compactness is the conclusion of the
  published `AdeleQuotientCompactStatement` (Cassels §14), which this module
  neither proves nor uses as a theorem.
- **Weak association.** `IsWeaklyAssociatedClass.{u, uV, uP} S T.isoClass`
  is the published relation from
  `Langlands.Automorphic.Unramified.RelativeWeilAssociation`. It requires
  that `S` is continuous of rank `r + 1` and that some spectral presentation
  of the class, in universe `uP`, exports a spectral system with the
  following property. At cofinitely many finite places `v`, the spectrum is
  defined, and for every place `w` above `v` some local map exists. Every
  local map `ι` attached to `w` makes `S ∘ ι` unramified with
  `det(1 - X S(ι Fr))` equal to the Euler polynomial of the spectrum.
- **Local components of `Π`.** For every
  `P : Automorphic.CuspidalSpectralPresentation.{u, uQ} T` and finite place
  `v`, `P.localComponent v` is the published local component at `v`: a
  nonzero subspace of forms with its action of `GL_{r+1}(F_v)`, realizing the
  presentation's tensor factor at `v` through a fixed complementary tensor
  vector. When
  it is irreducible (`hI`) and admissible (`hA`),
  `(P.localComponent v).padicObject hI hA` is the corresponding object of the
  published smooth representation category of `GL_{r+1}(F_v)`, for the p-adic
  field `padicField v`. `(P.localComponent v).padicClass hI hA` is its class
  in `Correspondence.AutomorphicClass (padicField v) (r + 1)`.
- **Local components of `S`.** For a place `w : FinitePlacesAbove E v`, a
  reciprocity candidate `e` of `E_w`, and a continuous homomorphism
  `ι : W_{F_v} →ₜ* W_{E/F}` with `IsLocalRelativeWeilMap v w.1 e ι`,
  `localComponent S ι` is `S ∘ ι`. `localPairClass S ι` is the
  zero-monodromy Weil–Deligne class of `S ∘ ι`, in
  `Correspondence.LocalPairClass (padicField v)`. Both are published.
- **Additive characters.** `ψ : HarmonicAnalysis.UnitaryAdditiveCharacter
  (Adeles F)` is a continuous unitary additive character of `𝔸_F`. The
  structure includes the field `nontrivial`, so `ψ` is nontrivial. Each
  statement assumes `ψ (diagonal F x) = 1` for every `x : F`, where
  `diagonal F` is the published diagonal embedding `F → 𝔸_F`. At `v`,
  `ψv : Correspondence.NontrivialAdditiveCharacter (padicField v)` is a
  nontrivial unitary character of `F_v`, continuous for the canonical
  topology of `padicField v`.
- **Local constants.** A local-constant system at `F_v` is a triple
  `(eC, ε, hε)` with `eC : LocalFactor.CommonClosure.ReciprocityFamily`,
  `ε : LocalFactor.NonabelianSystem.Assignment.{u, uE}` and
  `hε : LocalFactor.NonabelianSystem.IsSystem (padicField v) eC ε`. These are
  the published system parameters of the arithmetic epsilon and gamma
  factors.

## Declarations

### Local matching predicates

In the section `Local`, `K : PadicField.{u} p`,
`π : Correspondence.AutomorphicClass K (r + 1)`,
`π' : Correspondence.AutomorphicClass K (t + 1)`, and
`X Y : Correspondence.LocalPairClass.{u, uV} K`. Each predicate copies the
pattern of the published compatibility predicates `FullPairGammaCompatibility`,
`IsPairLCompatibleAt` and `IsPairEpsilonCompatibleAt`, applied to two given
Weil–Deligne classes `X`, `Y` in place of the images `parameterForget F D`,
`parameterForget F D'` of a full map.

- `IsPairGammaMatch K eC ε hε ψ π π' X Y`: some
  `ν : Correspondence.LocalAdditiveHaarMeasure K` satisfies the published
  `IsSelfDualMeasure K ψ ν`, and for every such `ν` some `G : RatFunc ℂ`
  satisfies both `IsAutomorphicPairGammaFactor K ψ ν π π' G` and
  `IsArithmeticPairGammaFactor K eC ε hε ψ X Y G`. This is
  `γ(s, π × π', ψ) = γ(s, X ⊗ Y, ψ)` as rational functions of `q^{-s}`.
- `IsPairLMatch K ψ π π' X Y`: a self-dual measure for `ψ` exists, and for
  every such `ν` some polynomial `P` satisfies
  `IsAutomorphicPairLPolynomial K ψ ν π π' P` and
  `arithmeticPairLFactor K X Y = 1 / P`. This is
  `L(s, π × π') = L(s, X ⊗ Y)`.
- `IsPairEpsilonMatch K eC ε hε ψ π π' X Y`: a self-dual measure for `ψ`
  exists, and for every such `ν` some `(c, m) : ℂˣ × ℤ` satisfies
  `IsAutomorphicPairEpsilonFactor K ψ ν π π' (c, m)` and
  `IsArithmeticPairEpsilonFactor K eC ε hε ψ X Y c m`. This is
  `ε(s, π × π', ψ) = ε(s, X ⊗ Y, ψ) = c q^{-ms}`.
- `IsPairFactorMatch K ψ π π' X Y Xd Yd` is the conjunction of
  1. `IsPairLMatch K ψ π π' X Y`;
  2. `IsPairLMatch K ψ πd πd' Xd Yd` for all classes `πd`, `πd'` that are
     smooth contragredients of `π`, `π'` in the sense of the published
     `Correspondence.IsSmoothDual`; and
  3. `IsPairEpsilonMatch K eC ε hε ψ π π' X Y` for every local-constant
     system `(eC, ε, hε)` of `K`.

  The statements apply it with `Xd`, `Yd` the classes of the duals of the
  Weil-side components. These are Henniart's three equalities in
  Corollaire 2.3.

The representation-side factors are the published Jacquet–Piatetski-Shapiro–
Shalika factors defined through the Langlands classification. The arithmetic
L-factor is the Euler factor of the actual tensor product on `(ker N)^I`, at
the published geometric Frobenius lift. The arithmetic epsilon and gamma
factors are those of the supplied system.

### Global auxiliary predicates

- `IsArithmeticClassFamily c` holds when some family `I` of local invariant
  maps forms a relative class formation with the arithmetic normalization at
  every prime, and `c` satisfies `Generates`, `Restriction`, `Inflation` and
  `LocalCompatibility I`. These are exactly the conclusion predicates of the
  published `GlobalFundamentalClassStatement`, and exactly the hypotheses on
  `c` in the published `LocalRelativeWeilMapExistenceStatement`. They make
  `W_{E/F}` the genuine Weil group of the fundamental class.
- `IsCanonicalFiniteAdditiveComponent ψ v ψv` holds when
  `ψv x = ψ (0, single v x)` for every `x ∈ F_v`, where `single v x` is the
  finite adele with `x` at `v` and `0` elsewhere. This is the published
  `IsFiniteAdditiveComponent` with the canonical topology of
  `padicField v` in place of the completion topology. The two topologies are
  equal by the published `completion_topology_eq`, but the published
  predicate is typed with the completion topology. The local factor
  predicates require the canonical one. Since both predicates fix all values
  of `ψv`, they hold of the same function.
- `HasUnitaryCentralCharacter T` holds when some continuous character
  `χ : NumberField.IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ` with `‖χ x‖ = 1` for every
  `x` satisfies the published `T.HasCentralCharacter χ`. That predicate says
  that the represented forms lie in the `χ`-central subrepresentation.

### The four statements

Write `Π_v` for `(P.localComponent v).padicClass hI hA`, `Π'_v` for
`(P'.localComponent v).padicClass hI' hA'`, `S_v` for `S ∘ ι` and `S'_v` for
`S' ∘ ι`. Every statement quantifies over all `c` with
`IsArithmeticClassFamily c`, all `F`, `E` as above with
`[CompactSpace (AdeleQuotient F)]`, all `r`, `t`, all representations and
realizations, all presentations `P`, `P'` in universe `uQ`, all finite
places `v`, and all proofs `hI`, `hA`, `hI'`, `hA'` that the local factors
of the presentations at `v` are irreducible and admissible. Where the
Weil-side components appear, it quantifies over all `w`, `e` and `ι` with
`IsLocalRelativeWeilMap v w.1 e ι`. Where additive characters appear, it
quantifies over all `ψ` trivial on `F` and all `ψv` with
`IsCanonicalFiniteAdditiveComponent ψ v ψv`.

- `AssociatedGammaStatement` (Théorème 2.3): if `S` is weakly associated with
  `T.isoClass` and `S'` with `T'.isoClass`, then
  `IsPairGammaMatch (padicField v) eC ε hε ψv Π_v Π'_v
    (localPairClass S ι) (localPairClass S' ι)` for every local-constant
  system `(eC, ε, hε)` of `F_v`.
- `AssociatedTemperedFactorStatement` (Corollaire 2.3): under the same
  association hypotheses, assume further that the actions of
  `(P.localComponent v).padicObject hI hA` and
  `(P'.localComponent v).padicObject hI' hA'` satisfy the published
  `PadicField.TopologicalData.IsTempered` for the canonical topological data
  of `padicField v`, and that `localComponent S ι` and
  `localComponent S' ι` satisfy `FiniteRepresentation.IsUnitary`. Then
  `IsPairFactorMatch (padicField v) ψv Π_v Π'_v (localPairClass S ι)
    (localPairClass S' ι) (localPairClass S.dual ι)
    (localPairClass S'.dual ι)`.
- `AssociatedSupercuspidalInductionStatement` (Théorème 2.4): if `S` is
  irreducible (`FiniteRepresentation.IsIrreducible`) and unitary
  (`FiniteRepresentation.IsUnitary`), `HasUnitaryCentralCharacter T` holds,
  and `S` is weakly associated with `T.isoClass`, then for every `P`, `v`,
  `hI`, `hA` there are a block shape `B : GeneralLinear.BlockShape (r + 1)`
  and supercuspidal representations
  `σ i : GeneralLinear.SupercuspidalRep.{u, u}` of `GL_{B.size i}(F_v)` such
  that each `(σ i).obj.representation` satisfies the published
  `IsUnitarizable`, and the action of
  `(P.localComponent v).padicObject hI hA` is equivalent to the published
  `normalizedProductInduced B (fun i => (σ i).obj.representation)` for the
  canonical topological data of `padicField v`.
- `AssociatedCuspidalFactorStatement` (Corollaire 2.4): if `S`, `S'` are
  irreducible and unitary, `T`, `T'` have unitary central characters, and
  `S`, `S'` are weakly associated with `T.isoClass`, `T'.isoClass`, then the
  conclusion of `AssociatedTemperedFactorStatement` holds without its
  temperedness and local unitarity hypotheses.
- `AssociatedFactorStatement` is the conjunction of the four statements
  above, at the same universe levels.

The published meanings used above are as follows.

- `BlockShape n` is a finite sequence of positive block sizes with sum `n`.
- `SupercuspidalRep` is the full subcategory of smooth representations that
  are irreducible and supercuspidal. The published supercuspidality includes
  admissibility.
- `normalizedProductInduced B σ` is Henniart's `i(σ_1, …, σ_k)`: normalized
  parabolic induction, from the standard upper block parabolic with the
  successive sizes of `B`, of the tensor product of the `σ_i`.
- `IsUnitarizable` means that some positive definite invariant Hermitian
  form exists.
- `FiniteRepresentation.IsUnitary` means that some invariant inner product
  exists on the finite-dimensional carrier.
- `IsTempered` means temperedness modulo the centre for every Borel Haar
  measure on the actual central quotient: for some unitary central
  character, every absolute smooth matrix coefficient lies in `L^{2+δ}` for
  every `δ > 0`.

The universe parameters are `u` for the fields, `uV` for the carriers of `S`
and `S'`, `uP` for the presentations witnessing the association, `uQ` for
the presentations `P`, `P'` whose local factors are compared, and `uE` for
the local-constant assignments. They are independent, and each statement is
asserted at every choice of levels.

## Source correspondence

The statements follow Henniart 2000, §2.3 and §2.4, printed pp.444–445
(PDF pp.6–7), registered as `henniart-2000-simple-proof`.

- **Théorème 2.3** (Henniart 1986, Theorem 4.1). Let `S`, `S'` be continuous
  representations of `W_F` of degrees `n`, `n'`, and `Π`, `Π'` automorphic
  representations of `GL_n(𝔸_F)`, `GL_{n'}(𝔸_F)`, with `S` associated with
  `Π` and `S'` with `Π'`. Then for every finite place `v`,
  `γ(Π_v × Π'_v, s, ψ_v) = γ(S_v ⊗ S'_v, s, ψ_v)`. Henniart notes that the
  proof uses Shahidi's global functional equations for pair L-functions.
- **Corollaire 2.3** (Henniart 1986, Proposition 4.5). If moreover `S_v`,
  `S'_v` are unitary and `Π_v`, `Π'_v` are tempered, then
  `L(Π_v × Π'_v, s) = L(S_v ⊗ S'_v, s)`,
  `L(Π_v^∨ × Π'^∨_v, s) = L(S_v^∨ ⊗ S'^∨_v, s)` and
  `ε(Π_v × Π'_v, s, ψ_v) = ε(S_v ⊗ S'_v, s, ψ_v)`.
- **Théorème 2.4.** If `S` is continuous, irreducible and unitary of degree
  `n`, `Π` is cuspidal unitary, and `S` and `Π` are associated, then for
  every finite place `v`, `Π_v` is parabolically induced from a unitary
  supercuspidal representation of a Levi subgroup of `GL_n(F_v)`. Henniart
  deduces that `Π_v` is tempered, so Corollaire 2.3 applies.
- **Corollaire 2.4.** For `S`, `S'` continuous irreducible unitary, `Π`, `Π'`
  cuspidal unitary, and both pairs associated, the three equalities of
  Corollaire 2.3 hold at every finite place.

In §2.1 Henniart fixes a nontrivial additive character `ψ` of `𝔸_F`, trivial
on `F`. Its component at `v` is `ψ_v`.

The formalization differs from the source in the following derived choices.

1. **Relative Weil group.** Henniart's `S`, `S'` are representations of the
   absolute Weil group `W_F`. Here they are representations of one
   finite-level group `W_{E/F}` for the same `c`, `F` and `E`, as in the
   published association relation. The library has no absolute global Weil
   group or inflation maps between levels. Those belong to Worker 2's
   construction. Using one group for both `S` and `S'` is what makes
   `S_v ⊗ S'_v` the restriction of `S ⊗ S'` along one local map.
2. **Fundamental class.** Each statement assumes `IsArithmeticClassFamily c`,
   so that `W_{E/F}` is the Weil group of the arithmetic fundamental class.
   For any other class family `c` the statements would be about a different
   group extension and could fail.
3. **Weil-side local components.** Henniart's `S_v` is the restriction to a
   decomposition group, defined up to conjugacy, and `S_v ⊗ S'_v` restricts
   both along the same embedding. Here the claims are made for every place
   `w` above `v`, every reciprocity candidate `e` and every local map `ι`
   with `IsLocalRelativeWeilMap v w.1 e ι`, with the same `ι` for `S` and
   `S'`. Conjugating `ι` changes `S ∘ ι` only up to equivalence. When no such
   `ι` exists, nothing is claimed at `v`. The published
   `LocalRelativeWeilMapExistenceStatement` (unproved) supplies maps under
   `IsArithmeticClassFamily c` for geometrically normalized `e`.
4. **Cuspidal classes only.** Théorème 2.3 and Corollaire 2.3 are stated by
   Henniart for automorphic `Π`, `Π'`. Here they are stated only for actual
   irreducible cuspidal classes, through the published association relation,
   which is defined only for those. Isobaric and other noncuspidal
   automorphic representations are not covered. Théorème 2.4 and
   Corollaire 2.4 are about cuspidal representations in the source as well.
5. **Local components of `Π`.** Henniart's `Π_v` is the local component of
   the irreducible representation `Π`. Here the local components are the
   local factors of every published spectral presentation `P` of the
   realization `T`, at places `v` where that factor is irreducible and
   admissible. These conditions are explicit hypotheses `hI`, `hA`. A
   presentation is a tensor equivalence onto a nonzero `GL_{r+1}(𝔸_{F,f})`-
   invariant subspace of the finite form image. Its factors are guaranteed
   irreducible and admissible only off its finite exceptional set, and at an
   exceptional place a factor may absorb a multiplicity and be reducible.
   Then nothing is claimed at that place for that presentation. When `hI`
   and `hA` hold, the factor is equivalent to the true local component of the
   cuspidal representation, because the presented subspace is isotypic for
   the finite part. This explains the choice and is not formalized here. By
   Flath's theorem some presentation has irreducible admissible factors at
   every finite place. That theorem is not in the library and is not used
   here. With such a presentation, the statements give Henniart's claims at
   every finite place.
6. **Presentations.** The association hypothesis is class-level: some
   presentation in universe `uP` has a weakly associated spectrum. The
   conclusion is asserted for every presentation `P` in universe `uQ`, not
   only for the witness.
7. **Local constants.** Henniart's `ε(S_v ⊗ S'_v, s, ψ_v)` is the
   Langlands–Deligne local constant. Here the arithmetic factors are taken
   for an arbitrary system `(eC, ε, hε)` with
   `NonabelianSystem.IsSystem`, and the claims are made for every such
   system. `IsSystem` consists of the normalized reciprocity conditions on
   `eC`, additivity, Haar scaling, inductivity in degree zero, and the
   rank-one relation to Tate's abelian local constants. These are the
   conditions of Deligne's uniqueness theorem; for a fixed `eC` the
   uniqueness is the published proposition `NonabelianSystem.Unique`, which
   is not proved or used here. Quantifying over all systems therefore asserts
   the equalities for the Langlands–Deligne constant, without choosing one
   system.
8. **Measures.** The representation-side factors of the published relations
   are parametrized by an additive Haar measure. As in the published
   `FullPairGammaCompatibility`, each matching predicate asserts that a
   `ψ`-self-dual measure exists and makes its claim for every such measure.
   The existence of a self-dual measure is Tate's theorem; it is asserted
   here, not assumed.
9. **Additive characters.** The global character is nontrivial by its type
   and trivial on `F` by hypothesis. The local character `ψv` is quantified
   over and constrained by its values. The component of a nontrivial
   character of `𝔸_F / F` is nontrivial and continuous at every place. If it
   were not, no `ψv` would exist and nothing would be claimed at `v`.
10. **Duals.** `S_v^∨` is `localComponent S.dual ι`, the restriction of the
    published algebraic dual of `S`. It is the dual of `S ∘ ι`, since the
    dual action is computed pointwise. `Π_v^∨` ranges over all classes that
    are smooth contragredients of `Π_v` in the published sense, so no choice
    of a contragredient class is made.
11. **Unitarity.** Henniart's unitary `S` and `S_v` are unitarizable
    representations; this is `FiniteRepresentation.IsUnitary`. A cuspidal
    representation is unitary exactly when its central character is unitary.
    The Petersson inner product then gives the unitary structure. Here
    "cuspidal unitary" is the explicit condition
    `HasUnitaryCentralCharacter T`, which does not rely on that equivalence.
12. **Temperedness.** The hypothesis of Corollaire 2.3 is stated on the
    actual action of the local factor, with the canonical topology of
    `padicField v` set explicitly. The published definition uses that
    instance, and the completion topology carried by the global objects is
    equal to it only propositionally.
13. **Levi subgroups.** Henniart's induction is from a supercuspidal
    representation of some Levi subgroup. Every Levi subgroup of `GL_n` is
    conjugate to a standard block-diagonal one
    `GL_{n_1} × ⋯ × GL_{n_k}`. An irreducible representation of that Levi is
    `σ_1 ⊗ ⋯ ⊗ σ_k`; it is supercuspidal when every `σ_i` is, and unitary
    when every `σ_i` is unitarizable. The statement uses the standard upper
    block parabolic and Henniart's `i(σ_1, …, σ_k)`. The supercuspidal
    factors are required to have carriers in universe `u`.

## Scope

The module states four unproved theorems and defines the predicates they
use. It does not assert:

- the existence of any weakly associated pair, of local maps `ι`, of
  presentations with irreducible factors, or of local-constant systems;
- the global functional equations of Shahidi or the Hecke character
  functional equation used in the proof;
- strong multiplicity one, the Jacquet–Shalika rigidity, or the Chebotarev
  uniqueness of Henniart §2.2;
- the consequences for duals, determinants and twists in Henniart §2.2;
- any statement about archimedean places.

## Sources

- G. Henniart, *Une preuve simple des conjectures de Langlands pour GL(n)
  sur un corps p-adique*, Invent. Math. 139 (2000), 439–455. Literature ID
  `henniart-2000-simple-proof`, SHA256
  `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
  Section 2.1, printed p.444 (PDF p.6): the global additive character.
  Section 2.2, printed p.444 (PDF p.6): association. Section 2.3, printed
  pp.444–445 (PDF pp.6–7): Théorème 2.3 and Corollaire 2.3. Section 2.4,
  printed p.445 (PDF p.7): Théorème 2.4 and Corollaire 2.4.
- G. Henniart, *On the local Langlands conjecture for GL(n): the cyclic
  case*, Ann. of Math. 123 (1986), 145–203. Literature ID
  `henniart-1986-cyclic`, SHA256
  `096fba993b7368b1af9f7cc1f0c053e5436ba447f291c2acd402f058eb44b0ba`
  (PDF page = printed page − 143). Theorem 4.1, printed p.157 (PDF p.14):
  the gamma equality at every finite place for automorphic `Π`, `Π'` and
  continuous `S`, `S'` matched outside a finite set. Lemma 4.4, printed
  p.159 (PDF p.16), and Proposition 4.5 with its Corollary, printed p.160
  (PDF p.17): from gamma equality to equality of L and epsilon factors when
  the reflected Euler polynomials have no common zero, and the cuspidal
  irreducible case. Henniart 2000 cites these as the sources of
  Théorème 2.3 and Corollaire 2.3.
