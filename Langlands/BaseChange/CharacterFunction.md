# Character functions of ordinary and twisted character distributions

The module `Langlands.BaseChange.CharacterFunction` defines when a function `Θ : G → ℂ`
represents the twisted character `φ ↦ trace(ρ(φ) ∘ A)` (definition 1,
`IsTwistedCharacterFunction`) or the ordinary character `f ↦ trace ρ(f)` (definition 2,
`IsCharacterFunction`) of an admissible representation `ρ`, and proves the elementary lemmas
3 about these predicates. It is the common vocabulary of the statements
`CharacterLocalIntegrabilityStatement` (statement 4) and
`TwistedCharacterLocalIntegrabilityStatement` (statement 5), which assert that such functions
exist for irreducible representations of `GL_n`. Nothing about `GL_n` is used here.

## Sources

- Henniart–Lemaire, *Changement de base et induction automorphe pour GL_n en
  caractéristique non nulle*, Mém. SMF 124 (2011), source ID
  `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`, cited as HL
  (PDF page = printed page + 8).
  - I.5.1, printed pp. 28–30, in the setting of sections I.4–I.5, where `E/F` is an
    unramified field extension (I.4.1, printed p. 26). For an admissible σ-stable `π` and an
    isomorphism `A` of `π` onto `π^σ`, the distribution `⟨φ, Θ^A_π⟩ = trace(π(φ dg_E) ∘ A)` (p. 29). For
    irreducible `π` (their reference [60], Lemaire 2004, Théorème 7.1) it is locally
    constant on `G(E)_{σ-r}` and locally integrable on `G(E)`, which HL spell out
    ("c'est-à-dire") as: there is a function, locally constant on `G(E)_{σ-r}` and again
    written `Θ^A_π`, with `⟨φ, Θ^A_π⟩ = ∫_{G(E)_{σ-r}} Θ^A_π(g) φ(g) dg_E` for every
    `φ ∈ C_c^∞(G(E))`, the integral being absolutely convergent (p. 29). Remarque 2 (p. 30):
    the function depends only on the isomorphism class of `(π, A)`, not on the choice of
    `dg_E`.
  - II.1.3, printed pp. 56–57, in the setting of Chapter II, where `E/F` is a finite cyclic
    field extension (printed p. 55). For an admissible σ-stable representation `Π` of `G(E)`
    and an isomorphism `A` of `Π` onto `Π^σ`, the distribution
    `Θ^A_Π(φ) = trace(Π(φ) ∘ A)` (p. 56). For an admissible representation `π` of `G(F)`, the
    distribution `Θ_π(f) = trace π(f)` (p. 57). Admissibility gives only these
    distributions. The representing functions need a further hypothesis: "si de plus `Π` est de
    longueur finie" (p. 57, after chap. I and their [60]), `Θ^A_Π` is given by a function
    locally constant on `G(E)_{σ-r}` and locally integrable on `G(E)`. The distribution depends
    on `dg_E`, the function does not. Likewise, "si de plus `π` est de longueur finie" (p. 57),
    `Θ_π` is given by a function locally constant on `G(F)_r`, locally integrable on `G(F)` and
    independent of the Haar measure `dg`. Finite length cannot be dropped (see "Admissibility
    and finite length" below).
  - HL work over local fields of positive characteristic (Chapter I, printed p. 5), and they
    take these facts from Lemaire's papers. They use [60] (Lemaire 2004) for twisted
    characters (I.5.1 and II.1.3) and [59] (Lemaire 1996) for ordinary characters (II.2.8,
    printed p. 69). Aizenbud, Gourevitch, Kazhdan and Sayag (arXiv:2602.16389, 2026) say that
    the arguments of these papers in positive characteristic have a flaw; see the section
    "Hypotheses" of `CharacterLocalIntegrabilityStatement` and of
    `TwistedCharacterLocalIntegrabilityStatement`. HL are cited here for the definitions of the
    distributions and the form of their representing functions, not for a proof that such
    functions exist. Definitions 1–2 are predicates only and assert no existence. The existence
    statements 4–5 that use them are made in characteristic zero, where Harish-Chandra (below)
    and Clozel 1987 prove them.
- Harish-Chandra, *Admissible invariant distributions on reductive p-adic groups*, notes by
  DeBacker and Sally, ULS 16, AMS 1999, source ID
  `harish-chandra-1999-admissible-invariant-distributions`, cited as HC (PDF page = printed
  page + 15). Introduction, printed p. 1, and Theorem 16.3, printed p. 75: the character
  `Θ_π` of an irreducible admissible representation is a locally summable function on `G`;
  the relation `Θ_π(f) = ∫_G f(x) F_π(x) dx` for all `f ∈ C_c^∞(G)` (p. 1) is what
  definition 2 expresses.

## Setting

Everything is stated for a group `G` with `[TopologicalSpace G] [IsTopologicalGroup G]
[T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G]` (a locally profinite group),
a complex vector space `V`, `ρ : Representation ℂ G V` with `hρ : IsAdmissible ρ`, and
`Θ : G → ℂ`. Test functions are the Library's `HarmonicAnalysis.SchwartzBruhat G`, the
locally constant compactly supported functions `G → ℂ` (HL's `C_c^∞(G)`). For a Haar
measure `μ`, the Library's `twistedDistribution μ ρ hρ A` is `φ ↦ trace(ρ(φ) ∘ A)` and
`Character.distribution μ ρ hρ` is `f ↦ trace ρ(f)`
(`Langlands/BaseChange/TwistedCharacter/Basic.lean`,
`Langlands/Representation/Character/Basic.lean`).

Two different integrals occur, and they should not be confused:

- the operator `ρ(φ)`, HL's `∫ φ(g) π(g) dg`, is the Library's integrated action
  `Hecke.integratedAction μ ρ hρ.1 φ` (`Langlands/Representation/Hecke/IntegratedAction.lean`).
  The space `V` carries no topology, so `ρ(φ) v` is an algebraic, vector-by-vector integral of
  `g ↦ φ(g) • ρ(g) v`: a finite sum `∑ μ(sᵢ) • wᵢ` over a presentation of this locally
  constant, compactly supported integrand by indicators of measurable sets `sᵢ`
  (`Hecke.integratedAction_eq_sum_of_presentation`). Its trace is the trace of a finite-rank
  endomorphism;
- the scalar integral `∫ x, φ x * Θ x ∂μ` on the right-hand side of definitions 1–2 is Mathlib's
  Bochner integral of a complex-valued function.

Both are taken for the Borel σ-algebra, which is introduced locally
(`letI : MeasurableSpace G := borel G` and the matching `BorelSpace` instance), as in the
Library's `HasTwistedCharacterValue`. No Haar measure is chosen or normalized; no instance is
declared.

## Definitions

1. `IsTwistedCharacterFunction ρ hρ A Θ`, for `A : Module.End ℂ V`: for every Haar measure
   `μ` on `G` (Borel σ-algebra), `Θ` is locally integrable for `μ` (Mathlib's
   `MeasureTheory.LocallyIntegrable`) and
   `twistedDistribution μ ρ hρ A φ = ∫ x, φ x * Θ x ∂μ` for every test function `φ`.
   This is HL's "the distribution `Θ^A_π` is the locally integrable function `Θ^A_π`"
   (I.5.1, printed p. 29; II.1.3, printed p. 57).
2. `IsCharacterFunction ρ hρ Θ`: for every Haar measure `μ`, `Θ` is locally integrable for
   `μ` and `Character.distribution μ ρ hρ f = ∫ x, f x * Θ x ∂μ` for every test function `f`
   (HL II.1.3, printed p. 57; HC, printed pp. 1 and 75).

`A` is any endomorphism in definition 1; the statements apply it to the isomorphisms of `τ`
onto `τ^σ` (`SigmaIntertwiner`).

### Admissibility and finite length

The predicates make sense for every admissible representation, but without finite length a
representing function need not exist; this is why HL II.1.3 (printed p. 57) add that
hypothesis. Take any nonarchimedean local field `F`, `G = GL_1(F) = F^×` and `K = O_F^×`. Let
`π` be the direct sum of all smooth characters of `K`, each extended to `F^×` by the value 1 on
a fixed uniformizer. Then `π` is admissible: for an open subgroup `U`, its `U`-fixed vectors
lie in the span of the characters trivial on `U ∩ K`, and there are finitely many of these.
Normalize `μ(K) = 1` and let `K_m = 1 + 𝔭^m` (`m ≥ 1`). Then `π(1_{K_m})` is `μ(K_m)` times the
projection onto the `K_m`-fixed space, whose dimension is `[K : K_m] = 1 / μ(K_m)`. So
`trace π(1_{K_m}) = 1` for every `m`. A locally integrable `Θ` would be integrable on `K`, so
`∫_{K_m} Θ dμ` would tend to 0, because the `K_m` decrease to the null set `{1}`. This example
comes from the review of an earlier version of this candidate. Statements 4–5 assert that
representing functions exist only for irreducible representations, which have finite length.

### Integral over `G` and integral over the regular set

HL integrate over the (σ-)regular set `G(E)_{σ-r}`, on which alone their function is
defined. Definitions 1–2 integrate over all of `G` a function defined everywhere. The two
agree because the complement of the regular set has measure zero for every Haar measure:
this is statements 6–7 (`RegularSemisimpleOpenConullStatement` and
`SigmaRegularOpenConullStatement`, module `Langlands.BaseChange.RegularSetOpenConullStatement`,
not proved), and lemma `congr_ae` below shows that the values of `Θ` on a Haar-null set
are irrelevant. Definitions 1–2 themselves do not mention any regular set.

### Why every Haar measure is quantified

For two Haar measures `μ` and `μ'` on `G`, Mathlib gives the constant
`c = haarScalarFactor μ' μ > 0` with `μ' s = c • μ s` for every set `s` with compact closure
(`measure_isMulInvariant_eq_smul_of_isCompact_closure`) and for every open set `s`
(`measure_isHaarMeasure_eq_smul_of_isOpen`). Sets with compact closure (relatively compact
sets) are all that the scaling argument below needs. Equality `μ' = c • μ` of measures, that
is, on all Borel sets, holds under regularity hypotheses (`isMulLeftInvariant_eq_smul_of_regular`,
`isMulLeftInvariant_eq_smul_of_innerRegular`), in particular for second-countable groups
such as `GL_n(F)` and `GL_n(E)` over a nonarchimedean local field
(`isMulLeftInvariant_eq_smul`). Without regularity it can fail: Mathlib's `IsHaarMeasure`
does not include regularity, and the group `G` of this module need not be σ-compact, so two
Haar measures can differ on Borel sets that are neither open nor relatively compact. The
argument below does not use global equality.

Proportionality on relatively compact sets is enough for definitions 1–2, because both sides
of the identity only involve compact sets:

- local integrability means integrability on some neighbourhood of each point, and in a
  locally compact group it suffices to take compact neighbourhoods;
- a test function `φ` has compact support `K`, so `∫ φ Θ dμ` only involves `μ` restricted to
  the compact set `K`;
- the integrated action `ρ(φ) v = ∑ μ(sᵢ) • wᵢ` can be computed with sets `sᵢ` inside the
  support of `φ` (support cutoffs are presentations in
  `Hecke.integratedAction_eq_sum_of_presentation`).

So replacing `μ` by `μ'` multiplies `ρ(φ)`, hence the distribution, by `c`, and it multiplies
`∫ φ Θ dμ` by `c`. Local integrability is unchanged. The identity for one Haar measure
therefore gives it for every Haar measure, with the same function `Θ`, so `Θ` does not
depend on the measure. HL record this independence for their groups (I.5.1, Remarque 2,
printed p. 30; II.1.3, printed p. 57). The definitions quantify over all Haar measures so
that no measure has to be chosen, and this scaling argument is why the quantification loses
nothing. The argument is not formalized here.

## Lemmas (proved)

The group, the representation and `hρ` are implicit.

- `isTwistedCharacterFunction_one_iff` (simp lemma):
  `IsTwistedCharacterFunction ρ hρ 1 Θ ↔ IsCharacterFunction ρ hρ Θ`. Proof: rewrite with the
  Library's `twistedDistribution_one`.
- `IsTwistedCharacterFunction.hasTwistedCharacterValue`: if
  `IsTwistedCharacterFunction ρ hρ A Θ` and `∀ᶠ x in nhds g, Θ x = Θ g`, then
  `HasTwistedCharacterValue ρ hρ A g (Θ g)`. Proof: take an open `U ∋ g` on which `Θ = Θ g`;
  for `φ` supported in `U`, `∫ φ Θ dμ = Θ g * ∫ φ dμ`, which is the Library's local value
  (`HasLocalValue`) for every Haar measure.
- `IsCharacterFunction.hasCharacterValue`: the same for `HasCharacterValue ρ hρ g (Θ g)`,
  deduced from the previous lemma with `A = 1` and the Library's
  `hasTwistedCharacterValue_one_iff`.
- `IsTwistedCharacterFunction.smul`: `IsTwistedCharacterFunction ρ hρ A Θ` gives
  `IsTwistedCharacterFunction ρ hρ (a • A) (fun x => a * Θ x)` for `a : ℂ`. Proof: the
  Library's `twistedDistribution_smul`, Mathlib's `LocallyIntegrable.smul` and
  `integral_const_mul`.
- `IsTwistedCharacterFunction.congr_ae` and `IsCharacterFunction.congr_ae`: if `Θ` has the
  property and `Θ =ᵐ[μ] Θ'` for every Haar measure `μ` (Borel σ-algebra), then `Θ'` has it.
  Proof: Mathlib's `LocallyIntegrable.congr` and `integral_congr_ae`.
- `IsTwistedCharacterFunction.apply_eq`: if `Θ` and `Θ'` both satisfy definition 1 for the
  same `ρ, hρ, A`, and `∀ᶠ x in nhds g, Θ x = Θ g` and `∀ᶠ x in nhds g, Θ' x = Θ' g`, then
  `Θ g = Θ' g`. Proof: both values are local twisted character values at `g`, which are
  unique (the Library's `HasTwistedCharacterValue.unique`).

### Determination of `Θ`

A character function is determined at best almost everywhere: by `congr_ae`, changing `Θ` on
a set that is null for every Haar measure gives again a character function. No converse is
stated or proved here, and none is claimed for the general group `G` of this module. For
`GL_n(F)` and `GL_n(E)` over a nonarchimedean local field the converse is standard. These
groups are second countable and are countable unions of compact open sets. On each compact
open set `U`, the compact open subsets form an algebra of sets that generates the Borel
σ-algebra of `U`, and their indicators are test functions. So two locally integrable
functions defining the same distribution agree almost everywhere on each such `U`, hence
almost everywhere on the group, for every Haar measure. Values are meaningful at points
where `Θ` is locally constant: there the value is the Library's local character value
(`hasTwistedCharacterValue`, `hasCharacterValue`), and any two character functions locally
constant at the same point agree there (`apply_eq`). This is how statements 4–5 give the
Library's `HasRegularSemisimpleCharacterValues` and `TwistedCharacterRegularValuesStatement`.

## Not included

No existence statement (that is statements 4–5), no uniqueness almost everywhere, no
statement about invariance of `Θ` under (σ-)conjugation (HL I.5.1, Remarque 2), and no
version for representations of finite length.
