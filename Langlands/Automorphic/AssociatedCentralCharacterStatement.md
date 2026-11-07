# The central character of a weakly associated cuspidal realization

Worker 1807 authored this statement unit for task
`00c5b3b4-b058-4ec7-9851-be9b60052094`. Worker 1693, collaborator on the
task, contributed the source and prerequisite audit that the sections
"The almost-all-place argument", "Bridge to `AssociatedGammaStatement`" and
"Source correspondence" rely on. The declaration lies in the namespace
`Langlands.ClassField.Global.RelativeWeilGroup`. The module imports only
`Langlands.Automorphic.AssociatedDeterminantTwistStatement`.

## Statement

Let `c` be an arithmetic class family, `F ⊆ E` a Galois extension of number
fields, `S` a finite-dimensional complex representation of the relative Weil
group `RelativeWeilGroup c F E`, and `T` an actual irreducible cuspidal
realization of `GL_{r+1}` over `F`. If `S` is weakly associated with the
cuspidal class of `T`, then there is a Hecke character `ω` of `F` such that

1. `ω` is a central character of `T`: every form `f` of `T` satisfies
   `f(z x) = ω(z) f(x)` for every idele `z`, embedded as a scalar matrix;
2. `det S = ω ∘ τ_F` on the whole relative Weil group, where `τ_F` is the
   pointwise inverse of the transfer `W_{E/F} → C_F`;
3. every Hecke character that is a central character of `T` equals `ω`;
4. every Hecke character `χ` with `det S = χ ∘ τ_F` equals `ω`.

So the actual central character of `T` exists, the actual Hecke character
of `det S` exists, and the two are the same Hecke character. Neither
character is a hypothesis. This is the global identity `det S = ω_Π ∘ τ_F`
of Henniart 2000, §2.2. Henniart 1986, §4.3, uses it to compare the
determinant and central-character terms of Lemma 4.2 at the places of `T`.
The statement is not proved.

## Declaration

```lean
def AssociatedCentralCharacterStatement : Prop :=
  ∀ c : FundamentalClass.ClassFamily.{u}, IsArithmeticClassFamily c →
  ∀ (F E : Type u) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsGalois F E] [CompactSpace (AdeleQuotient F)] {r : ℕ}
    (S : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E))
    (T : Automorphic.CuspidalOperatorRealization F r),
    IsWeaklyAssociatedClass.{u, uV, uP} S T.isoClass →
    ∃ ω : HeckeCharacter F,
      T.HasCentralCharacter ω ∧
        FiniteRepresentation.determinantCharacter S = reciprocityCharacter c F E ω ∧
        (∀ ω' : HeckeCharacter F, T.HasCentralCharacter ω' → ω' = ω) ∧
        ∀ χ : HeckeCharacter F,
          FiniteRepresentation.determinantCharacter S = reciprocityCharacter c F E χ → χ = ω
```

The hypotheses on `c`, `F`, `E`, `S` and `T` are exactly those that the
published `Langlands.ClassField.Global.RelativeWeilGroup.AssociatedGammaStatement`
(in `Langlands.Automorphic.AssociatedFactorStatement`) places on one of its
two pairs `(S, T)`, at the same universe levels.

## Objects

The objects are those of the published
[AssociatedDeterminantTwistStatement](AssociatedDeterminantTwistStatement.md),
section "Objects": the arithmetic class family and `IsArithmeticClassFamily`,
the transfer, `reciprocityCharacter c F E χ` (the homomorphism
`w ↦ (χ (transfer c F E w))⁻¹`), the representation `S`, its determinant
`FiniteRepresentation.determinantCharacter S`, the cuspidal realization `T`
under the explicit assumption `[CompactSpace (AdeleQuotient F)]`, the
central-character condition `T.HasCentralCharacter ω`, and weak
association. In addition:

- **Hecke characters.** `HeckeCharacter F` is the published abbreviation
  (`Langlands.Global.HeckeCharacter`) for continuous homomorphisms
  `IdeleClasses F →ₜ* ℂˣ` on the idele class group `C_F`. They need not be
  unitary or of finite order: they are Henniart's quasicharacters of
  `𝔸_F^×/F^×`. Equality `χ = ω` in the conclusion is equality of these
  continuous homomorphisms on all of `C_F`, including the components at
  ramified finite and at infinite places.
- **Weak association with the class of `T`.** The published
  `IsWeaklyAssociatedClass.{u, uV, uP} S T.isoClass` (from
  `Langlands.Automorphic.Unramified.RelativeWeilAssociation`) is, by the
  published `isWeaklyAssociatedClass_isoClass_iff`, equivalent to the
  existence of a cuspidal spectral presentation `P` of `T` with local factors
  in universe `uP` such that `IsWeaklyAssociated S P.spectralSystem`. The
  latter says that `S` is continuous of rank `r + 1` and that on one
  cofinite set of finite places `v` of `F` the spectrum of `P` is defined and
  `IsUnramifiedMatchAt S v` holds for its Euler polynomial. This is the
  cofinite place hypothesis of Henniart's association ("presque toute place
  finie"). It is kept unchanged: no condition is imposed at the finitely many
  remaining places, and the cofinite set contains places that are not split
  in `E`.

## Universe levels

The parameters are `u` for the fields and the automorphic realization, `uV`
for the carrier of `S`, and `uP` for the local factors of the presentation
that witnesses weak association. They are independent, and the statement is
asserted at every choice: `AssociatedCentralCharacterStatement.{u, uV, uP}`.
The conclusion mentions no presentation, so it holds for every presentation
of `T` in every universe; see the bridge section below.

## Relation to existing declarations

- **`PresentedDeterminantAssociationStatement`** (published, same
  namespace, `Langlands.Automorphic.AssociatedDeterminantTwistStatement`)
  assumes a continuous character `ω` with `T.HasCentralCharacter ω` and a
  presentation `P` with `IsWeaklyAssociated S P.spectralSystem`, and
  concludes `det S = reciprocityCharacter c F E ω`. The present statement
  differs in two ways. The central character is a conclusion, so the
  statement also applies when no central character is supplied. And it adds
  the two uniqueness clauses, which identify the Hecke character of
  `det S` with the central character as actual Hecke characters.
  The present statement at levels `{u, uV, uP}` implies
  `PresentedDeterminantAssociationStatement.{u, uV, uP}`: given `ω₀` and `P`
  as there, `isWeaklyAssociatedClass_isoClass_iff` gives the class
  hypothesis, the conclusion gives `ω` with `det S = reciprocityCharacter c F E ω`,
  and clause 3 gives `ω₀ = ω`. This implication is not formalized. The
  converse fails: the presented statement says nothing when `T` has no
  supplied central character.
- **Determinant-twist transport.** The published
  `AutomorphicCentralCharacterDeterminantMultiplier` and
  `CentralCharacterDeterminantMultiplier` transport a supplied central
  character along a determinant twist, and the published
  `PresentedTwistAssociationStatement` and `ClassTwistAssociationStatement`
  say that twisting preserves association. None of them relates the central
  character to the determinant of an associated representation, and the
  present statement says nothing about twists.
- **Rank-one rigidity.** The published statement-only
  `Langlands.Automorphic.Unramified.HeckeLocalComponentRigidityStatement`
  (two Hecke characters that are unramified and have equal finite local
  components outside a finite set are equal) is the rigidity input of the
  argument below. It is not imported and not assumed.

## Normalization

| Henniart | Lean |
| --- | --- |
| `S`, a representation of `W_F` | `S`, a representation of `RelativeWeilGroup c F E` (`W_{E/F}` for arithmetic `c`) |
| `Π` | the actual cuspidal realization `T` |
| `ω_Π`, the central character | `ω : HeckeCharacter F` with `T.HasCentralCharacter ω` |
| `det S` | `FiniteRepresentation.determinantCharacter S` |
| `τ_F : W_F → 𝔸_F^×/F^×` | `w ↦ (transfer c F E w)⁻¹` |
| `ω_Π ∘ τ_F` | `reciprocityCharacter c F E ω` |

The inverse in `τ_F` comes from the Library's arithmetic normalization of
the fundamental class, opposite to Tate's geometric normalization (1.4.1).
The published section "The sign" of
[AssociatedDeterminantTwistStatement](AssociatedDeterminantTwistStatement.md)
derives it. At an unramified place `v`, with a local map `ι` as in weak
association and a geometric Frobenius `Fr` of `W_{F_v}`, it gives
`det S(ι Fr) = ω_v(ϖ_v)` with no inverse on the local value, where `ω_v` is
the component of `ω` at `v` and `ϖ_v` a uniformizer. Replacing
`reciprocityCharacter c F E ω` by `ω ∘ transfer` would turn the statement
into `det S(ι Fr) = ω_v(ϖ_v)⁻¹`, which is false in general.

## Why the statement is assumed only for arithmetic class families

The published section "Why the statements assume the arithmetic hypothesis"
of [AssociatedDeterminantTwistStatement](AssociatedDeterminantTwistStatement.md)
applies unchanged. In short: a character of `C_F / N C_E`, such as the
quadratic character `η_{E/F}` of a quadratic extension, is trivial at every
place that splits completely in `E`. So agreement at split places cannot
determine `det S`; the argument needs the local–global compatibility of the
transfer at nonsplit places and the reciprocity law, which the cited
sources establish only for the arithmetic fundamental class.

## The almost-all-place argument

This argument is not formalized. Fix `c`, `F`, `E`, `S` and `T` as in the
statement, with `n = r + 1`. Each step names its prerequisites; the next
section lists their status.

1. **Central character (existence).** `T` has a central character `ω`.
   The forms of `T` are smooth, `K_∞`-finite and `Z(𝔤)`-finite, and of
   finite level, so the space of `T` has countable dimension. The ideles act
   through scalar matrices by operators commuting with the irreducible
   action of the operator algebra of `T`. By the countable-dimension form of
   Schur's lemma (Dixmier) each such operator is a scalar, which gives a
   homomorphism `ω` from the ideles to `ℂ^×`. It is trivial on `F^×` because
   automorphic forms are left `GL_n(F)`-invariant, and it is continuous
   because the forms are continuous and `T` is nonzero, so `ω` is a Hecke
   character. This step is independent of `S`.
2. **Central character (uniqueness).** The space of `T` is nontrivial
   (`CuspidalOperatorRealization.space_nontrivial`) and the inclusion of the
   space into forms is injective. A nonzero form `f` with `f(x) ≠ 0` gives
   `ω(z) f(x) = f(z x) = ω'(z) f(x)` for every idele `z`, so `ω = ω'` on
   the ideles and hence on `C_F`. This is clause 3.
3. **Hecke character of `det S`.** `S` is continuous, so `det S` is a
   continuous character of `W_{E/F}` (the published
   `Langlands.Weil.representationCharacterNormalization`). By the reciprocity
   law (Tate 1979 §1.2 and §2 opening), the
   transfer is a continuous surjection with kernel the commutator subgroup
   and it induces a topological isomorphism `W_{E/F}^{ab} ≅ C_F`. So
   `det S = reciprocityCharacter c F E δ` for a unique continuous `δ`.
   Uniqueness (clause 4 once `δ = ω`) needs only surjectivity of the
   transfer.
4. **Weak association at good places.** By
   `isWeaklyAssociatedClass_isoClass_iff` there is a presentation `P` of `T`
   in universe `uP` and a cofinite set of finite places `v`, including
   nonsplit ones, where every local map `ι` with `IsLocalRelativeWeilMap`
   makes `S ∘ ι` unramified with `det(1 - X S(ι Fr)) = ∏ (1 - z_i X)`, the
   `z_i` being the spectral parameters of `P` at `v`. Comparing the
   coefficients of `X^n` gives `det S(ι Fr) = z_1 ⋯ z_n`. This needs no
   semisimplicity.
5. **Automorphic side at good places.** For `i = n` the standard spherical
   Hecke operator at `v` (`Langlands/Representation/Unramified/HeckeOperators.lean`)
   is the double coset of the scalar matrix `ϖ_v · 1`, and its normalizing
   exponent `i(n − i)/2` is `0`. On the nonzero spherical fixed space of the
   embedded local component, `HasSphericalHeckeSpectrum` makes it act by
   `e_n(z) = z_1 ⋯ z_n`. The local component inherits `T.HasCentralCharacter ω`
   (`CuspidalOperatorRealization.FiniteSlice.hasCentralCharacter`, then
   `FiniteTensorPresentation.localComponent_hasCentralCharacter`, evaluated
   by `LocalRealization.centralCharacter_evaluate`), so the same operator
   acts by `ω_v(ϖ_v)`, and integral scalar units act trivially on spherical
   vectors, so `ω` is unramified at `v`. Hence `z_1 ⋯ z_n = ω_v(ϖ_v)`.
6. **Local–global compatibility at good places.** For every unramified `v`
   in the cofinite set, split or not, `transfer ∘ ι` agrees on `W_{F_v}` with
   local reciprocity for `F_v` followed by `F_v^× → C_F`, in the
   normalization of "The sign". Then `δ` is unramified at `v` and
   `det S(ι Fr) = δ_v(ϖ_v)`. With steps 4 and 5, `δ_v(ϖ_v) = ω_v(ϖ_v)`.
7. **Local components.** Outside a finite set of places, `δ` and `ω` are
   unramified (proved: `Langlands.Global.HeckeFunctionalEquation.exists_finset_isUnramifiedAt`).
   An unramified character of `F_v^×` is determined by its value at a
   uniformizer, because `F_v^×` is the product of the integral units and the
   powers of `ϖ_v`. So `δ.finiteComponent v = ω.finiteComponent v` outside a
   finite set of finite places.
8. **Rigidity.** Two Hecke characters with equal finite local components
   outside a finite set are equal: weak approximation makes `F^×` times the
   ideles that are `1` at a finite set of places dense in the ideles. This is
   `HeckeLocalComponentRigidityStatement`. So `δ = ω` as Hecke characters,
   which gives clauses 1, 2 and 4. The equality then holds on all of `C_F`,
   so `T.HasCentralCharacter δ` holds at every place, including the bad
   finite places and the infinite places.

The argument uses only unramified matching, the reciprocity law and rank-one
rigidity. It uses no ramified local Langlands compatibility, no
global-to-local gamma comparison and not `AssociatedGammaStatement`.

## Prerequisites and their status

The real prerequisites of the argument, with their status in the Library at
base `b8342b18a9c917d5ef97606f056f47113f610808`:

| Prerequisite | Step | Status |
| --- | --- | --- |
| Existence of a central character for an actual irreducible cuspidal realization (Schur–Dixmier) | 1 | not stated in the Library |
| Uniqueness of the central character from `space_nontrivial` and injective form inclusion | 2 | ingredients published; the deduction is not formalized |
| Continuity of `det S` | 3 | proved: `Langlands.Weil.representationCharacterNormalization` |
| Transfer surjective with commutator kernel | 3 | statement only: `Langlands.ClassField.Global.RelativeWeilGroup.RelativeWeilTransferReciprocityStatement` |
| Transfer is a topological quotient map onto `C_F` (continuous descent of characters) | 3 | not stated; `continuous_transfer` gives continuity only under `IsEmbedding (ideleClassInclusion …)` |
| Top coefficient of `det(1 − X A)` and of `∏ (1 − z_i X)` | 4 | elementary; not formalized |
| `i = n` Hecke operator is the scalar double coset with exponent `0`; central character acts on spherical vectors by `ω_v(ϖ_v)` | 5 | definitions and inheritance chain published; the computation is not formalized |
| Local–global compatibility of `transfer ∘ ι` with local reciprocity of `F_v` at every unramified `v`, split or not | 6 | not stated in the Library |
| Finite ramification of Hecke characters | 7 | proved: `Langlands.Global.HeckeFunctionalEquation.exists_finset_isUnramifiedAt` (the content of the statement-only `HeckeFiniteRamificationStatement`) |
| Unramified local characters are determined at a uniformizer | 7 | elementary; not formalized |
| Rank-one rigidity | 8 | statement only: `Langlands.Automorphic.Unramified.HeckeLocalComponentRigidityStatement` |

Step 6 deserves a comment. The published `IsLocalRelativeWeilMap` constrains
`ι` only on `W_{E_w}` (its condition 3). At a nonsplit unramified place this
still determines `transfer ∘ ι`: since `H^1` of the decomposition group with
coefficients in `C_E` vanishes, any two such `ι` differ by conjugation by an
element of `C_E` (both have the same image in `Gal(E/F)` by condition 2,
and their quotient is a 1-cocycle of the decomposition group with values in
`C_E`), and the transfer is invariant under conjugation. So the
compatibility is a property of the arithmetic class, not an extra choice. It
is classical (Tate 1979, Prop. 1.6.1) but absent from the Library.

## Separate proof obligations

A proof of the statement, to be a separate exact-target task after
publication, must discharge:

1. existence of a central character for every actual irreducible cuspidal
   realization (step 1);
2. uniqueness of the central character (step 2);
3. the continuous descent `det S = reciprocityCharacter c F E δ` and
   uniqueness of `δ`, from the reciprocity law and the topology of the
   transfer (step 3);
4. the good-place identity `δ_v(ϖ_v) = ω_v(ϖ_v)` at cofinitely many finite
   places, from weak association, the `i = n` Hecke operator and local–global
   compatibility of the transfer at every unramified place (steps 4–6);
5. rigidity, `δ = ω`, from finite ramification, unramified local components
   and `HeckeLocalComponentRigidityStatement` (steps 7–8).

Obligations 1 and 2 concern `T` alone; 3 concerns `S` alone; only 4 uses
association.

## Bridge to `AssociatedGammaStatement`

Henniart 1986, §4.3, step (3), needs at each place `v` of a finite set the
equality `γ(η_v Σ_v ⊗ Σ'_v) = γ(η_v Π_v × Π'_v)` for highly ramified `η_v`.
By Lemma 4.2 (2) and (4) this reduces to the equality of the characters
`det(Σ_v ⊗ Σ'_v) = (det Σ_v)^{n'} (det Σ'_v)^{n}` and
`ω_{Π_v}^{n'} ω_{Π'_v}^{n}` of `F_v^×` under local class field theory.
The present statement supplies the global input for each pair: an actual
Hecke character `ω` with `T.HasCentralCharacter ω` and
`det S = reciprocityCharacter c F E ω`, and likewise for `(S', T')`. Since
its hypotheses are exactly those of `AssociatedGammaStatement` on each pair,
it applies to that consumer without further assumptions. Between this global
identity and the local terms of the consumer, the following bridges remain
and are not part of this statement:

- **Automorphic side, any presentation.** `AssociatedGammaStatement` tests
  arbitrary presentations `P` in universe `uQ`, not the witness in `uP`.
  Because the conclusion is the global `T.HasCentralCharacter ω`, it passes
  to every such presentation by the published chain
  `CuspidalOperatorRealization.FiniteSlice.hasCentralCharacter`,
  `FiniteTensorPresentation.localComponent_hasCentralCharacter` and
  `LocalRealization.centralCharacter_evaluate`. What is missing is the
  identification of this condition with the central character of
  `(P.localComponent v).padicObject hI hA`, as a character of `F_v^×` equal
  to `ω` composed with `F_v^× → C_F`, in the form the local-constant system
  uses.
- **Galois side, any local map.** `AssociatedGammaStatement` quantifies
  every `ι` with `IsLocalRelativeWeilMap` at every finite `v`, including
  ramified ones. Turning `det S = reciprocityCharacter c F E ω` into
  `det (S ∘ ι) = ω_v ∘ (local reciprocity)` needs the local–global
  compatibility of `transfer ∘ ι` at `v` (step 6, now at every finite place)
  and the identification of the arithmetic local reciprocity with the
  reciprocity family `eC` of the local-constant system.
- **Tensor determinants.** `det (S_v ⊗ S'_v) = (det S_v)^{n'} (det S'_v)^{n}`
  follows from the published `Langlands.det_tensorProduct_map` and rank
  identities.
- **Stability.** Lemma 4.2 itself, the degeneracy of epsilon factors under
  highly ramified twists on both sides, and the existence of the global
  character `η` of §4.3 are separate inputs.

So this statement supplies the central/determinant part of the stability
step, not stability itself.

## Source correspondence

- **Henniart 1986, Theorem 4.1, printed p.157 (PDF p.14).** `K` is a global
  field, `Σ`, `Σ'` are continuous complex representations of `W_K`, `Π`,
  `Π'` automorphic representations of `GL(n, 𝔸_K)`, `GL(n', 𝔸_K)`, and
  "outside a finite subset S of S_K, Π_v corresponds to Σ_v and Π'_v to Σ'_v
  by the unramified correspondence". This is the association hypothesis,
  modelled here by `IsWeaklyAssociatedClass`.
- **Henniart 1986, Lemma 4.2, printed p.158 (PDF p.15).** For `χ` of
  sufficiently large exponent, (2) `ε(χσ) = ε(χ)^{n−1} ε(χ Det σ)` and
  (4) `ε(χπ × π') = ε(χ)^{mm'−1} ε(χ ω_π^{m'} ω_{π'}^{m})`.
- **Henniart 1986, §4.3, printed pp.158–159 (PDF pp.15–16).** Equation (2)
  compares the global functional equations. For `v ∈ T` and highly ramified
  `η_v`: "If N is large enough we have, by Lemma 4.2,
  (3) γ(η_vΣ_v ⊗ Σ'_v) = γ(η_vΠ_v × Π'_v) for v ∈ T." Henniart does not
  state the determinant/central-character identity there; step (3) uses it
  through Lemma 4.2 (2) and (4). The present statement is that implicit
  global input.
- **Henniart 2000, §2.2, printed p.444 (PDF p.6).** "Cela implique
  immédiatement que S^∨ et Π^∨ sont associées et qu'on a det S = ω_Π ∘ τ_F,
  où ω_Π est le caractère central de Π." This is the identity stated here,
  with Henniart's `τ_F` of §2.1 (same page).
- **Tate 1979.** §1.2, printed pp.4–5 (PDF pp.13–14): transfer and the
  reciprocity isomorphism `W_{E/F}^{ab} ≅ C_F`; (1.4.1), printed p.6
  (PDF p.15): uniformizers correspond to geometric Frobenius elements;
  Prop. 1.6.1, printed p.8 (PDF p.17): compatibility of local and global
  Weil groups with the local maps into idele classes; §2, opening, printed
  p.9 (PDF p.18): determinants of continuous representations correspond to
  quasicharacters of the idele class group.

Derived choices, beyond those listed in the published
[AssociatedDeterminantTwistStatement](AssociatedDeterminantTwistStatement.md)
section "Source correspondence" (finite level, arithmetic class, `τ_F` as an
inverse transfer, cuspidal realizations only), which apply here unchanged:

1. **Central character as a conclusion.** Henniart writes `ω_Π` for the
   central character of `Π`, whose existence he takes for granted. Here its
   existence is part of the conclusion, so the statement assumes neither the
   central character nor the comparison.
2. **Uniqueness clauses.** Henniart's identity is an equality of characters.
   Clauses 3 and 4 make explicit that the central character and the Hecke
   character of `det S` are each unique, so that "the" central character and
   "the" Hecke character of `det S` are well defined and equal.
3. **Class form.** The hypothesis is weak association with the cuspidal
   class of `T`, as in `AssociatedGammaStatement`, rather than with a fixed
   presentation.

## Scope

The module states one unproved theorem. It does not assert:

- the existence of any weakly associated pair or local map;
- the reciprocity law or the local–global compatibility of the transfer;
- any local identity at a ramified place, any epsilon-factor stability, or
  any gamma-factor comparison;
- anything about twists, contragredients, non-arithmetic class families,
  the absolute Weil group `W_F`, or noncuspidal automorphic representations.

## Sources

- G. Henniart, *On the local Langlands conjecture for GL(n): the cyclic
  case*, Ann. of Math. (2) 123 (1986), 145–203. Literature ID
  `henniart-1986-cyclic`, SHA256
  `096fba993b7368b1af9f7cc1f0c053e5436ba447f291c2acd402f058eb44b0ba`.
  Theorem 4.1 (printed p.157), Lemma 4.2 (p.158), §4.3 (pp.158–159). PDF page
  = printed page − 143.
- G. Henniart, *Une preuve simple des conjectures de Langlands pour GL(n)
  sur un corps p-adique*, Invent. Math. 139 (2000), 439–455. Literature ID
  `henniart-2000-simple-proof`, SHA256
  `be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
  §§2.1–2.2, printed p.444. PDF page = printed page − 438.
- J. Tate, *Number theoretic background*, in Automorphic Forms,
  Representations and L-Functions, Proc. Sympos. Pure Math. 33, Part 2
  (1979). Literature ID `tate-1979-number-theoretic-background`, SHA256
  `c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`.
  §1.2, (1.4.1), Prop. 1.6.1 and §2 opening, printed pp.4–9. PDF page =
  printed page + 9.
