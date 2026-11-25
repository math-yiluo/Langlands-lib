# Twisted traces are detected by σ-regularly supported test functions

The module `Langlands.BaseChange.TwistedTraceRegularNonvanishingStatement` states, as the
proposition `TwistedTraceRegularNonvanishingStatement.{u, v, uW}`, that the twisted distribution
character `φ ↦ tr(τ(φ) ∘ A)` of an irreducible admissible representation `τ` of `GL_n(E)`, with
`A` an isomorphism of `τ` onto `τ^σ`, does not vanish on all Schwartz–Bruhat functions supported
in the σ-regular set. The statement is **not** proved here.

## Notation (Library and Mathlib)

- `IsCyclicAlgebra σ l`, `IsSigmaRegular σ l δ` (module `Langlands.BaseChange.Norm`): `E` is a
  cyclic `F`-algebra of group `⟨σ⟩` of order `l` (HL I.2.1), and `δ ∈ GL_n(E)` is σ-regular
  when `N(δ) = δ σ(δ) ⋯ σ^{l-1}(δ)` is conjugate in `GL_n(E)` to a regular semisimple element
  of `GL_n(F)` (separable characteristic polynomial).
- `IsSigmaRegularSupported σ l φ` (module `Langlands.BaseChange.OrbitalIntegral`): every `δ`
  with `φ δ ≠ 0` is σ-regular.
- `SchwartzBruhat (GeneralLinear n E)` (namespace `Langlands.HarmonicAnalysis`): locally
  constant compactly supported functions `GL_n(E) → ℂ`.
- `IsAdmissible τ` means that `τ` is smooth and has finite-dimensional fixed-vector spaces
  for open subgroups. `Representation.IsIrreducible` is Mathlib's irreducibility predicate.
- `SigmaIntertwiner σ n τ` (module `Langlands.BaseChange.TwistedCharacter`): an isomorphism
  (`Representation.Equiv`) of `τ` onto `τ^σ = τ ∘ (entrywise σ)`, that is a linear bijection
  `A` with `A ∘ τ(g) = τ(σ(g)) ∘ A` (HL II.1.3, II.2.7). `A.toLinearMap` is its linear map.
- `twistedDistribution μ τ hτ A φ` (module `Langlands.BaseChange.TwistedCharacter.Basic`): the
  trace of the finite-rank operator `τ(φ) ∘ A`, where `τ(φ) = ∫ φ(g) τ(g) dμ(g)`.

## Statement

`TwistedTraceRegularNonvanishingStatement.{u, v, uW}` quantifies over a field `F : Type u` with
`[ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]`; a
commutative `F`-algebra `E : Type v` with `[TopologicalSpace E] [IsTopologicalRing E]
[IsModuleTopology F E]`; `σ : E ≃ₐ[F] E` and `l n : ℕ` with `hE : IsCyclicAlgebra σ l`. Under
these, the instances `Module.Finite F E` (from `hE`), `T2Space`, `LocallyCompactSpace` and
`TotallyDisconnectedSpace` on `GL_n(E)` (lemmas `generalLinear_*_of_finite` of
`Langlands.BaseChange.TwistedCharacter`) and the Borel σ-algebra on `GL_n(E)` are introduced
inside the statement, as in the Library's `TwistedCharacterRegularValuesStatement`.

The claim: for every complex vector space `W : Type uW`, every
`τ : Representation ℂ (GeneralLinear n E) W` with `hτ : IsAdmissible τ` and `τ.IsIrreducible`,
every `A : SigmaIntertwiner σ n τ` and every Haar measure `μ` on `GL_n(E)`, there is
`φ : SchwartzBruhat (GeneralLinear n E)` with `IsSigmaRegularSupported σ l φ` and
`twistedDistribution μ τ hτ A.toLinearMap φ ≠ 0`.

For `σ = id`, `l = 1` and `E = F` it is the corresponding untwisted statement for `GL_n(F)`.

## Why it is true (sketch)

The one-character case of the lemma in HL II.2.8 (printed p. 69) gives a point of
nonvanishing in the σ-regular set. In characteristic zero the argument is as follows.

1. Choose a compact open subgroup `K` small enough that `W^K ≠ 0` and intersect its finitely
   many σ-translates to make it σ-stable. Then `A` restricts to an automorphism of `W^K`.
   This fixed space is finite dimensional by admissibility and simple as a module over
   the bi-`K`-invariant Hecke algebra by irreducibility of `τ`. By density its Hecke operators
   span `End(W^K)`, and on `W` they factor through the averaging projection onto `W^K`.
   The trace pairing with `A|_{W^K}` is therefore nonzero. This is the compact-open argument
   of Arthur–Clozel, Chapter 1, Lemma 6.3 (printed p. 52).
2. The twisted distribution is integration against `Θ^A_τ`, a locally integrable function
   locally constant on the open, conull σ-regular set. Use the characteristic-zero theorem
   (Arthur–Clozel, Chapter 1, Proposition 2.2) in the field case and the product reduction of
   HL II.2.8 for cyclic algebras. The field theorem can use a normalized intertwiner: by Schur's
   lemma any `A` differs from it by a nonzero scalar. The Library's
   `TwistedCharacterRegularValuesStatement` states local constancy;
   `TwistedCharacterLocalIntegrabilityStatement` and `SigmaRegularOpenConullStatement` (module
   `RegularSetOpenConullStatement`) state twisted local integrability and regular-set
   conullness. Since the distribution is nonzero, `Θ^A_τ(δ) ≠ 0` for some σ-regular `δ`.
3. Choose a compact open neighbourhood `U` of `δ` inside the σ-regular set on which `Θ^A_τ`
   is constant. The indicator of `U` has twisted trace `μ(U) Θ^A_τ(δ)`, which is nonzero
   because every Haar measure gives positive finite mass to `U`.

For `n = 0` the group is trivial, its only element is σ-regular, and `φ = 1` works.

## Sources

- Henniart–Lemaire, *Changement de base et induction automorphe pour `GL_n` en
  caractéristique non nulle*, Mém. SMF 124 (2011), file
  `/home/taskhub/central-library/Henniart-Lemaire--Changement de base et induction automorphe pour GLn en caracteristique non nulle--2011.pdf`
  (PDF page = printed page + 8), cited as HL. I.2.1, printed pp. 10–11 (cyclic algebras);
  II.1.3, printed pp. 56–57 (twisted character for a field `E`); II.2.7–II.2.8, printed
  pp. 66–69 (twisted characters for cyclic algebras, with linear independence on the
  σ-regular set in the lemma on p. 69).
- Arthur–Clozel 1989, source ID `arthur-clozel-1989-base-change` (PDF page = printed page + 14),
  Chapter 1, Proposition 2.2, printed pp. 11–12 (characteristic-zero local integrability and
  local constancy near σ-regular elements, after Clozel), and Lemma 6.3, printed p. 52
  (compact-open Hecke algebra argument).

## Derived content

The lemma of HL II.2.8 concerns values of character functions. The project statement takes
its one-character case and passes to a compactly supported test function with nonzero trace,
for every cyclic algebra `E` and each choice of Haar measure. The support restriction serves
the regularly supported concordant-pair comparison of HL II.6.10 (printed pp. 125–126,
(1)–(3)). HL II.6.16 (pp. 131–132) obtains nonzero local twisted factors in the twisted
globalization; II.6.17 (p. 132) uses nonvanishing of the σ-regular character at the place of
descent. These are applications, not hypotheses of the local statement.

The hypothesis `[CharZero F]` is used as in `TwistedCharacterRegularValuesStatement`: the
Library's regular semisimple set (separable characteristic polynomial) is HL's regular set in
characteristic zero.
