# The σ-lift of a supercuspidal representation is a product of Galois conjugates

This module `Langlands.BaseChange.CuspidalSigmaLiftStructureStatement` (namespace
`Langlands.BaseChange`) states, as the proposition
`CuspidalSigmaLiftStructureStatement.{u, v, uV, uW}`, Henniart–Lemaire's description of the
σ-lift of an irreducible supercuspidal representation of `GL_n` over a nonarchimedean local
field of characteristic zero. The statement is **not** proved here.

## Sources

- Henniart–Lemaire, *Changement de base et induction automorphe pour GL_n en
  caractéristique non nulle*, Mém. SMF 124 (2011), source ID
  `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`
  (PDF page = printed page + 8). Cited below as HL.
  - II.4.12, Proposition (printed p. 96, PDF p. 104): for an irreducible cuspidal `π` of
    `G(F)` and `s` the order of the stabilizer of its isomorphism class in `K(E/F)`, every
    σ-lift `Π` of `π` satisfies: `s` divides `n`, `n = n₁ s`, and
    `Π ≅ Π₁ × Π₁^σ × ⋯ × Π₁^{σ^{s-1}}` for an irreducible cuspidal `Π₁` of `G_{n₁}(E)` such
    that `σ^s` generates the stabilizer of the isomorphism class of `Π₁` in `Σ = ⟨σ⟩`. (The
    printed text writes "de `ρ`" for the class of `π`.)
  - II.1.3 (printed p. 56): `K(E/F)` and `Π^σ`; II.2.7 (printed p. 67): σ-lifts
    (σ-relèvements).
  - II.3.5 (printed pp. 80–81), II.4.6 (printed pp. 88–89): the tools of HL's proof (see
    "Proof routes").
- Arthur–Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the Trace
  Formula* (1989), source ID `arthur-clozel-1989-base-change`, Chapter 1, Lemma 6.10
  (printed p. 62, PDF p. 76) and the paragraph before it: the case of prime degree.

## Notation

`GL_m(R)` is the Library's `Langlands.GeneralLinear m R`. From
`Langlands.BaseChange.Norm` (Task 7405): `entrywiseAut σ m`, the entrywise action
`g ↦ g^σ` on `GL_m(E)`, and `IsCyclicAlgebra σ l`. From
`Langlands.BaseChange.TwistedCharacter` (Task 7432): `SigmaIntertwiner σ m Π`, the
isomorphisms `A` of `Π` onto `Π^σ`, and `IsSigmaLift σ l π hπ Π hΠ A c`, HL's σ-lift
(II.2.7): `c ≠ 0` and `trace(Π(φ) ∘ A) = c · trace π(f)` for all Haar measures and all
concordant pairs `(φ, f)`. From `Langlands.BaseChange.CuspidalSigmaLift`:
`normTwistStabilizer E π` and `sigmaOrbitProduct σ s hn₁ Π₁`. For a representation `Π₁`
of `GL_m(E)` and `i : ℕ`, `Π₁^{σ^i}` is `Π₁.comp (entrywiseAut (σ ^ i) m).toMonoidHom`.
"Irreducible" is Mathlib's `Representation.IsIrreducible`, "isomorphic" is
`Nonempty (Representation.Equiv _ _)`, "admissible" is the Library's `IsAdmissible`, and
"supercuspidal" is the Library's `GeneralLinear.IsSupercuspidal` (which includes
admissibility). In Lean the representation `Π` is written `P` and `Π₁` is written `P₁`.

## Statement

`CuspidalSigmaLiftStructureStatement` says: for

- a field `F : Type u` with `[ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [CharZero F]`,
- a field `E : Type v` with `[ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E] [Algebra F E] [IsModuleTopology F E]`,
- `σ : E ≃ₐ[F] E` and `l n : ℕ` with `IsCyclicAlgebra σ l` and `0 < n`,
- an irreducible supercuspidal `π : Representation ℂ (GL_n(F)) V` (`V : Type uV`) with
  `hπ : IsAdmissible π`,
- an irreducible `Π : Representation ℂ (GL_n(E)) W` (`W : Type uW`) with
  `hΠ : IsAdmissible Π`,
- `A : SigmaIntertwiner σ n Π` and `c : ℂ` with `IsSigmaLift σ l π hπ Π hΠ A c`,

writing `s := Nat.card (normTwistStabilizer E π)`:

1. `s ∣ l`, and
2. there are `n₁ : ℕ`, `hn₁ : 0 < n₁`, `h : s * n₁ = n`, a complex vector space
   `W₁ : Type uW` and `Π₁ : Representation ℂ (GL_{n₁}(E)) W₁` such that `Π₁` is
   supercuspidal and irreducible, `Π₁ ≅ Π₁^{σ^i}` holds exactly for the `i : ℕ` with
   `s ∣ i`, and
   `Π ≅ (sigmaOrbitProduct σ s hn₁ Π₁).comp (GeneralLinear.reindex (R := E) (finCongr h)).symm.toMonoidHom`,
   that is, `Π ≅ Π₁ × Π₁^σ × ⋯ × Π₁^{σ^{s-1}}` after the rank transport
   `GL_{s * n₁}(E) ≃* GL_n(E)`.

`IsSigmaLift` takes `T2Space`, `LocallyCompactSpace` and `TotallyDisconnectedSpace` for
`GL_n(F)` and `GL_n(E)` as instance arguments; the statement supplies them with `haveI` from
the Library's `LocalFieldTopology.generalLinear_t2Space`,
`LocalFieldTopology.generalLinear_locallyCompactSpace` and
`LocalFieldTopology.generalLinear_totallyDisconnectedSpace`, applied to `F` and to `E` (a
nonarchimedean local field in its own right).

## The group `K(E/F)` and the value of `s`

By local class field theory, when `E/F` is cyclic of degree `l`, `N_{E/F}(E^×)` is an open
subgroup of `F^×` of index `l` with cyclic quotient, so `K(E/F)` (the norm-trivial characters,
`IsNormTrivial`) is cyclic of order `l`, and its elements are automatically continuous;
`IsNormTrivial` therefore asks no continuity. The stabilizer `normTwistStabilizer E π` is a
subgroup of `K(E/F)`, so its order divides `l` (Lagrange). These facts are not formalized;
the statement asserts `s ∣ l` as its first conclusion. `s` is `Nat.card` of the stabilizer,
and `Nat.card` of an infinite type is `0`. The statement nevertheless asserts
`s * n₁ = n` with `0 < n`, so `s ≠ 0`: it implies that the stabilizer is finite (and it is
nonempty, as a subgroup).

## The stabilizer clause

When `E` is a field with `IsCyclicAlgebra σ l`, `σ` has order `l = [E : F]` and fixes exactly
`F`, so `σ` generates `Gal(E/F)`, which is cyclic of order `l`. The stabilizer of the
isomorphism class of `Π₁` in `Gal(E/F)` is then generated by some `σ^t` with `t ∣ l`, and the
clause `∀ i : ℕ, (Π₁ ≅ Π₁^{σ^i}) ↔ s ∣ i` says exactly that `t = s`: this is HL's "`σ^s`
engendre le stabilisateur de la classe d'isomorphisme de `Π₁` dans `Σ`".

## Convention for `Π^σ`

`Π₁^{σ^i}` is `g ↦ Π₁(g^{σ^i})`, as in HL II.1.3 and Task 7432. The factors
`{Π₁^{σ^i} : 0 ≤ i < s}` form the `Gal(E/F)`-orbit of the class of `Π₁`, so the other
convention (`σ⁻¹`) gives the same factors in another order; for pairwise unlinked cuspidal
factors (as here, see `CuspidalSigmaLiftExistenceStatement.md`) the product does not depend
on the order (Bernstein–Zelevinsky).

## The product

`sigmaOrbitProduct σ s hn₁ Π₁` is normalized parabolic induction from the standard block
upper triangular parabolic subgroup of `GL_{s * n₁}(E)` with `s` diagonal blocks of size
`n₁`, the `i`-th block carrying `Π₁^{σ^i}`; this is HL's `×` (Bernstein–Zelevinsky product).
Its carrier is the Library's space of smooth induced functions. The isomorphism with `Π` is
transported along `GeneralLinear.reindex (finCongr h) : GL_{s * n₁}(E) ≃* GL_n(E)`, the same
rank transport as the Library's `LocalFieldData.singleBlockNormalizedProductEquiv`.

## Prime degree

If `l` is prime, then `s ∈ {1, l}` since `s ∣ l`. For `s = 1`, `n₁ = n` and lemma
`sigmaOrbitProduct_one_equiv` (module `CuspidalSigmaLift`) gives `Π ≅ Π₁` up to the rank
transport, so `Π` is supercuspidal and, by the stabilizer clause with `i = 1`, σ-stable.
For `s = l`, `Π ≅ Π₁ × Π₁^σ × ⋯ × Π₁^{σ^{l-1}}` with `Π₁` supercuspidal and `Π₁ ≇ Π₁^σ`.
These are the two cases (i) and (ii) of Arthur–Clozel, Chapter 1, Lemma 6.10.

## Universes

The carrier `W₁` of `Π₁` is existential, in the universe `uW` of the carrier of `Π`. This is
harmless: an irreducible admissible representation of `GL_m` over a nonarchimedean local
field has countable dimension, so it has a model in every universe.

## The field `E` and `CharZero F`

HL II.4.12 is stated for a cyclic extension field `E` of `F`. The statement requires `E` to be
a nonarchimedean local field (with its own `ValuativeRel`) because the Library's product
induction (`LocalFieldData.ofInstances E`) needs it. `[IsModuleTopology F E]` makes the
topology of `E` the one induced from `F`, as in Task 7432. `CharZero F` is assumed as in
Tasks 7416, 7432, 7442 and 7449: the concordance of test functions inside `IsSigmaLift` uses
the Library's `IsRegularSemisimple` (separable characteristic polynomial), which agrees with
HL's regularity (squarefree characteristic polynomial) in characteristic zero; Arthur–Clozel
also work in characteristic zero.

## Proof routes

HL prove the Proposition as follows. `π` is essentially discrete, so `Π` is essentially
σ-discrete (II.4.6, Théorème (1), and II.4.7: Task 7449). By the classification of σ-discrete
series (II.4.6, citing Arthur–Clozel, Chapter 1, Lemma 2.8),
`Π ≅ Π₁ × Π₁^σ × ⋯ × Π₁^{σ^{t-1}}` with `Π₁` essentially discrete and `σ^t` generating the
stabilizer of its class. The identity of Rankin–Selberg factors
`L(Π, Π̌) = ∏_{κ ∈ K(E/F)} L(π, κπ̌)` (II.4.6, Théorème (4)) and the properties of
`L`-functions of pairs (II.3.5 (i) and (iii)) then give `t = s` and that `Π₁` is cuspidal.
In prime degree Arthur–Clozel instead prove the cuspidality of the factor with Jacquet
modules and the twisted Casselman theorem (Chapter 1, Proposition 2.3). A later proof task
must not derive this statement from a result that depends on it, in particular not from
`CuspidalSigmaLiftExistenceStatement` if that is proved from this statement (as HL's
Remarque is proved from the Proposition and its Corollaire).
