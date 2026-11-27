# Descent of σ-stable supercuspidal representations of `GL_n(E)`

The module `Langlands.BaseChange.SigmaStableSupercuspidalDescentStatement` states, as the
proposition `SigmaStableSupercuspidalDescentStatement.{u, v, uV, uW}`, that for a cyclic field
extension `E/F` of nonarchimedean local fields of characteristic zero with generator `σ`, every
σ-stable irreducible supercuspidal representation `τ` of `GL_n(E)`, `0 < n`, with any
isomorphism `A` of `τ` onto `τ^σ`, is a σ-lift of an irreducible supercuspidal representation
`π` of `GL_n(F)`. The module states the proposition and does not prove it.

## Notation (Library and Mathlib)

- `IsCyclicAlgebra σ l` (module `Langlands.BaseChange.Norm`); `E` is a field here.
- `GeneralLinear.IsSupercuspidal τ` (module
  `Langlands.Representation.Classification.Supercuspidal`): admissible (first component `hτ.1`)
  with vanishing Jacquet coinvariants along every proper block parabolic subgroup and its
  conjugates. `τ.IsIrreducible` is Mathlib's irreducibility of a representation.
- `SigmaIntertwiner σ n τ` (module `Langlands.BaseChange.TwistedCharacter`): an isomorphism of
  `τ` onto `τ^σ = τ ∘ entrywiseAut σ n`, that is `A τ(g) = τ(g^σ) A`.
- `IsSigmaLift σ l π hπ τ hτ A c` (module `Langlands.BaseChange.TwistedCharacter`, HL II.2.7,
  Définition, printed p. 67): `c ≠ 0`, and for all Haar measures `μF` on `GL_n(F)` and `μE` on
  `GL_n(E)` and all concordant Schwartz–Bruhat functions `φ` and `f`,
  `tr(τ(φ) ∘ A) = c · tr π(f)`.

## Statement

`SigmaStableSupercuspidalDescentStatement.{u, v, uV, uW}` quantifies over a field `F : Type u`
with `[ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]`; a
field `E : Type v` with `[Algebra F E] [TopologicalSpace E] [IsTopologicalRing E]
[IsModuleTopology F E]`; `σ : E ≃ₐ[F] E` and `l n : ℕ` with `hE : IsCyclicAlgebra σ l` and
`0 < n`. The topological instances on `GL_n(F)` and `GL_n(E)` are those of the Library
(`LocalFieldTopology.generalLinear_*` and `generalLinear_*_of_finite`).

The claim: for every complex vector space `W : Type uW`, every
`τ : Representation ℂ (GeneralLinear n E) W` with `hτ : GeneralLinear.IsSupercuspidal τ` and
`τ.IsIrreducible`, and every `A : SigmaIntertwiner σ n τ`, there are a complex vector space
`V : Type uV`, `π : Representation ℂ (GeneralLinear n F) V` with
`hπ : GeneralLinear.IsSupercuspidal π`, and `c : ℂ` such that `π.IsIrreducible` and
`IsSigmaLift σ l π hπ.1 τ hτ.1 A c`.

The generator `σ` is arbitrary; the statement applies in particular to `σ⁻¹`, which generates
the same cyclic algebra.

## Sources

- Henniart–Lemaire, *Changement de base et induction automorphe pour `GL_n` en
  caractéristique non nulle*, Mém. SMF 124 (2011), file
  `/home/taskhub/central-library/Henniart-Lemaire--Changement de base et induction automorphe pour GLn en caracteristique non nulle--2011.pdf`
  (PDF page = printed page + 8), cited as HL. II.2.7, Définition, printed p. 67 (σ-lifts);
  II.4.6, Théorème (2), printed p. 88 (every σ-discrete series of `G(E)` lifts a discrete series
  of `G(F)`); II.4.12, Remarque, printed p. 97 (an essentially σ-discrete `Π` lifts an
  essentially discrete `π = L(ρ, a)`; `π` is cuspidal if and only if `Π` is isomorphic to a
  parabolic induction of an irreducible cuspidal representation of a Levi subgroup, for example
  `Π` itself when `Π` is cuspidal).
- Arthur–Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the Trace Formula*
  (1989), source ID `arthur-clozel-1989-base-change`, file
  `/home/taskhub/central-library/Arthur-Clozel--Simple algebras, base change, and the advanced theory of the trace formula (book)--1989.pdf`
  (PDF page = printed page + 14). Chapter 1, Theorem 6.2 (b), printed p. 51, the
  characteristic-zero source for the descent of σ-discrete series.

## Proof sketch

Twist `τ` by an unramified character `|det|_E^{-s}` so that its central character is unitary;
`|det x^σ|_E = |det x|_E`, so `A` is still a σ-intertwiner. A supercuspidal representation with
unitary central character is a discrete series, and an irreducible σ-stable supercuspidal is not
isomorphic to a proper parabolic induction, so the twist is a σ-discrete series. HL II.4.6 (2)
gives a discrete series `π₁` of `GL_n(F)` with the twist a σ-lift of `π₁`, and `π₁` is cuspidal
by the last sentence of HL II.4.12, Remarque. Twisting back by `|det|_F^{s}` (HL II.2.9,
Remarque (4); `|N_{E/F}(y)|_F = |y|_E`) gives `π`. The σ-lift property holds for every
σ-intertwiner of `τ` once it holds for one, with the constant scaled, since two σ-intertwiners
of an irreducible admissible representation differ by a nonzero scalar.

`SigmaDiscreteDescentStatement` uses the same hypotheses on `E` and states descent from
σ-discrete series to discrete series. The case `s = 1` of `CuspidalSigmaLiftExistenceStatement`
states supercuspidal descent with the module topology and additional valued local-field
structure on `E`.

## Derived content

The statement specializes the descent of HL II.4.6 (2) and II.4.12 to σ-stable supercuspidal
representations of `GL_n(E)` for a field `E` with its module topology over `F`, with an
arbitrary σ-intertwiner, and records the supercuspidality of the descended representation.
