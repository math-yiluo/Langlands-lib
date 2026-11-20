# Uniqueness of σ-lifts

This module `Langlands.BaseChange.SigmaLiftUniquenessStatement` (namespace
`Langlands.BaseChange`) states, as the proposition `SigmaLiftUniquenessStatement`, that an
irreducible admissible representation of `GL_n(F)` has at most one irreducible σ-lift to
`GL_n(E)` up to isomorphism. The statement is **not** proved here.

## Sources

- Henniart–Lemaire, *Changement de base et induction automorphe pour GL_n en
  caractéristique non nulle*, Mém. SMF 124 (2011), source ID
  `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`
  (PDF page = printed page + 8). Cited as HL.
  - II.2.7, Définition (printed p. 67): σ-relèvement.
  - II.2.8, Lemme (printed p. 69): the twisted characters of pairwise non-isomorphic
    irreducible σ-stable representations are linearly independent.
  - II.2.9, Proposition and Remarque (2) (printed pp. 69–70): "si Π est un σ-relèvement de
    π, alors à isomorphisme près, ce relèvement est unique, et sa classe d'isomorphisme ne
    dépend que de celle de π".
- Arthur–Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the Trace
  Formula* (1989), source ID `arthur-clozel-1989-base-change` (PDF page = printed page + 14).
  Cited as AC. Chapter 1, Theorem 6.2 (a) (printed p. 51), "unique lift", for tempered
  representations of a cyclic field extension, and Lemma 6.3 (printed p. 52), the linear
  independence of the twisted characters of non-isomorphic irreducible σ-stable
  representations, from which AC deduce the uniqueness.

## Setting

`GL_n(R)` is the Library's `GeneralLinear n R`. The statement quantifies over:

- a nonarchimedean local field `F : Type u` of characteristic zero (`[Field F]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F]`);
- a commutative `F`-algebra `E : Type v` with a topology making it a topological ring that
  is the `F`-module topology (`[CommRing E] [Algebra F E] [TopologicalSpace E]
  [IsTopologicalRing E] [IsModuleTopology F E]`);
- `σ : E ≃ₐ[F] E` and `l n : ℕ` with `hσ : IsCyclicAlgebra σ l` (module
  `Langlands.BaseChange.Norm`): `E` is a cyclic `F`-algebra of group `⟨σ⟩` of order `l`.

The first conjunct `hσ.1` of `IsCyclicAlgebra` gives `Module.Finite F E`. With it, the
topologies of `GL_n(F)` and `GL_n(E)` are made Hausdorff, locally compact and totally
disconnected inside the statement (`haveI`) by the Library's
`LocalFieldTopology.generalLinear_t2Space` and companions and by
`generalLinear_t2Space_of_finite` and companions of `Langlands.BaseChange.TwistedCharacter`.
These are the instance arguments of `IsSigmaLift`.

## Statement

`SigmaLiftUniquenessStatement.{u, v, uV, uW, uW'}`: for every complex vector space
`V : Type uV` and irreducible (`π.IsIrreducible`, Mathlib) admissible (`hπ : IsAdmissible π`)
representation `π : Representation ℂ (GL_n(F)) V`, all irreducible admissible
representations `ρ : Representation ℂ (GL_n(E)) W` (`W : Type uW`, `hρ : IsAdmissible ρ`)
and `ρ' : Representation ℂ (GL_n(E)) W'` (`W' : Type uW'`, `hρ' : IsAdmissible ρ'`), all
`A : SigmaIntertwiner σ n ρ`, `A' : SigmaIntertwiner σ n ρ'` and `c c' : ℂ`: if
`IsSigmaLift σ l π hπ ρ hρ A c` and `IsSigmaLift σ l π hπ ρ' hρ' A' c'`, then
`Nonempty (ρ.Equiv ρ')`, that is, `ρ` and `ρ'` are isomorphic representations.

The carriers `W` and `W'` may lie in different universes; Mathlib's `Representation.Equiv`
allows this.

**Names.** HL write `Π` for representations of `GL_n(E)`. The letters `Π` and `Σ` are reserved
tokens in Lean, so the Lean statement writes `ρ` and `ρ'` for HL's `Π` and `Π'`, and `π` as
in HL for representations of `GL_n(F)`.

## Explanations

- **σ-lifts.** `IsSigmaLift σ l π hπ ρ hρ A c` (module `Langlands.BaseChange.TwistedCharacter`, Task 7432) is HL's σ-relèvement (II.2.7,
  printed p. 67): `c ≠ 0`, and for all Haar measures on `GL_n(F)` and `GL_n(E)` and every
  pair `(φ, f)` of concordant test functions (`AreConcordant` of `Langlands.BaseChange.OrbitalIntegral`, Task 7416), the twisted trace
  `trace(ρ(φ) ∘ A)` equals `c` times the trace `trace(π(f))`. Task 7432's
  `SigmaLiftCharacterIdentityStatement` (HL II.2.9, Proposition) states its equivalence with
  the Shintani identity `IsShintaniLift` of AC Definition 6.1.
- **The constant.** HL show that `c = 1` when `A` is the Whittaker-normalized intertwiner
  `I_σ(Π)` (II.4.6, Théorème (1)). That normalization is not defined in the programme, so σ-lifts
  are taken with an arbitrary intertwiner and some constant, which is nonzero by the
  definition of `IsSigmaLift`. Replacing `A` by a nonzero multiple `a • A` replaces `c` by
  `a * c`. Here the intertwiners `A`, `A'` and the constants `c`, `c'` are arbitrary and
  unrelated: the conclusion concerns only the isomorphism class of the lift.
- **Field and algebra.** HL treat a cyclic `F`-algebra `E` in II.2 and reduce it to a field
  (II.2.8, Remarque; II.2.9, Remarque (1)), so this statement allows `IsCyclicAlgebra σ l`
  with `E` a commutative ring, which includes the split algebra `F^l` with the cyclic shift.
  The degree `l` is not assumed prime.
- **`CharZero F`.** As in Tasks 7416, 7432 and 7442: the Library's `IsRegularSemisimple` asks
  for a separable characteristic polynomial, while HL's regular elements have squarefree
  characteristic polynomial; the two agree in characteristic zero, where HL's results and
  AC's apply verbatim.
- **Proof route.** HL deduce Remarque (2) from the Lemme of II.2.8 (linear independence of the
  twisted characters of pairwise non-isomorphic irreducible σ-stable representations) and the
  Proposition of II.2.9 (σ-lifts are Shintani lifts): two lifts of `π` have proportional
  twisted characters on the σ-regular set, so they are isomorphic. A later proof task must not
  derive this statement from a result that depends on it.
