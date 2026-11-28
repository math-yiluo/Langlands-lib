# Characters are detected by regularly supported functions near the norms (statement)

Module `Langlands.BaseChange.RegularNormTraceNonvanishingStatement`, namespace
`Langlands.BaseChange`. It contains one proposition definition and no proof:

- `Langlands.BaseChange.RegularNormTraceNonvanishingStatement.{u, v, uV}`.

In words: let `F` be a nonarchimedean local field of characteristic zero, `E` a cyclic
`F`-algebra with group `⟨σ⟩` of order `l` (for instance a cyclic field extension of degree
`l`), and `n > 0`. For every irreducible admissible representation `π` of `GL_n(F)` and every
Haar measure `μ` on `GL_n(F)` there is a Schwartz–Bruhat function `f` on `GL_n(F)` such that

1. `f` is supported in the regular semisimple set;
2. the orbital integrals of `f` (for `μ`) vanish at the regular semisimple elements that are
   not norms from `GL_n(E)`;
3. `det g` lies in the norm group `N_{E/F}(E^×)` whenever `f g ≠ 0`;
4. `tr π(f) ≠ 0`.

The statement concerns ordinary (untwisted) characters only. Through regular transfer (the
Library's `regularTransfer`, a proof of `RegularTransferStatement`), a function `f` with
properties 1–3 is concordant with some `φ` supported in the `σ`-regular set of `GL_n(E)`, so the
statement provides concordant pairs of the kind used in `IsRegularSigmaLift` (module
`Langlands.BaseChange.SigmaDiscreteRegularDescentStatement`) on which the ordinary side does
not vanish. The module
`Langlands.TraceFormula.CuspidalCyclicBaseChangeRegularLiftAnyDegreeReductionStatement` uses it
in this way.

## Setting and notation

- `F : Type u` with `[Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [CharZero F]`.
- `E : Type v` a commutative `F`-algebra with a topological ring structure and the module
  topology over `F` (`IsModuleTopology F E`), `σ : E ≃ₐ[F] E` and `l : ℕ` with
  `IsCyclicAlgebra σ l` (module `Langlands.BaseChange.Norm`).
- `GL_n(F)` carries the topology of `Langlands.Group.GL.LocalFieldTopology` (Hausdorff, locally
  compact, totally disconnected) and the Borel σ-algebra.
- `π : Representation ℂ (GeneralLinear n F) V` on a complex vector space `V : Type uV`, with
  `hπ : IsAdmissible π` and `π.IsIrreducible`.
- `IsRegularSupported`, `VanishesOffNorms` (module `Langlands.BaseChange.OrbitalIntegral`):
  `f g ≠ 0` only at regular semisimple `g`; and `orbitalIntegral γ νγ f = 0` for every regular
  semisimple `γ` with `¬ IsNorm σ l γ` and every quotient measure `νγ` compatible with `μ` and a
  Haar measure on the centralizer of `γ`.
- `(Units.map (Algebra.norm F : E →* F)).range` is the norm subgroup of `F^×`, and
  `GeneralLinear.determinant` the determinant `GL_n(F) → F^×`.
- `Character.distribution μ π hπ f` (module `Langlands.Representation.Character.Basic`) is the
  trace of `π(f) = ∫ f(g) π(g) dμ(g)`.

## Statement

For all `F`, `E`, `σ`, `l`, `n` as above with `IsCyclicAlgebra σ l` and `0 < n`, every `V`,
`π`, `hπ` with `π.IsIrreducible`, and every Haar measure `μ` on `GL_n(F)`, there is
`f : SchwartzBruhat (GeneralLinear n F)` with

- `IsRegularSupported f`,
- `VanishesOffNorms σ l μ f`,
- `∀ g, f g ≠ 0 → GeneralLinear.determinant g ∈ (Units.map (Algebra.norm F : E →* F)).range`,
- `Character.distribution μ π hπ f ≠ 0`.

The universe parameters are those of `F`, of `E` and of the representation space `V`.

## Why the statement is true

The argument uses three facts about `GL_n(F)` in characteristic zero.

- **Norms near the identity.** Some neighbourhood of `1` in `GL_n(F)` consists of norms
  (Henniart–Lemaire 2011, II.6.7, printed p. 123; the Library's `normNeighbourhood`, a proof of
  `NormNeighbourhoodStatement`, part (a)). The norm group `N_{E/F}(E^×)` is an open subgroup of
  `F^×`, so `det g` is a norm for `g` near `1`.
- **The regular set.** The regular semisimple set is open and its complement has Haar measure
  zero (the Library's proposition `Langlands.BaseChange.RegularSemisimpleOpenConullStatement`,
  module `Langlands.BaseChange.RegularSetOpenConullStatement`, and its proof
  `Langlands.BaseChange.regularSemisimpleOpenConull`, module
  `Langlands.BaseChange.RegularSetOpenConull`).
- **Local integrability of the character** (Harish-Chandra; the Library's
  `CharacterLocalIntegrabilityStatement`, which that module states and does not prove): there
  is a locally integrable function `Θ_π` on `GL_n(F)` with `tr π(f) = ∫ f Θ_π dμ` for every
  Schwartz–Bruhat `f`.

Choose a compact open subgroup `J` of `GL_n(F)`, inside the neighbourhood of `1` of the first
fact and inside the preimage of the norm group under `det`, so small that `π` has nonzero
`J`-fixed vectors. Then `tr π(1_J) = μ(J) · dim V^J ≠ 0`, that is `∫_J Θ_π dμ ≠ 0`. The set
`J_r` of regular semisimple elements of `J` is open in the totally disconnected, second
countable space `J` and has full measure in `J`, so it is an increasing union of compact open
subsets `C_1 ⊆ C_2 ⊆ ⋯`; by dominated convergence `∫_{C_m} Θ_π dμ → ∫_J Θ_π dμ`. For `m` large,
`f := 1_{C_m}` has `tr π(f) = ∫_{C_m} Θ_π dμ ≠ 0`. It is supported in the regular semisimple set
and in `J`, so its determinants are norms. Its orbital integral at a regular semisimple `γ` is
an integral of `f` over the conjugacy class of `γ`, and vanishes unless that class meets
`C_m ⊆ J`; all elements of `J` are norms and being a norm is invariant under conjugation, so the
orbital integrals of `f` vanish at the non-norms.

## Provenance

This is derived content: the statement is formulated here as the local input that makes the
constant of a regular σ-lift identity nonzero, and no source states it in this form. It is the
untwisted counterpart of the nonvanishing of twisted traces on the `σ`-regular set
(`TwistedTraceRegularNonvanishingStatement`, module
`Langlands.BaseChange.TwistedTraceRegularNonvanishingStatement`). Henniart–Lemaire 2011, II.6.13
(printed pp. 129–130), obtain the nonvanishing of their constant from a concordant pair with
regular support and nonzero trace; Arthur–Clozel 1989, Chapter 1, §6.3 (printed pp. 55–57), use
the coincidence of the local characters of the twists on the image of the norm.

Sources: Harish-Chandra, *Admissible invariant distributions on reductive p-adic groups*, notes
by DeBacker and Sally, University Lecture Series 16, AMS, 1999 (Library source
`harish-chandra-1999-admissible-invariant-distributions`): Theorem 16.3 (printed p. 75).
Henniart–Lemaire, *Changement de base et induction automorphe pour GL_n en caractéristique non
nulle*, Mémoires de la SMF 124, 2011: I.2.5 (printed pp. 17–18), II.1.3 (printed p. 57), II.6.7
(printed p. 123), II.6.13 (printed pp. 129–130). Arthur–Clozel, *Simple Algebras, Base Change,
and the Advanced Theory of the Trace Formula*, Annals of Mathematics Studies 120, Princeton
University Press, 1989 (Library source `arthur-clozel-1989-base-change`): Chapter 1, §6.3
(printed pp. 55–57).
