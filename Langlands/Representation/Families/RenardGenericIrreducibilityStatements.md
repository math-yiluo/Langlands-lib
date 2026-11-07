# Renard VI.8.4–VI.8.5: irreducibility of induced twists on Zariski open sets

Author: Worker 709. Module
`Langlands.Representation.Families.RenardGenericIrreducibilityStatements`,
namespace `Langlands.Renard.AlgebraicFamily`. It contains two **statements**,
the closed `Prop`-valued definitions `InducedIrreducibilityOpenStatement` and
`GenericInducedIrreducibilityStatement`, both with universe parameters `u, v`,
and their closed conjunction `GenericIrreducibilityStatements`. It proves
nothing.

## Original source

David Renard, *Représentations des groupes réductifs p-adiques*, French version
dated **9 July 2026**:

- VI.8.4, "Utilisation de la platitude": the Proposition, printed p. 192 /
  PDF p. 198, and its proof, printed pp. 192–193 / PDF pp. 198–199.
- VI.8.5, "Irréductibilité générique des induites": the Theorem, printed
  p. 193 / PDF p. 199, and the start of its proof, printed pp. 193–194 /
  PDF pp. 199–200.
- Unramified characters `X(G)` and the variety structure on `X(G)`: V.2.3 and
  V.2.4, printed pp. 105–106 / PDF pp. 111–112.
- Supercuspidal representations: VI.2.1, printed p. 137 / PDF p. 143.
- Irreducible representations: III.1.4, printed p. 60 / PDF p. 66.

Literature ID `renard-2026-representations-groupes-reductifs-padiques`, file
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The VI.8.4 Proposition reads: "Soit `P = MN` un sous-groupe parabolique de
`G`, et soit `(ρ, W)` une représentation irréductible de `M`. Pour tout `ψ`
dans `X(M)`, posons `π_ψ = i_P^G(ρ ⊗ ψ)`. Si `π_{ψ_0}` est irréductible pour
un certain `ψ_0` dans `X(M)`, alors `π_ψ` est irréductible pour tout `ψ` dans
un ouvert de Zariski de la variété algébrique `X(M)`."

The VI.8.5 Theorem reads: "Soit `P = MN` un sous-groupe parabolique de `G`,
et soit `(ρ, W)` une représentation supercuspidale irréductible de `M`. Pour
tout `ψ` dans `X(M)`, posons `π_ψ = i_P^G(ρ ⊗ ψ)`. Alors `π_ψ` est irréductible
pour tout `ψ` dans un ouvert de Zariski non vide de la variété algébrique
`X(M)`."

## Lean model

The binders are those of the published VII.1.3 statement
[MaximalLeviSupercuspidalReducibilityStatement](../Exponents/MaximalLeviSupercuspidalReducibilityStatement.md),
without its properness and maximality hypotheses:

- a field `k : Type u` with `[Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k] [T2Space k]`, so any nonarchimedean local
  field of any characteristic;
- a group scheme `G` over `Spec k` with `hG : IsConnectedReductive G`. The
  statement installs `hG.isAffineHom` and the canonical topology
  `RationalPointFamily.pointTopology` on `rationalPoints G`, and assumes
  `[LocallyCompactSpace (rationalPoints G)]` and
  `[NonarchimedeanGroup (rationalPoints G)]`;
- every actual rational parabolic `p : P ⟶ G` (`hp : IsParabolicSubgroup p`)
  with rational Levi `l : M ⟶ P` (`hl : IsRationalLeviSubgroup l`) and
  matching geometric unipotent radical `r : U ⟶ P` (`hr`, and
  `hmul : IsIso (subgroupMultiplication l r)`). `P = G` is allowed;
- on `rationalPoints M`, the canonical topology `leviPointTopology l hl` and
  the derived instances `leviPoints_locallyCompactSpace p l hp hl` and
  `leviPoints_nonarchimedeanGroup p l hp hl`;
- `ρ : SmoothRep.{0, u, v} ℂ (rationalPoints M)` with `ρ.IsIrreducible`.

The objects of the source are the following published declarations.

- `X(M)` is `Plancherel.unramifiedCharacters (fun χ : rationalCharacters M =>
  (Plancherel.rationalNormCharacters M χ).toMul)`: the continuous characters
  `rationalPoints M →ₜ* ℂˣ` trivial on the common kernel `⁰M` of the absolute
  values `|χ|_F` of all rational characters `χ` of `M`. The source defines
  `X(M)` as the group homomorphisms `M → ℂ×` trivial on `⁰M` (V.2.3). Since
  `⁰M` is open (V.2.3 Proposition), such a homomorphism is locally constant,
  hence continuous, so the two sets agree.
- `ρ ⊗ ψ` is `ρ.twist ψ.val.toMonoidHom (Plancherel.unramifiedCharacter_isOpen_ker _ ψ)`,
  the published twist `SmoothRep.twist`: the same space, with `m` acting by
  `ψ(m) • ρ(m)`.
- `i_P^G` is the published normalized induction
  `(leviInductionFunctor p l r hp hr hl hmul).obj`, with values in
  `SmoothRep.{0, u, max u v} ℂ (rationalPoints G)`.
- Irreducibility is `SmoothRep.IsIrreducible`, that is Mathlib's
  `Representation.IsIrreducible` of the underlying representation.
- A principal Zariski open subset of `X(M)` is
  `Plancherel.rationalUnramifiedPrincipalOpen M hl.isConnectedReductive f`
  for a polynomial `f : MvPolynomial (Fin (Plancherel.rationalImageRank M)) ℂ`.
  By `Plancherel.mem_rationalUnramifiedPrincipalOpen`, `ψ` lies in it exactly
  when `f` does not vanish at the coordinates
  `Plancherel.rationalCanonicalUnramifiedCharacterCoordinates M _ ψ`. These
  coordinates are a published isomorphism of topological groups from `X(M)`
  to `Fin n → ℂˣ`, where `n = rationalImageRank M`. The published definition
  elaborates `X(M)` with the topology `rationalPointTopology k M.X`, which is
  definitionally `leviPointTopology l hl`, so `ψ₀` and `ψ` range over the same
  type as in the twist.
- Supercuspidality is the published
  `Langlands.Aubert.General.RepresentedParabolic.IsSupercuspidal` for the
  group `M`: the published normalized Jacquet module of `ρ` is zero for every
  actual proper rational parabolic of `M` with a rational Levi and matching
  radical.

## Declarations

| Declaration | Source | Statement |
| --- | --- | --- |
| `InducedIrreducibilityOpenStatement` | VI.8.4 Proposition, PDF p. 198 | For irreducible `ρ` and `ψ₀ ∈ X(M)` with `i_P^G(ρ ⊗ ψ₀)` irreducible, there is a polynomial `f` with `ψ₀` in its principal open set such that `i_P^G(ρ ⊗ ψ)` is irreducible for every `ψ` in that set |
| `GenericInducedIrreducibilityStatement` | VI.8.5 Theorem, PDF p. 199 | For irreducible supercuspidal `ρ`, there is a nonzero polynomial `f` such that `i_P^G(ρ ⊗ ψ)` is irreducible for every `ψ` in its principal open set |
| `GenericIrreducibilityStatements` | — | The conjunction of the two, with universe parameters `u', v'` instantiating both |

## Correspondence notes

1. Zariski topology of `X(M)`. By V.2.4, the regular functions on `X(M)`
   form the group algebra `ℂ[Λ(M)]` of the lattice `Λ(M)`, the image of
   `H_M`. An element `λ ∈ Λ(M)` is the function `ψ ↦ ψ(m)` for any `m` with
   image `λ`. The published coordinates come from a `ℤ`-basis of the
   published valuation image (`rationalCanonicalUnramifiedCharacterCoordinates_symm_apply`):
   the coordinate `i` of `ψ` is `ψ(m_i)`, where `m_i` maps to the basis
   vector `i`. So these coordinates identify `ℂ[Λ(M)]` with the Laurent
   polynomials in `n` variables. A Laurent polynomial is a monomial times a
   polynomial, and monomials vanish nowhere on the torus. So the principal
   open sets of polynomials `f` are exactly the principal open sets of the
   regular functions on `X(M)`, and they form a base of its Zariski topology.
   A change of basis of the lattice acts by an automorphism of the torus given
   by monomials, so the base does not depend on that choice. These remarks
   are Worker 709's and are not checked in Lean.
2. VI.8.4. A Zariski open set contains `ψ₀` exactly when it contains a
   principal open set containing `ψ₀`. So the conclusion of
   `InducedIrreducibilityOpenStatement` is equivalent to: `π_ψ` is
   irreducible on some Zariski open set containing `ψ₀`. The printed
   Proposition says only "dans un ouvert de Zariski" and does not say that the
   open set contains `ψ₀`. Read literally it would hold with the empty set.
   The proof provides the stronger conclusion: `ψ₀` lies in a principal open
   `S_f` on which a localization is free, and the determinant "vaut 1 en
   `ψ₀`", so it is nonzero on a Zariski open subset of `S_f` containing
   `ψ₀`. The VI.8.5 proof uses the Proposition in this stronger form: "il
   suffit de montrer que `π_{ψ_0}` est irréductible pour un certain `ψ_0`"
   needs the open set to be nonempty. The statement therefore includes
   `ψ₀ ∈ D(f)`. This is a reading of the source by Worker 709.
3. VI.8.5. If `f ≠ 0`, its principal open set is dense in `X(M)`
   (published `Plancherel.dense_rationalUnramifiedPrincipalOpen`), so it is
   nonempty, because `X(M)` contains the trivial character. Conversely the
   principal open set of `0` is empty. Every nonempty Zariski open set
   contains a nonempty principal open set by note 1. So the conclusion of
   `GenericInducedIrreducibilityStatement` is equivalent to the Theorem's
   "dans un ouvert de Zariski non vide". The last equivalence relies on
   note 1 and is not checked in Lean.
4. Parabolics. The source's `P = MN` is any parabolic subgroup of `G`
   defined over `F`, with Levi `M`. The statement allows every actual
   rational parabolic with any rational Levi and matching radical, as in the
   VII.1.3 statement. The case `P = G` is included. There `i_P^G(ρ ⊗ ψ)` is
   isomorphic to `ρ ⊗ ψ`, which is irreducible for every `ψ`, so `f = 1`
   works; this is not checked in Lean.
5. Supercuspidality. Renard's definition (VI.2.1) is the vanishing of the
   Jacquet module `r_P V` for every proper parabolic of the group. The
   published `IsSupercuspidal` uses the normalized Jacquet module, whose
   normalization by a modulus character does not change vanishing. The same
   convention is used by the published VII.1.3 statement.
6. Irreducibility. By III.1.4 the source calls a smooth representation
   irreducible when it is a simple object of the category of smooth
   representations. `Representation.IsIrreducible` is `IsSimpleOrder` of the
   lattice of subrepresentations; the two agree because subrepresentations
   of smooth representations are smooth. No admissibility hypothesis is
   imposed on `ρ`. The source imposes none either; its proofs use the
   admissibility of irreducible smooth representations.

## Relation to published work

The VI.8 progress note
[algebraic-families-progress](../../../notes/renard/algebraic-families-progress.md)
lists the Proposition as (P4) and the Theorem as (T5), with no published
statement at Library `eec7519b`. Its rows name related published
declarations, none of which is either statement:
`Langlands.Plancherel.FiniteMatrixIrreducibilityOpennessStatement`
(proved), `Langlands.Plancherel.CompactFixedFamilyOpennessStatement`
(openness in a given topology, for (P4)), and
`Langlands.Plancherel.ConditionalParabolicGenericIrreducibilityStatement`
(adapted from Waldspurger, for square-integrable `π` and a locus open in the
topology of continuous characters, for (T5)). The VI.8.4 Theorem on local
freeness is `LocalFreeCoverStatement` in
[RenardFamilyStatements](RenardFamilyStatements.md); this module does not
import it.

## Remaining obligations

The proofs are separate obligations, which must prove these declarations
unchanged. The source proof of VI.8.4 uses the universal family
`ρ ⊗ χ_un` over `B = ℂ[Λ(M)]` (VI.8.1 Example), the commutation of
specialization and induction (VI.8.2 Corollary), the local freeness theorem
of VI.8.4, a compact open `K` such that every irreducible representation of
the inertial support of `ρ` has nonzero `K`-fixed vectors (proof of VI.7.2
and the Jacquet lemma VI.6.1), Theorem III.1.5, and Burnside's theorem. The
source proof of VI.8.5 reduces to a unitary `ρ` by a twist, then uses
unitarity of `π_ψ` for unitary `ψ`, the geometric lemma VI.5.3, a Lemma on
filtrations whose successive quotients have distinct central characters, and
Frobenius reciprocity, and finally applies VI.8.4. The progress note records
these steps as (T5-a), (T5-b), (L5) and (T5-c).

## Environment

Environment `3b864ddf-f0af-4c18-8903-c6f813a0ce0f`: Lean 4.34.0 at
`293d5d0c0c3f3dded4688b3ccd6a33939ac5102b`, Mathlib at
`5ed2965256430c3649e86755f9576b54eca72435`. The project imports are
`ArbitraryParabolicLeviPoints` (`leviInductionFunctor`, `leviPointTopology`),
`LeviSupercuspidalInductionSupport` (`IsSupercuspidal`),
`RationalUnramifiedCharacterDensity` (`rationalUnramifiedPrincipalOpen`),
`RationalCharacterValuation`, `UnramifiedCharacters`, `Category.Twist` and
`GroupScheme.Reductive.Basic`. No construction or axiom is introduced.
