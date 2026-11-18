# Twisted characters, σ-lifts and Shintani lifts for `GL_n` over a cyclic algebra

The module `Langlands.BaseChange.TwistedCharacter` (namespace `Langlands.BaseChange`)
provides the twisted character `Θ^A_Π(φ) = trace(Π(φ) ∘ A)` of an admissible representation
and its values at points. These generic items and their lemmas are declared in the module
`Langlands.BaseChange.TwistedCharacter.Basic`, which this module imports, so importing
`Langlands.BaseChange.TwistedCharacter` makes all of them available. For `GL_n` over a
commutative algebra `E` with an automorphism `σ`, this module itself defines the isomorphisms
of a representation `Π` of `GL_n(E)` onto `Π^σ`, σ-stability, the identity "à la Shintani"
between twisted and ordinary character values, and the σ-lift relation through concordant
test functions. It proves the lemmas listed below and the topological facts about `GL_n(E)`
that the statements in
`Langlands.BaseChange.TwistedCharacterRegularValuesStatement` and
`Langlands.BaseChange.SigmaLiftCharacterIdentityStatement` need. No analytic theorem about
characters is proved or assumed here.

## Sources

- Henniart–Lemaire, *Changement de base et induction automorphe pour GL_n en
  caractéristique non nulle*, Mém. SMF 124 (2011), source ID
  `provided-a0a5445aba86b871bcd83f08813de3234fddb463ff9bb3c9dfd60d2d2fcdae61`, file
  `/home/taskhub/pilot/literature/Henniart-Lemaire, Changement de base et induction automorphe pour GLn en caracteristique non nulle (2011).pdf`.
  PDF page = printed page + 8. Cited below as HL.
  - II.1.3, printed pp. 56–57: `Π^σ`, σ-stable representations, the isomorphism `A` of `Π`
    onto `Π^σ` and the distribution `Θ^A_Π(φ) = trace(Π(φ) ∘ A)`; the first form of the
    definition of σ-lift, by character values.
  - II.2.7, printed pp. 66–67: the same objects for admissible `Π`, with
    `Π(φ) = ∫ φ(g) Π(g) dg_E`, the distribution `Θ_π(f) = trace π(f)`, the versions with a
    central character, and the Définition of σ-relèvement through concordant functions.
  - II.2.8, printed pp. 67–69: reduction from a cyclic algebra to a field, the twisted
    character as a locally constant function on `G(E)_{σ-r}`.
  - II.2.9, printed pp. 69–70: the Proposition (identity "à la Shintani"), its Corollaire
    and the Remarques; Remarque (2) names the constant `c(π, A)`.
- Arthur–Clozel, *Simple Algebras, Base Change, and the Advanced Theory of the Trace
  Formula* (1989), source ID `arthur-clozel-1989-base-change`. PDF page = printed page + 14.
  Chapter 1, §2, printed pp. 10–11: the intertwining operator `I_σ` normalized by Whittaker
  models, the twisted character `Θ_{Π,σ}(φ) = trace(Π(φ) I_σ)` and Proposition 2.2.
  Chapter 1, Definition 6.1, printed p. 51: Shintani's definition of the base-change lift.

## Notation

`GL_n(R)` is the Library's `Langlands.GeneralLinear n R`. HL write `Π` for a representation
of `GL_n(E)`. `Π` is not a usable Lean identifier, so the Lean code calls it `τ`, on a space
`W`, and calls a representation of `GL_n(F)` `π`, on a space `V`. `Θ_π` is the Library's
`Character.distribution` (`Langlands/Representation/Character/Basic.lean`). `δ^σ` is
`entrywiseAut σ n δ`, `σ` applied to every entry (module
`Langlands.BaseChange.Norm`).

## Generic part (module `Langlands.BaseChange.TwistedCharacter.Basic`)

Items 1 and 2 and the lemmas of item 7 are declared in
`Langlands.BaseChange.TwistedCharacter.Basic`, which has its own Markdown with the proofs. They
are summarized here because `Langlands.BaseChange.TwistedCharacter` re-exports them through
its import. Here `G` is a group with `[TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
[LocallyCompactSpace G] [TotallyDisconnectedSpace G]`, `V` is a complex vector space,
`ρ : Representation ℂ G V` and `hρ : IsAdmissible ρ`. These are the hypotheses of
`Character.distribution` and `HasCharacterValue`.

1. `twistedDistribution μ ρ hρ A : Distribution G`, for a measure `μ` on `G` with
   `[MeasurableSpace G] [BorelSpace G] [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]`
   and an endomorphism `A : Module.End ℂ V`. It is the linear form
   `φ ↦ trace(ρ(φ) ∘ A)` on `SchwartzBruhat G`, the locally constant compactly supported
   functions. Here `ρ(φ)` is the Library's integrated action
   `Hecke.integratedAction μ ρ hρ.1 φ`, `∫ φ(g) ρ(g) dμ(g)`, which has finite rank because
   `ρ` is admissible (`Character.finiteRankIntegratedAction`). So `ρ(φ) ∘ A` has finite
   rank (its range lies in the range of `ρ(φ)`), and the trace is the Library's
   `FiniteRankEnd.trace`. This is HL's `Θ^A_Π(φ) = trace(Π(φ) ∘ A)` (II.2.7, printed p. 67;
   II.1.3, printed p. 56).
2. `HasTwistedCharacterValue ρ hρ A g c : Prop`, for `g : G` and `c : ℂ`. For every Haar
   measure `μ` on `G`, with the Borel σ-algebra introduced locally as in
   `HasCharacterValue`, the distribution `twistedDistribution μ ρ hρ A` has the local value
   `c` at `g` (`HasLocalValue`). That is, on some open neighbourhood `U` of `g`,
   `Θ^A(φ) = c ∫ φ dμ` for every test function `φ` supported in `U`. This is the
   statement that the twisted character is given near `g` by a locally constant function
   whose value at `g` is `c` (HL II.1.3, printed p. 57; II.2.8, printed p. 68).

Lemmas (item 7 of the task), all proved:

- `twistedDistribution_apply`: the unfolding of item 1 at `φ`, the finite-rank trace of
  `ρ(φ) ∘ A`.
- `twistedDistribution_one`: for `A = 1`, `twistedDistribution μ ρ hρ 1` is
  `Character.distribution μ ρ hρ`.
- `twistedDistribution_smul`: `twistedDistribution μ ρ hρ (a • A) =
  a • twistedDistribution μ ρ hρ A` for `a : ℂ`.
- `hasTwistedCharacterValue_one_iff`: `HasTwistedCharacterValue ρ hρ 1 g c ↔
  HasCharacterValue ρ hρ g c`.
- `HasTwistedCharacterValue.unique`: two twisted character values at the same point are
  equal (from `HasLocalValue.unique` for one Haar measure).
- `HasTwistedCharacterValue.smul`: a value `c` for `A` at `g` gives the value `a * c` for
  `a • A` at `g`.
- `hasTwistedCharacterValue_trace`: if `V` is finite-dimensional, then for every `g₀` the
  twisted character has the value `LinearMap.trace ℂ V (ρ g₀ ∘ₗ A)` at `g₀`. This is the
  twisted analogue of `hasCharacterValue_trace`. The proof takes the open set on which
  `ρ(g)` agrees with `ρ(g₀)` on a basis. On it the integrated action of a test function `f`
  supported there is `(∫ f dμ) • ρ(g₀)`.

## `GL_n` part

In items 3 and 4, `F` is a commutative ring, `E` a commutative `F`-algebra,
`σ : E ≃ₐ[F] E`, `n : ℕ` and `τ : Representation ℂ (GL_n(E)) W`. In items 5 and 6, `F` is
a field with `[TopologicalSpace F] [IsTopologicalRing F]`, `E` is a commutative `F`-algebra
with `[TopologicalSpace E] [IsTopologicalRing E]`, and `l n : ℕ`. Items 5 and 6 take as
instance arguments `T2Space`, `LocallyCompactSpace` and `TotallyDisconnectedSpace` for
`GL_n(F)` and for `GL_n(E)`, the hypotheses of `HasCharacterValue` and of item 2.
Lemma 9 below supplies them for nonarchimedean local fields.

3. `SigmaIntertwiner σ n τ`, a reducible abbreviation for Mathlib's
   `Representation.Equiv τ (τ.comp (entrywiseAut σ n).toMonoidHom)`. The type
   `Representation.Equiv ρ₁ ρ₂` (`Mathlib/RepresentationTheory/Intertwining.lean`)
   consists of linear equivalences `A : W ≃ₗ[ℂ] W` with `A ∘ ρ₁(g) = ρ₂(g) ∘ A` for every
   `g`. For `ρ₁ = τ` and `ρ₂ = τ ∘ θ` with `θ = entrywiseAut σ n`, this is
   `A ∘ τ(g) = τ(θ g) ∘ A = τ(g^σ) ∘ A`. It is HL's condition `A ∘ Π(g) = Π(g^σ) ∘ A` for an
   automorphism `A` of the space of `Π`, an isomorphism of `Π` onto `Π^σ` (II.1.3, printed
   p. 56; II.2.7, printed p. 67). The lemma `SigmaIntertwiner.comp_apply_eq` states this
   relation for the underlying linear map. The underlying linear map `A.toLinearMap` is
   the endomorphism given to item 1.
4. `IsSigmaStable σ n τ : Prop` is `Nonempty (SigmaIntertwiner σ n τ)`, that is, `τ` is
   isomorphic to `τ^σ` (HL II.1.3, printed p. 56; II.2.7, printed p. 66).
5. `IsShintaniLift σ l π hπ τ hτ A c : Prop`, for admissible `π` of `GL_n(F)` and `τ` of
   `GL_n(E)`, `A : SigmaIntertwiner σ n τ` and `c : ℂ`. It says that `c ≠ 0`, and that for
   all `δ : GL_n(E)` and `γ : GL_n(F)` with `IsNormAssociated σ l δ γ` and
   `IsRegularSemisimple γ` there is `a : ℂ` with `HasCharacterValue π hπ γ a` and
   `HasTwistedCharacterValue τ hτ A δ (c * a)`, where `A` enters through its underlying
   linear map. This is HL's identity "à la Shintani" `Θ^A_Π(δ) = c Θ_π(γ)` for associated
   pairs with regular `γ` (II.2.9, Proposition, printed p. 69; II.1.3, printed p. 57). The
   existence of the two character values at the points used is made explicit; see below.
6. `IsSigmaLift σ l π hπ τ hτ A c : Prop`. It says that `c ≠ 0`, and that for all Haar
   measures `μF` on `GL_n(F)` and `μE` on `GL_n(E)` (Borel σ-algebras introduced locally,
   as in item 2), and all `φ : SchwartzBruhat (GL_n(E))` and
   `f : SchwartzBruhat (GL_n(F))` with `AreConcordant σ l μF μE φ f`,
   `twistedDistribution μE τ hτ A φ = c * Character.distribution μF π hπ f`. Here
   `AreConcordant` is the concordance of test functions of module
   `Langlands.BaseChange.OrbitalIntegral` (HL I.2.5, Définition), applied to the
   underlying functions of `φ` and `f`. It says that the orbital integrals of `f`
   vanish at every regular semisimple `γ` that is not a norm, and that at every pair
   `(δ, γ)` with `IsNormAssociated σ l δ γ` and `γ` regular semisimple, the σ-orbital
   integral of `φ` at `δ` equals the orbital integral of `f` at `γ`, for associated Haar
   measures on the centralizers and quotient measures compatible with `μE` and `μF`.
   This is HL's Définition
   of σ-relèvement, `Θ^A_Π(φ) = c Θ_π(f)` for every concordant pair (II.2.7, printed
   p. 67), with the constant `c` as an explicit argument. HL's "Π is a σ-lift of π" is
   `∃ c, IsSigmaLift σ l π hπ τ hτ A c`.

In HL's Définition, `π` and `Π` are irreducible and `Π` is σ-stable. Items 5 and 6 are
defined for all admissible `π` and `τ`. σ-stability is implied by the existence of `A`, and
irreducibility is a hypothesis of the statement `SigmaLiftCharacterIdentityStatement`, not
part of the definitions. Association is `IsNormAssociated` of `Langlands.BaseChange.Norm`, HL's formulation in
I.1.2. Its agreement with HL's `N(O_σ(δ)) = O(γ)` (II.1.2, printed p. 56; I.2.2) is
explained in the Markdown of `Langlands.BaseChange.Norm`. Regularity of `γ` is the Library's
`IsRegularSemisimple`, a separable characteristic polynomial. HL's regular elements (II.1.2,
printed p. 56) only need a squarefree characteristic polynomial, and the two notions agree in
characteristic zero (`PerfectField.separable_iff_squarefree`). The statements that use
items 5 and 6 assume `CharZero F`.

8. `isShintaniLift_trivial` (proved). Take the trivial representations of `GL_n(F)` and
   `GL_n(E)` on `ℂ` (Mathlib's `Representation.trivial`). There is
   `A : SigmaIntertwiner σ n (Representation.trivial ℂ (GL_n(E)) ℂ)` whose underlying
   linear map is the identity, and `IsShintaniLift σ l _ hπ _ hτ A 1` holds for all
   admissibility proofs `hπ` and `hτ`. Both character values are `1`, by
   `hasCharacterValue_trace` and `hasTwistedCharacterValue_trace`. This shows that item 5
   is satisfiable.

## Topology of `GL_n(E)` (item 9)

Let `F` be a nonarchimedean local field, with the instance arguments the Library uses,
`[ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]`. Let `E` be a
commutative `F`-algebra with `[Module.Finite F E] [TopologicalSpace E] [IsModuleTopology F E]`.
Then, for every `n`:

- `generalLinear_t2Space_of_finite F E n : T2Space (GL_n(E))`;
- `generalLinear_locallyCompactSpace_of_finite F E n : LocallyCompactSpace (GL_n(E))`,
  which also assumes `[IsTopologicalRing E]`;
- `generalLinear_totallyDisconnectedSpace_of_finite F E n :
  TotallyDisconnectedSpace (GL_n(E))`.

The task lists `[IsTopologicalRing E]` among the hypotheses. The Hausdorff and totally
disconnected parts do not use it and omit it, so they are slightly more general. Callers pass
the same arguments either way. As in the Library's `Langlands/Group/GL/LocalFieldTopology.lean`,
these are theorems, not global instances. The statements use them with `haveI`. The proof
goes through the auxiliary homeomorphism `finiteCoordinateHomeomorph F E : E ≃ₜ (Fin d → F)`,
the coordinate map of `Module.finBasis F E`. It is continuous in both directions because
linear maps between module topologies are continuous. From it, the auxiliary theorems
`finiteAlgebra_t2Space`, `finiteAlgebra_locallyCompactSpace` and
`finiteAlgebra_totallyDisconnectedSpace` transfer the properties of `F`
(`LocalFieldTopology.t2Space`, `LocalFieldTopology.totallyDisconnectedSpace`, and local
compactness) to `E`. They then pass to matrices and to units as in
`LocalFieldTopology.generalLinear_*`.

## Remarks required by the task

**Dependence on `A`.** The twisted character depends on the chosen `A`. For irreducible
admissible `Π`, Schur's lemma makes `A` unique up to a nonzero scalar. Schur's lemma is not
proved here. Replacing `A` by `a • A` multiplies the twisted character by `a`
(`twistedDistribution_smul`) and its values by `a` (`HasTwistedCharacterValue.smul`), so the
constant `c` in items 5 and 6 becomes `a * c`. This is HL's remark that the constant depends on
`A` and is written `c(π, A)` (II.2.9, Remarque (2), printed p. 70; also II.1.3, printed
p. 57). Arthur–Clozel instead normalize the operator `I_σ` by Whittaker models (Chapter 1,
§2, printed pp. 10–11) and then require `c = 1` in Shintani's definition (Definition 6.1,
printed p. 51). That normalization is not formalized here. Items 5 and 6 keep `A` and `c` as
arguments.

**Haar measures.** HL fix Haar measures `dg` on `G(F)` and `dg_E` on `G(E)`, while item 6
quantifies over all of them. The two readings agree, by the following paper argument, which
is not formalized. Every Haar measure is a positive multiple of a fixed one. Scaling `μE` by
`t > 0` scales the twisted character by `t`, and it scales the σ-orbital integrals of `φ` by
`t`, through the quotient measures `dg_E / dg^σ_δ`. Scaling `μF` by `s > 0` scales both
`Θ_π(f)` and the orbital integrals of `f` by `s`. Hence `(φ, f)` is concordant for
`(μF, t μE)` exactly when `(φ, f / t)` is concordant for `(μF, μE)`, and the identity
`Θ^A(φ) = c Θ_π(f)` transforms consistently. Similarly `(φ, f)` is concordant for
`(s μF, μE)` exactly when `(φ, s f)` is concordant for `(μF, μE)`. So the identity holds with
a given `c` for one pair of Haar measures if and only if it holds with the same `c` for all
pairs. The values in items 2 and 5 do not depend on the Haar measure either (HL II.1.3,
printed p. 57: "la fonction Θ^A_Π sur G(E)_{σ-r} n'en dépend pas"). Item 2 quantifies over
all Haar measures, as `HasCharacterValue` does.

**Character functions.** HL's Proposition (II.2.9) compares the character functions
`Θ^A_Π(δ)` and `Θ_π(γ)`. These exist on `G(E)_{σ-r}` and `G(F)_r` by the results recalled in
II.2.8 (HL's reference [60] and I.5.1 for twisted characters, [59] for ordinary ones). Item 5
does not presuppose them. Instead it asserts the existence of the two values at the points
it uses. The statement `TwistedCharacterRegularValuesStatement`, together with the Library's
`HasRegularSemisimpleCharacterValues` (`Langlands/JacquetLanglands/CharacterStatements.lean`),
provides these values for irreducible admissible representations. Neither is proved here.

**Central characters.** HL also use versions with a fixed central character, the spaces
`C^∞_c(G(E), χ)` and `C^∞_c(G(F), ω)` and the linear forms `Θ^A_Π` and `Θ_π` on them (II.2.6
and II.2.7, printed pp. 66–67). They are not part of this module.

## Provenance of auxiliary declarations

`SigmaIntertwiner.comp_apply_eq`, `finiteCoordinateHomeomorph` and the three
`finiteAlgebra_*` theorems are internal helpers for the items above. They are not
mathematical content taken from the sources. Every Haar measure is an explicit or
universally quantified argument. None is chosen or normalized inside a definition.
