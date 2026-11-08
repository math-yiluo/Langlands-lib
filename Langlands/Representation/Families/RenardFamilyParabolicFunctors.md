# Renard VI.8.2–VI.8.3: base change, parabolic induction and Jacquet modules of families

This module contains **definitions**, in namespace `Langlands.Renard.AlgebraicFamily`,
together with their defining laws and one comparison lemma between two normalizations.
It states and proves no theorem of Renard: no flatness, admissibility, finiteness or
base-change isomorphism is asserted here.

## Original source

David Renard, *Représentations des groupes réductifs p-adiques*, French version
dated **9 July 2026**:

- VI.8.2, "`(G, B)`-modules et induction": the opening paragraph, printed p. 189 /
  PDF p. 195, and the base-change paragraph before the Proposition, printed p. 190 /
  PDF p. 196.
- VI.8.3, "`(G, B)`-modules et restriction": the opening paragraph, printed p. 191 /
  PDF p. 197.
- `(G, B)`-modules: VI.8.1, printed pp. 187–189 / PDF pp. 193–195.
- The normalization of `i_P^G` and `r_P^G`: VI.1.2, formulas (VI.1.2.1) and (VI.1.2.2),
  printed p. 135 / PDF p. 141, and on printed p. 136 / PDF p. 142 the Remarque on the
  convention for `δ_P`, the Remarques after the Corollaire and formula (VI.1.2.3).
- The modular functions: V.5.4, Lemme, printed pp. 126–127 / PDF pp. 132–133; and
  V.5.2 Théorème (iii), printed p. 123 / PDF p. 129, which gives that the unipotent
  radical of a parabolic subgroup is the union of its compact open subgroups.

Literature ID `renard-2026-representations-groupes-reductifs-padiques`, file
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 709 checked this hash and read PDF pages 129, 132–133, 141–142 and 193–197.

The source passages are:

- Induction (PDF p. 195): for a parabolic `P = MN` and an `(M, B)`-module `(σ, E)`,
  "`i_P^G(E)` est muni d'une structure de `B`-module (on fait agir `B` sur l'espace
  d'arrivée `E` des fonctions dans `i_P^G(E)`). Il est évident que l'action du groupe,
  par translation à droite des fonctions, commute à cette action de `B`."
- Base change (PDF p. 196): for "une autre `ℂ`-algèbre commutative noethérienne
  réduite" `C` which is a `B`-module, the left adjoint of the forgetful functor is
  "`M(B) → M(C)`, `W ↦ C ⊗_B W`, que l'on appelle dans ce cadre foncteur de
  changement de base de `B` à `C`", which gives "un foncteur de changement de base
  `M(G, B) → M(G, C)`, `V ↦ V ⊗_B C`".
- Jacquet module (PDF p. 197): for a `(G, B)`-module `(π, V)`, "`r_P^G(π, V)` est muni
  d'une structure de `B`-module. Il est évident que l'action de `M` sur `r_P^G(V)`
  commute à cette action de `B`", with `r_P^G(V) = V_N = V/V(N)` as a vector space.
- Normalization (PDF p. 141): `i_P^G(τ, E) = Ind_P^G(τ ⊗ δ_P^{-1/2}, E)` (VI.1.2.1) and
  `r_P^G(π, V) = (π_N ⊗ δ_P^{1/2}, V_N)` (VI.1.2.2). By the Remarques on PDF p. 142,
  `δ_P` is trivial on `N`, since `N` is the union of its compact open subgroups, so
  the space of `i_P^G(τ, E)` is the set of `f : G → E` with
  `f(m n g) = δ_P^{-1/2}(m) τ(m) · f(g)` for `m ∈ M`, `n ∈ N`, `g ∈ G` (VI.1.2.3).

So `i_P^G` and `r_P^G` of a family are Renard's normalized induction and Jacquet
module, with `B` acting through the values of functions and on the coinvariants. The
source then proves that they preserve flatness and gives the base-change isomorphism
(VI.8.2 Proposition) and the finiteness result (VI.8.3 Proposition); those are not
part of this module.

## Renard's convention for `δ_P`

The Remarque on printed p. 136 / PDF p. 142 says that Renard's `δ_P` is the inverse
of the usual one, because of his choice of modular function in II.3.7, and that the
computations of Lemma V.5.4 show the same inversion. The half-modulus characters used
here are the published `HaarModulus.closedHalfCharacter` and
`closedInverseHalfCharacter`: the positive square root `c_U^{1/2}`, and its inverse,
of the modulus `c_U` of conjugation `u ↦ m u m⁻¹` on the closed subgroup `U`, in the
scaling convention of the published `HaarModulus` documentation. On Renard's actual
parabolic `P = MN`, the Levi restriction of `c_U` (with `U = N`) is Renard's
`δ_P^{-1}`, so:

- the induction factor `c_U^{1/2}` on `M` is Renard's `δ_P^{-1/2}` in (VI.1.2.1) and
  (VI.1.2.3);
- the Jacquet factor `c_U^{-1/2}` on `M` is Renard's `δ_P^{1/2}` in (VI.1.2.2).

This is the identification already used for the Jacquet functor in the "Source
identification" section of the published `Aubert/General/Parabolic` documentation.
Below, `c_U` always denotes the Library modulus and `δ_P` always denotes Renard's.

## Lean model

A family over `B` is a `B`-linear representation `ρ : Representation B H V`, as in the
published `RenardFamilyStatements`: the `B`-module structure of `V` commutes with the
group action because each `ρ h` is `B`-linear. The definitions below impose none of
Renard's standing hypotheses (Noetherian, finite type, reduced, flat, smooth); later
statements impose them where the source does.

### Base change

For `[CommRing B] [CommRing C] [Algebra B C]` and a family `ρ` of a group `H` over `B`,
`baseChange C ρ : Representation C H (C ⊗[B] V)` is
`(Module.End.baseChangeHom B C V).toMonoidHom.comp ρ`, so `h` acts by `1 ⊗ ρ(h)`
(`baseChange_tmul`). This is the action Renard's base-change functor puts on the
tensor product. Lean writes the scalars on the left, `C ⊗[B] V`, as Mathlib's base
change does; Renard writes `V ⊗_B C` in the functor and `C ⊗_B W` in the module
adjunction, and the two orders are identified by the symmetry of the tensor product
over the commutative ring `B`. Renard's "`C` soit un `B`-module" is read as a
`B`-algebra structure `[Algebra B C]`, which `C ⊗_B W` needs to be a `C`-module; this
reading is Worker 709's. `C` need not be a `ℂ`-algebra, Noetherian or reduced for the
definition. Specialization at a point `χ : B →ₐ[ℂ] ℂ` in the
published `SpecializationAdmissibilityStatement` is the same construction with
`C = ℂ`.

### Constant characters

For `[CommRing B] [Algebra ℂ B]`, `constantCharacter B ψ` maps a complex character
`ψ : H →* ℂˣ` into `Bˣ` through `Units.map (algebraMap ℂ B)`
(`constantCharacter_val`). Its kernel contains `ker ψ`
(`ker_le_constantCharacter_ker`), so if `ker ψ` is open,
`constantSmoothCharacter B ψ hψ` is a published `Induction.SmoothCharacter B H`, by
`Subgroup.isOpen_mono`. Equality of kernels is not needed and fails for the zero ring.

### Induction and Jacquet module for a semidirect decomposition

Let `G` be a locally compact nonarchimedean group and `P, M, U` subgroups with
`h : Aubert.General.IsSemidirectDecomposition P M U` and `U` closed.

- `inductionCharacter B U M hU hMU` is the constant image on the Levi `M` of the
  published `HaarModulus.closedHalfCharacter U hU M hMU`, that is `c_U^{1/2}` with
  values `c_U(m)^{1/2} · 1_B`, Renard's `δ_P^{-1/2}`. `jacquetCharacter B U M hU hMU`
  is the constant image of `HaarModulus.closedInverseHalfCharacter U hU M hMU`, that
  is `c_U^{-1/2}`, Renard's `δ_P^{1/2}`.
- `inducingRepresentation h hU σ` twists a family `σ` of `M` by `inductionCharacter`
  and then inflates it along the actual projection `h.projection : P →* M`, so `U`
  acts trivially.
- `Induced h hU σ` is the published `Induction.SmoothFunctions P` of that
  representation: functions `f : G → V` with
  `f(p g) = c_U(m(p))^{1/2} σ(m(p)) f(g)`, where `m(p) = h.projection p`
  (`induced_covariant`), that are right invariant under an open subgroup. `B` acts on
  the values of the functions. For `m ∈ M` and `n ∈ U` this reads
  `f(m n g) = c_U(m)^{1/2} σ(m) f(g)` (`induced_covariant_levi_unipotent`), which is
  Renard's (VI.1.2.3) after the conversion `c_U^{1/2} = δ_P^{-1/2}` on `M`.
- `inducedRepresentation h hU σ` is the published `Induction.smoothInduced`, right
  translation (`induced_action`); it is smooth (`isSmooth_inducedRepresentation`).
- `Jacquet ρ U` is the published `Jacquet.Localization.Coinvariants ρ U 1`, the
  quotient of `V` by the `B`-span of the `ρ(u) v - v`, which is Renard's
  `V/V(N)`.
- `jacquetRepresentation ρ U M hU hMU` is the descended action of `M`, from the
  published `Jacquet.Localization.action`, twisted by `jacquetCharacter`:
  `m · [v] = c_U(m)^{-1/2} [ρ(m) v]` (`jacquet_action_mk`), which is Renard's
  (VI.1.2.2). It is smooth when `ρ` is (`isSmooth_jacquetRepresentation`).

Renard defines `i_P^G` by (VI.1.2.1), with the character `δ_P^{-1/2}` of the whole
`P`, and derives the covariance (VI.1.2.3) from the triviality of `δ_P` on `N`. The
Lean definition takes the covariance (VI.1.2.3) itself: the Levi character inflated
along the projection. For an arbitrary semidirect decomposition this needs no
hypothesis on `U`, and the inducing representation is trivial on `U` by construction.

### Comparison with the half modulus on the whole `P`

The published complex `Aubert.General.normalizedInductionFunctor` and the published
`Plancherel.UnramifiedNormalizedModels` (one particular algebra of unramified regular
functions) instead twist `σ ∘ h.projection` by the half modulus
`closedHalfCharacter U hU P h.le_normalizer` on the whole `P`. At `u ∈ U` that
character is the half modulus of an inner automorphism of `U`, which need not be `1`
for an arbitrary closed `U`; then the two inducing representations differ.

`inducingRepresentation_eq_twist_of_isUnimodularModulus` proves that under the
published hypothesis `Aubert.General.IsUnimodularModulus U hU` (every inner
automorphism of `U` has modulus `1`) the inducing representation equals
`Langlands.twist (constantCharacter B (closedHalfCharacter U hU P h.le_normalizer))
(σ.comp h.projection)`. Its proof rewrites by the published
`Aubert.General.closedHalfCharacter_eq_comp_projection`. The published
`isUnimodularModulus_of_isLimitOfCompactSubgroups` derives that hypothesis from
`Jacquet.Localization.IsLimitOfCompactSubgroups U`; this is the argument of Renard's
Remarques on PDF p. 142.

So the present `Induced` and `inducedRepresentation` have the same underlying
functions and action as the full-`P` construction whenever the two inducing
representations agree, in particular when `U` is unimodular in this sense. For `B = ℂ`,
the further identification of `constantCharacter ℂ ψ` with `ψ` is not stated in Lean,
and neither is any identification of these objects with the published complex functors.

### Represented parabolics

For a represented parabolic `p : P ⟶ G` with rational Levi `l : M ⟶ P`, geometric
unipotent radical `r : U ⟶ P` and `IsIso (subgroupMultiplication l r)`, in the
binders of the published `RepresentedParabolic.leviInductionFunctor`:

- `leviImageRepresentation p l hp hl σ` reads a family `σ` of `M(F)` on the literal
  Levi image `pointImage (l ≫ p)` in `G(F)` through the inverse of the published
  `leviPointsEquiv`.
- `LeviInduced` and `leviInducedRepresentation` are `Induced` and
  `inducedRepresentation` for the published decomposition
  `isSemidirectDecomposition_pointImage` and closedness
  `isClosed_pointImage_comp` of the unipotent image. With the Levi-inflated character,
  this is the covariance (VI.1.2.3) of Renard's `i_P^G(σ)` for a family `σ` of `M(F)`,
  under the convention identification above.
- `leviJacquetRepresentation p l r hp hr hl hmul ρ` is `jacquetRepresentation` for the
  unipotent and Levi images, read on `M(F)` through `leviPointsEquiv`. This is
  Renard's `r_P^G(ρ)` of a family `ρ` of `G(F)`.

The transports are the ones the published `leviInductionFunctor` and
`leviJacquetFunctor` use for complex representations: pull back along the inverse of
`leviPointsEquiv` before inducing, and along `leviPointsEquiv` after taking the
Jacquet module.

The published complex `RepresentedParabolic.inductionFunctor` uses the full-`P` half
modulus instead. The hypothesis of the comparison lemma above, `IsUnimodularModulus`
of the radical image `pointImage (r ≫ p)`, is a published theorem over a
nonarchimedean local field: `RepresentedParabolic.isUnimodularModulus_pointImage_radical`
(module `Langlands.Representation.Exponents.LeviRadicalCompactSubgroups`), for a closed
subgroup `p` and an `IsUnipotentRadical r`, such as `hr.1` here. It applies the
published `isUnimodularModulus_of_isLimitOfCompactSubgroups` to the published
`isLimitOfCompactSubgroups_pointImage_radical`, which says that every compact subset
of the radical image lies in a compact subgroup (compare Renard V.5.2 (iii), PDF
p. 129). That theorem assumes `[ValuativeRel k] [IsNonarchimedeanLocalField k]` in
addition to the `[T2Space k]`, `[LocallyCompactSpace (rationalPoints G)]` and
`[NonarchimedeanGroup (rationalPoints G)]` of this section, whereas the definitions
here allow any topological field `k`. This module does not import it, and no Library
theorem applies it, together with `inducingRepresentation_eq_twist_of_isUnimodularModulus`,
to the decomposition and closedness used by `LeviInduced`. Nor does the Library
identify `leviInducedRepresentation` at `B = ℂ` with the published complex induction
on represented parabolics, and this module does not claim it. The Jacquet side needs
no such comparison: both use `c_U^{-1/2}` on the Levi.

## Scope

Only objects are defined. Renard's functors `i_P^G : M(M, B) → M(G, B)`,
`r_P^G : M(G, B) → M(M, B)` and `M(G, B) → M(G, C)` are not bundled, and their action
on morphisms is not defined. That the constructions send `B`-flat modules to flat
modules, the base-change isomorphism (VI.8.2.2) and the finiteness of Jacquet modules
are not asserted. The identification of the Library modulus with Renard's `δ_P^{-1}`
is the documented convention conversion above, not a Lean statement.
