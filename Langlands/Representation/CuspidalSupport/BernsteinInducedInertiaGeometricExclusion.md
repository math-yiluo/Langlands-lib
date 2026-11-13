# The geometric step of the Bernstein decomposition (Renard VI.7.2)

Author: Worker 53, Task 5313 (`03088b22-a403-46ae-a6ed-6dea22f5472a`), as a
collaborator of Worker 5313. The two workers agreed on the split of the proof.

This module proves a derived intermediate step of the proof of Renard VI.7.2
(David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`; VI.7.2 and its
proof on printed pp.181–184 / PDF pp.187–190, the step used here on printed
p.183 / PDF p.189). In that step Renard shows that `i_P^G(W_D)` splits along `Ω(G)`.
If `(σ, E)` is a composition factor of `i_P^G(W_D)`, then `r_P^G(σ, E)` is a
subquotient of `r_P^G i_P^G(W_D)`. By VI.5.3 (iii) and (V.4.3.3), this module
has a filtration whose successive quotients are conjugates `w(W_D)`, so
every irreducible subquotient lies in the inertia class of a conjugate of
`D`. The Lean result below is the Jacquet-module form of this step that the
Library's conditional assembly of the Bernstein decomposition uses
(`BernsteinJacquetExclusion`, see `BernsteinJacquetInertiaExclusion.lean`).
For a standard Levi `L` that is not conjugate to `M`, it also needs VI.5.3 (ii)
(printed p.173 / PDF p.179). In the Library that result is derived from the
geometric lemma and Lemma VI.5.2 (printed pp.172–173 / PDF pp.178–179).
VI.5.2 is not proved here: it is a hypothesis `hind`.

## Main declarations

Throughout, `i : T ⟶ G` and `ν` fix the standard parabolic data of a connected
reductive group `G` over a nonarchimedean local field `F`, and `family` is a
`BernsteinStandardFamily i ν`. The standard Levi scheme for a set `I` of simple
roots is `bernsteinLeviScheme i ν I`. Its rational points carry the rational
point topology. Representations have carriers in `Type (max uF uV)`, as do
the Bernstein data.

- `bernsteinJacquetExclusion_of_inertiaBlock_supercuspidal (hind) (a) (τ) (hτ)
  (hcusp)`. Fix:
  - `hind : RepresentedParabolic.LeviInductionNoSupercuspidalSubquotientStatement.{uF, max uF uV}`,
    the represented form of Renard VI.5.2;
  - a Bernstein cuspidal datum `a`;
  - a smooth representation `τ` of the rational points of the standard Levi of
    `a` such that:
    - `hτ : rationalInertiaBlockProperty (bernsteinLeviScheme i ν a.roots) a.representation τ`,
      meaning every irreducible subquotient of `τ` is inertia-related to
      `a.representation`;
    - `hcusp : RepresentedParabolic.IsSupercuspidal τ`, meaning the normalized
      Jacquet module of `τ` along every proper actual represented parabolic of
      the Levi vanishes.

  Then `BernsteinJacquetExclusion i ν family a V` holds for the normalized
  parabolic induction
  `V = (normalizedInductionFunctor (family.decomposition a.roots) (family.closedUnipotent a.roots)).obj (bernsteinLiteralLeviRep i ν a.roots τ)`.
  So for every Bernstein cuspidal datum `b` that is not inertia-related to `a`
  (`¬ IsBernsteinInertiaRelated i ν family a b`), the literal representation
  of `b` is not a subquotient of the normalized Jacquet module of `V` along
  the standard parabolic of `b`.
- `bernsteinJacquetExclusionOfInertiaBlockSupercuspidal (hind)`. This is the
  same result, with type the implication
  `∀ a τ, rationalInertiaBlockProperty … a.representation τ → RepresentedParabolic.IsSupercuspidal τ → BernsteinJacquetExclusion i ν family a (…)`.
  This type is exactly the hypothesis `hsc` of Worker 5313's
  `bernsteinInducedInertiaJacquetExclusion_of_supercuspidal` (in the module
  `BernsteinDecompositionInputsAssembly`). It is a `def` with a
  proposition-valued type, so it can be named as the entry declaration of a
  definition record. It is not a new mathematical definition.

## Supporting declarations

- `RepresentedParabolic.leviJacquetInduction_conjugateConstituent`. This is
  Renard VI.5.3 (iii) in constituent form, for actual rational parabolics
  `P = MN` and `Q = LU` of `G` and a hypothesis that `M` and `L` are
  conjugate (some `g ∈ G(F)` and an isomorphism `φ : M ≅ L` with
  `φ ≫ (L → Q → G) = (M → P → G) ≫ Int(g)`). Let `ρ` be a supercuspidal smooth
  representation of `M(F)`, in the sense of vanishing of all proper
  represented Jacquet modules. Let `σ` be an irreducible subquotient of
  `r_Q i_P ρ`, with the represented Levi Jacquet and induction functors. Then
  there are:
  - `z ∈ G(F)`;
  - an isomorphism `φ : L ≅ M` with `φ ≫ (M → P → G) = (L → Q → G) ≫ Int(z)`;
  - a topological group isomorphism `e : L(F) ≃ M(F)` that agrees pointwise
    with the point map of `φ`,

  such that `σ` is a subquotient of the pullback of `ρ` along `e`.

  Proof: the published filtration `leviJacquetInductionSupercuspidalFiltration`
  (VI.5.3 (iii)) gives a finite filtration of `r_Q i_P ρ` whose graded pieces
  are isomorphic to such pullbacks. Then
  `ObjectRepFiltration.exists_smoothGradedObject_subquotient` puts the
  irreducible subquotient `σ` into one graded piece.
- `pullbackNormalizedJacquetIsoOfEq`. Equal unipotent radicals and Levi
  subgroups, with Levi parametrizations that agree pointwise, give
  isomorphic transported normalized Jacquet modules. The proof uses `subst`.
- `isRationalInertiaRelated_rationalIsoPullback_of_pointwise`. If a point
  homeomorphism `e` agrees pointwise with the point map of an algebraic
  isomorphism `φ : K ≅ H`, then inertia-relatedness of `A` with
  `pullback e.symm B` gives inertia-relatedness of `A` with
  `rationalIsoPullback φ.symm B`. The two pullbacks are isomorphic, by
  `equivOfRepresentationEq`.
- `bernsteinStandardRepresentedJacquetFunctor` is the represented normalized
  Jacquet functor (`RepresentedParabolic.leviJacquetFunctor`) of the actual
  standard parabolic of a root set `I`.
  `bernsteinStandardRepresentedJacquetIso` identifies it, object by object,
  with the literal standard Jacquet module `bernsteinSchemeJacquet`. The
  identification uses `pullbackNormalizedJacquetIsoOfEq` together with the
  published equalities `standardCompression_unipotentPoints` and
  `standardCompression_leviPoints`.
- Private lemmas:
  - `bernsteinConjugateConstituent` specializes the constituent form of
    VI.5.3 (iii) to two standard Levis of the family.
  - `bernsteinNonConjugateExclusion` specializes VI.5.3 (ii). It obtains
    that result as
    `RepresentedParabolic.leviJacquetInductionNoSupercuspidal_of_geometricLemma representedGeometricLemma hind`.
  - `bernsteinInertiaRelated_of_conjugateConstituent` turns a conjugating
    isomorphism `φ : M_b ≅ M_a` (compatible with the two standard Levi
    embeddings through `Int(z)`), together with inertia-relatedness of
    `a.representation` with the transport of `b.representation`, into
    `IsBernsteinInertiaRelated i ν family a b`. It builds the
    `RationalLeviConjugacy` from `z` and `φ` and uses its `symm`.

## Proof of the main theorem

Let `b` be a datum that is not inertia-related to `a`. Assume that the literal
representation of `b` is a subquotient of the literal standard Jacquet module
of `V`.

1. `isSubquotient_bernsteinSchemeJacquet_iff`,
   `bernsteinStandardRepresentedJacquetIso` and
   `bernsteinStandardRepresentedInductionIso` move this to the represented
   functors. Then `b.representation` is a subquotient of `r_{P_b} i_{P_a} τ`,
   with the represented functors on the actual standard parabolics.
2. If the standard Levis `M_a` and `M_b` are conjugate in `G` (case split on
   the existence of `g` and `φ`), then `bernsteinConjugateConstituent` gives
   `z`, `φ : M_b ≅ M_a` and `e`, with `b.representation` a subquotient of
   `pullback e τ`. Pulling back along `e.symm`
   (`SmoothRep.subquotient_pullback_right_iff`) makes `pullback e.symm
   b.representation` an irreducible subquotient of `τ`. Irreducibility comes
   from `SmoothRep.isIrreducible_pullbackFunctor_obj_iff`. By `hτ`, it is
   inertia-related to `a.representation`.
   `bernsteinInertiaRelated_of_conjugateConstituent` then gives
   `IsBernsteinInertiaRelated i ν family a b`, which contradicts the choice
   of `b`.
3. Otherwise, `bernsteinNonConjugateExclusion` with `hind` says that no
   irreducible subquotient of `r_{P_b} i_{P_a} τ` is supercuspidal. But
   `b.representation` is irreducible and supercuspidal
   (`BernsteinCuspidalDatum.isSupercuspidal`), which is a contradiction.

The only hypothesis beyond the standing setup is `hind` (VI.5.2); the
supercuspidality of `τ` is the hypothesis `hcusp`. No admissibility,
finite-length or finite-generation hypothesis is used.
