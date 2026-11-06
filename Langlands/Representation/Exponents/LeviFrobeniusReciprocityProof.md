# Proof of Frobenius reciprocity for normalized parabolic induction

Author: Worker 16, task `27fe1be6-a9cb-4bc5-8f71-3af15cd3d92b`. Module
`Langlands.Representation.Exponents.LeviFrobeniusReciprocityProof`, namespace
`Langlands.Aubert.General.RepresentedParabolic`.

The theorem `leviFrobeniusReciprocity` proves the published statement
`LeviFrobeniusReciprocityStatement.{u, v, w}` (module
`Langlands.Representation.Exponents.LeviFrobeniusReciprocityStatement`). This is the
adjunction part of the Proposition of Renard 2026, VI.1.2: normalized parabolic induction
`i_P^G` is right adjoint to normalized parabolic restriction `r_P^G`, in the explicit form of
an evaluation-at-identity bijection of intertwiner spaces. The universes `u`, `v`, `w` of the
field and of the two carriers stay independent. No hypothesis beyond the statement's is
used. In particular the unimodularity of the radical is proved, not assumed.

## Helper modules

The proof uses three helper modules, submitted with it:

- `Langlands.Algebra.GradedHopf.TrivialGrading`: ungraded unitriangular matrix coefficients
  of a unipotent Hopf algebra of finite type over a field.
- `Langlands.GroupScheme.Rational.UnipotentCompactSubgroups`: every compact set of rational
  points of a closed unipotent subgroup over a nonarchimedean local field lies in a compact
  subgroup.
- `Langlands.Representation.Exponents.LeviRadicalCompactSubgroups`: the same property and
  unimodularity for the radical image `pointImage (r ≫ p)` of every actual parabolic.

Each has its own Markdown note.

## The transport lemma

`intertwiningPullbackEquiv` takes topological groups `H` and `N`, an isomorphism
`e : H ≃ₜ* N` of topological groups, and representations `ρ` of `N` on `V` and `σ` of `H`
on `W`. It is a `ℂ`-linear equivalence between the intertwiners from `ρ` to
`σ ∘ e.symm` and the intertwiners from `ρ ∘ e` to `σ`. Both directions keep the
underlying linear map. The intertwining identities correspond under `h = e.symm n`,
using `e.symm_apply_apply` and `e.apply_symm_apply`. The two inverse laws hold by `rfl`.

## The proof

After introducing the field, `G` and `hG`, the proof installs the same instances as the
statement: `hG.isAffineHom` and the topology `RationalPointFamily.pointTopology` on
`rationalPoints G`. It then introduces the two instance hypotheses on `G(F)` and the
parabolic data `p`, `l`, `r`, `hp`, `hl`, `hr`, `hmul`. It installs, as the statement does,
`hl.isConnectedReductive.isAffineHom`, the topology `leviPointTopology l hl` on
`rationalPoints M`, and the instances `leviPoints_locallyCompactSpace p l hp hl` and
`leviPoints_nonarchimedeanGroup p l hp hl`. Finally it introduces `π` and `σ`.

1. Unimodularity: `isUnimodularModulus_pointImage_radical p r hp.isClosedSubgroup hr.1`
   gives `hδ : IsUnimodularModulus (pointImage (r ≫ p)) _`. Here `hr.1` is the
   `IsUnipotentRadical` part of `LeviSubgroup.IsGeometricUnipotentRadical`.
2. Adjunction for the image subgroups: the published
   `Langlands.Aubert.General.FirstAdjointness.equiv` takes the decomposition
   `isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul` of
   `pointImage p` and the closedness proof
   `isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup` of the radical
   image. With `hδ`, `π` and the pulled-back representation
   `SmoothRep.pullback (leviPointsEquiv p l hp hl).symm σ` of the Levi image, it gives
   `Hom_G(π, i σ') ≃ₗ[ℂ] Hom(j π, σ')`. Here `σ'` is that pull-back, `i` is the normalized
   induction functor and `j` is the normalized Jacquet functor of the image decomposition.
3. Transport to `M(F)`: by definition, `leviInductionFunctor … σ` is `i σ'`, and
   `leviJacquetFunctor … π` is `j π` pulled back along `leviPointsEquiv p l hp hl`. So
   `intertwiningPullbackEquiv (leviPointsEquiv p l hp hl) _ σ.representation` identifies
   `Hom(j π, σ')` with `Hom_M(r_P^G π, σ)`. Here `σ'` is `σ ∘ e.symm` for
   `e = leviPointsEquiv p l hp hl`. The composite equivalence is the required `e`.
4. The evaluation formula: both steps keep the underlying linear maps, and
   `FirstAdjointness.equiv` sends `F` to the map whose value on the class
   `Jacquet.Localization.mk π.representation (pointImage (r ≫ p)) 1 x` is
   `Induction.eval (pointImage p) (inducingRepresentation …) (F x) 1`. The published
   `FirstAdjointness.equiv_mk` records this by `rfl`. So the formula clause is proved by
   `rfl`.

The proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.
