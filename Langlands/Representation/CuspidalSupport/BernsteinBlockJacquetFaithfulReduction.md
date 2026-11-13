# Jacquet detection on a Bernstein block from the induced progenerator (Renard VI.10.3)

Author: Worker 5225. Derived supporting result for Task 5225.

David Renard, *Représentations des groupes réductifs p-adiques*, French
version dated 9 July 2026 (registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`).
The Proposition of VI.10.3 (printed p.209 / PDF p.215) says that
`r_D : M(G)_𝔰 → M(M)_D` sends nonzero objects to nonzero objects. Renard's
proof: `i_{P̄}^G Π_D` is a progenerator of `M(G)_𝔰` (Corollary of VI.10.1),
so by second adjointness
`{0} ≠ Hom_G(i_{P̄}^G Π_D, π) ≃ Hom_M(Π_D, r_P^G π) = Hom_M(Π_D, r_D π)`.

The Library states this Proposition as `BernsteinBlockJacquetFaithfulStatement`:
for every block object `X` with nontrivial carrier there is a nonzero
morphism from `Π_D` (transported to the literal standard Levi) to the
normalized Jacquet module of `X` along the standard parabolic of `a.roots`.
This module derives that statement from three unproved Library
propositions, which are explicit premises:

- `BernsteinInducedProgeneratorStatement.{uF, uV}` (`hProg`), Renard
  VI.10.1, Theorem. It is a target of Task 5225 and is not proved here. Only
  its block membership and its generator conjunct are used.
- `RepresentedParabolic.InducedProgeneratorIndependenceStatement.{uF, max uF uV}`
  (`hIndep`), Renard VI.10.1, Lemma, Proposition and Corollary. It is a
  target of Task 5225 and is not proved here.
- `RepresentedParabolic.LeviSecondAdjointnessStatement.{uF, uV}` (`hAdj`),
  Renard VI.9.6, second adjointness, owned by another task.

## Route of the Lean proof

The Lean proof follows Renard's argument. Renard uses that `i_{P̄}^G Π_D`
is a progenerator. The Lean proof uses that `i_P^G Π_D` is a generator (the
generator conjunct of `hProg`). It then moves to `i_{P̄}^G Π_D` with the
isomorphism `i_P^G Π_D ≅ i_{P̄}^G Π_D` from `hIndep`. Second adjointness
`i_{P̄}^G ⊣ r_P^G` (`hAdj` applied to the pair `(P̄, P)`) then gives the
nonzero morphism into `r_P^G X`. The statement uses `r_P^G` itself, without
the projection to `M(M)_D`, so no projection is needed.

There are two technical points.

1. The core step is stated for an arbitrary actual parabolic `P = MN`
   (`exists_ne_zero_leviJacquet_of_ne_zero_leviInduction`). It is then
   specialized to the standard parabolic. Applying `hIndep` and `hAdj`
   directly to the standard data made unification time out. Lean kept
   unfolding two spellings of the standard Levi group scheme,
   `Standard.leviScheme i ν (rootSet i ν I)` and `bernsteinLeviScheme i ν I`.
   The general lemma never mentions the standard family.
2. The statement uses the literal normalized Jacquet module
   `normalizedJacquetFunctor (unipotent i ν I) (levi i ν I) …` of subgroups
   of `G(F)`. `hAdj` gives the represented Jacquet functor
   `RepresentedParabolic.leviJacquetFunctor`. The module proves that the two
   agree (`bernsteinStandardFaithfulRepresentedJacquetIso`). This mirrors the
   published induction comparison `bernsteinStandardRepresentedInductionIso`.

## Declarations

- `jacquetPullbackIsoOfEmbeddedLevi` (definition): let `M = M'` and `U = U'`
  be equal subgroups of a group `H`, with `U`, `U'` closed and `M`, `M'`
  normalizing them. Let `e : L ≃ₜ* M` and `e' : L ≃ₜ* M'` agree pointwise in
  `H`. Then the pulled-back normalized Jacquet modules
  `SmoothRep.pullback e (J_{U,M} X)` and `SmoothRep.pullback e' (J_{U',M'} X)`
  are isomorphic. Proof: `subst` the two subgroup equalities, show `e = e'`
  by extensionality, and take `Iso.refl`.

- `smoothRepPullbackReflIso` (definition): pullback along
  `ContinuousMulEquiv.refl H` is isomorphic to the original smooth
  representation; the carrier map is the identity linear equivalence.

- `exists_ne_zero_leviJacquet_of_ne_zero_leviInduction` (theorem, core
  step): fix a nonarchimedean local field `k`, a connected reductive `G`
  (`hG`) whose rational points carry the published point topology and are
  locally compact and nonarchimedean, and an actual parabolic `p : P ⟶ G`
  with rational Levi `l : M ⟶ P`, unipotent radical `r : N ⟶ P` and
  `subgroupMultiplication l r` an isomorphism. Assume `hIndep` and `hAdj`.
  Let `π` be an irreducible supercuspidal representation of `M(F)`, `ρ₀` an
  irreducible representation of `⁰M(F)` and `j : ρ₀ ⟶ Res_{⁰M(F)} π`
  injective. Then every nonzero morphism
  `(leviInductionFunctor p l r …).obj (rationalNormKernelSummandInduction M ρ₀) ⟶ X`
  yields a nonzero morphism
  `rationalNormKernelSummandInduction M ρ₀ ⟶ (leviJacquetFunctor p l r …).obj X`.
  Proof: let `O := oppositeLeviParabolic hG p l hp hl` be the published
  opposite parabolic `P̄ = M N̄`. Apply `hIndep` to `(P, P̄)` with `g = 1`,
  `φ = Iso.refl M` and `e = ContinuousMulEquiv.refl`. The conjugation
  hypothesis follows from `G.innerIso_one_hom` and `O.levi_comp`. This gives
  `ψ : i_P(Π_D) ≅ i_{P̄}(pullback refl Π_D)`. Apply `hAdj` to `(P̄, P)`, with
  `O.levi_comp.symm` and the intersection identity
  `P̄(F) ∩ P(F) = M(F)` from `O.intersection`. This gives an adjunction
  `adj : i_{P̄} ⊣ r_P`. The morphism is
  `(smoothRepPullbackReflIso _).inv ≫ adj.homEquiv _ _ (ψ.inv ≫ f)`. If it
  were zero, then `adj.homEquiv _ _ (ψ.inv ≫ f) = 0`, because the first
  factor is an isomorphism. Then `ψ.inv ≫ f = 0`: invert `homEquiv` with
  `Adjunction.homEquiv_counit`, and use that the left adjoint `i_{P̄}`
  preserves zero morphisms. Hence `f = 0`.

- `bernsteinStandardFaithfulRepresentedJacquetFunctor i ν family I` (definition,
  entry declaration): the represented normalized Jacquet functor
  `RepresentedParabolic.leviJacquetFunctor` along the standard parabolic
  `Standard.parabolicHom i ν (rootSet i ν I)`, with Levi
  `Standard.leviToParabolic` and radical `Standard.unipotentToParabolic`,
  from `SmoothRep ℂ G(F)` to `SmoothRep ℂ M(F)` for
  `M = bernsteinLeviScheme i ν I`, in the carrier universe `max uF uV`. The
  geometric facts come from the published
  `bernsteinStandardRepresentativesGeometric i ν family I`.

- `bernsteinStandardLiteralJacquetFunctor i ν family I` (definition): the
  literal normalized Jacquet functor
  `normalizedJacquetFunctor (unipotent i ν I) (levi i ν I) …` followed by
  pullback along `leviRationalPointHomeomorph i ν I`, from `SmoothRep ℂ G(F)`
  to `SmoothRep ℂ M(F)`.

- `bernsteinStandardFaithfulRepresentedJacquetIso i ν family I X` (definition): the
  two functors agree on every `X`. Proof: apply
  `jacquetPullbackIsoOfEmbeddedLevi` with the published subgroup
  equalities `standardCompression_leviPoints` and
  `standardCompression_unipotentPoints`. The Levi identifications
  `leviPointsEquiv` and `leviRationalPointHomeomorph` agree pointwise by
  `Standard.leviToParabolic_comp`.

- `exists_ne_zero_bernsteinLiteralJacquet_of_ne_zero` (theorem): the core
  step for the standard data. Assume `hIndep` and `hAdj`. Let `a` be a
  Bernstein cuspidal datum, `ρ₀` irreducible and `j` injective as in the
  target statement. Then every nonzero morphism `h0` from the literal
  standard induction
  `(normalizedInductionFunctor (family.decomposition a.roots) …).obj
  (bernsteinLiteralLeviRep i ν a.roots Π_D)` to `X` gives a nonzero morphism
  `bernsteinLiteralLeviRep i ν a.roots Π_D ⟶ (normalizedJacquetFunctor
  (unipotent i ν a.roots) (levi i ν a.roots) …).obj X`, with
  `Π_D = rationalNormKernelSummandInduction (bernsteinLeviScheme i ν a.roots) ρ₀`.
  Proof: apply the core step to the standard parabolic, passing
  `M := bernsteinLeviScheme i ν a.roots` explicitly. The supercuspidal input
  is `a.representation`, with `a.irreducible` and the published
  `BernsteinCuspidalDatum.isSupercuspidal`. The induced morphism is
  `(bernsteinStandardRepresentedInductionIso …).hom ≫ h0`. This gives a
  nonzero `g : Π_D ⟶ r_P^{rep}(X)`. Compose with
  `bernsteinStandardFaithfulRepresentedJacquetIso` to get `g'`, then apply
  `SmoothRep.pullbackFunctor e.symm` for `e = leviRationalPointHomeomorph`,
  then `SmoothRep.pullbackSymmIso`. The result is nonzero because the
  isomorphism factors do not create zeros. The pullback functor is the
  functor of the equivalence `SmoothRep.pullbackEquivalence e.symm`, so it
  is faithful and preserves zero morphisms (`Functor.map_eq_zero_iff`).

- `bernsteinBlockJacquetFaithful_of_inducedProgenerator` (theorem, main
  result): `hProg`, `hIndep` and `hAdj` imply
  `BernsteinBlockJacquetFaithfulStatement.{uF, uV}`. Proof: introduce the
  data, `X` and `Nontrivial X.obj`. Apply `hProg` to obtain the membership
  `hmem` of `piOmega` and the generator conjunct. In the block,
  `𝟙 X ≠ 0`. Otherwise `𝟙 X.obj = 0`, so `X.obj` is a zero object
  (`IsZero.iff_id_eq_zero`), hence subsingleton
  (`SmoothRep.isZero_iff_subsingleton`), which contradicts nontriviality.
  The generator conjunct, applied to `𝟙 X ≠ 0`, gives
  `h : ⟨piOmega, hmem⟩ ⟶ X` with `h ≫ 𝟙 X ≠ h ≫ 0`. So `h.hom ≠ 0`, using
  `ObjectProperty.zero_hom` and extensionality of full-subcategory
  morphisms. Then `exists_ne_zero_bernsteinLiteralJacquet_of_ne_zero`
  applies to `h.hom`.

## Lean setup notes

The `Core` section mirrors the instance context of `hIndep`: `[T2Space k]`,
the published point topology on `G(F)` as a local instance, and
`leviPointTopology l hl` on `M(F)`. The `Standard` section copies the setup
of the published `BernsteinRepresentedInduction` module: `maxHeartbeats
1200000`, `backward.isDefEq.respectTransparency.types false`, and local
instances for affineness, finite type and the point topology of `G(F)` and
of the standard Levi points. The target statement topologizes the standard
Levi points by `rationalPointTopology F (bernsteinLeviScheme i ν a.roots).X`.
The local instance is `pointTopology`, which unfolds to that topology, so
the final application unifies. The declarations raise heartbeats per
declaration (400000 for the core step, 600000 for the last two theorems).
Universes are declared in the order `uF uV`, so `.{uF, uV}` at call sites
fixes the carrier level `max uF uV`.

## Scope

This module is a conditional reduction for the Proposition of VI.10.3. Its
three premises are unproved: two are targets of Task 5225 and one belongs
to another task. It does not prove `BernsteinBlockJacquetFaithfulStatement`
and is not submitted as acceptance of that target. The premise `hProg`
contributes only membership and the generator property; projectivity and
finite generation are not used.
