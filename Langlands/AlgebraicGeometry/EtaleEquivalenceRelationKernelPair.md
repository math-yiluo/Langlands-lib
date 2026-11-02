# The kernel pair relation of an étale morphism and a cartesian criterion for affine quotients

Authors: Worker 1110.

This helper module defines the kernel pair `U ×_M U ⇉ U` of an étale morphism `q : U ⟶ M` as
an étale equivalence relation, proves that it has an affine quotient when `q` is surjective
and `M` is affine, and gives a criterion, at the level of schemes and at the level of rings,
for an étale equivalence relation `E` with `E.U` affine to have an affine quotient: a
cartesian morphism from `E` to such a kernel pair. It uses the published definitions of
`Langlands.AlgebraicGeometry.EtaleEquivalenceRelation` unchanged (`EtaleEquivalenceRelation`,
`IsCartesianHom`, `HasAffineQuotient`), the published theorem
`Langlands.AlgebraicGeometry.etaleEquivalenceRelationCartesianAffineQuotient` (module
`Langlands.AlgebraicGeometry.EtaleEquivalenceRelationCartesianAffineQuotientProof`) and
Mathlib (pinned commit `5ed2965256430c3649e86755f9576b54eca72435`). It introduces no axioms.

## Provenance

The module contains no statement taken from the literature. The kernel pair `U ×_M U` of a
surjective étale morphism is the standard presentation of `M` by an étale equivalence
relation (Stacks Project, Properties of Spaces, Section 66.9, not used here). The affine
quotient result is the published statement
`EtaleEquivalenceRelationCartesianAffineQuotientStatement` (fpqc descent of affine morphisms,
Stacks Project Lemma 35.37.1, Tag 0245, source `stacks-noetherian-approximation-2026-11-01`,
directory SHA-256 `a9a500a6ecf5ab8155bccd57e5fff0616f581d41e9256563c7821a5b81019625`). The
criteria below are derived helpers for the proof of
`EtaleEquivalenceRelationNoetherianCoverLevelStatement`, where a relation at a Noetherian
level is shown to have an affine quotient by mapping it cartesianly to the kernel pair of
`Spec B₁ → Spec A₁` for an étale faithfully flat `A₁ → B₁`.

## Part 1: the kernel pair (namespace `Langlands.AlgebraicGeometry.EtaleEquivalenceRelation`)

- `kernelPair (q : U ⟶ M) [Etale q] : EtaleEquivalenceRelation.{u}`: `U := U`,
  `R := pullback q q`, `t := pullback.fst q q`, `s := pullback.snd q q`. The pair `(t, s)` is
  jointly monic (`mono_lift`) by `pullback.hom_ext`. Reflexivity, symmetry and transitivity
  are given by `pullback.lift a a`, by swapping the two projections, and by
  `pullback.lift (r ≫ fst) (r' ≫ snd)`. Both projections are étale as base changes of `q`.
  The simp lemmas `kernelPair_U`, `kernelPair_R`, `kernelPair_t` and `kernelPair_s` record the
  fields (all `rfl`).
- `kernelPair_hasAffineQuotient [Surjective q] [IsAffine M]`: `(kernelPair q).HasAffineQuotient`,
  with quotient `M` and quotient map `q`. The square `IsPullback t s q q` is
  `IsPullback.of_hasPullback`, and `q` is flat, locally of finite presentation (both because
  it is étale) and surjective.
- `isCartesianHom_kernelPair (E) (f : E.U ⟶ U) (h : IsPullback (E.t ≫ f) E.s q (f ≫ q))`:
  `IsCartesianHom E (kernelPair q) f g` with
  `g = pullback.lift (E.t ≫ f) (E.s ≫ f) _`. The identity `g ≫ fst = E.t ≫ f` is
  `pullback.lift_fst`. The square formed by `g`, `E.s`, `snd` and `f` is a pullback by
  `IsPullback.of_right`: its composite with the pullback square of `fst` and `snd` is `h`.
- `hasAffineQuotient_of_isPullback_kernelPair [Surjective q] [IsAffine M] [IsAffine U] (E)
  [IsAffine E.U] (f) (h)`: `E.HasAffineQuotient`. This applies
  `etaleEquivalenceRelationCartesianAffineQuotient` to the cartesian morphism of the previous
  item and to `kernelPair_hasAffineQuotient`.

## Part 2: ring-level forms

Namespace `Langlands.AlgebraicGeometry.CommRingCat`, for commutative rings `R, S, A, P` in one
universe with `R`-algebras `S` and `A`:

- `tensorLift i j hw : S ⊗[R] A →+* P` for ring maps `i : S →+* P`, `j : A →+* P` that agree
  on `R` (`hw : i.comp (algebraMap R S) = j.comp (algebraMap R A)`). It is the map out of the
  pushout `CommRingCat.isPushout_tensorProduct R S A` given by `i` and `j`.
  `tensorLift_tmul`: `tensorLift i j hw (x ⊗ₜ y) = i x * j y`.
- `isPushout_of_bijective i j F hF hbij`: if `F : S ⊗[R] A →+* P` is bijective and
  `F (x ⊗ₜ y) = i x * j y`, then the square of `algebraMap R S`, `algebraMap R A`, `i` and `j`
  is a pushout in `CommRingCat`. The proof transports `isPushout_tensorProduct` along the ring
  isomorphism `RingEquiv.ofBijective F hbij` (`IsPushout.of_iso`).

Namespace `Langlands.AlgebraicGeometry.EtaleEquivalenceRelation`, for `A₁ → B₁` an algebra:

- `specAlgebraMap A₁ B₁ : Spec B₁ ⟶ Spec A₁`, the abbreviation for
  `Spec.map (CommRingCat.ofHom (algebraMap A₁ B₁))`. It is `Etale` when `B₁` is étale over
  `A₁` (`HasRingHomProperty.Spec_iff`, `RingHom.etale_algebraMap`) and `Surjective` when
  `B₁` is faithfully flat over `A₁` (`flat_and_surjective_SpecMap_iff`,
  `RingHom.faithfullyFlat_algebraMap_iff`).
- `hasAffineQuotient_of_bijective`. Hypotheses: `A₁ → B₁` étale and faithfully flat; rings
  `D` and `C` with `[Algebra A₁ D]`, `[Algebra D C]` and a ring map `τ : D →+* C`; an étale
  equivalence relation `E` with isomorphisms `eU : E.U ≅ Spec D` and `eR : E.R ≅ Spec C` such
  that `E.t ≫ eU.hom = eR.hom ≫ Spec.map τ` and
  `E.s ≫ eU.hom = eR.hom ≫ Spec.map (algebraMap D C)`; an `A₁`-algebra map
  `φ : B₁ →ₐ[A₁] D`; and a bijective ring map `F : B₁ ⊗[A₁] D →+* C` with
  `F (b ⊗ₜ d) = τ (φ b) * algebraMap D C d`. Conclusion: `E.HasAffineQuotient`.
  Proof: `isPushout_of_bijective` (with `i = τ ∘ φ`, `j = algebraMap D C`) gives a pushout of
  rings, and Mathlib's `isPullback_SpecMap_of_isPushout` turns it into a pullback square
  `Spec C ≅ Spec B₁ ×_{Spec A₁} Spec D`. Transported along `eU` and `eR`
  (`IsPullback.of_iso`), with `Spec.map_comp` and `AlgHom.comp_algebraMap`, it becomes
  `IsPullback (E.t ≫ f) E.s q (f ≫ q)` for `q = specAlgebraMap A₁ B₁` and
  `f = eU.hom ≫ Spec.map φ`. `E.U` is affine as it is isomorphic to `Spec D`, so
  `hasAffineQuotient_of_isPullback_kernelPair` applies. When `E.U = Spec D`, `E.R = Spec C`,
  `E.t = Spec.map τ` and `E.s = Spec.map (algebraMap D C)` hold by definition, take
  `eU = eR = Iso.refl _`.
