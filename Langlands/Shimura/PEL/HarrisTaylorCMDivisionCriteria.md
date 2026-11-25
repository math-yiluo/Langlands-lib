# Infinitesimal and valuative criteria for division-case CM representability

This module is an internal derivation from Library results. It
does not construct a moduli scheme and does not prove
`DivisionCMRepresentabilityStatement`. It splits the geometric premise of the
published assembly `HarrisTaylorCMDivisionAssembly` into three independent
premises:

1. a representing scheme with an immersion into projective space over `F`;
2. infinitesimal lifting of classes of the existing presheaf along Artinian
   thickenings;
3. extension of classes of the existing presheaf from the fraction field of a
   discrete valuation ring to the ring.

Premises 2 and 3 concern only the existing normalized class presheaf, not any
representing scheme. The module proves that the three premises give
`CMLevelGeometricRepresentation`, the smooth and proper representation data
of the assembly. Hence they give the division-case target.

All declarations live in namespace
`Langlands.Shimura.PEL.HarrisTaylorCMWeilLevel`. They carry the same variables
and named prerequisite hypotheses as
`HarrisTaylorCMDivisionRepresentabilityStatement`. Below, "…" stands for that
argument list, and `moduli` for the existing presheaf tower
`smallLevelClassPresheafTower …`.

## Spectra as admissible tests

- `specTest B β`. Let `B : Type` be a noetherian commutative ring and
  `β : Spec B ⟶ Spec F` a structure morphism. Then `Over.mk β` is an object of
  `ComponentwiseAdmissibleCMBaseCategory`. Admissibility is
  `componentwiseAdmissibleCMBase_of_relativeDual` applied to the Library
  theorems `relativeDualSchemeExistence` and `relativeDualSchemeGeometry`.
  That bridge needs only that `Spec B` is locally noetherian.
- `specTestMap φ β`. A ring map `φ : B' →+* B` of noetherian rings gives the
  test morphism `Spec φ` from `specTest B (Spec φ ≫ β)` to `specTest B' β`.

## The two presheaf statements

- `CMLevelArtinianLiftingStatement U`. Let `B'` and `B` be local Artinian rings
  in `Type`. Let `φ : B' →+* B` be surjective with
  `maximalIdeal B' * ker φ = ⊥`, and let `β : Spec B' ⟶ Spec F` be any
  structure morphism. Then restriction of classes
  `(moduli.obj U).map (specTestMap φ β).op` is surjective. Informally: every
  normalized class over `Spec B` lifts to `Spec B'`. The thickenings are the
  elementary ones of the Library's `ArtinianLiftingSmooth.LiftsArtinian`.
- `CMLevelDiscreteValuativeExistenceStatement U`. Let `V` be a discrete
  valuation ring in `Type` with fraction field `K` (`IsFractionRing V K`), and
  let `β : Spec V ⟶ Spec F` be any structure morphism. Then restriction of
  classes `(moduli.obj U).map (specTestMap (algebraMap V K) β).op` is
  surjective. Informally: every normalized class over `Spec K` extends over
  `Spec V`.

## Quasi-projective representation data

`CMLevelQuasiProjectiveRepresentation U` is a structure for a small level `U`.
It consists of:

- an arbitrary scheme `scheme : Over (Spec F)`;
- a natural number `dim` and an immersion
  `embedding : scheme.left ⟶ ℙ^dim_F` with
  `embedding ≫ projectiveSpaceToSpec F dim = scheme.hom`;
- a natural isomorphism
  `represents : admissibleTestPoints scheme ≅ moduli.obj U` on the
  componentwise admissible test category.

The structure contains no smoothness, properness or admissibility. It is
`CMLevelGeometricRepresentation` without the fields `smooth` and `proper`.
`CMLevelGeometricRepresentation.toQuasiProjective` forgets those two fields.

## Proofs

Let `R : CMLevelQuasiProjectiveRepresentation U`, and write `X` for
`R.scheme`.

- `exists_lift`. Let `r : T ⟶ T'` be a test morphism on which restriction of
  classes is surjective. Then every point `a : T.obj ⟶ X` over `F` extends
  along `r`: some `c : T'.obj ⟶ X` has `r.hom ≫ c = a`. Proof: send `a` to a
  class by `represents.hom`, and lift that class to `T'`. Send the lift back by
  `represents.inv` to get `c`. Naturality of `represents.inv` and
  `hom_inv_id` give `r.hom ≫ c = a`.
- Instances `locallyOfFiniteType`, `quasiCompact` and `isSeparated` for
  `X.hom`.
  - Local finite type and separatedness: an immersion is locally of finite
    type and separated, and `projectiveSpaceToSpec F dim` is proper.
  - Quasi-compactness: `ℙ^dim_F` is locally noetherian and compact, being
    of finite type and proper over a field, so it is a noetherian scheme. Its
    underlying space is therefore noetherian. `X` embeds in it, so the
    underlying space of `X` is noetherian, and every morphism out of `X` is
    quasi-compact.
- `smooth hlift : Smooth X.hom`, from
  `hlift : CMLevelArtinianLiftingStatement U`. By the Library theorem
  `ArtinianLiftingSmooth.smooth_of_liftsArtinian` (`Spec F` is noetherian,
  `X.hom` is locally of finite type), it suffices to prove
  `LiftsArtinian X.hom`. Given `α : Spec B ⟶ X` and `β : Spec B' ⟶ Spec F`
  with `α ≫ X.hom = Spec φ ≫ β`, the morphism `α` is a point of
  `specTest B (Spec φ ≫ β)`. `exists_lift` along `specTestMap φ β` gives
  the required `γ = c.left`. Here `γ ≫ X.hom = β` is `Over.w c`.
  The residue-point hypothesis of `LiftsArtinian` is not needed.
- `universallyClosed hval` and `isProper hval`, from
  `hval : CMLevelDiscreteValuativeExistenceStatement U`. The Library theorem
  `universallyClosed_of_forall_isDiscreteValuationRing_hasLift` applies to the
  quasi-compact, locally finite-type morphism `X.hom` to `Spec F`. So it
  suffices to lift every Mathlib `ValuativeCommSq` of `X.hom` whose ring
  `S.R` is a discrete valuation ring. The top map `S.i₁` is a point of
  `specTest S.K (Spec (algebraMap S.R S.K) ≫ S.i₂)`, by the square's
  commutativity. `exists_lift` along `specTestMap (algebraMap S.R S.K) S.i₂`
  gives the lift `c.left`. Properness then combines universal closedness with
  the instances above.
- `toGeometric hlift hval : CMLevelGeometricRepresentation U` keeps the
  scheme, immersion and natural isomorphism, and adds `smooth` and
  `isProper`.

Necessity of the valuative statement:
`CMLevelGeometricRepresentation.discreteValuativeExistence` shows that any
`CMLevelGeometricRepresentation U` implies
`CMLevelDiscreteValuativeExistenceStatement U`. Properness gives the existence
part of Mathlib's valuative criterion (`UniversallyClosed.eq_valuativeCriterion`).
Transport through `represents` then lifts each class over `Spec K` to one over
`Spec V`. The module does not prove the corresponding necessity of the lifting
statement. Mathematically it holds: since `ker φ ⊆ maximalIdeal B'`, the
kernel has square zero, so a smooth representer lifts along `Spec φ`.

## Assembly

- `cmGeometricRepresentabilityStatement_of_criteria hrep hlift hval`. If at
  every small level there are quasi-projective representation data, and the
  lifting and valuative statements hold, then
  `CMGeometricRepresentabilityStatement …` holds.
- `divisionCMRepresentabilityStatement_of_criteria hrep hlift hval`. If each
  of the three premises holds at every small level whenever `D.IsDivision`,
  then `DivisionCMRepresentabilityStatement …` holds. The proof is the
  published `divisionCMRepresentabilityStatement_of_geometric`, applied to
  `relativeDualSchemeExistence.{0}`, `relativeDualSchemeGeometry.{0}` and the
  previous theorem.

None of the three premises is proved here. Their expected sources are:

- Quasi-projective representability: the PEL locus over the ordinary
  polarized moduli scheme, then level comparison and finite
  quotients.
- Lifting: deformation theory of the PEL data.
- Valuative existence: division-case potentially good reduction and Néron
  extension. These are the representability, smoothness and projectivity steps
  of Kottwitz, *Points on some Shimura varieties over finite fields* (1992),
  §5, pp.390–392 (`kottwitz-1992-points-shimura-finite-fields`), in
  characteristic zero.

## Provenance

Internal. The module specializes published Library declarations: the
assembly, the base admissibility bridge, the relative dual theorems, the
Artinian lifting smoothness criterion and the discrete valuation ring
criterion for universal closedness. It also uses Mathlib facts about
immersions, noetherian spaces and the valuative criterion. No literature
definition is transcribed. The compiled axioms are `propext`,
`Classical.choice` and `Quot.sound`.
