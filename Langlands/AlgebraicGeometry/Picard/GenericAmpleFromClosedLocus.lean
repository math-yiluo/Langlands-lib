import Langlands.AlgebraicGeometry.Picard.AbelianFibreAmpleLocusClosedStatement
import Langlands.AlgebraicGeometry.Picard.ProperAffineFibrewiseAmpleStatement
import Langlands.AlgebraicGeometry.Picard.NoetherianAffineAbelianGenericAmpleStatement
import Langlands.AlgebraicGeometry.Picard.FieldBaseChangeAmpleReflectionProof
import Langlands.AlgebraicGeometry.Picard.AmpleFiniteAffineOpen

/-! # Generic ampleness from the closed ample-fibre locus -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

set_option backward.isDefEq.respectTransparency false

namespace Langlands.AlgebraicGeometry.Picard

variable {X S : Scheme.{u}}

/-- Ampleness after pullback to a field point reflects to its residue-field fibre. -/
theorem LineBundle.isAmple_fibre_of_fieldPoint
    (f : X ⟶ S) (L : LineBundle X) (K : Type u) [Field K]
    (g : Spec (CommRingCat.of K) ⟶ S)
    (hL : ((LineBundle.pullback (pullback.fst f g)).obj L).IsAmple) :
    ((LineBundle.pullback (f.fiberι (g (IsLocalRing.closedPoint K)))).obj L).IsAmple := by
  let s := g (IsLocalRing.closedPoint K)
  let k := S.residueField s
  let b := Spec.map (S.descResidueField (Scheme.stalkClosedPointTo g))
  have hb : b ≫ S.fromSpecResidueField s = g :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField K S g
  let p := f.fiberToSpecResidueField s
  let q := pullback.fst p b
  have hsquare : IsPullback (q ≫ f.fiberι s) (pullback.snd p b) f g := by
    rw [← hb]
    exact (IsPullback.of_hasPullback p b).paste_horiz
      (IsPullback.of_hasPullback f (S.fromSpecResidueField s))
  let e := hsquare.isoPullback
  have he : e.hom ≫ pullback.fst f g = q ≫ f.fiberι s :=
    hsquare.isoPullback_hom_fst
  have h := hL.pullback_of_isAffineHom e.hom
  let comparison :
      (Scheme.Modules.pullback e.hom).obj
          ((Scheme.Modules.pullback (pullback.fst f g)).obj L.obj) ≅
        (Scheme.Modules.pullback q).obj
          ((Scheme.Modules.pullback (f.fiberι s)).obj L.obj) :=
    (Scheme.Modules.pullbackComp e.hom (pullback.fst f g)).app L.obj ≪≫
      (Scheme.Modules.pullbackCongr he).app L.obj ≪≫
        ((Scheme.Modules.pullbackComp q (f.fiberι s)).app L.obj).symm
  exact fieldBaseChangeAmpleReflection k K b (f.fiber s) p
    ((LineBundle.pullback (f.fiberι s)).obj L) (h.of_iso comparison)

/-- The canonical fraction-field point of a domain has zero prime ideal. -/
theorem fractionFieldPoint_asIdeal (R : Type u) [CommRing R] [IsDomain R] :
    (Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
      (IsLocalRing.closedPoint (FractionRing R))).asIdeal = ⊥ := by
  change Ideal.comap (algebraMap R (FractionRing R))
    (IsLocalRing.closedPoint (FractionRing R)).asIdeal = ⊥
  rw [Ideal.eq_bot_of_prime (IsLocalRing.closedPoint (FractionRing R)).asIdeal,
    Ideal.comap_bot_of_injective _ (IsFractionRing.injective R (FractionRing R))]

/-- Closedness of the fibrewise ample locus and affine-base globalization
imply the canonical generic-to-total ampleness criterion. -/
theorem noetherianAffineAbelianGenericAmple_of_closedLocus
    (closedLocus : AbelianFibreAmpleLocusClosedStatement.{u})
    (fibrewiseAmple : ProperAffineFibrewiseAmpleStatement.{u}) :
    NoetherianAffineAbelianGenericAmpleStatement.{u} := by
  intro R _ _ _ A L hL
  let S := Spec (CommRingCat.of R)
  let g := Spec.map (CommRingCat.ofHom (algebraMap R (FractionRing R)))
  let s := g (IsLocalRing.closedPoint (FractionRing R))
  have hs : ((LineBundle.pullback (A.X.hom.fiberι s)).obj L).IsAmple :=
    L.isAmple_fibre_of_fieldPoint A.X.hom (FractionRing R) g hL
  have hclosure : closure ({s} : Set S) = Set.univ := by
    change closure ({s} : Set (PrimeSpectrum R)) = Set.univ
    rw [PrimeSpectrum.closure_singleton, fractionFieldPoint_asIdeal R,
      PrimeSpectrum.zeroLocus_bot]
  apply fibrewiseAmple A.X.left S A.X.hom L
  have hc := closedLocus S A L
  have hsub : closure ({s} : Set S) ⊆
      {t : S | ((LineBundle.pullback (A.X.hom.fiberι t)).obj L).IsAmple} :=
    closure_minimal (Set.singleton_subset_iff.mpr hs) hc
  rw [hclosure] at hsub
  exact fun t => hsub (Set.mem_univ t)

end Langlands.AlgebraicGeometry.Picard
