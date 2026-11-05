import Langlands.GroupScheme.Torus.AffineCharacterAction
import Langlands.GroupScheme.Torus.CentralizerSmooth
import Langlands.CommutativeAlgebra.FixedQuotientFinitePresentation

/-! # Smooth actual diagonalizable fixed subgroups over arbitrary rings -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace AffineCoordinates

variable {R : CommRingCat.{u}} (G : GroupScheme (Spec R)) [IsAffine G.X.left]

theorem groupSchemeIso_hom_eq_coordinateSchemeIso :
    (groupSchemeIso G).hom.hom.hom = (coordinateSchemeIso G).hom := by
  change (algSpec R).map (Corepresented.cogroupRecoveryIso (coordinateCogroup G)).hom.hom.hom ≫
    (coordinateSchemeIso G).hom = _
  have h : (Corepresented.cogroupRecoveryIso (coordinateCogroup G)).hom.hom.hom = 𝟙 _ := rfl
  rw [h, CategoryTheory.Functor.map_id, Category.id_comp]

end AffineCoordinates

namespace CharacterAction

variable {R : CommRingCat.{u}} {M : Type u} [AddCommGroup M]
  {G : GroupScheme (Spec R)} [IsAffine G.X.left]
  (a : AutomorphicAction (Diagonalizable.groupScheme R M).toGrp G)

/-- The actual fixed subgroup viewed in the chosen affine coordinates. -/
def coordinateFixedSubgroup :
    SubgroupFunctor (Corepresented.groupScheme (AffineCoordinates.functor G)
      (AffineCoordinates.corepresentation G)) :=
  a.fixedSubgroup.comap (AffineCoordinates.groupSchemeIso G).hom

/-- The fixed ideal cuts out the actual coordinate fixed subgroup. -/
theorem isCutOutBy_coordinateFixedSubgroup :
    Corepresented.IsCutOutBy (AffineCoordinates.corepresentation G)
      (Corepresented.affineSubgroups (coordinateFixedSubgroup a)) (schemeFixedIdeal a) := by
  intro C x
  obtain ⟨φ, rfl⟩ := (AffineCoordinates.corepresentation G).homEquiv.surjective x
  have hx : (Corepresented.affinePointsEquiv (AffineCoordinates.functor G)
      (AffineCoordinates.corepresentation G) C).symm
        ((AffineCoordinates.corepresentation G).homEquiv φ) = (algSpec R).map φ.op :=
    (Corepresented.affinePointsEquiv (AffineCoordinates.functor G)
      (AffineCoordinates.corepresentation G) C).symm_apply_eq.mpr
        (Corepresented.affinePointsEquiv_map _ _ _ _).symm
  change (Corepresented.affinePointsEquiv (AffineCoordinates.functor G)
    (AffineCoordinates.corepresentation G) C).symm
      ((AffineCoordinates.corepresentation G).homEquiv φ) ≫
    (AffineCoordinates.groupSchemeIso G).hom.hom.hom ∈
    a.fixedSubgroup.carrier _ ↔ _
  rw [hx, AffineCoordinates.groupSchemeIso_hom_eq_coordinateSchemeIso,
    Equiv.symm_apply_apply]
  exact (schemeFixedIdeal_le_ker_iff a φ).symm

/-- The actual fixed scheme, defined by the full fixed ideal. -/
abbrev schemeFixedGroupScheme : GroupScheme (Spec R) :=
  Corepresented.cutGroupScheme (isCutOutBy_coordinateFixedSubgroup a)

/-- The actual closed fixed-subgroup inclusion into the original group. -/
def schemeFixedHom : schemeFixedGroupScheme a ⟶ G :=
  Corepresented.cutHom (isCutOutBy_coordinateFixedSubgroup a) ≫
    (AffineCoordinates.groupSchemeIso G).hom

/-- The fixed scheme represents the existing all-test fixed subgroup. -/
theorem isRepresentedBy_schemeFixedHom :
    a.fixedSubgroup.IsRepresentedBy (schemeFixedHom a) := by
  have h : (coordinateFixedSubgroup a).IsRepresentedBy
      (Corepresented.cutHom (isCutOutBy_coordinateFixedSubgroup a)) :=
    Corepresented.isRepresentedBy_cutHom_affineSubgroups
      (Corepresented.isAffineCutOutBy_of_isCutOutBy
        (isCutOutBy_coordinateFixedSubgroup a))
  have ht := h.comp_iso (AffineCoordinates.groupSchemeIso G)
  have hK : (coordinateFixedSubgroup a).comap (AffineCoordinates.groupSchemeIso G).inv =
      a.fixedSubgroup := by
    rw [coordinateFixedSubgroup, ← SubgroupFunctor.comap_comp,
      Iso.inv_hom_id, SubgroupFunctor.comap_id]
  rw [hK] at ht
  exact ht

/-- The actual fixed-subgroup inclusion is a closed immersion. -/
theorem isClosedSubgroup_schemeFixedHom : IsClosedSubgroup (schemeFixedHom a) :=
  (Corepresented.isClosedSubgroup_cutHom (isCutOutBy_coordinateFixedSubgroup a)).comp_iso
    (AffineCoordinates.groupSchemeIso G)

/-- No noetherian hypothesis is needed for the finite presentation of the
actual fixed-locus coordinate quotient. -/
theorem finitePresentation_schemeFixedQuotient
    [Algebra.FinitePresentation R (AffineCoordinates.algebra G)] :
    Algebra.FinitePresentation R (AffineCoordinates.algebra G ⧸ schemeFixedIdeal a) :=
  Langlands.CommutativeAlgebra.GradedFixedQuotient.finitePresentation_fixedQuotient
    (coaction (ofAutomorphicAction a)).hom

/-- The coordinate ring of the actual fixed scheme is smooth over an arbitrary
base ring if the original coordinate ring is smooth. -/
theorem smooth_schemeFixedQuotient [Algebra.Smooth R (AffineCoordinates.algebra G)] :
    Algebra.Smooth R (AffineCoordinates.algebra G ⧸ schemeFixedIdeal a) where
  finitePresentation := finitePresentation_schemeFixedQuotient a
  formallySmooth := formallySmooth_schemeFixedQuotient a

/-- Fixed subgroups of diagonalizable actions on smooth affine groups are
smooth over arbitrary commutative rings. -/
theorem smooth_schemeFixedGroupScheme (hG : Smooth G.X.hom) :
    Smooth (schemeFixedGroupScheme a).X.hom := by
  let := AffineCoordinates.smooth_algebra G hG
  let := smooth_schemeFixedQuotient a
  exact Corepresented.smooth_cutGroupScheme (isCutOutBy_coordinateFixedSubgroup a)

/-- The representative is closed, smooth and represents fixedness on all
scheme tests, including refinements. -/
theorem fixedSubgroup_hasSmoothClosedRepresentative (hG : Smooth G.X.hom) :
    a.fixedSubgroup.HasSmoothClosedRepresentative :=
  ⟨schemeFixedGroupScheme a, schemeFixedHom a, isClosedSubgroup_schemeFixedHom a,
    smooth_schemeFixedGroupScheme a hG, isRepresentedBy_schemeFixedHom a⟩

end CharacterAction

namespace Diagonalizable

variable {R : CommRingCat.{u}} {M : Type u} [AddCommGroup M]
  {G : GroupScheme (Spec R)} [IsAffine G.X.left]
  (i : (groupScheme R M).toGrp ⟶ G)

/-- The actual centralizer group, using the fixed ideal of conjugation. -/
abbrev relativeCentralizerGroupScheme : GroupScheme (Spec R) :=
  CharacterAction.schemeFixedGroupScheme (AutomorphicAction.conjugation i)

/-- The closed inclusion of the actual diagonalizable centralizer. -/
def relativeCentralizerHom : relativeCentralizerGroupScheme i ⟶ G :=
  CharacterAction.schemeFixedHom (AutomorphicAction.conjugation i)

/-- This is the existing centralizer on all test schemes. -/
theorem isRepresentedBy_relativeCentralizerHom :
    (torusCentralizer i).IsRepresentedBy (relativeCentralizerHom i) := by
  rw [← AutomorphicAction.conjugation_fixedSubgroup_eq_torusCentralizer]
  exact CharacterAction.isRepresentedBy_schemeFixedHom _

theorem isClosedSubgroup_relativeCentralizerHom :
    IsClosedSubgroup (relativeCentralizerHom i) :=
  CharacterAction.isClosedSubgroup_schemeFixedHom _

/-- The actual centralizer is smooth over an arbitrary base ring. -/
theorem smooth_relativeCentralizerGroupScheme (hG : Smooth G.X.hom) :
    Smooth (relativeCentralizerGroupScheme i).X.hom :=
  CharacterAction.smooth_schemeFixedGroupScheme _ hG

end Diagonalizable

/-- Over arbitrary commutative rings, the centralizer of any diagonalizable
group-scheme map into a smooth affine group has a smooth closed representative.
The map need not be an immersion. -/
theorem diagonalizableCentralizer_hasSmoothClosedRepresentative_overRing
    {R : CommRingCat.{u}} {M : Type u} [AddCommGroup M]
    {G : GroupScheme (Spec R)} [IsAffine G.X.left]
    (i : (Diagonalizable.groupScheme R M).toGrp ⟶ G) (hG : Smooth G.X.hom) :
    (torusCentralizer i).HasSmoothClosedRepresentative := by
  rw [← AutomorphicAction.conjugation_fixedSubgroup_eq_torusCentralizer]
  exact CharacterAction.fixedSubgroup_hasSmoothClosedRepresentative _ hG

/-- The centralizer of any split-torus map into a smooth affine group has a
smooth closed representative over an arbitrary commutative base ring. -/
theorem splitTorusCentralizer_hasSmoothClosedRepresentative_overRing
    {R : CommRingCat.{u}} {G : GroupScheme (Spec R)} [IsAffine G.X.left]
    {T : CommGroupScheme (Spec R)} (i : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp)
    (hG : Smooth G.X.hom) :
    (torusCentralizer i).HasSmoothClosedRepresentative := by
  classical
  obtain ⟨I, hfin, ⟨eT⟩⟩ := hT
  let : Fintype I := Fintype.ofFinite I
  let e := Diagonalizable.splitIso R (AddEquiv.refl (I → ℤ)) ≪≫ eT.symm
  have h := diagonalizableCentralizer_hasSmoothClosedRepresentative_overRing (e.hom ≫ i) hG
  rw [torusCentralizer_eq_centralizer_range,
    SubgroupFunctor.range_precomp_iso, ← torusCentralizer_eq_centralizer_range] at h
  exact h

end Langlands.GroupScheme
