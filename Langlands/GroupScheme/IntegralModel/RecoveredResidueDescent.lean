import Langlands.GroupScheme.IntegralModel.SemilinearCoefficientDescent
import Langlands.BruhatTits.IntegralModels.RelativeComponentCoefficientComparison

/-! # Coefficient descent on recovered special fibres -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

private theorem recovery_square_comm {C : Type*} [Category C]
    (F : C ⥤ C) {X Y N X' N' : C}
    (S : X ≅ Y) (s : X ≅ N)
    (tX : F.obj X ⟶ X') (tN : F.obj N ⟶ N')
    (aS : X' ⟶ N') (dX : X' ⟶ X) (dN : N' ⟶ N)
    (dY : F.obj Y ⟶ Y)
    (hNat : F.map s.hom ≫ tN = tX ≫ aS)
    (hRec : aS ≫ dN = dX ≫ s.hom)
    (hSem : F.map S.hom ≫ dY = tX ≫ dX ≫ S.hom) :
    F.map (S.inv ≫ s.hom) ≫ tN ≫ dN = dY ≫ S.inv ≫ s.hom := by
  apply (cancel_epi (F.mapIso S).hom).mp
  rw [CategoryTheory.Functor.map_comp]
  change (F.mapIso S).hom ≫
    ((F.mapIso S).inv ≫ F.map s.hom) ≫ tN ≫ dN =
      (F.mapIso S).hom ≫ dY ≫ S.inv ≫ s.hom
  simp only [Category.assoc, CategoryTheory.Iso.hom_inv_id_assoc]
  rw [← Category.assoc (F.map s.hom) tN, hNat, Category.assoc, hRec]
  simp only [CategoryTheory.Functor.mapIso_hom]
  conv_rhs =>
    rw [← Category.assoc (F.map S.hom) dY, hSem]
  simp only [Category.assoc, CategoryTheory.Iso.hom_inv_id_assoc]

private theorem iso_recovery_naturality {C : Type*} [Category C]
    (F : C ⥤ C) {X Y Z : C} (s : X ≅ Y) (f : X ⟶ Z)
    (dX : F.obj X ⟶ X) (dY : F.obj Y ⟶ Y) (dZ : F.obj Z ⟶ Z)
    (hRec : F.map s.hom ≫ dY = dX ≫ s.hom)
    (hNat : F.map f ≫ dZ = dX ≫ f) :
    dY ≫ s.inv ≫ f = F.map (s.inv ≫ f) ≫ dZ := by
  apply (cancel_epi (F.mapIso s).hom).mp
  simp only [CategoryTheory.Functor.mapIso_hom, CategoryTheory.Functor.map_comp,
    Category.assoc]
  rw [← Category.assoc (F.map s.hom) dY, hRec]
  simp only [Category.assoc, CategoryTheory.Iso.hom_inv_id_assoc]
  rw [← Category.assoc (F.map s.hom) (F.map s.inv), ← CategoryTheory.Functor.map_comp,
    CategoryTheory.Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp]
  exact hNat.symm

namespace Langlands.GroupScheme.IntegralModel

open Descent

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  (M : IntegralModel R K G)
  (A L : Type u) [CommRing A] [IsDomain A] [Field L]
  [Algebra R A] [Algebra A L] [IsFractionRing A L]
  [Algebra K L] [Algebra R L] [IsScalarTower R A L] [IsScalarTower R K L]
  (a : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of A))
  (ha : a ≫ Spec.algebraMap R A = Spec.algebraMap R A)
  (v : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of L))
  (hv : v ≫ Spec.algebraMap K L = Spec.algebraMap K L)
  (hva : v ≫ Spec.algebraMap A L = Spec.algebraMap A L ≫ a)

/-- The canonical coefficient comparison of the pullback model extends the
canonical coefficient comparison of its prescribed generic group. -/
def baseChangeDescentIso :
    ((M.baseChange A L).twist a v hva).Iso (M.baseChange A L)
      (descentBaseChangeIso (Spec.algebraMap K L) v hv G) where
  iso := descentBaseChangeIso (Spec.algebraMap R A) a ha M.group
  generic_comm := by
    change (GroupScheme.baseChange (Spec.algebraMap A L)).map
        (descentBaseChangeIso (Spec.algebraMap R A) a ha M.group).hom ≫
          (M.baseChangeGenericIso A L).hom =
      ((squareComparison (Spec.algebraMap A L) v a (Spec.algebraMap A L)
        hva ((GroupScheme.baseChange (Spec.algebraMap R A)).obj M.group)).inv ≫
          (GroupScheme.baseChange v).map (M.baseChangeGenericIso A L).hom) ≫
            (descentBaseChangeIso (Spec.algebraMap K L) v hv G).hom
    rw [baseChangeGenericIso_eq_square]
    simp only [baseChangeSquareIso, CategoryTheory.Iso.trans_hom,
      CategoryTheory.Functor.mapIso_hom, CategoryTheory.Functor.map_comp, Category.assoc]
    rw [descentBaseChangeIso_naturality]
    conv_rhs =>
      rw [← Category.assoc _ _
        ((GroupScheme.baseChange (Spec.algebraMap K L)).map M.genericIso.hom)]
    rw [squareComparison_semilinear (Spec.algebraMap R A) (Spec.algebraMap A L)
        (Spec.algebraMap R K) (Spec.algebraMap K L)
        (solutionCoefficientSquare (R := R) (K := K) (A := A) (L := L))
        a ha v hv hva M.group]
    simp only [Category.assoc, CategoryTheory.Iso.inv_hom_id_assoc]

variable
  {N : IntegralModel A L ((GroupScheme.baseChange (Spec.algebraMap K L)).obj G)}
  (s : (M.baseChange A L).Iso N (CategoryTheory.Iso.refl _))
  (ψ : (N.twist a v hva).Iso N
    (descentBaseChangeIso (Spec.algebraMap K L) v hv G))

/-- Any actual comparison with the prescribed generic map equals canonical
coefficient transport through the recovery isomorphism. -/
theorem recovery_descent_comm :
    (GroupScheme.baseChange a).map s.iso.hom ≫ ψ.iso.hom =
      (descentBaseChangeIso (Spec.algebraMap R A) a ha M.group).hom ≫ s.iso.hom := by
  let p : ((M.baseChange A L).twist a v hva).Hom N
      (descentBaseChangeIso (Spec.algebraMap K L) v hv G).hom :=
    { hom := (GroupScheme.baseChange a).map s.iso.hom ≫ ψ.iso.hom
      generic_comm := by
        simpa only [Hom.comp, Hom.twist, Iso.toHom,
          CategoryTheory.Iso.refl_hom, CategoryTheory.Functor.map_id, Category.id_comp] using
          ((s.toHom.twist a v hva).comp ψ.toHom).generic_comm }
  let q : ((M.baseChange A L).twist a v hva).Hom N
      (descentBaseChangeIso (Spec.algebraMap K L) v hv G).hom :=
    { hom := (descentBaseChangeIso (Spec.algebraMap R A) a ha M.group).hom ≫ s.iso.hom
      generic_comm := by
        simpa only [Hom.comp, baseChangeDescentIso, Iso.toHom,
          CategoryTheory.Iso.refl_hom, Category.comp_id] using
          ((M.baseChangeDescentIso A L a ha v hv hva).toHom.comp s.toHom).generic_comm }
  exact p.hom_eq q

variable [IsLocalRing R] [IsLocalRing A]
  (e : Spec (CommRingCat.of (IsLocalRing.ResidueField A)) ⟶
    Spec (CommRingCat.of (IsLocalRing.ResidueField R)))
  (he : residueBaseMap A ≫ Spec.algebraMap R A = e ≫ residueBaseMap R)

/-- Specialize an actual coefficient recovery using the original residue
coefficient square. -/
def residueRecoveryIso :
    (GroupScheme.baseChange e).obj M.specialFibre ≅ N.specialFibre :=
  (squareComparison (Spec.algebraMap R A) (residueBaseMap A) (residueBaseMap R)
    e he M.group).symm ≪≫ (GroupScheme.baseChange (residueBaseMap A)).mapIso s.iso

/-- Pull an actual downstairs special-fibre map to the recovered model. -/
def residueDescendedMap {H : GroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField R)))}
    (q : M.specialFibre ⟶ H) :
    N.specialFibre ⟶ (GroupScheme.baseChange e).obj H :=
  (residueRecoveryIso M A L s e he).inv ≫ (GroupScheme.baseChange e).map q

variable
  (r : Spec (CommRingCat.of (IsLocalRing.ResidueField A)) ⟶
    Spec (CommRingCat.of (IsLocalRing.ResidueField A)))
  (hre : r ≫ e = e)
  (hra : r ≫ residueBaseMap A = residueBaseMap A ≫ a)

include ha

/-- Residue specialization of any actual comparison with the canonical
generic map intertwines recovery with canonical residue transport. -/
theorem recovery_residue_descent_comm :
    (GroupScheme.baseChange r).map (residueRecoveryIso M A L s e he).hom ≫
        (Iso.residueTwistIso N N a v hva
          (descentBaseChangeIso (Spec.algebraMap K L) v hv G) ψ r hra).hom =
      (descentBaseChangeIso e r hre M.specialFibre).hom ≫
        (residueRecoveryIso M A L s e he).hom := by
  simp only [residueRecoveryIso, Iso.residueTwistIso, CategoryTheory.Iso.trans_hom,
    CategoryTheory.Iso.symm_hom, CategoryTheory.Functor.mapIso_hom]
  exact recovery_square_comm (GroupScheme.baseChange r)
    (squareComparison (Spec.algebraMap R A) (residueBaseMap A) (residueBaseMap R)
      e he M.group)
    ((GroupScheme.baseChange (residueBaseMap A)).mapIso s.iso)
    (squareComparison (residueBaseMap A) r a (residueBaseMap A) hra
      ((GroupScheme.baseChange (Spec.algebraMap R A)).obj M.group)).hom
    (squareComparison (residueBaseMap A) r a (residueBaseMap A) hra N.group).hom
    ((GroupScheme.baseChange (residueBaseMap A)).map
      ((GroupScheme.baseChange a).map s.iso.hom))
    ((GroupScheme.baseChange (residueBaseMap A)).map
      (descentBaseChangeIso (Spec.algebraMap R A) a ha M.group).hom)
    ((GroupScheme.baseChange (residueBaseMap A)).map ψ.iso.hom)
    (descentBaseChangeIso e r hre M.specialFibre).hom
    (squareComparison_naturality (residueBaseMap A) r a (residueBaseMap A)
      hra s.iso.hom)
    (by
      simp only [CategoryTheory.Functor.mapIso_hom]
      rw [← CategoryTheory.Functor.map_comp,
        recovery_descent_comm M A L a ha v hv hva s ψ,
        CategoryTheory.Functor.map_comp])
    (squareComparison_semilinear (Spec.algebraMap R A) (residueBaseMap A)
      (residueBaseMap R) e he a ha r hre hra M.group)

/-- Any actual special-fibre map pulled from downstairs satisfies the literal
coefficient square with the constructed recovered comparison. -/
theorem residueDescendedMap_naturality
    {H : GroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField R)))}
    (q : M.specialFibre ⟶ H) :
    (Iso.residueTwistIso N N a v hva
      (descentBaseChangeIso (Spec.algebraMap K L) v hv G) ψ r hra).hom ≫
        residueDescendedMap M A L s e he q =
      (GroupScheme.baseChange r).map (residueDescendedMap M A L s e he q) ≫
        (descentBaseChangeIso e r hre H).hom := by
  exact iso_recovery_naturality (GroupScheme.baseChange r)
    (residueRecoveryIso M A L s e he) ((GroupScheme.baseChange e).map q)
    (descentBaseChangeIso e r hre M.specialFibre).hom
    (Iso.residueTwistIso N N a v hva
      (descentBaseChangeIso (Spec.algebraMap K L) v hv G) ψ r hra).hom
    (descentBaseChangeIso e r hre H).hom
    (recovery_residue_descent_comm M A L a ha v hv hva s ψ e he r hre hra)
    (descentBaseChangeIso_naturality e r hre q)

/-- Recovered integral comparisons are natural on every special-fibre map
obtained by actual coefficient pullback from downstairs. -/
def RecoveredResidueDescentStatement : Prop :=
  ∀ (H : GroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField R))))
    (q : M.specialFibre ⟶ H),
    (Iso.residueTwistIso N N a v hva
      (descentBaseChangeIso (Spec.algebraMap K L) v hv G) ψ r hra).hom ≫
        residueDescendedMap M A L s e he q =
      (GroupScheme.baseChange r).map (residueDescendedMap M A L s e he q) ≫
        (descentBaseChangeIso e r hre H).hom

theorem recoveredResidueDescent :
    RecoveredResidueDescentStatement M A L a v hv hva s ψ e he r hre hra := by
  intro H q
  exact residueDescendedMap_naturality M A L a ha v hv hva s ψ e he r hre hra q

end Langlands.GroupScheme.IntegralModel
