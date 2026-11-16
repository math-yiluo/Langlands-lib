import Langlands.GroupScheme.IntegralModel.CoefficientSpecialFibreTorus
import Langlands.GroupScheme.Torus.MaximalBaseChangeForwardProof
import Langlands.GroupScheme.Torus.MaximalSplitComparison

/-! # Maximal residue tori under actual coefficient extension -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme.IntegralModel

section ResidueComparison

variable {R A : Type u} [CommRing R] [CommRing A]
  [IsLocalRing R] [IsLocalRing A] [Algebra R A]
  [IsLocalHom (algebraMap R A)]

/-- The canonical source comparison between extending a residue torus and
taking the residue fibre after integral coefficient extension. -/
def residueTorusCoefficientIso
    (T : CommGroupScheme (Spec (CommRingCat.of R))) :
    ((CommGroupScheme.baseChange
      (Spec.algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField A))).obj
      ((CommGroupScheme.baseChange (residueBaseMap R)).obj T)).toGrp ≅
    ((CommGroupScheme.baseChange (residueBaseMap A)).obj
      ((CommGroupScheme.baseChange (Spec.algebraMap R A)).obj T)).toGrp :=
  Descent.squareComparison (residueBaseMap R)
    (Spec.algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField A))
    (Spec.algebraMap R A) (residueBaseMap A) residue_coefficient_square T.toGrp

end ResidueComparison

section Coefficients

variable {R K A : Type u}
  [CommRing R] [IsDomain R] [IsLocalRing R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  [CommRing A] [IsLocalRing A]
  [Algebra R A] [IsLocalHom (algebraMap R A)]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  (M : IntegralModel R K G) [Smooth M.group.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of R))}
  (i : T.toGrp ⟶ M.group)

/-- A maximal actual residue torus stays maximal in the actual special fibre
of the coefficient-extended model. -/
theorem isMaximalTorus_residue_baseChange
    (hi : IsMaximalTorus (T := (CommGroupScheme.baseChange (residueBaseMap R)).obj T)
      ((GroupScheme.baseChange (residueBaseMap R)).map i)) :
    IsMaximalTorus
      (T := (CommGroupScheme.baseChange (residueBaseMap A)).obj
        ((CommGroupScheme.baseChange (Spec.algebraMap R A)).obj T))
      ((GroupScheme.baseChange (residueBaseMap A)).map
        ((GroupScheme.baseChange (Spec.algebraMap R A)).map i)) := by
  let : Smooth M.specialFibre.X.hom := by
    change Smooth (pullback.snd M.group.X.hom (residueBaseMap R))
    infer_instance
  let : IsAffineHom M.specialFibre.X.hom := by
    change IsAffineHom (pullback.snd M.group.X.hom (residueBaseMap R))
    infer_instance
  let eT := residueTorusCoefficientIso (A := A) T
  let eM := Descent.squareComparison (residueBaseMap R)
    (Spec.algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField A))
    (Spec.algebraMap R A) (residueBaseMap A) residue_coefficient_square M.group
  have hmax := maximalTorusBaseChangeForward
    (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField A) M.specialFibre
    ((CommGroupScheme.baseChange (residueBaseMap R)).obj T)
    ((GroupScheme.baseChange (residueBaseMap R)).map i) hi
  have hcomm :
      (GroupScheme.baseChange
          (Spec.algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField A))).map
          ((GroupScheme.baseChange (residueBaseMap R)).map i) ≫ eM.hom =
        eT.hom ≫ (GroupScheme.baseChange (residueBaseMap A)).map
          ((GroupScheme.baseChange (Spec.algebraMap R A)).map i) :=
    Descent.squareComparison_naturality (residueBaseMap R)
      (Spec.algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField A))
      (Spec.algebraMap R A) (residueBaseMap A) residue_coefficient_square i
  have hactual :
      (GroupScheme.baseChange (residueBaseMap A)).map
          ((GroupScheme.baseChange (Spec.algebraMap R A)).map i) =
        eT.inv ≫ (GroupScheme.baseChange
          (Spec.algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField A))).map
          ((GroupScheme.baseChange (residueBaseMap R)).map i) ≫ eM.hom := by
    rw [hcomm, Iso.inv_hom_id_assoc]
  rw [hactual]
  have hmax' : IsMaximalTorus
      (T := (CommGroupScheme.baseChange
        (Spec.algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField A))).obj
        ((CommGroupScheme.baseChange (residueBaseMap R)).obj T))
      ((GroupScheme.baseChange
          (Spec.algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField A))).map
          ((GroupScheme.baseChange (residueBaseMap R)).map i) ≫ eM.hom) :=
    IsMaximalTorus.comp_iso
      (T := (CommGroupScheme.baseChange
        (Spec.algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField A))).obj
        ((CommGroupScheme.baseChange (residueBaseMap R)).obj T)) hmax eM
  exact IsMaximalTorus.iso_comp
    (T := (CommGroupScheme.baseChange
      (Spec.algebraMap (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField A))).obj
      ((CommGroupScheme.baseChange (residueBaseMap R)).obj T))
    (T' := (CommGroupScheme.baseChange (residueBaseMap A)).obj
      ((CommGroupScheme.baseChange (Spec.algebraMap R A)).obj T))
    eT.symm hmax'

/-- If the coefficient-extended integral torus is split, its actual residue
map is maximal split. -/
theorem isMaximalSplitTorus_residue_baseChange
    (hi : IsMaximalTorus (T := (CommGroupScheme.baseChange (residueBaseMap R)).obj T)
      ((GroupScheme.baseChange (residueBaseMap R)).map i))
    (hT : IsSplitTorus
      ((CommGroupScheme.baseChange (Spec.algebraMap R A)).obj T).toGrp) :
    IsMaximalSplitTorus
      (T := (CommGroupScheme.baseChange (residueBaseMap A)).obj
        ((CommGroupScheme.baseChange (Spec.algebraMap R A)).obj T))
      ((GroupScheme.baseChange (residueBaseMap A)).map
        ((GroupScheme.baseChange (Spec.algebraMap R A)).map i)) :=
  (M.isMaximalTorus_residue_baseChange (A := A) i hi).isMaximalSplitTorus
    (hT.baseChange (residueBaseMap A))

end Coefficients

section Bounded

variable {R K A L : Type u}
  [CommRing R] [IsDomain R] [IsLocalRing R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  [CommRing A] [IsDomain A] [Field L]
  [IsNoetherianRing A] [ValuationRing A] [HenselianLocalRing A]
  [Algebra R A] [IsLocalHom (algebraMap R A)]
  [Algebra A L] [IsFractionRing A L]
  [Algebra K L] [Algebra R L] [IsScalarTower R A L] [IsScalarTower R K L]
  [IsAlgClosed (IsLocalRing.ResidueField A)]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  {M N : IntegralModel R K G}
  [Smooth M.group.X.hom] [Smooth N.group.X.hom]
  [ConnectedSpace M.specialFibre.X.left]

/-- A bounded generic maximal split torus makes an integral lift of any
source-residue maximal torus maximal split in the actual coefficient-extended
target residue fibre, once the lifted integral torus splits there. -/
theorem Hom.isMaximalSplitTorus_residue_baseChange_of_coefficient_bounded
    (φ : M.Hom N (𝟙 G))
    (hG : IsConnectedReductive
      ((GroupScheme.baseChange (Spec.algebraMap K L)).obj G))
    {Γ₀ : Type u} [LinearOrderedCommGroupWithZero Γ₀]
    (v : Valuation L Γ₀) (hv : ∀ a : Aˣ, v (algebraMap A L (a : A)) = 1)
    {T₀ : CommGroupScheme (Spec (CommRingCat.of L))}
    {i₀ : T₀.toGrp ⟶ (GroupScheme.baseChange (Spec.algebraMap K L)).obj G}
    (hi₀ : IsMaximalSplitTorus i₀)
    (hb : (Langlands.Geometry.Building.characterValuationKernel v T₀.toGrp).map
      (rationalPoints.map i₀) ≤ (M.baseChange A L).integralPoints)
    {T : CommGroupScheme (Spec (CommRingCat.of R))}
    (i : T.toGrp ⟶ M.group)
    (hi : IsMaximalTorus (T := (CommGroupScheme.baseChange (residueBaseMap R)).obj T)
      ((GroupScheme.baseChange (residueBaseMap R)).map i))
    (hT : IsSplitTorus
      ((CommGroupScheme.baseChange (Spec.algebraMap R A)).obj T).toGrp) :
    IsMaximalSplitTorus
      (T := (CommGroupScheme.baseChange (residueBaseMap A)).obj
        ((CommGroupScheme.baseChange (Spec.algebraMap R A)).obj T))
      ((GroupScheme.baseChange (residueBaseMap A)).map
        ((GroupScheme.baseChange (Spec.algebraMap R A)).map (i ≫ φ.hom))) := by
  have hmax := φ.isMaximalTorus_specialFibreMap_of_coefficient_bounded
    hG v hv hi₀ hb hi
  have hmax' : IsMaximalTorus
      (T := (CommGroupScheme.baseChange (residueBaseMap R)).obj T)
      ((GroupScheme.baseChange (residueBaseMap R)).map (i ≫ φ.hom)) := by
    simpa only [Functor.map_comp, Hom.specialFibreMap] using hmax
  exact N.isMaximalSplitTorus_residue_baseChange (A := A)
    (i ≫ φ.hom) hmax' hT

end Bounded

end Langlands.GroupScheme.IntegralModel
