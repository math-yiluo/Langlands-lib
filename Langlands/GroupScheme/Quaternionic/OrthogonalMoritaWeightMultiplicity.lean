import Langlands.GroupScheme.Quaternionic.OrthogonalMoritaWeightTransport
import Langlands.GroupScheme.Torus.SplitLatticeBaseChange

/-! # Character eigenbases and original division-algebra weight multiplicities -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Module
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.PointTopology

section CoefficientPoints

variable {K L S : Type u} [CommRing K] [CommRing L] [CommRing S]
  [Algebra K L] [Algebra K S] [Algebra L S] [IsScalarTower K L S]

/-- Compatible affine point base change is natural in the group scheme. -/
theorem affinePointsBaseChangeMulEquiv_comp
    {G H : GroupScheme (Spec (CommRingCat.of K))} (f : G ⟶ H)
    (t : G.affinePoints (CommAlgCat.of (CommRingCat.of K) S)) :
    affinePointsBaseChangeMulEquiv K L S H (t ≫ f.hom.hom) =
      affinePointsBaseChangeMulEquiv K L S G t ≫
        ((GroupScheme.baseChange (Spec.algebraMap K L)).map f).hom.hom := by
  apply (affinePointsBaseChangeMulEquiv K L S H).symm.injective
  rw [MulEquiv.symm_apply_apply]
  apply Over.OverMorphism.ext
  rw [affinePointsBaseChangeMulEquiv_symm_left]
  change (t ≫ f.hom.hom).left =
    (baseChangePointsEquiv (Spec.algebraMap K L) H (ringTest L S)
      (affinePointsBaseChangeMulEquiv K L S G t ≫
        ((GroupScheme.baseChange (Spec.algebraMap K L)).map f).hom.hom)).left
  rw [baseChangePointsEquiv_comp]
  simp only [Over.comp_left, baseChangePointsEquiv_left]
  have ht := congrArg (fun x => x.left)
    ((affinePointsBaseChangeMulEquiv K L S G).symm_apply_apply t)
  rw [affinePointsBaseChangeMulEquiv_symm_left] at ht
  exact congrArg (fun x => x ≫ f.hom.hom.left) ht.symm

/-- The canonical affine base change of the multiplicative group preserves
the coefficient unit. -/
theorem Gm.affineUnitsEquiv_baseChange
    (t : GroupScheme.affinePoints (GroupScheme.Gm (Spec (CommRingCat.of K))).toGrp
      (CommAlgCat.of (CommRingCat.of K) S)) :
    Gm.affineUnitsEquiv (CommRingCat.of L) (CommAlgCat.of (CommRingCat.of L) S)
        (affinePointsBaseChangeMulEquiv K L S
          (GroupScheme.Gm (Spec (CommRingCat.of K))).toGrp t ≫
            (Gm.baseChangeIso (Spec.algebraMap K L)).hom.hom.hom) =
      Gm.affineUnitsEquiv (CommRingCat.of K) (CommAlgCat.of (CommRingCat.of K) S) t := by
  apply Units.ext
  change (Scheme.ΓSpecIso (CommRingCat.of S)).hom
      (Gm.pointsEquiv (Spec (CommRingCat.of L)) _
        (affinePointsBaseChangeMulEquiv K L S _ t ≫
          (Gm.baseChangeIso (Spec.algebraMap K L)).hom.hom.hom)).val =
    (Scheme.ΓSpecIso (CommRingCat.of S)).hom (Gm.pointsEquiv _ _ t).val
  rw [Gm.pointsEquiv_baseChangeIso_hom, Gm.baseChangeUnitsEquiv_apply]
  congr 2
  apply Units.ext
  have ht := congrArg (fun x => x.left)
    ((affinePointsBaseChangeMulEquiv K L S
      (GroupScheme.Gm (Spec (CommRingCat.of K))).toGrp).symm_apply_apply t)
  simp only [affinePointsBaseChangeMulEquiv_symm_left] at ht
  change _ = (Gm.pointsEquiv _ _ t).val
  have hp := Gm.pointsEquiv_naturality (Spec (CommRingCat.of K))
    (ringTestRestrictScalarsIso K L S).hom t
  have hpoint : baseChangePointsEquiv (Spec.algebraMap K L)
      (GroupScheme.Gm (Spec (CommRingCat.of K))).toGrp (ringTest L S)
      (affinePointsBaseChangeMulEquiv K L S _ t) =
      (ringTestRestrictScalarsIso K L S).hom ≫ t := by
    apply Over.OverMorphism.ext
    simpa only [baseChangePointsEquiv_left, Over.comp_left,
      ringTestRestrictScalarsIso_hom_left, Category.id_comp] using ht
  erw [hpoint]
  convert congrArg Units.val hp using 1
  all_goals rfl

/-- Evaluating the base-changed cocharacter uses the same coefficient unit. -/
theorem affinePointsBaseChangeMulEquiv_cocharacter
    {G : GroupScheme (Spec (CommRingCat.of K))}
    (f : (GroupScheme.Gm (Spec (CommRingCat.of K))).toGrp ⟶ G)
    (t : GroupScheme.affinePoints
      (GroupScheme.Gm (Spec (CommRingCat.of K))).toGrp
      (CommAlgCat.of (CommRingCat.of K) S)) :
    affinePointsBaseChangeMulEquiv K L S G (t ≫ f.hom.hom) =
      (affinePointsBaseChangeMulEquiv K L S
          (GroupScheme.Gm (Spec (CommRingCat.of K))).toGrp t ≫
        (Gm.baseChangeIso (Spec.algebraMap K L)).hom.hom.hom) ≫
          (Dynamic.baseChangeCocharacter (Spec.algebraMap K L) f).hom.hom := by
  rw [affinePointsBaseChangeMulEquiv_comp]
  have hf : (Gm.baseChangeIso (Spec.algebraMap K L)).hom ≫
      Dynamic.baseChangeCocharacter (Spec.algebraMap K L) f =
      (GroupScheme.baseChange (Spec.algebraMap K L)).map f := by
    simp only [Dynamic.baseChangeCocharacter, Iso.hom_inv_id_assoc]
  rw [← hf, Grp.comp_hom_hom, Category.assoc]

end CoefficientPoints

section CharacterEvaluation

variable {K : Type u} [CommRing K] [IsDomain K]
  (T : CommGroupScheme (Spec (CommRingCat.of K)))

/-- The cocharacter weights obtained by pairing a family of characters with
a fixed cocharacter. -/
def characterWeights {I : Type*} (chi : I → characterLattice T)
    (nu : cocharacterLattice T) : I → ℤ :=
  fun i => latticePairing T (chi i) nu

/-- A character on a cocharacter evaluates as the integer lattice pairing
on every coefficient algebra. -/
theorem affineUnitsEquiv_character_cocharacter
    (chi : characterLattice T) (nu : cocharacterLattice T)
    (R : CommAlgCat.{u} (CommRingCat.of K))
    (t : GroupScheme.affinePoints
      (GroupScheme.Gm (Spec (CommRingCat.of K))).toGrp R) :
    Gm.affineUnitsEquiv (CommRingCat.of K) R
        ((t ≫ (CommGroupScheme.groupHom nu).hom.hom) ≫
          (CommGroupScheme.groupHom chi).hom.hom) =
      Gm.affineUnitsEquiv (CommRingCat.of K) R t ^ latticePairing T chi nu := by
  rw [← comp_groupHom_comp, eq_gmEndEquiv_zsmul K (nu ≫ chi),
    Gm.comp_zsmul_id, map_zpow]
  rfl

end CharacterEvaluation

namespace Quaternionic.OrthogonalMorita

variable {K D L : Type u} [Field K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Field L] [Algebra K L]
  {sigma : FirstKindInvolution K D} {m n degree : ℕ}
  {q : sigma.QuadraticForms (Fin m)}

/-- A supplied equality of the actual base-changed group morphisms gives
the corresponding equality on every compatible coefficient point. -/
theorem splitPoint_cocharacter
    (e : OrthogonalMoritaComparison sigma q L degree n)
    (f : (GroupScheme.Gm (Spec (CommRingCat.of K))).toGrp ⟶ sigma.isometryGroup q)
    (T : CommGroupScheme (Spec (CommRingCat.of L)))
    (nu : cocharacterLattice T)
    (rho : T.toGrp ⟶ OrthogonalMatrix.groupScheme (Fin n) (CommRingCat.of L))
    (hf : Dynamic.baseChangeCocharacter (Spec.algebraMap K L) f ≫ e.groupIso.hom =
      CommGroupScheme.groupHom nu ≫ rho)
    (S : Type u) [CommRing S] [Algebra K S] [Algebra L S]
    [IsScalarTower K L S]
    (t : GroupScheme.affinePoints
      (GroupScheme.Gm (Spec (CommRingCat.of K))).toGrp
      (CommAlgCat.of (CommRingCat.of K) S)) :
    splitPoint sigma q e.groupIso S (t ≫ f.hom.hom) =
      ((affinePointsBaseChangeMulEquiv K L S
          (GroupScheme.Gm (Spec (CommRingCat.of K))).toGrp t ≫
        (Gm.baseChangeIso (Spec.algebraMap K L)).hom.hom.hom) ≫
          (CommGroupScheme.groupHom nu).hom.hom) ≫ rho.hom.hom := by
  unfold splitPoint
  rw [affinePointsBaseChangeMulEquiv_cocharacter,
    Category.assoc, ← Grp.comp_hom_hom, hf, Grp.comp_hom_hom, Category.assoc]
  simp only [Category.assoc]

/-- A supplied all-coefficient character eigenbasis of the actual split row
representation computes the original division-algebra weight multiplicities. -/
theorem weight_card_of_characterBasis
    (e : OrthogonalMoritaComparison sigma q L degree n)
    (hdegree : 0 < degree) (hdim : finrank K D = degree ^ 2)
    (f : (GroupScheme.Gm (Spec (CommRingCat.of K))).toGrp ⟶ sigma.isometryGroup q)
    (T : CommGroupScheme (Spec (CommRingCat.of L)))
    (nu : cocharacterLattice T)
    (rho : T.toGrp ⟶ OrthogonalMatrix.groupScheme (Fin n) (CommRingCat.of L))
    (hf : Dynamic.baseChangeCocharacter (Spec.algebraMap K L) f ≫ e.groupIso.hom =
      CommGroupScheme.groupHom nu ≫ rho)
    {I : Type*} [Fintype I]
    (chi : I → characterLattice T) (b : Basis I L ((Fin n ⊕ Fin n) → L))
    (hb : ∀ (R : CommAlgCat.{u} (CommRingCat.of L))
        (t : GroupScheme.affinePoints T.toGrp R) (i : I),
      Matrix.vecMul (fun x => algebraMap L R (b i x))
          ((MatrixRepresentation.affineMatrix
            (OrthogonalMatrix.inclusion (Fin n) (CommRingCat.of L))
            R (t ≫ rho.hom.hom))⁻¹ :
              Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) =
        ((Gm.affineUnitsEquiv (CommRingCat.of L) R
          (t ≫ (CommGroupScheme.groupHom (chi i)).hom.hom) : Rˣ) : R) •
            (fun x => algebraMap L R (b i x))) (c : ℤ) :
    Nat.card {i // latticePairing T (chi i) nu = c} =
      degree * finrank D (sigma.cocharacterWeightSpace q f c) := by
  refine weight_card_of_rowBasis e hdegree hdim f b
    (characterWeights T chi nu) ?_ c
  intro p
  refine rowBasis_mem_of_split_eigen e f b
    (characterWeights T chi nu) ?_ p
  intro S _ _ _ _ t i
  let tL := affinePointsBaseChangeMulEquiv K L S
      (GroupScheme.Gm (Spec (CommRingCat.of K))).toGrp t ≫
    (Gm.baseChangeIso (Spec.algebraMap K L)).hom.hom.hom
  have h := hb (CommAlgCat.of (CommRingCat.of L) S)
    (tL ≫ (CommGroupScheme.groupHom nu).hom.hom) i
  rw [affineUnitsEquiv_character_cocharacter] at h
  dsimp only [tL] at h
  rw [Gm.affineUnitsEquiv_baseChange] at h
  simpa only [characterWeights, splitPoint_cocharacter e f T nu rho hf] using h

end Quaternionic.OrthogonalMorita

end Langlands.GroupScheme
