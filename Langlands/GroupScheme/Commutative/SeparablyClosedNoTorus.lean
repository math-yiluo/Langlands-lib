import Langlands.GroupScheme.Commutative.NoTorus
import Langlands.GroupScheme.Torus.CocharacterBaseChange
import Langlands.GroupScheme.GeometricConnectedness
import Langlands.GroupScheme.Unipotent.FieldReflectionProof
import Mathlib.CategoryTheory.HomCongr

/-! # Commutative groups without cocharacters over separably closed fields -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CommutativeNoTorus

variable {k : Type u} [Field k]
    (Z : CommGroupScheme (Spec (CommRingCat.of k)))

section Cocharacters

variable [IsAffine Z.toGrp.X.left] [LocallyOfFiniteType Z.toGrp.X.hom]
    (K : Type u) [Field K] [Algebra k K] [IsPurelyInseparable k K]

/-- The actual cocharacter sets before and after purely inseparable extension
are equivalent for an affine finite type commutative target. -/
def cocharacterEquivOfIsPurelyInseparable :
    ((Gm (Spec (CommRingCat.of k))).toGrp ⟶ Z.toGrp) ≃
      ((Gm (Spec (CommRingCat.of K))).toGrp ⟶
        ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj Z).toGrp) :=
  let e : (Gm (Spec (CommRingCat.of k))).toGrp ≅
      (Diagonalizable.groupScheme (CommRingCat.of k) (PUnit.{u+1} → ℤ)).toGrp :=
    splitTorus.gmIso _ ≪≫
      (Diagonalizable.splitIso (CommRingCat.of k)
        (AddEquiv.refl (PUnit.{u+1} → ℤ))).symm
  let eK : (Gm (Spec (CommRingCat.of K))).toGrp ≅
      (Diagonalizable.groupScheme (CommRingCat.of K) (PUnit.{u+1} → ℤ)).toGrp :=
    splitTorus.gmIso _ ≪≫
      (Diagonalizable.splitIso (CommRingCat.of K)
        (AddEquiv.refl (PUnit.{u+1} → ℤ))).symm
  (e.homCongr (Iso.refl Z.toGrp)).trans
    ((CocharacterDatum.homEquivOfIsPurelyInseparable (Z := Z)
      (Λ := PUnit.{u+1} → ℤ) K).trans
      (eK.symm.homCongr (Iso.refl _)))

@[simp]
theorem cocharacterEquivOfIsPurelyInseparable_zero :
    cocharacterEquivOfIsPurelyInseparable Z K 0 = 0 := by
  simp only [cocharacterEquivOfIsPurelyInseparable, Equiv.trans_apply,
    Iso.homCongr_apply, comp_zero, zero_comp,
    CocharacterDatum.homEquivOfIsPurelyInseparable_zero]

end Cocharacters

variable [Smooth Z.toGrp.X.hom] [IsAffineHom Z.toGrp.X.hom]
    [ConnectedSpace Z.toGrp.X.left]

/-- Over a separably closed field, a smooth connected affine commutative group
with no nontrivial cocharacters is unipotent. -/
theorem isUnipotent_of_gm_hom_eq_zero_of_isSepClosed [IsSepClosed k]
    (hZ : ∀ φ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ Z.toGrp, φ = 0) :
    IsUnipotent Z.toGrp := by
  let K := AlgebraicClosure k
  let ZK := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj Z
  have : IsAffine Z.toGrp.X.left := isAffine_of_isAffineHom Z.toGrp.X.hom
  have : ConnectedSpace ZK.toGrp.X.left :=
    GroupScheme.connectedSpace_baseChange_of_smooth_affine Z.toGrp (algebraBaseMap k K)
  have : Smooth ZK.toGrp.X.hom := by
    change Smooth (pullback.snd Z.toGrp.X.hom (algebraBaseMap k K))
    infer_instance
  have : IsAffineHom ZK.toGrp.X.hom := by
    change IsAffineHom (pullback.snd Z.toGrp.X.hom (algebraBaseMap k K))
    infer_instance
  apply IsUnipotent.of_baseChange (K := K)
  apply isUnipotent_of_gm_hom_eq_zero ZK
  exact CocharacterDatum.gm_hom_eq_zero_of_isPurelyInseparable (Z := Z) K hZ

/-- The commutative separably closed instance of the no-torus implication. -/
theorem isUnipotent_of_no_torus_of_isSepClosed [IsSepClosed k]
    (hZ : ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))),
      IsTorus T.toGrp → ∀ φ : T.toGrp ⟶ Z.toGrp, SubgroupFunctor.range φ = ⊥) :
    IsUnipotent Z.toGrp := by
  apply isUnipotent_of_gm_hom_eq_zero_of_isSepClosed Z
  intro φ
  exact SubgroupFunctor.eq_zero_of_range_eq_bot
    (hZ (Gm (Spec (CommRingCat.of k))) isSplitTorus_gm.isTorus φ)

end Langlands.GroupScheme.CommutativeNoTorus
