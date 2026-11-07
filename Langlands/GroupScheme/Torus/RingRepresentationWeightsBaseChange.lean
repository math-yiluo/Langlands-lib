import Langlands.GroupScheme.Torus.RingRepresentationWeights
import Langlands.GroupScheme.Rational.ValuedRepresentationBaseChange
import Langlands.LinearAlgebra.LocalIdempotentMatrix
import Mathlib.Algebra.MonoidAlgebra.MapDomain

/-! # Base change of the actual split-torus representation projectors -/

noncomputable section
universe u
open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.MatrixRepresentation

variable {R R' : CommRingCat.{u}} {G : GroupScheme (Spec R)}
  {n : Type} [Fintype n] [DecidableEq n]

/-- Affine coefficient matrices commute with a map of test rings over a base change. -/
theorem affineMatrix_baseChange_map (ρ : MatrixRepresentation G n) (f : R ⟶ R')
    (B : CommAlgCat R) (B' : CommAlgCat R')
    (φ : CommRingCat.of B ⟶ CommRingCat.of B')
    (a : (Over.map (Spec.map f)).obj ((algSpec R').obj (op B')) ⟶
      (algSpec R).obj (op B)) (ha : a.left = Spec.map φ)
    (x : (algSpec R').obj (op B') ⟶ ((GroupScheme.baseChange (Spec.map f)).obj G).X)
    (y : (algSpec R).obj (op B) ⟶ G.X)
    (hxy : GroupScheme.baseChangePointsEquiv (Spec.map f) G _ x = a ≫ y) :
    (ρ.baseChange (Spec.map f)).affineMatrix B' x =
      Matrix.GeneralLinearGroup.map φ.hom (ρ.affineMatrix B y) := by
  have hm := pointMatrix_baseChange ρ (Spec.map f) ((algSpec R').obj (op B')) x
  rw [hxy, pointMatrix_naturality, pointMatrix_eq_affineMatrix,
    pointMatrix_eq_affineMatrix, Corepresented.affineSectionsIso_inv_ringHom,
    Corepresented.affineSectionsIso_inv_ringHom] at hm
  simp only [ha] at hm
  apply Units.ext
  ext i j
  have hij := congrArg
    (fun z : Matrix.GeneralLinearGroup n Γ(Spec (CommRingCat.of B'), ⊤) =>
      (Scheme.ΓSpecIso (CommRingCat.of B')).hom (z i j)) hm
  change (Scheme.ΓSpecIso (CommRingCat.of B')).hom
      ((Scheme.ΓSpecIso (CommRingCat.of B')).inv
        ((ρ.baseChange (Spec.map f)).affineMatrix B' x i j)) =
    ((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ (Spec.map φ).appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of B')).hom) (ρ.affineMatrix B y i j) at hij
  rw [Iso.inv_hom_id_apply, Scheme.ΓSpecIso_naturality,
    Iso.inv_hom_id_assoc] at hij
  exact hij

end Langlands.GroupScheme.MatrixRepresentation

namespace Langlands.GroupScheme.splitTorus

variable {S : Scheme.{u}} (I : Type u) [Finite I]

/-- Base change of a map from a coordinate split torus, using its canonical identification. -/
def baseChangeHomAlong {S' : Scheme.{u}} (b : S' ⟶ S)
    {G : GroupScheme S} (j : splitTorus S I ⟶ G) :
    splitTorus S' I ⟶ (GroupScheme.baseChange b).obj G :=
  (baseChangeIso b I).inv ≫ (GroupScheme.baseChange b).map j

/-- Affine torus coordinates restrict along the actual spectrum of a test-ring map. -/
theorem affinePointsEquiv_homMk_comp {A B : CommRingCat.{u}}
    {p : Spec A ⟶ S} {q : Spec B ⟶ S} (φ : A ⟶ B) (h : Spec.map φ ≫ p = q)
    (x : Over.mk p ⟶ (splitTorus S I).X) :
    affinePointsEquiv I q ((Over.homMk (Spec.map φ) h : Over.mk q ⟶ Over.mk p) ≫ x) =
      fun i => Units.map φ.hom.toMonoidHom (affinePointsEquiv I p x i) := by
  funext i
  change Gm.affinePointsEquiv q
    (((Over.homMk (Spec.map φ) h : Over.mk q ⟶ Over.mk p) ≫ x) ≫ _) =
    Units.map φ.hom.toMonoidHom
      (Gm.affinePointsEquiv p (x ≫ (Limits.Pi.π (fun _ : I => (Gm S).toGrp) i).hom.hom))
  rw [Category.assoc]
  apply Units.ext
  rw [Gm.affinePointsEquiv_val, Gm.pointsEquiv_naturality, Units.coe_map, Units.coe_map,
    Gm.affinePointsEquiv_val]
  change ((Spec.map φ).appTop ≫ (Scheme.ΓSpecIso B).hom) _ = _
  rw [Scheme.ΓSpecIso_naturality]
  rfl

/-- The inverse canonical base-change identification preserves the affine coordinates. -/
theorem affinePointsEquiv_baseChangeIso_inv {S' : Scheme.{u}} (b : S' ⟶ S)
    {B : CommRingCat.{u}} (p : Spec B ⟶ S')
    (x : Over.mk p ⟶ (splitTorus S' I).X) :
    affinePointsEquiv I (p ≫ b)
        (GroupScheme.baseChangePointsEquiv b (splitTorus S I) (Over.mk p)
          (x ≫ (baseChangeIso b I).inv.hom.hom)) =
      affinePointsEquiv I p x := by
  have hc : pointsEquiv I ((Over.map b).obj (Over.mk p))
      (GroupScheme.baseChangePointsEquiv b (splitTorus S I) (Over.mk p)
        (x ≫ (baseChangeIso b I).inv.hom.hom)) =
      pointsEquiv I (Over.mk p) x := by
    change baseChangePointsEquiv b I (Over.mk p)
      (x ≫ (baseChangeIso b I).inv.hom.hom) = pointsEquiv I (Over.mk p) x
    exact isoOfPointModels_inv _ _ _ _ _ _ (Over.mk p) x
  funext i
  apply Units.ext
  change (Scheme.ΓSpecIso B).hom
      ((pointsEquiv I ((Over.map b).obj (Over.mk p))
        (GroupScheme.baseChangePointsEquiv b (splitTorus S I) (Over.mk p)
          (x ≫ (baseChangeIso b I).inv.hom.hom)) i).val) =
    (Scheme.ΓSpecIso B).hom ((pointsEquiv I (Over.mk p) x i).val)
  rw [hc]

variable {R A : Type u} [CommRing R] [CommRing A]
  [Fintype I] [DecidableEq I] (f : R →+* A)

/-- The actual map between the two universal affine test schemes. -/
def universalBaseChangeMap :
    (Over.map (Spec.map (CommRingCat.ofHom f))).obj
        ((algSpec (CommRingCat.of A)).obj
          (op (CommAlgCat.of (CommRingCat.of A) (AddMonoidAlgebra A (I → ℤ))))) ⟶
      (algSpec (CommRingCat.of R)).obj
        (op (CommAlgCat.of (CommRingCat.of R) (AddMonoidAlgebra R (I → ℤ)))) :=
  Over.homMk (Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom (I → ℤ) f))) (by
    change Spec.map (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom (I → ℤ) f)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R (I → ℤ)))) =
      Spec.map (CommRingCat.ofHom (algebraMap A (AddMonoidAlgebra A (I → ℤ)))) ≫
        Spec.map (CommRingCat.ofHom f)
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    change AddMonoidAlgebra.mapRingHom (I → ℤ) f
      (AddMonoidAlgebra.single 0 r) = AddMonoidAlgebra.single 0 (f r)
    exact AddMonoidAlgebra.mapRingHom_single f 0 r)

omit [Fintype I] in
/-- Forgetting the base change of the new universal point gives coefficient extension
of the old universal point. -/
theorem universalPoint_baseChange :
    GroupScheme.baseChangePointsEquiv (Spec.map (CommRingCat.ofHom f))
        (splitTorus (Spec (CommRingCat.of R)) I) _
        (universalPoint (R := CommRingCat.of A) I ≫
          (baseChangeIso (Spec.map (CommRingCat.ofHom f)) I).inv.hom.hom) =
      universalBaseChangeMap I f ≫ universalPoint (R := CommRingCat.of R) I := by
  apply (affinePointsEquiv I
    (((algSpec (CommRingCat.of A)).obj
      (op (CommAlgCat.of (CommRingCat.of A) (AddMonoidAlgebra A (I → ℤ))))).hom ≫
        Spec.map (CommRingCat.ofHom f))).injective
  erw [affinePointsEquiv_baseChangeIso_inv]
  change algebraPointsEquiv I _ (universalPoint (R := CommRingCat.of A) I) =
    affinePointsEquiv I _
      (universalBaseChangeMap I f ≫ universalPoint (R := CommRingCat.of R) I)
  rw [universalBaseChangeMap, affinePointsEquiv_homMk_comp]
  change (algebraPointsEquiv I _ (universalPoint (R := CommRingCat.of A) I)) =
    fun i => Units.map (AddMonoidAlgebra.mapRingHom (I → ℤ) f).toMonoidHom
      (algebraPointsEquiv I _ (universalPoint (R := CommRingCat.of R) I) i)
  rw [algebraPointsEquiv_universalPoint, algebraPointsEquiv_universalPoint]
  funext i
  apply Units.ext
  change AddMonoidAlgebra.single (Pi.single i 1) (1 : A) =
    AddMonoidAlgebra.mapRingHom (I → ℤ) f (AddMonoidAlgebra.single (Pi.single i 1) 1)
  rw [AddMonoidAlgebra.mapRingHom_single, map_one]

end Langlands.GroupScheme.splitTorus

namespace Langlands.GroupScheme.SplitTorusRepresentationWeights

open splitTorus

variable {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)
  {G : GroupScheme (Spec (CommRingCat.of R))} {N : ℕ}
  (ρ : MatrixRepresentation G (Fin N))
  (I : Type u) [Fintype I] [DecidableEq I]
  (j : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)

/-- The actual universal representation matrix commutes with coefficient base change. -/
theorem universalMatrix_baseChange :
    universalMatrix (ρ.baseChange (Spec.map (CommRingCat.ofHom f))) I
        (baseChangeHomAlong I (Spec.map (CommRingCat.ofHom f)) j) =
      Matrix.GeneralLinearGroup.map (AddMonoidAlgebra.mapRingHom (I → ℤ) f)
        (universalMatrix ρ I j) := by
  change (ρ.baseChange (Spec.map (CommRingCat.ofHom f))).affineMatrix
      (CommAlgCat.of (CommRingCat.of A) (AddMonoidAlgebra A (I → ℤ)))
      (universalPoint (R := CommRingCat.of A) I ≫
        (baseChangeHomAlong I (Spec.map (CommRingCat.ofHom f)) j).hom.hom) =
    Matrix.GeneralLinearGroup.map (AddMonoidAlgebra.mapRingHom (I → ℤ) f)
      (ρ.affineMatrix
        (CommAlgCat.of (CommRingCat.of R) (AddMonoidAlgebra R (I → ℤ)))
        (universalPoint (R := CommRingCat.of R) I ≫ j.hom.hom))
  refine MatrixRepresentation.affineMatrix_baseChange_map ρ (CommRingCat.ofHom f)
    (CommAlgCat.of (CommRingCat.of R) (AddMonoidAlgebra R (I → ℤ)))
    (CommAlgCat.of (CommRingCat.of A) (AddMonoidAlgebra A (I → ℤ)))
    (CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom (I → ℤ) f))
    (universalBaseChangeMap I f) rfl
    (universalPoint (R := CommRingCat.of A) I ≫
      (baseChangeHomAlong I (Spec.map (CommRingCat.ofHom f)) j).hom.hom)
    (universalPoint (R := CommRingCat.of R) I ≫ j.hom.hom) ?_
  change GroupScheme.baseChangePointsEquiv (Spec.map (CommRingCat.ofHom f)) G _
      (universalPoint (R := CommRingCat.of A) I ≫
        ((baseChangeIso (Spec.map (CommRingCat.ofHom f)) I).inv.hom.hom ≫
          ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom f))).map j).hom.hom)) =
    universalBaseChangeMap I f ≫
      (universalPoint (R := CommRingCat.of R) I ≫ j.hom.hom)
  rw [← Category.assoc, GroupScheme.baseChangePointsEquiv_comp,
    universalPoint_baseChange, Category.assoc]

/-- Each actual coefficient projector is obtained by applying the base ring map entrywise. -/
theorem weight_baseChange (m : I → ℤ) :
    weight (ρ.baseChange (Spec.map (CommRingCat.ofHom f))) I
        (baseChangeHomAlong I (Spec.map (CommRingCat.ofHom f)) j) m =
      (weight ρ I j m).map f := by
  ext a b
  change ((universalMatrix (ρ.baseChange (Spec.map (CommRingCat.ofHom f))) I
      (baseChangeHomAlong I (Spec.map (CommRingCat.ofHom f)) j) :
        Matrix (Fin N) (Fin N) (AddMonoidAlgebra A (I → ℤ))) a b).coeff m =
    f (((universalMatrix ρ I j :
      Matrix (Fin N) (Fin N) (AddMonoidAlgebra R (I → ℤ))) a b).coeff m)
  rw [universalMatrix_baseChange]
  exact AddMonoidAlgebra.coeff_mapRingHom f _ m

/-- Over a local base, every nontrivial scalar extension has exactly the same weights. -/
theorem weight_baseChange_ne_zero_iff [IsLocalRing R] [Nontrivial A] (m : I → ℤ) :
    weight (ρ.baseChange (Spec.map (CommRingCat.ofHom f))) I
        (baseChangeHomAlong I (Spec.map (CommRingCat.ofHom f)) j) m ≠ 0 ↔
      weight ρ I j m ≠ 0 := by
  rw [weight_baseChange]
  exact Langlands.LinearAlgebra.idempotent_matrix_map_ne_zero_iff f _
    (weight_mul_self ρ I j m)

/-- The actual finite universal-matrix support is constant over a local base. -/
theorem weightSupport_baseChange [IsLocalRing R] [Nontrivial A] :
    weightSupport (ρ.baseChange (Spec.map (CommRingCat.ofHom f))) I
        (baseChangeHomAlong I (Spec.map (CommRingCat.ofHom f)) j) =
      weightSupport ρ I j := by
  ext m
  rw [mem_weightSupport, mem_weightSupport]
  exact weight_baseChange_ne_zero_iff f ρ I j m

/-- The set of occurring integral coordinate vectors is constant on nontrivial fibres. -/
theorem weights_baseChange_eq [IsLocalRing R] [Nontrivial A] :
    {m : I → ℤ | weight (ρ.baseChange (Spec.map (CommRingCat.ofHom f))) I
      (baseChangeHomAlong I (Spec.map (CommRingCat.ofHom f)) j) m ≠ 0} =
    {m : I → ℤ | weight ρ I j m ≠ 0} := by
  ext m
  exact weight_baseChange_ne_zero_iff f ρ I j m

/-- The support identification preserves each integral coordinate vector. -/
def weightSupportBaseChangeEquiv [IsLocalRing R] [Nontrivial A] :
    {m : I → ℤ // weight ρ I j m ≠ 0} ≃
      {m : I → ℤ // weight (ρ.baseChange (Spec.map (CommRingCat.ofHom f))) I
        (baseChangeHomAlong I (Spec.map (CommRingCat.ofHom f)) j) m ≠ 0} where
  toFun m := ⟨m.1, (weight_baseChange_ne_zero_iff f ρ I j m.1).2 m.2⟩
  invFun m := ⟨m.1, (weight_baseChange_ne_zero_iff f ρ I j m.1).1 m.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
theorem weightSupportBaseChangeEquiv_apply [IsLocalRing R] [Nontrivial A]
    (m : {m : I → ℤ // weight ρ I j m ≠ 0}) :
    (weightSupportBaseChangeEquiv f ρ I j m).1 = m.1 := rfl

@[simp]
theorem weightSupportBaseChangeEquiv_symm_apply [IsLocalRing R] [Nontrivial A]
    (m : {m : I → ℤ // weight (ρ.baseChange (Spec.map (CommRingCat.ofHom f))) I
      (baseChangeHomAlong I (Spec.map (CommRingCat.ofHom f)) j) m ≠ 0}) :
    ((weightSupportBaseChangeEquiv f ρ I j).symm m).1 = m.1 := rfl

end Langlands.GroupScheme.SplitTorusRepresentationWeights
