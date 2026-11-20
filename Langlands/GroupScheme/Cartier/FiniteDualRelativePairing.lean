import Langlands.GroupScheme.Cartier.FiniteDualPairing
import Langlands.GroupScheme.Cartier.FiniteDualSpectrum
import Langlands.GroupScheme.Cartier.RelativeHomSheaf
import Langlands.AlgebraicGeometry.Picard.KernelCartierDuality

/-! # Actual relative characters from the finite dual pairing -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite WithConv
open scoped CategoryTheory.MonObj TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.Cartier.FiniteDual

section RelativeHom

variable {S : Scheme.{u}} {G H : CommGroupScheme S} {T V : Over S}

theorem relativeHom_ext {χ ψ : RelativeHom G H T}
    (h : ∀ (V : Over S) (a : V ⟶ T) (x : V ⟶ G.X),
      relativeHomLocalPoints G H χ a x = relativeHomLocalPoints G H ψ a x) :
    χ = ψ := by
  apply (relativeHomLocalNatEquiv G H T).injective
  apply NatTrans.ext
  funext V
  exact GrpCat.hom_ext (MonoidHom.ext fun x => h V.unop.left V.unop.hom x)

theorem relativeHomLocalPoints_add (χ ψ : RelativeHom G H T) (a : V ⟶ T) (x : V ⟶ G.X) :
    relativeHomLocalPoints G H (χ + ψ) a x =
      relativeHomLocalPoints G H χ a x * relativeHomLocalPoints G H ψ a x := by
  open LocalGroupIso in
  change coverPointsEquiv H.toGrp a
      ((coverPointsEquiv G.toGrp a).symm x ≫ (χ.toMul * ψ.toMul).hom.hom) =
    coverPointsEquiv H.toGrp a ((coverPointsEquiv G.toGrp a).symm x ≫ χ.toMul.hom.hom) *
      coverPointsEquiv H.toGrp a ((coverPointsEquiv G.toGrp a).symm x ≫ ψ.toMul.hom.hom)
  rw [← map_mul (coverPointsEquiv H.toGrp a)]
  exact congrArg (coverPointsEquiv H.toGrp a) (MonObj.comp_mul _ _ _)

theorem relativeHomLocalPoints_restrict {T' : Over S} (b : T' ⟶ T)
    (χ : RelativeHom G H T) (a : V ⟶ T') (x : V ⟶ G.X) :
    relativeHomLocalPoints G H (restrict G H b χ) a x =
      relativeHomLocalPoints G H χ (a ≫ b) x := by
  apply Over.OverMorphism.ext
  rw [relativeHomLocalPoints_left, relativeHomLocalPoints_left, restrict_fst]
  rw [← Category.assoc]
  congr 1
  apply pullback.hom_ext <;> simp [baseChangeProj, Category.assoc]

theorem relativeHomLocalPoints_id (χ : RelativeHom G H T) (x : T ⟶ G.X) :
    relativeHomLocalPoints G H χ (𝟙 T) x = evaluation χ x := by
  apply Over.OverMorphism.ext
  rw [relativeHomLocalPoints_left, evaluation_def, sectionPointsEquiv_left, Over.comp_left]
  have h :
      pullback.lift x.left (𝟙 T.left) (by simp) = ((sectionPointsEquiv G T).symm x).left := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
      exact (congrArg (fun z => z.left) ((sectionPointsEquiv G T).apply_symm_apply x)).symm
    · rw [pullback.lift_snd]
      exact (Over.w ((sectionPointsEquiv G T).symm x)).symm
  change pullback.lift x.left (𝟙 T.left) _ ≫ CommGroupScheme.hom χ ≫
    pullback.fst H.X.hom T.hom = _
  rw [h, Category.assoc]

end RelativeHom

variable (R : CommRingCat.{u}) (A : Type u) [CommRing A] [HopfAlgebra R A]
  [Coalgebra.IsCocomm R A] [Module.Finite R A] [Module.Projective R A]

local notation "G" => specGroup R A
local notation "D" => specGroup R (Dual R A)
local notation "M" => Gm (Spec R)

local instance : GrpObj (specOver R A) := (G).grp
local instance : GrpObj (specOver R (Dual R A)) := (D).grp

/-- The unit-valued coefficient pairing as a map on actual test scheme points. -/
def schemePairing (T : Over (Spec R)) (y : T ⟶ (D).X) : (T ⟶ (G).X) →* (T ⟶ (M).X) :=
  (Gm.pointsEquiv (Spec R) T).symm.toMonoidHom.comp
    ((pointCharacter (specPoints R (Dual R A) T y)).comp (specPoints R A T).toMonoidHom)

@[simp] theorem schemePairing_units (T : Over (Spec R)) (y : T ⟶ (D).X) (x : T ⟶ (G).X) :
    Gm.pointsEquiv (Spec R) T (schemePairing R A T y x) =
      pointCharacter (specPoints R (Dual R A) T y) (specPoints R A T x) :=
  (Gm.pointsEquiv (Spec R) T).apply_symm_apply _

theorem schemePairing_naturality {T V : Over (Spec R)} (a : V ⟶ T) (y : T ⟶ (D).X)
    (x : T ⟶ (G).X) :
    schemePairing R A V (a ≫ y) (a ≫ x) = a ≫ schemePairing R A T y x := by
  apply (Gm.pointsEquiv (Spec R) V).injective
  rw [schemePairing_units, Gm.pointsEquiv_naturality, schemePairing_units,
    specPoints_naturality, specPoints_naturality]
  exact pointCharacter_postcomp (sectionsMap a) (specPoints R (Dual R A) T y) (specPoints R A T x)

theorem schemePairing_mul (T : Over (Spec R)) (y z : T ⟶ (D).X) (x : T ⟶ (G).X) :
    schemePairing R A T (y * z) x = schemePairing R A T y x * schemePairing R A T z x := by
  apply (Gm.pointsEquiv (Spec R) T).injective
  rw [schemePairing_units, map_mul (specPoints R (Dual R A) T), map_mul,
    schemePairing_units, schemePairing_units, pointCharacter_mul]

private def pairingOnTests {T : Over (Spec R)} (y : T ⟶ (D).X) :
    (presheafHom (GroupScheme.points (G).toGrp) (GroupScheme.points (M).toGrp)).obj (op T) where
  app V := GrpCat.ofHom (schemePairing R A V.unop.left (V.unop.hom ≫ y))
  naturality V W a := by
    ext x
    change schemePairing R A W.unop.left (W.unop.hom ≫ y) (a.unop.left ≫ x) =
      a.unop.left ≫ schemePairing R A V.unop.left (V.unop.hom ≫ y) x
    rw [← Over.w a.unop, Category.assoc, schemePairing_naturality]

/-- A dual point gives an actual relative group-scheme character. -/
def characterOfPoint {T : Over (Spec R)} (y : T ⟶ (D).X) : RelativeHom G M T :=
  localNatTransToRelativeHom G M (pairingOnTests R A y)

@[simp] theorem characterOfPoint_local {T V : Over (Spec R)} (a : V ⟶ T)
    (y : T ⟶ (D).X) (x : V ⟶ (G).X) :
    relativeHomLocalPoints G M (characterOfPoint R A y) a x =
      schemePairing R A V (a ≫ y) x := by
  let eval (α : (presheafHom (GroupScheme.points (G).toGrp)
      (GroupScheme.points (M).toGrp)).obj (op T)) : V ⟶ (M).X :=
    (α.app (op (Over.mk a))).hom x
  have h := relativeHomToLocalNatTrans_toRelativeHom G M (pairingOnTests R A y)
  exact congrArg eval h

theorem characterOfPoint_evaluation {T : Over (Spec R)} (y : T ⟶ (D).X) (x : T ⟶ (G).X) :
    evaluation (characterOfPoint R A y) x = schemePairing R A T y x := by
  rw [← relativeHomLocalPoints_id, characterOfPoint_local, Category.id_comp]

theorem characterOfPoint_restrict {T V : Over (Spec R)} (a : V ⟶ T) (y : T ⟶ (D).X) :
    restrict G M a (characterOfPoint R A y) = characterOfPoint R A (a ≫ y) := by
  apply relativeHom_ext
  intro W b x
  rw [relativeHomLocalPoints_restrict, characterOfPoint_local,
    characterOfPoint_local, Category.assoc]

theorem characterOfPoint_mul {T : Over (Spec R)} (y z : T ⟶ (D).X) :
    characterOfPoint R A (y * z) = characterOfPoint R A y + characterOfPoint R A z := by
  apply relativeHom_ext
  intro V a x
  rw [relativeHomLocalPoints_add, characterOfPoint_local, characterOfPoint_local,
    characterOfPoint_local, MonObj.comp_mul, schemePairing_mul]

/-- The character comparison on the additive point presheaf of the dual spectrum. -/
def characterComparison : additivePoints (D).toGrp ⟶ characters G where
  app T := AddCommGrpCat.ofHom (AddMonoidHom.mk'
    (fun y => characterOfPoint R A (Additive.toMul y)) (characterOfPoint_mul R A))
  naturality T V a := by
    ext y
    exact (characterOfPoint_restrict R A a.unop (Additive.toMul y)).symm

/-- Switching the scheme points agrees with evaluation into the double-dual spectrum. -/
theorem schemePairing_bidual (T : Over (Spec R)) (x : T ⟶ (G).X) (y : T ⟶ (D).X) :
    schemePairing R (Dual R A) T (x ≫ specMap (bidualEquiv R A).symm.toAlgEquiv.toAlgHom) y =
      schemePairing R A T y x := by
  apply (Gm.pointsEquiv (Spec R) T).injective
  rw [schemePairing_units, schemePairing_units]
  simp only [specPoints_apply, specHomEquiv_postcomp]
  exact pointCharacter_bidual _ _

end Langlands.GroupScheme.Cartier.FiniteDual
