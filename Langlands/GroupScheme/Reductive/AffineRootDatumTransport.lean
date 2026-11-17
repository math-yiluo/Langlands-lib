import Langlands.GroupScheme.Reductive.FibrewiseRootDatumBaseChange
import Langlands.GroupScheme.Torus.AffineProfileBaseChange

/-! # Fibrewise root data and free root lines on arbitrary affine charts -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

variable {R A : Type u} [CommRing R] [CommRing A]
  {I : Type u} [Fintype I]
  {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]

/-- A full fibrewise coordinate root datum together with free actual root
weight lines over the coefficient ring. -/
def HasFreeRootWeightDatum
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    {J : Type u} (P : RootDatum J (I → ℤ) (I → ℤ)) : Prop :=
  IsFibrewiseRootDatumOf I G i P ∧
    ∀ a : J, Nonempty
      (splitTorus.exponentWeightSpace I G i (P.root a) ≃ₗ[CommRingCat.of R]
        CommRingCat.of R)

local instance affineChartPullback
    (b : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R)) :
    IsAffineHom ((baseChange b).obj G).X.hom :=
  MorphismProperty.pullback_snd G.X.hom b inferInstance

namespace splitTorus

variable (I) (G)
  (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
  (b : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R))

/-- The canonical coordinate torus remains fibrewise maximal along any
specified map of affine schemes. -/
theorem isFibrewiseMaximalTorus_affineBaseChangedTorusHom [Smooth G.X.hom]
    (hmax : IsFibrewiseMaximalTorus (T := commGroupScheme _ I) i) :
    IsFibrewiseMaximalTorus (T := commGroupScheme _ I)
      (RelativeCocharacterCentralizer.baseChangedTorusHom I G i b) :=
  IsFibrewiseMaximalTorus.iso_comp
    (T := (CommGroupScheme.baseChange b).obj (commGroupScheme _ I))
    (T' := commGroupScheme _ I) (hmax.baseChange b) (baseChangeIso b I).symm

/-- A supplied trivialization of an actual exponent weight line remains a
trivialization on every affine chart, with no flatness premise. -/
theorem exponentWeightLine_affineBaseChange [Smooth G.X.hom]
    (m : I → ℤ)
    (hfree : Nonempty
      (exponentWeightSpace I G i m ≃ₗ[CommRingCat.of R] CommRingCat.of R)) :
    Nonempty
      (exponentWeightSpace I ((baseChange b).obj G)
        (RelativeCocharacterCentralizer.baseChangedTorusHom I G i b) m ≃ₗ[CommRingCat.of A]
          CommRingCat.of A) := by
  classical
  let : Algebra R A := (Spec.preimage b).hom.toAlgebra
  obtain ⟨e⟩ := hfree
  exact ⟨(affineExponentWeightBaseChangeEquiv I G i b m).symm.trans
    ((TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl A A) e).trans
      (TensorProduct.AlgebraTensorModule.rid R A A))⟩

end splitTorus

variable {J : Type u} {P : RootDatum J (I → ℤ) (I → ℤ)}
  {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  (b : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R))

/-- The same full coordinate root datum pulls back along any specified
affine scheme map, using its induced coefficient-algebra structure. -/
theorem IsFibrewiseRootDatumOf.affineBaseChange
    (hP : IsFibrewiseRootDatumOf I G i P) :
    IsFibrewiseRootDatumOf I ((baseChange b).obj G)
      (splitTorus.RelativeCocharacterCentralizer.baseChangedTorusHom I G i b) P := by
  let : Algebra R A := (Spec.preimage b).hom.toAlgebra
  have hb : algebraBaseMap R A = b := Spec.map_preimage b
  let C (f : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R)) : Prop :=
    IsFibrewiseRootDatumOf I ((baseChange f).obj G)
      (splitTorus.RelativeCocharacterCentralizer.baseChangedTorusHom I G i f) P
  have h : C (algebraBaseMap R A) := hP.baseChange_implicit
  exact Eq.mp (congrArg C hb) h

/-- Full fibrewise root data and free actual root lines survive arbitrary
affine base change of a smooth affine group. -/
theorem HasFreeRootWeightDatum.affineBaseChange [Smooth G.X.hom]
    (h : HasFreeRootWeightDatum i P) :
    HasFreeRootWeightDatum
      (splitTorus.RelativeCocharacterCentralizer.baseChangedTorusHom I G i b) P :=
  ⟨h.1.affineBaseChange b,
    fun a => splitTorus.exponentWeightLine_affineBaseChange I G i b (P.root a) (h.2 a)⟩

end Langlands.GroupScheme
