import Langlands.GroupScheme.Reductive.SchemeCoordinateRootDatum
import Langlands.GroupScheme.Reductive.AffinePinnedRootVectors
import Langlands.GroupScheme.Reductive.AffinePinnedComparisonProperties

/-! # Actual affine pinned models from coherent global root frames -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace CoordinateRootDatum

section Frames

variable {S : Scheme.{u}} {I J : Type u} [Fintype I]
    {G : GroupScheme S} [IsAffineHom G.X.hom]
    (t : splitTorus S I ⟶ G) (P : RootDatum J (I → ℤ) (I → ℤ))

local instance affineFramePullback {R : Type u} [CommRing R]
    (a : Spec (CommRingCat.of R) ⟶ S) : IsAffineHom ((baseChange a).obj G).X.hom :=
  inferInstanceAs (IsAffineHom (pullback.snd G.X.hom a))

/-- A supplied frame of every actual coordinate root module on every
affine test of the original base. This is data, not a freeness theorem. -/
abbrev AffineRootFrames :=
  ∀ (R : Type u) [CommRing R] (a : Spec (CommRingCat.of R) ⟶ S) (α : J),
    R ≃ₗ[R] splitTorus.exponentWeightSpace I ((baseChange a).obj G)
      ((splitTorus.baseChangeIso a I).inv ≫ (baseChange a).map t) (P.root α)

/-- The frame vector at one, regarded as an actual dual-number point in the
original group over the base. -/
def AffineRootFrames.point (F : AffineRootFrames t P)
    (R : Type u) [CommRing R] (a : Spec (CommRingCat.of R) ⟶ S) (α : J) :
    Spec (CommRingCat.of (DualNumber R)) ⟶ G.X.left :=
  (F R a α 1).val.toMul.val.left ≫ pullback.fst G.X.hom a

/-- The original projection of the coefficient-extended frame point agrees
with the frame on the corresponding direct affine test. -/
def AffineRootFrames.IsCoherent (F : AffineRootFrames t P) : Prop :=
  ∀ (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (a : Spec (CommRingCat.of R) ⟶ S) (α : J),
    (lieKernelMap ((baseChange a).obj G) (Algebra.ofId R A)
      (F R a α 1).val.toMul).val.left ≫ pullback.fst G.X.hom a =
      AffineRootFrames.point t P F A (algebraBaseMap R A ≫ a) α

variable (hG : IsReductive G) (ht : IsClosedSubgroup t)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) t)
    (hP : IsGlobalCoordinateRootDatumOf I G t P)

include hP in
/-- Global actual field realization gives the standard affine fibrewise
datum on every normalized affine pullback. -/
theorem IsGlobalCoordinateRootDatumOf.affinePullback
    (R : Type u) [CommRing R] (a : Spec (CommRingCat.of R) ⟶ S) :
    IsFibrewiseRootDatumOf I ((baseChange a).obj G)
      ((splitTorus.baseChangeIso a I).inv ≫ (baseChange a).map t) P := by
  refine ⟨hP.1, hP.2.1, fun k _ _ => ?_⟩
  exact (isRealizedOver_baseChange_iff I G t P a k (algebraBaseMap R k)).mpr
    (hP.2.2 k (algebraBaseMap R k ≫ a))

variable [Fintype J] (F : AffineRootFrames t P) (b : P.Base)

/-- The actual affine pinned model of the original group on the specified
affine test, using the supplied global root frames. -/
abbrev pinnedAffineModelOfFrames (R : Type u) [CommRing R]
    (a : Spec (CommRingCat.of R) ⟶ S) : AffinePinnedModel.{u} where
  ring := R
  group := (baseChange a).obj G
  reductive := hG.baseChange a
  coordinates := I
  inclusion := (splitTorus.baseChangeIso a I).inv ≫ (baseChange a).map t
  closed := (IsClosedSubgroup.of_iso (splitTorus.baseChangeIso a I).symm).comp (ht.baseChange a)
  maximal := by
    let := hG.smooth
    exact hmax.baseChange_coordinates a
  rootIndex := J
  rootDatum := P
  fibrewiseRootDatum := hP.affinePullback t P R a
  rootLines := fun α => ⟨(F R a α).symm⟩
  basis := b
  pinning := fun α => F R a α

end Frames

end CoordinateRootDatum

end Langlands.GroupScheme
