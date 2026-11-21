import Langlands.GroupScheme.CliffordSpin.ScalarKernel
import Langlands.GroupScheme.AffineCartierSmoothProof
import Langlands.GroupScheme.CentralIsogeny.ProjectionCentralIsogeny
import Langlands.GroupScheme.CentralIsogeny.FiniteKernelQuotient
import Langlands.GroupScheme.Dynamic.CentralizerReductiveTransport
import Langlands.GroupScheme.Dynamic.RepresentedStructure
import Langlands.GroupScheme.GeneralLinearSmoothProof
import Langlands.GroupScheme.Torus.BoundedExponentSubgroup

/-! # The scalar Clifford projection is a central isogeny -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.CliffordSpin

open Quaternionic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

private theorem isFinite_muTwo (F : Type u) [Field F] :
    IsFinite (mu (Spec (CommRingCat.of F)) 2).X.hom := by
  let R := CommRingCat.of F
  let G := (Gm (Spec R)).toGrp
  let i := torsionι G 2
  let e := splitTorus.gmIso (Spec R) ≪≫
    (Diagonalizable.splitIso R (AddEquiv.refl (PUnit.{u+1} → ℤ))).symm
  have hG : IsAffineHom G.X.hom := by
    change IsAffineHom (Gm (Spec R)).X.hom
    rw [← Over.w (Gm.relativeLaurentIso R).hom]
    infer_instance
  have hi : IsClosedSubgroup i := torsionι_isClosedImmersion G 2
  refine Diagonalizable.isFinite_closedSubgroup_of_uniformPower (i ≫ e.hom) (hi.comp_iso e) 2 (by decide) ?_
  intro T x
  let d := mu.pointsEquiv (Spec R) 2 T
  apply d.injective
  rw [map_pow, map_one]
  exact Subtype.ext ((mem_rootsOfUnity 2 _).mp (d x).property)

private theorem finiteType_tensor (F A B : Type u) [Field F] [CommRing A] [CommRing B]
    [Algebra F A] [Algebra F B] [Algebra.FiniteType F A] [Algebra.FiniteType F B] :
    Algebra.FiniteType F (A ⊗[F] B) :=
  Algebra.FiniteType.trans (R := F) (S := A) (A := A ⊗[F] B) inferInstance inferInstance

variable {F V : Type u} [Field F] [AddCommGroup V] [Module F V]
  [Invertible (2 : F)] {n : ℕ} (Q : QuadraticForm F V) (b : Module.Basis (Fin n) F V)

instance groupScheme_isAffine : IsAffine (groupScheme Q b).X.left := by
  change IsAffine (Spec (CommRingCat.of ((ambientAlgebra Q b) ⧸ ideal Q b)))
  infer_instance

instance groupScheme_locallyOfFiniteType : LocallyOfFiniteType (groupScheme Q b).X.hom := by
  let c := (algebraBasis Q b).reindex (Fintype.equivFin (Finset (Fin n)))
  let A := FiniteAlgebraUnits.candidateRing c
  let B := GeneralLinear.CoordinateRing (Fin n) F
  let : Algebra.FiniteType F A := by
    have h := FiniteAlgebraUnits.groupScheme_smooth c
    have h' : LocallyOfFiniteType (FiniteAlgebraUnits.groupScheme c).X.hom := inferInstance
    change LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap F A))) at h'
    exact RingHom.finiteType_algebraMap.mp ((HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp h')
  let : Algebra.Smooth F B := GeneralLinear.coordinateRing_smooth (Fin n) F
  let : Algebra.FiniteType F B := inferInstance
  let hAB := finiteType_tensor F A B
  let : Algebra.FiniteType F (ambientAlgebra Q b) := hAB
  let D := (ambientAlgebra Q b) ⧸ ideal Q b
  let : Algebra.FiniteType F D := Algebra.FiniteType.of_surjective
    (Ideal.Quotient.mkₐ F (ideal Q b)) Ideal.Quotient.mk_surjective
  change LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap F D)))
  exact (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
    (RingHom.finiteType_algebraMap.mpr inferInstance)

variable [CharZero F] [NeZero n] (q : (FirstKindInvolution.scalar F).QuadraticForms (Fin n))

local notation "τ" => FirstKindInvolution.scalar F
local notation "SO" => FirstKindInvolution.normOneIsometryGroup τ q
local notation "π" => projection q
local notation "μ₂" => CommGroupScheme.toGrp (mu (Spec (CommRingCat.of F)) 2)

/-- For nondegenerate scalar forms the vector action of the Clifford lift group is a
finite, faithfully flat, locally finitely presented homomorphism with central kernel. -/
theorem isCentralIsogeny_projection (hq : (τ).IsNondegenerateQuadratic q) : IsCentralIsogeny (π) := by
  let i := FirstKindInvolution.normOneIsometryAmbientι τ q
  have hi : IsClosedSubgroup i := FirstKindInvolution.isClosedSubgroup_normOneIsometryAmbientι τ q
  let : IsAffineHom (SO).X.hom := hi.isAffineHom
  let : LocallyOfFiniteType (SO).X.hom := hi.locallyOfFiniteType
  let : Smooth (SO).X.hom := affineCartierSmooth F (SO) inferInstance inferInstance
  let : IsAffine (SO).X.left := isAffine_of_isAffineHom (SO).X.hom
  let : Surjective (π).hom.hom.left := surjective_projection q hq
  let : Flat (π).hom.hom.left := flat_of_surjective (π)
  let e := kernelIso q hq
  let : IsFinite (μ₂).X.hom := isFinite_muTwo F
  let : IsIso e.hom.hom.hom.left := Functor.map_isIso (Grp.forget _ ⋙ Over.forget _) e.hom
  let : IsFinite (kernel (π)).X.hom := by
    rw [← Over.w e.hom.hom.hom]
    infer_instance
  let : IsFinite (π).hom.hom.left := isFinite_of_finite_kernel (π)
  let : IsLocallyNoetherian (SO).X.left := LocallyOfFiniteType.isLocallyNoetherian (SO).X.hom
  exact ⟨⟨inferInstance, inferInstance, inferInstance⟩,
    LocallyOfFinitePresentation.iff_locallyOfFiniteType.mpr inferInstance,
    isCentral_kernel_projection q hq⟩

/-- For a regular scalar quadratic presentation of positive dimension in characteristic zero,
the Clifford vector action is a central isogeny onto the norm-one isometry group. -/
def ScalarCliffordCentralIsogenyStatement : Prop :=
  ∀ (F : Type u) [Field F] [CharZero F] [Invertible (2 : F)] (n : ℕ) [NeZero n]
    (q : (FirstKindInvolution.scalar F).QuadraticForms (Fin n)),
    (FirstKindInvolution.scalar F).IsNondegenerateQuadratic q → IsCentralIsogeny (projection q)

end Langlands.GroupScheme.CliffordSpin
