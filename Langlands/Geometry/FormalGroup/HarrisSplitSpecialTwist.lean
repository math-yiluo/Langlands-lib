import Langlands.Geometry.FormalGroup.HarrisSplitSpecialAffine
import Langlands.Geometry.FormalGroup.PolarizedFramedTwist

/-! # Coefficient twist of the split-special affine functor -/

noncomputable section

universe u s

namespace Langlands.FormalGroup.Harris

open CategoryTheory ValuativeRel LocalDivision ModuleLaw

attribute [local instance] ModuleLaw.coefficientAlgebra ModuleLaw.coefficientScalarTower
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

variable {prime : ℕ} [Fact prime.Prime]
variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable [Algebra ℤ_[prime] 𝒪[K]]
variable {W : Type} [CommRing W] [Algebra 𝒪[K] W] [Algebra ℤ_[prime] W]
variable [wTower : IsScalarTower ℤ_[prime] 𝒪[K] W] {ϖ : 𝒪[K]}
variable {L : Type s} [Field L] [Algebra K L] (ι : L →ₐ[K] D)
variable {frame frame' : SplitPolarizedFrame prime K D W ϖ}
variable {T U : Nilp.{0, 0} W (algebraMap 𝒪[K] W ϖ)}

local instance splitSpecialTwistPadicIntegerRingAlgebra : Algebra ℤ_[prime] (IntegerRing K D) :=
  Algebra.compHom (IntegerRing K D) (algebraMap ℤ_[prime] 𝒪[K])

open PolarizedFramedAffinePoint

omit wTower in
/-- A coefficient square preserving the structural scalars preserves split-special classes. -/
theorem isSplitSpecialClass_mapCoefficients (c : CoefficientChange frame frame' T U)
    (hc : c.scalar.toRingHom.comp (algebraMap 𝒪[K] T.obj) = algebraMap 𝒪[K] U.obj)
    {q : IsomorphismClass (frame := frame) (T := T)} (h : isSplitSpecialClass ι q) :
    isSplitSpecialClass ι (q.mapCoefficients c) := by
  induction q using Quotient.inductionOn with
  | h X =>
    change HasSplitSpecialTangent ι X at h
    change HasSplitSpecialTangent ι (X.mapCoefficients c)
    have hs := h.2.1.map c.scalar
    rw [hc] at hs
    exact ⟨h.1, hs, h.2.2.map c.scalar⟩

variable (σ : W ≃ₐ[𝒪[K]] W)

local notation "σₚ" => AlgEquiv.restrictScalars ℤ_[prime] σ
local notation "hπ" => AlgEquiv.commutes σ ϖ
local notation "σ₀" => AlgEquiv.toAlgHom (Nilp.twistResidueEquiv σₚ hπ)

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem twistScalar_structural (T : Nilp.{0, 0} W (algebraMap 𝒪[K] W ϖ)) :
    (Nilp.twistScalarEquiv σₚ hπ T).toRingHom.comp (algebraMap 𝒪[K] T.obj) =
      algebraMap 𝒪[K] (Nilp.twistObj σₚ hπ T).obj := by
  apply RingHom.ext
  intro a
  change algebraMap W T.obj (algebraMap 𝒪[K] W a) =
    algebraMap W (Nilp.twistObj σₚ hπ T).obj (algebraMap 𝒪[K] W a)
  rw [Nilp.twistObj_algebraMap]
  exact congrArg (algebraMap W T.obj) (σ.commutes a).symm

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in
private theorem untwistScalar_structural (T : Nilp.{0, 0} W (algebraMap 𝒪[K] W ϖ)) :
    (Nilp.twistScalarEquiv σₚ hπ T).symm.toRingHom.comp
        (algebraMap 𝒪[K] (Nilp.twistObj σₚ hπ T).obj) =
      algebraMap 𝒪[K] T.obj := by
  apply RingHom.ext
  intro a
  let α := Nilp.twistScalarEquiv σₚ hπ T
  change α.symm (algebraMap 𝒪[K] (Nilp.twistObj σₚ hπ T).obj a) = algebraMap 𝒪[K] T.obj a
  exact α.symm_apply_eq.mpr (DFunLike.congr_fun (twistScalar_structural σ T) a).symm

variable (frame)

/-- On each test the coefficient comparison restricts to an equivalence of split-special loci. -/
def splitSpecialTwistFrameEquiv (T : Nilp.{0, 0} W (algebraMap 𝒪[K] W ϖ)) :
    (splitSpecialAffineFunctor ι (frame.map σ₀)).obj T ≃
      (splitSpecialAffineFunctor ι frame).obj (Nilp.twistObj σₚ hπ T) where
  toFun q := ⟨twistFrameEquiv σₚ hπ frame T q.val,
    isSplitSpecialClass_mapCoefficients ι (CoefficientChange.twist σₚ hπ frame T)
      (twistScalar_structural σ T) q.property⟩
  invFun q := ⟨(twistFrameEquiv σₚ hπ frame T).symm q.val,
    isSplitSpecialClass_mapCoefficients ι (CoefficientChange.untwist σₚ hπ frame T)
      (untwistScalar_structural σ T) q.property⟩
  left_inv q := Subtype.ext ((twistFrameEquiv σₚ hπ frame T).left_inv q.val)
  right_inv q := Subtype.ext ((twistFrameEquiv σₚ hπ frame T).right_inv q.val)

/-- Structural twisting and extension of the residue frame give the same split-special functor. -/
def splitSpecialTwistFrameNatIso :
    splitSpecialAffineFunctor ι (frame.map σ₀) ≅
      Nilp.twistFunctor σₚ hπ ⋙ splitSpecialAffineFunctor ι frame :=
  NatIso.ofComponents (fun T => (splitSpecialTwistFrameEquiv ι frame σ T).toIso) (by
    intro T U j
    ext q
    apply Subtype.ext
    exact ConcreteCategory.congr_hom
      ((twistFrameNatIso σₚ hπ frame).hom.naturality j) q.val)

@[simp]
theorem splitSpecialTwistFrameNatIso_hom_app_val
    (q : (splitSpecialAffineFunctor ι (frame.map σ₀)).obj T) :
    ((splitSpecialTwistFrameNatIso ι frame σ).hom.app T q).val =
      (twistFrameNatIso σₚ hπ frame).hom.app T q.val :=
  rfl

end Langlands.FormalGroup.Harris
