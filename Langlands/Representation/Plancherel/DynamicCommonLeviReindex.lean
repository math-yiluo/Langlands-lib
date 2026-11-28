import Langlands.Representation.Plancherel.RealizedCommonLeviCompactCharts
import Langlands.Representation.Plancherel.DynamicOppositePairScalarProof
import Langlands.Representation.Plancherel.StandardIntertwiningFullDomainTransport

/-! # Reindexing fixed compact pictures across presentations of the common Levi -/

noncomputable section

set_option hygiene false
set_option quotPrecheck false
set_option maxRecDepth 4096
set_option maxHeartbeats 1800000

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel.StandardIntertwining

open Aubert.General Induction QuotientIntegration

universe u uV

section Literal

variable {G : Type u} [Group G] [TopologicalSpace G] [LocallyCompactSpace G] [NonarchimedeanGroup G]
  {P Q U W M M' : Subgroup G} (hM : M' = M)
  (e : M' ≃ₜ* M) (he : ∀ m, (e m : G) = (m : G))
  (A : SmoothRep.{0, u, uV} ℂ M) (B : SmoothRep.{0, u, uV} ℂ M')
  (eB : (SmoothRep.pullback e A).representation.Equiv B.representation)
  (d : IsSemidirectDecomposition P M U) (d' : IsSemidirectDecomposition P M' U)
  (K : OpenSubgroup G)

include hM he in
/-- Change the presentation of the common Levi and apply the fixed
inducing equivalence pointwise on compact sections. -/
def compactPictureReindex : CompactInductionPicture d K A ≃ₗ[ℂ] CompactInductionPicture d' K B := by
  subst M'
  obtain rfl : e = ContinuousMulEquiv.refl M := ContinuousMulEquiv.ext fun x => Subtype.ext (he x)
  exact (compactInductionPictureEquiv d K eB).toLinearEquiv

omit [LocallyCompactSpace G] in
/-- The compact coordinate change acts on the value at each compact point. -/
theorem compactPictureReindex_eval (f : CompactInductionPicture d K A) (k : K) :
    Induction.eval _ _ (compactPictureReindex hM e he A B eB d d' K f) k =
      eB (Induction.eval _ (compactPictureInducingRepresentation d K A) f k) := by
  subst M'
  obtain rfl : e = ContinuousMulEquiv.refl M := ContinuousMulEquiv.ext fun x => Subtype.ext (he x)
  rfl

variable (du : IsClosed (U : Set G)) [MeasurableSpace (QuotientSpace (U := U) W)]
  (qm : Measure (QuotientSpace (U := U) W))

include hM he eB in
/-- Under this reindexing, full weak convergence holds on both presentations. -/
theorem domain_eq_top_reindex :
    domain d du W A qm = ⊤ ↔ domain d' du W B qm = ⊤ := by
  subst M'
  obtain rfl : e = ContinuousMulEquiv.refl M := ContinuousMulEquiv.ext fun x => Subtype.ext (he x)
  exact domain_eq_top_iff_equiv d du W qm eB

variable (c : IsSemidirectDecomposition Q M W) (c' : IsSemidirectDecomposition Q M' W)
  (dw : IsClosed (W : Set G)) (hMc : IsClosed (M : Set G))
  (A₁ : SmoothRep.{0, u, uV} ℂ M) (B₁ : SmoothRep.{0, u, uV} ℂ M')
  (eB₁ : (SmoothRep.pullback e A₁).representation.Equiv B₁.representation)
  (a : A ≃ₗ[ℂ] A₁) (b : B ≃ₗ[ℂ] B₁)
  (hlin : ∀ v : A, eB₁ (a v) = b (eB v))

local notation "I[" d "," du "," A "]" => (DynamicNormalization.leviTwistedInductionFunctor d du).obj A
local notation "C[" d "," A "]" => CompactInductionPicture d K A
local notation "R[" d "," d' "]" => compactPictureReindex hM e he A B eB d d' K

variable (E₀ : I[d,du,A₁] ≃ₗ[ℂ] C[d,A]) (E₁ : I[c,dw,A₁] ≃ₗ[ℂ] C[c,A])
  (E₀' : I[d',du,B₁] ≃ₗ[ℂ] C[d',B]) (E₁' : I[c',dw,B₁] ≃ₗ[ℂ] C[c',B])
  (hE₀ : ∀ f (k : K), a (Induction.eval _ _ (E₀ f) k) = Induction.eval _ _ f (k : G))
  (hE₁ : ∀ f (k : K), a (Induction.eval _ _ (E₁ f) k) = Induction.eval _ _ f (k : G))
  (hE₀' : ∀ f (k : K), b (Induction.eval _ _ (E₀' f) k) = Induction.eval _ _ f (k : G))
  (hE₁' : ∀ f (k : K), b (Induction.eval _ _ (E₁' f) k) = Induction.eval _ _ f (k : G))

include hlin hE₀ hE₁ hE₀' hE₁' hMc in
set_option backward.isDefEq.respectTransparency.types false in
/-- Two compact operators representing the same weak standard integral in
compatible inducing coordinates commute with the fixed compact reindexing. -/
theorem compactIntegral_reindex_square
    (J : C[d,A] →ₗ[ℂ] C[c,A]) (J' : C[d',B] →ₗ[ℂ] C[c',B])
    (hJ : ∀ v, HasIntegral d du W A₁ qm (E₀.symm v) (Induction.eval _ _ (E₁.symm (J v))))
    (hJ' : ∀ v, HasIntegral d' du W B₁ qm (E₀'.symm v) (Induction.eval _ _ (E₁'.symm (J' v)))) :
    J'.comp (R[d,d']).toLinearMap = (R[c,c']).toLinearMap.comp J := by
  subst M'
  obtain rfl : e = ContinuousMulEquiv.refl M := ContinuousMulEquiv.ext fun x => Subtype.ext (he x)
  let R₀ := compactPictureReindex (M' := M) rfl (ContinuousMulEquiv.refl M) (fun _ => rfl) A B eB d d' K
  let R₁ := compactPictureReindex (M' := M) rfl (ContinuousMulEquiv.refl M) (fun _ => rfl) A B eB c c' K
  have he₀ (v : C[d,A]) (k : K) : Induction.eval _ _ (R₀ v) k =
      eB (Induction.eval _ (compactPictureInducingRepresentation d K A) v k) :=
    compactPictureReindex_eval rfl (ContinuousMulEquiv.refl M) (fun _ => rfl) A B eB d d' K v k
  have he₁ (v : C[c,A]) (k : K) : Induction.eval _ _ (R₁ v) k =
      eB (Induction.eval _ (compactPictureInducingRepresentation c K A) v k) :=
    compactPictureReindex_eval rfl (ContinuousMulEquiv.refl M) (fun _ => rfl) A B eB c c' K v k
  change J'.comp R₀.toLinearMap = R₁.toLinearMap.comp J
  apply LinearMap.ext
  intro v
  let F := E₀.symm v
  let F' := inducedMap d du eB₁.toIntertwiningMap F
  have hsrc : E₀' F' = R₀ v := by
    apply Subtype.ext
    apply Subtype.ext
    funext k
    change Induction.eval _ _ (E₀' F') k = Induction.eval _ _ (R₀ v) k
    apply b.injective
    rw [hE₀', he₀, ← hlin]
    change eB₁ (Induction.eval _ _ F (k : G)) = eB₁ (a (Induction.eval _ _ v k))
    have h := hE₀ F k
    rw [E₀.apply_symm_apply] at h
    exact congrArg eB₁ h.symm
  have hF' : E₀'.symm (R₀ v) = F' := by rw [← hsrc, E₀'.symm_apply_apply]
  have hA := HasIntegral.map_induced d du W qm eB₁.toIntertwiningMap (hJ v)
  have hB := hJ' (R₀ v)
  rw [hF'] at hB
  change J' (R₀ v) = R₁ (J v)
  apply Subtype.ext
  apply Subtype.ext
  funext k
  change Induction.eval _ _ (J' (R₀ v)) k = Induction.eval _ _ (R₁ (J v)) k
  apply b.injective
  rw [he₁, ← hlin]
  have hAout := hE₁ (E₁.symm (J v)) k
  have hBout := hE₁' (E₁'.symm (J' (R₀ v))) k
  rw [E₁.apply_symm_apply] at hAout
  rw [E₁'.apply_symm_apply] at hBout
  exact hBout.trans ((HarmonicAnalysis.SmoothWeakIntegral.HasIntegral.unique
    (compactCofinal hMc) B₁.property (hB (k : G)) (hA (k : G))).trans
      ((congrArg (fun a₁ : A₁ => eB₁ a₁) hAout).symm))

end Literal

end Langlands.Plancherel.StandardIntertwining
