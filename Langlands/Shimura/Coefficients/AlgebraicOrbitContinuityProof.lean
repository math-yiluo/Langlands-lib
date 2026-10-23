import Langlands.Shimura.Coefficients.AlgebraicOrbitContinuityStatement
import Langlands.Shimura.Unitary.SimilitudeCoordinates
import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Continuity of algebraic coefficient orbit maps

Naturality along the classifying map of a point expresses the action of that
point through the action of the universal similitude over the coordinate ring.
The classifying map is polynomial evaluation at the coordinates of the point,
which depend continuously on the point.
-/

noncomputable section

universe u

namespace Langlands.Shimura.AlgebraInvolution

open scoped TensorProduct
open MvPolynomial

variable {K A : Type u} [CommRing K] [Ring A] [Algebra K A]
variable (σ : AlgebraInvolution K A)
variable {ι : Type u} [Fintype ι] (b : Module.Basis ι K A)

section Classifying

variable {S : Type u} [CommRing S] [Algebra K S] [TopologicalSpace S] [IsTopologicalRing S]

/-- Each value of the classifying map depends continuously on the point. -/
theorem continuous_similitudeHom_apply (c : σ.similitudeCoordinateRing b) :
    Continuous fun g : σ.Points S => σ.similitudeHom b g c := by
  let : TopologicalSpace (S ⊗[K] A) := moduleTopology S (S ⊗[K] A)
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mkₐ_surjective K (σ.similitudeIdeal b) c
  have hunit : Continuous fun g : σ.Points S => ((g.1.1 : (S ⊗[K] A)ˣ) : S ⊗[K] A) :=
    Units.continuous_val.comp (continuous_fst.comp continuous_subtype_val)
  have hunitInv :
      Continuous fun g : σ.Points S => (((g.1.1)⁻¹ : (S ⊗[K] A)ˣ) : S ⊗[K] A) :=
    Units.continuous_coe_inv.comp (continuous_fst.comp continuous_subtype_val)
  have hcoord (i : ι) : Continuous fun x : S ⊗[K] A => coordinate b x i :=
    IsModuleTopology.continuous_of_linearMap
      ((Finsupp.lapply i).comp (Algebra.TensorProduct.basis S b).repr.toLinearMap)
  have hvalues : Continuous fun g : σ.Points S => σ.similitudeValues b g := by
    refine continuous_pi fun v => ?_
    cases v with
    | unit i => exact (hcoord i).comp hunit
    | unitInv i => exact (hcoord i).comp hunitInv
    | multiplier => exact Units.continuous_val.comp (continuous_snd.comp continuous_subtype_val)
    | multiplierInv =>
      exact Units.continuous_coe_inv.comp (continuous_snd.comp continuous_subtype_val)
  have h : (fun g : σ.Points S => σ.similitudeHom b g (σ.similitudeQuotient b p)) =
      fun g => eval (σ.similitudeValues b g) (MvPolynomial.map (algebraMap K S) p) :=
    funext fun g => (σ.similitudeHom_quotient b g p).trans (by rw [aeval_def, eval_map])
  rw [h]
  exact (MvPolynomial.continuous_eval _).comp hvalues

end Classifying

namespace AlgebraicRepresentation

variable {σ}
variable {W : Type u} [AddCommGroup W] [Module K W]

/-- Naturality along the classifying map: a point acts on `1 ⊗ w` by
specializing the action of the universal similitude. -/
theorem act_one_tmul (ρ : σ.AlgebraicRepresentation W) {S : Type u} [CommRing S]
    [Algebra K S] (g : σ.Points S) (w : W) :
    ρ.act S g ((1 : S) ⊗ₜ[K] w) =
      (σ.similitudeHom b g).toLinearMap.rTensor W
        (ρ.act (σ.similitudeCoordinateRing b) (σ.universalSimilitude b)
          ((1 : σ.similitudeCoordinateRing b) ⊗ₜ[K] w)) := by
  have h := ρ.naturality (σ.similitudeHom b g) (σ.universalSimilitude b)
    ((1 : σ.similitudeCoordinateRing b) ⊗ₜ[K] w)
  have hg : σ.pointsMap (σ.similitudeHom b g) (σ.universalSimilitude b) = g :=
    σ.similitudePoint_similitudeHom b g
  rw [hg, LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, _root_.map_one] at h
  exact h

variable {S : Type u} [CommRing S] [Algebra K S] [TopologicalSpace S] [IsTopologicalRing S]

/-- Specializing a fixed element along the classifying map is continuous. -/
theorem continuous_rTensor_similitudeHom
    (y : σ.similitudeCoordinateRing b ⊗[K] W) :
    letI : TopologicalSpace (S ⊗[K] W) := moduleTopology S (S ⊗[K] W)
    Continuous fun g : σ.Points S => (σ.similitudeHom b g).toLinearMap.rTensor W y := by
  let : TopologicalSpace (S ⊗[K] W) := moduleTopology S (S ⊗[K] W)
  have : ContinuousAdd (S ⊗[K] W) := ModuleTopology.continuousAdd S (S ⊗[K] W)
  have : ContinuousSMul S (S ⊗[K] W) := ModuleTopology.continuousSMul S (S ⊗[K] W)
  induction y using TensorProduct.inductionOn with
  | tmul c w =>
    have h : ∀ g : σ.Points S, (σ.similitudeHom b g).toLinearMap.rTensor W (c ⊗ₜ[K] w) =
        σ.similitudeHom b g c • ((1 : S) ⊗ₜ[K] w) := fun g => by
      rw [LinearMap.rTensor_tmul, AlgHom.toLinearMap_apply, TensorProduct.smul_tmul',
        smul_eq_mul, mul_one]
    simp_rw [h]
    exact (σ.continuous_similitudeHom_apply (S := S) b c).smul
      (continuous_const : Continuous fun _ : σ.Points S => (1 : S) ⊗ₜ[K] w)
  | add y z hy hz =>
    simp_rw [map_add]
    exact hy.add hz

/-- Every orbit map of an algebraic representation is continuous. -/
theorem continuous_act [Module.Free K A] [Module.Finite K A]
    (ρ : σ.AlgebraicRepresentation W) (x : S ⊗[K] W) :
    letI : TopologicalSpace (S ⊗[K] W) := moduleTopology S (S ⊗[K] W)
    Continuous fun g : σ.Points S => ρ.act S g x := by
  let b := Module.Free.chooseBasis K A
  let : TopologicalSpace (S ⊗[K] W) := moduleTopology S (S ⊗[K] W)
  have : ContinuousAdd (S ⊗[K] W) := ModuleTopology.continuousAdd S (S ⊗[K] W)
  have : ContinuousSMul S (S ⊗[K] W) := ModuleTopology.continuousSMul S (S ⊗[K] W)
  induction x using TensorProduct.inductionOn with
  | tmul s w =>
    have h : ∀ g : σ.Points S, ρ.act S g (s ⊗ₜ[K] w) =
        s • (σ.similitudeHom b g).toLinearMap.rTensor W
          (ρ.act (σ.similitudeCoordinateRing b) (σ.universalSimilitude b)
            ((1 : σ.similitudeCoordinateRing b) ⊗ₜ[K] w)) := fun g => by
      rw [← act_one_tmul b ρ g w, ← LinearEquiv.map_smul, TensorProduct.smul_tmul',
        smul_eq_mul, mul_one]
    simp_rw [h]
    exact (continuous_const : Continuous fun _ : σ.Points S => s).smul
      (continuous_rTensor_similitudeHom (S := S) b
        (ρ.act (σ.similitudeCoordinateRing b) (σ.universalSimilitude b)
          ((1 : σ.similitudeCoordinateRing b) ⊗ₜ[K] w)))
  | add x y hx hy =>
    simp_rw [map_add]
    exact hx.add hy

end AlgebraicRepresentation

end Langlands.Shimura.AlgebraInvolution

namespace Langlands.Shimura.Coefficients

/-- Naturality of a finite-dimensional algebraic representation forces
continuous orbit maps on points over a topological commutative algebra. -/
theorem algebraicOrbitContinuity : AlgebraicOrbitContinuityStatement.{u} := by
  intro K A W _ _ _ _ _ _ _ σ ρ S _ _ _ _ x
  exact ρ.continuous_act x

end Langlands.Shimura.Coefficients
