import Langlands.Shimura.Unitary.ImaginaryQuadraticSplitPoints

/-!
# The split similitude points as topological groups

For a topological commutative `L`-algebra `S`, give `S ⊗[L] A` its `S`-module
topology and its units the units topology. The identification
`σ.Points S ≃* (S ⊗[L] A)ˣ × Sˣ` of `ImaginaryQuadraticSplitPoints` is then an
isomorphism of topological groups.
-/

noncomputable section

open scoped TensorProduct
open NumberField

set_option autoImplicit false

universe u v w

namespace Langlands.Shimura.ImaginaryQuadraticSplit

section FactorUnits

variable (L : Type u) (A : Type v) (S : Type w)
variable [CommRing L] [Ring A] [Algebra L A] [CommRing S] [Algebra L S]

/-- The units of `S ⊗[L] A`, with a named carrier on which to install the units
topology of the `S`-module topology. -/
def FactorUnits : Type (max v w) := (S ⊗[L] A)ˣ

instance : Group (FactorUnits L A S) := inferInstanceAs (Group (S ⊗[L] A)ˣ)

instance [TopologicalSpace S] : TopologicalSpace (FactorUnits L A S) :=
  letI : TopologicalSpace (S ⊗[L] A) := moduleTopology S (S ⊗[L] A)
  inferInstanceAs (TopologicalSpace (S ⊗[L] A)ˣ)

instance [TopologicalSpace S] [IsTopologicalRing S] [Module.Finite L A] :
    IsTopologicalGroup (FactorUnits L A S) := by
  let : TopologicalSpace (S ⊗[L] A) := moduleTopology S (S ⊗[L] A)
  let : IsTopologicalRing (S ⊗[L] A) := IsModuleTopology.isTopologicalRing S _
  exact inferInstanceAs (IsTopologicalGroup (S ⊗[L] A)ˣ)

end FactorUnits

variable {L : Type u} [Field L] [NumberField L] [IsCMField L] [Algebra.IsQuadraticExtension ℚ L]
variable {A : Type v} [Ring A] [Algebra ℚ A] [Algebra L A]
variable {S : Type w} [CommRing S] [Algebra ℚ S] [Algebra L S]

variable (L A S) in
/-- The section `s ⊗ a ↦ e (s ⊗ a)` is `S`-linear. -/
def liftLinearMap : S ⊗[L] A →ₗ[S] S ⊗[ℚ] A where
  toFun := liftAddHom L A S
  map_add' := map_add (liftAddHom L A S)
  map_smul' t x := by
    induction x using TensorProduct.inductionOn with
    | tmul s a =>
      rw [TensorProduct.smul_tmul', liftAddHom_tmul, liftAddHom_tmul, RingHom.id_apply,
        ← mul_smul_comm, TensorProduct.smul_tmul']
    | add x y hx hy =>
      rw [smul_add, map_add, hx, hy, map_add, smul_add]

@[simp] theorem liftLinearMap_apply (x : S ⊗[L] A) :
    liftLinearMap L A S x = liftAddHom L A S x := rfl

variable (σ : AlgebraInvolution ℚ A)

section Topology

variable [TopologicalSpace S]

theorem continuous_pointsEquiv (hσ : IsConjugationOn L σ) :
    Continuous (Y := FactorUnits L A S × Sˣ) (pointsEquiv σ S hσ) := by
  let : TopologicalSpace (S ⊗[ℚ] A) := moduleTopology S (S ⊗[ℚ] A)
  let : TopologicalSpace (S ⊗[L] A) := moduleTopology S (S ⊗[L] A)
  let : ContinuousAdd (S ⊗[L] A) := ModuleTopology.continuousAdd S _
  let : ContinuousSMul S (S ⊗[L] A) := ModuleTopology.continuousSMul S _
  have hπ : Continuous (projection L A S) :=
    IsModuleTopology.continuous_of_linearMap (projection L A S).toLinearMap
  exact ((hπ.units_map (projection L A S).toRingHom.toMonoidHom).comp
    (continuous_fst.comp continuous_subtype_val)).prodMk
    (continuous_snd.comp continuous_subtype_val)

theorem continuous_pointsEquiv_symm (hσ : IsConjugationOn L σ) :
    Continuous (X := FactorUnits L A S × Sˣ) (pointsEquiv σ S hσ).symm := by
  let : TopologicalSpace (S ⊗[ℚ] A) := moduleTopology S (S ⊗[ℚ] A)
  let : TopologicalSpace (S ⊗[L] A) := moduleTopology S (S ⊗[L] A)
  let : ContinuousAdd (S ⊗[ℚ] A) := ModuleTopology.continuousAdd S _
  let : ContinuousSMul S (S ⊗[ℚ] A) := ModuleTopology.continuousSMul S _
  have hψ : Continuous (liftAddHom L A S) :=
    IsModuleTopology.continuous_of_linearMap (liftLinearMap L A S)
  have hτ : Continuous (σ.baseChange S) :=
    IsModuleTopology.continuous_of_linearMap (σ.baseChange S).linear
  -- the value `ψ a + c • τ (ψ a⁻¹)` and the value of the inverse at `(a⁻¹, c⁻¹)`
  have hval : Continuous fun p : (S ⊗[L] A)ˣ × Sˣ =>
      liftAddHom L A S (p.1 : S ⊗[L] A) +
        (p.2 : S) • σ.baseChange S (liftAddHom L A S ((p.1⁻¹ : (S ⊗[L] A)ˣ) : S ⊗[L] A)) :=
    (hψ.comp (Units.continuous_val.comp continuous_fst)).add
      ((Units.continuous_val.comp continuous_snd).smul
        (hτ.comp (hψ.comp (Units.continuous_coe_inv.comp continuous_fst))))
  have hinv : Continuous fun p : (S ⊗[L] A)ˣ × Sˣ =>
      liftAddHom L A S ((p.1⁻¹ : (S ⊗[L] A)ˣ) : S ⊗[L] A) +
        ((p.2⁻¹ : Sˣ) : S) • σ.baseChange S (liftAddHom L A S (p.1 : S ⊗[L] A)) :=
    (hψ.comp (Units.continuous_coe_inv.comp continuous_fst)).add
      ((Units.continuous_coe_inv.comp continuous_snd).smul
        (hτ.comp (hψ.comp (Units.continuous_val.comp continuous_fst))))
  refine Continuous.subtype_mk (Continuous.prodMk ?_ continuous_snd) _
  exact Units.continuous_iff.mpr ⟨hval, hinv⟩

/-- The identification of `pointsEquiv` as an isomorphism of topological groups, for the
`S`-module topologies of `S ⊗[ℚ] A` and `S ⊗[L] A`. -/
def pointsHomeomorph (hσ : IsConjugationOn L σ) : σ.Points S ≃ₜ* FactorUnits L A S × Sˣ where
  toMulEquiv := pointsEquiv σ S hσ
  continuous_toFun := continuous_pointsEquiv σ hσ
  continuous_invFun := continuous_pointsEquiv_symm σ hσ

@[simp] theorem pointsHomeomorph_apply (hσ : IsConjugationOn L σ) (g : σ.Points S) :
    pointsHomeomorph σ hσ g = pointsEquiv σ S hσ g := rfl

@[simp] theorem pointsHomeomorph_symm_apply (hσ : IsConjugationOn L σ)
    (p : FactorUnits L A S × Sˣ) :
    (pointsHomeomorph σ hσ).symm p = (pointsEquiv σ S hσ).symm p := rfl

end Topology

end Langlands.Shimura.ImaginaryQuadraticSplit
