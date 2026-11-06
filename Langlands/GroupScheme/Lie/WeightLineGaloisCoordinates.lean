import Langlands.GroupScheme.Lie.WeightSupportGalois
import Langlands.GroupScheme.Rational.RootGaloisOrbits
import Langlands.LinearAlgebra.GaloisLineDescent

/-! # Stabilizer-compatible coordinates on actual Lie weight lines -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme
namespace Lie

variable (k L : Type u) [CommRing k] [CommRing L] [Algebra k L]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]

local notation "b" => algebraBaseMap k L
local notation "G_L" => CategoryTheory.Functor.obj (GroupScheme.baseChange (algebraBaseMap k L)) G

local instance : IsAffineHom (G_L).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

@[simp] theorem baseChangeGaloisEquiv_one (x : Additive (lieKernel G_L L)) :
    baseChangeGaloisEquiv k L G 1 x = x := by
  rw [baseChangeGaloisEquiv_apply]
  change (kernelBaseChangeLinearEquiv k L G L).symm
    (lieKernelMapLinear G (AlgHom.id k L) (kernelBaseChangeLinearEquiv k L G L x)) = x
  rw [kernelCoefficientMap_id, LinearEquiv.symm_apply_apply]

theorem baseChangeGaloisEquiv_mul (σ τ : L ≃ₐ[k] L)
    (x : Additive (lieKernel G_L L)) :
    baseChangeGaloisEquiv k L G (σ * τ) x =
      baseChangeGaloisEquiv k L G σ (baseChangeGaloisEquiv k L G τ x) := by
  simp only [baseChangeGaloisEquiv_apply, LinearEquiv.apply_symm_apply]
  change (kernelBaseChangeLinearEquiv k L G L).symm
    (lieKernelMapLinear G (σ.toAlgHom.comp τ.toAlgHom)
      (kernelBaseChangeLinearEquiv k L G L x)) = _
  rw [kernelCoefficientMap_comp]

/-- The canonical coefficient maps give an actual additive Galois action. -/
@[instance_reducible]
def baseChangeGaloisAction : DistribMulAction (L ≃ₐ[k] L) (Additive (lieKernel G_L L)) where
  smul σ x := baseChangeGaloisEquiv k L G σ x
  one_smul := baseChangeGaloisEquiv_one k L G
  mul_smul := baseChangeGaloisEquiv_mul k L G
  smul_zero σ := (baseChangeGaloisEquiv k L G σ).map_zero
  smul_add σ := (baseChangeGaloisEquiv k L G σ).map_add

attribute [local instance] baseChangeGaloisAction

/-- This action is semilinear for the ordinary action on coefficients. -/
theorem baseChangeGaloisAction_semilinear :
    SMulDistribClass (L ≃ₐ[k] L) L (Additive (lieKernel G_L L)) where
  smul_distrib_smul σ c x := (baseChangeGaloisEquiv k L G σ).map_smulₛₗ c x

end Lie

namespace RelativeRoot

section FixedWeight

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {U : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom U.X.hom]
    (a : AutomorphicAction T.toGrp U)

local instance : IsAffineHom
    ((GroupScheme.baseChange (algebraBaseMap k L)).obj U).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd U.X.hom (algebraBaseMap k L))
  infer_instance

/-- Restrict the canonical action to a subgroup fixing the actual weight character. -/
@[instance_reducible]
def fixedWeightGaloisAction
    (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T))
    (H : Subgroup (L ≃ₐ[k] L))
    (hH : ∀ σ : H, characterLattice.galoisRepresentation k L T σ.val χ = χ) :
    DistribMulAction H (actionWeightSpace (a.baseChange (algebraBaseMap k L)) χ) where
  smul σ x := ⟨Lie.baseChangeGaloisEquiv k L U σ.val x.val, by
    have hx := galois_mem_actionWeightSpace k L a σ.val χ x.property
    rwa [hH σ] at hx⟩
  one_smul x := by
    apply Subtype.ext
    exact Lie.baseChangeGaloisEquiv_one k L U x.val
  mul_smul σ τ x := by
    apply Subtype.ext
    exact Lie.baseChangeGaloisEquiv_mul k L U σ.val τ.val x.val
  smul_zero σ := by
    apply Subtype.ext
    exact (Lie.baseChangeGaloisEquiv k L U σ.val).map_zero
  smul_add σ x y := by
    apply Subtype.ext
    exact (Lie.baseChangeGaloisEquiv k L U σ.val).map_add x.val y.val

/-- Any actual one-dimensional weight space has coordinates compatible with its
coefficient Galois stabilizer. Dimension one is an explicit remaining input. -/
theorem exists_fixedWeight_equivariant_coordinates [FiniteDimensional k L]
    (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T))
    (H : Subgroup (L ≃ₐ[k] L))
    (hH : ∀ σ : H, characterLattice.galoisRepresentation k L T σ.val χ = χ)
    (hV : Module.finrank L (actionWeightSpace (a.baseChange (algebraBaseMap k L)) χ) = 1) :
    ∃ e : L ≃ₗ[L] actionWeightSpace (a.baseChange (algebraBaseMap k L)) χ,
      ∀ (σ : H) (x : L),
        Lie.baseChangeGaloisEquiv k L U σ.val (e x).val = (e (σ.val x)).val := by
  let instAction : DistribMulAction H
      (actionWeightSpace (a.baseChange (algebraBaseMap k L)) χ) :=
    fixedWeightGaloisAction k L a χ H hH
  let : SMul H (actionWeightSpace (a.baseChange (algebraBaseMap k L)) χ) :=
    SemigroupAction.toSMul (self := MulAction.toSemigroupAction
      (self := DistribMulAction.toMulAction (self := instAction)))
  let : SMulDistribClass H L
      (actionWeightSpace (a.baseChange (algebraBaseMap k L)) χ) :=
    ⟨fun σ c x => Subtype.ext
      ((Lie.baseChangeGaloisEquiv k L U σ.val).map_smulₛₗ c x.val)⟩
  obtain ⟨e, he⟩ := Langlands.LinearAlgebra.GaloisLineDescent.exists_equivariant_linearEquiv H hV
  exact ⟨e, fun σ x => congrArg Subtype.val (he σ x)⟩

end FixedWeight
end RelativeRoot

section ActualRoot

variable (k L : Type u) [Field k] [Field L] [Algebra k L] [FiniteDimensional k L]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (j : T.toGrp ⟶ G)

local notation "b" => algebraBaseMap k L
local notation "j_L" => CategoryTheory.Functor.map (GroupScheme.baseChange (algebraBaseMap k L)) j
local notation "T_L" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange (algebraBaseMap k L)) T
local notation "G_L" => CategoryTheory.Functor.obj (GroupScheme.baseChange (algebraBaseMap k L)) G

local instance : IsAffineHom (G_L).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

attribute [local instance] rootsGaloisAction

/-- The actual-root stabilizer gives compatible coordinates whenever its actual
adjoint weight space is a line. This makes no restriction-fiber transitivity claim. -/
theorem exists_rootWeight_equivariant_coordinates
    (β : roots (T := T_L) (G := G_L) j_L)
    (hV : Module.finrank L (weightSpace j_L β.val) = 1) :
    ∃ e : L ≃ₗ[L] weightSpace j_L β.val,
      ∀ (σ : MulAction.stabilizer (L ≃ₐ[k] L) β) (x : L),
        Lie.baseChangeGaloisEquiv k L G σ.val (e x).val = (e (σ.val x)).val := by
  have hH (σ : MulAction.stabilizer (L ≃ₐ[k] L) β) :
      characterLattice.galoisRepresentation k L T σ.val β.val = β.val := by
    exact congrArg Subtype.val (MulAction.mem_stabilizer_iff.mp σ.property)
  have hV' : Module.finrank L
      (RelativeRoot.actionWeightSpace ((AutomorphicAction.conjugation j).baseChange b) β.val) = 1 := by
    rw [AutomorphicAction.baseChange_conjugation, RelativeRoot.actionWeightSpace_conjugation]
    exact hV
  have h := RelativeRoot.exists_fixedWeight_equivariant_coordinates k L
    (AutomorphicAction.conjugation j) β.val (MulAction.stabilizer (L ≃ₐ[k] L) β) hH hV'
  rw [AutomorphicAction.baseChange_conjugation, RelativeRoot.actionWeightSpace_conjugation] at h
  exact h

/-- A chosen linear coordinate on the actual adjoint root line, equivariant for
its actual character stabilizer. The dimension-one hypothesis is retained. -/
def rootWeightEquivariantLinearEquiv
    (β : roots (T := T_L) (G := G_L) j_L)
    (hV : Module.finrank L (weightSpace j_L β.val) = 1) :
    L ≃ₗ[L] weightSpace j_L β.val :=
  Classical.choose (exists_rootWeight_equivariant_coordinates k L j β hV)

/-- The chosen coordinate intertwines canonical Lie Galois transport with the
ordinary automorphism of its coefficient. -/
theorem rootWeightEquivariantLinearEquiv_galois
    (β : roots (T := T_L) (G := G_L) j_L)
    (hV : Module.finrank L (weightSpace j_L β.val) = 1)
    (σ : MulAction.stabilizer (L ≃ₐ[k] L) β) (x : L) :
    Lie.baseChangeGaloisEquiv k L G σ.val
        (rootWeightEquivariantLinearEquiv k L j β hV x).val =
      (rootWeightEquivariantLinearEquiv k L j β hV (σ.val x)).val :=
  Classical.choose_spec (exists_rootWeight_equivariant_coordinates k L j β hV) σ x

end ActualRoot
end Langlands.GroupScheme
