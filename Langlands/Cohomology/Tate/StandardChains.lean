import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality

noncomputable section

universe u

open CategoryTheory MonoidalCategory
open scoped TensorProduct

namespace Langlands.Tate

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {R G : Type u} [CommRing R] [Group G]

/-- The explicit inverse component of Mathlib's bar/standard comparison. -/
lemma diagonalFree_inv_single (n : ℕ) (f : Fin n → G) (g : G) (r : R) :
    (Rep.diagonalSuccIsoFree R G n).inv.hom
        (Finsupp.single f (MonoidAlgebra.single g r)) =
      MonoidAlgebra.single (g • Fin.partialProd f) r := by
  simp only [Rep.diagonalSuccIsoFree, Rep.diagonalSuccIsoTensorTrivial, Iso.trans_inv,
    Rep.hom_comp, Representation.IntertwiningMap.comp_apply]
  have step :
      (Rep.leftRegularTensorTrivialIsoFree R G (Fin n → G)).inv.hom
          (Finsupp.single f (MonoidAlgebra.single g r)) =
        MonoidAlgebra.single g 1 ⊗ₜ[R] MonoidAlgebra.single f r :=
    Representation.leftRegularTensorTrivialIsoFree_symm_apply_single_single f g r
  rw [step]
  simp only [Rep.mkIso_inv, Representation.linearizeOfMulActionIso,
    Representation.Equiv.mk_symm, LinearEquiv.refl_symm, ConcreteCategory.hom_ofHom,
    Action.tensorObj_V, Action.trivial_V, Functor.mapIso_inv, Rep.tensor_V, Rep.tensor_ρ,
    Iso.symm_inv, Functor.Monoidal.μIso_hom, Rep.μ_hom, tensorIso_inv, Rep.hom_tensorHom,
    Representation.IntertwiningMap.tensor_apply, Representation.Equiv.coe_toIntertwiningMap,
    Representation.Equiv.mk_apply, LinearEquiv.refl_apply]
  have key₁ := Representation.linearizeMap_single (k := R)
    (Action.diagonalSuccIsoTensorTrivial G n).inv (g, f) ((1 : R) * r)
  have key₂ := Representation.LinearizeMonoidal.μ_apply_single_single (k := R)
    (X := Action.leftRegular G) (Y := Action.trivial G (Fin n → G)) g f 1 r
  exact ((congrArg (fun z => (Representation.linearizeMap
    (Action.diagonalSuccIsoTensorTrivial G n).inv) z) key₂).trans key₁).trans (by simp)

/-- The explicit forward component of the same comparison. -/
lemma diagonalFree_hom_single (n : ℕ) (c : Fin (n + 1) → G) (r : R) :
    (Rep.diagonalSuccIsoFree R G n).hom.hom (MonoidAlgebra.single c r) =
      Finsupp.single (fun i => (c i.castSucc)⁻¹ * c i.succ) (MonoidAlgebra.single (c 0) r) := by
  apply (Representation.equivOfIso (Rep.diagonalSuccIsoFree R G n)).symm.injective
  have h := diagonalFree_inv_single n (fun i => (c i.castSucc)⁻¹ * c i.succ) (c 0) r
  rw [Fin.partialProd_left_inv] at h
  exact ((Representation.equivOfIso (Rep.diagonalSuccIsoFree R G n)).symm_apply_apply
    (MonoidAlgebra.single c r)).trans h.symm

/-- The existing bar and standard comparisons for actual inhomogeneous chains. -/
def chainsIsoStandard (A : Rep.{u} R G) :
    groupHomology.inhomogeneousChains A ≅ (Rep.standardComplex R G).coinvariantsTensorObj A := by
  classical
  exact groupHomology.inhomogeneousChainsIso A ≪≫
    (((Rep.coinvariantsTensor R G).obj A).mapHomologicalComplex (ComplexShape.down ℕ)).mapIso
      (Rep.barComplex.isoStandardComplex R G)

/-- An inhomogeneous generator becomes its partial-product homogeneous tuple. -/
lemma chainsIsoStandard_hom_single (A : Rep.{u} R G) (n : ℕ)
    (g : Fin n → G) (a : A) :
    (chainsIsoStandard A).hom.f n (Finsupp.single g a) =
      Representation.Coinvariants.mk (A ⊗ (Rep.standardComplex R G).X n).ρ
        (a ⊗ₜ[R] MonoidAlgebra.single (Fin.partialProd g) 1) := by
  classical
  change Representation.Coinvariants.map _ _
      ((𝟙 A) ⊗ₘ (Rep.diagonalSuccIsoFree R G n).inv).hom
        ((Rep.coinvariantsTensorFreeLEquiv A (Fin n → G)).symm (Finsupp.single g a)) =
      Representation.Coinvariants.mk (A ⊗ Rep.diagonal R G (n + 1)).ρ
        (a ⊗ₜ[R] MonoidAlgebra.single (Fin.partialProd g) 1)
  refine (congrArg
    (Representation.Coinvariants.map _ _
      ((𝟙 A) ⊗ₘ (Rep.diagonalSuccIsoFree R G n).inv).hom)
    (Rep.finsuppToCoinvariantsTensorFree_single (A := A) g a)).trans ?_
  change Representation.Coinvariants.mk (A ⊗ Rep.diagonal R G (n + 1)).ρ
      (a ⊗ₜ[R] (Rep.diagonalSuccIsoFree R G n).inv.hom
        (Finsupp.single g (MonoidAlgebra.single 1 1))) = _
  exact congrArg (fun b : MonoidAlgebra R (Fin (n + 1) → G) =>
    Representation.Coinvariants.mk (A ⊗ Rep.diagonal R G (n + 1)).ρ (a ⊗ₜ[R] b))
    ((diagonalFree_inv_single n g 1 1).trans (by rw [one_smul]))

/-- Homogeneous generators return to the usual inhomogeneous coordinates and coefficient action. -/
lemma chainsIsoStandard_inv_single (A : Rep.{u} R G) (n : ℕ)
    (c : Fin (n + 1) → G) (a : A) (r : R) :
    (chainsIsoStandard A).inv.f n
        (Representation.Coinvariants.mk (A ⊗ (Rep.standardComplex R G).X n).ρ
          (a ⊗ₜ[R] MonoidAlgebra.single c r)) =
      Finsupp.single (fun i => (c i.castSucc)⁻¹ * c i.succ) (r • A.ρ (c 0)⁻¹ a) := by
  classical
  change Rep.coinvariantsTensorFreeLEquiv A (Fin n → G)
      (Representation.Coinvariants.map _ _
        ((𝟙 A) ⊗ₘ (Rep.diagonalSuccIsoFree R G n).hom).hom
          (Representation.Coinvariants.mk _
            (a ⊗ₜ[R] MonoidAlgebra.single c r))) = _
  change Rep.coinvariantsTensorFreeLEquiv A (Fin n → G)
      (Representation.Coinvariants.mk (A ⊗ Rep.free R G (Fin n → G)).ρ
        (a ⊗ₜ[R] (Rep.diagonalSuccIsoFree R G n).hom.hom
          (MonoidAlgebra.single c r))) = _
  refine (congrArg (fun b : (Fin n → G) →₀ MonoidAlgebra R G =>
      Rep.coinvariantsTensorFreeLEquiv A (Fin n → G)
        (Representation.Coinvariants.mk (A ⊗ Rep.free R G (Fin n → G)).ρ (a ⊗ₜ[R] b)))
      (diagonalFree_hom_single n c r)).trans ?_
  change Rep.coinvariantsTensorFreeToFinsupp A (Fin n → G)
      (Representation.Coinvariants.mk (A.ρ.tprod (Representation.free R G (Fin n → G)))
        (a ⊗ₜ[R] Finsupp.single (fun i => (c i.castSucc)⁻¹ * c i.succ)
          (MonoidAlgebra.single (c 0) r))) = _
  have h := Rep.coinvariantsTensorFreeToFinsupp_mk_tmul_single
    (k := R) (G := G) (A := A) (α := Fin n → G)
    a (fun i => (c i.castSucc)⁻¹ * c i.succ) (c 0) r
  convert h using 1

end Langlands.Tate
