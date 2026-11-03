import Langlands.GroupScheme.Rational.KernelCentralizerLie
import Langlands.GroupScheme.Torus.KernelDiagonalizable

/-! # The integral weight image of character-kernel invariants -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000

namespace Diagonalizable

variable {k : Type u} [Field k]
variable (T : CommGroupScheme (Spec (CommRingCat.of k))) (hT : IsSplitTorus T.toGrp)
variable (a : characterLattice T)

/-- The actual kernel point realizing the universal quotient-lattice monomials. -/
def kernelUniversalPoint :
    Lie.AffinePoints (RelativeRoot.characterKernel a)
      (AddMonoidAlgebra k (quotientLattice a)) :=
  let B := AddMonoidAlgebra k (quotientLattice a)
  let U := (algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k B))
  let v := Units.mapEquiv
    (Scheme.ΓSpecIso (CommRingCat.of B)).commRingCatIsoToRingEquiv.toMulEquiv
  (kernelCharacterPointsEquiv T hT a U).symm
    ⟨v.symm.toMonoidHom.comp (quotientUniversalCharacter (CommRingCat.of k) a).val,
      by
        change v.symm ((quotientUniversalCharacter (CommRingCat.of k) a).val (.ofAdd a)) = 1
        rw [(quotientUniversalCharacter (CommRingCat.of k) a).property, map_one]⟩

/-- Every character at the universal kernel point is the monomial at its full quotient class. -/
theorem characterValue_kernelUniversalPoint (b : characterLattice T) :
    Lie.characterValue b
      (kernelUniversalPoint T hT a ≫ (RelativeRoot.characterKernelι a).hom.hom) =
    monomialUnits (CommRingCat.of k) (quotientLattice a) (.ofAdd (quotientMap a b)) := by
  let B := AddMonoidAlgebra k (quotientLattice a)
  let U := (algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k B))
  let v := Units.mapEquiv
    (Scheme.ΓSpecIso (CommRingCat.of B)).commRingCatIsoToRingEquiv.toMulEquiv
  change v ((kernelCharacterPointsEquiv T hT a U
    (kernelUniversalPoint T hT a)).val (.ofAdd b)) = _
  dsimp only [kernelUniversalPoint]
  change v ((kernelCharacterPointsEquiv T hT a U
    ((kernelCharacterPointsEquiv T hT a U).symm _)).val (.ofAdd b)) = _
  rw [MulEquiv.apply_symm_apply]
  exact v.apply_symm_apply _

end Diagonalizable

namespace RelativeRoot

variable {k : Type u} [Field k]
variable (G : GroupScheme (Spec (CommRingCat.of k)))
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
variable (T : CommGroupScheme (Spec (CommRingCat.of k))) (hT : IsSplitTorus T.toGrp)
variable (i : T.toGrp ⟶ G) (a : characterLattice T)

include hT in
/-- Invariance under the actual character kernel forces support in all integral weights. -/
theorem kernelLieInvariants_le_integralWeightSpan :
    kernelLieInvariants i a ≤ integralWeightSpan i a := by
  classical
  intro X hX
  let W := weightSpace i
  let : DirectSum.Decomposition W :=
    (isInternal_weightSpace_of_isSplitTorus k G T hT i).chooseDecomposition
  let d := DirectSum.decompose W X
  have hsum : (∑ χ ∈ d.support, (d χ : Additive (lieKernel G k))) = X :=
    DirectSum.sum_support_decompose W X
  let Q := Diagonalizable.quotientLattice a
  let B := AddMonoidAlgebra k Q
  let c := Diagonalizable.kernelUniversalPoint T hT a
  let t := c ≫ (characterKernelι a).hom.hom
  let z := lieKernelMapLinear G (Algebra.ofId k B)
  have hf : IsScalarTower.toAlgHom (CommRingCat.of k) k B = Algebra.ofId k B := by ext
  have hwt (χ : characterLattice T) :
      adjoint G B (t ≫ i.hom.hom) (z (d χ)) =
        AddMonoidAlgebra.single (Diagonalizable.quotientMap a χ) (1 : k) • z (d χ) := by
    have hw := (mem_weightSpace.mp (d χ).property) B t
    rw [Diagonalizable.characterValue_kernelUniversalPoint] at hw
    exact hw
  have hinv : adjoint G B (t ≫ i.hom.hom) (z X) = z X := by
    simpa only [t, Grp.comp_hom_hom, Category.assoc] using hX B c
  have haction :
      (∑ χ ∈ d.support,
        AddMonoidAlgebra.single (Diagonalizable.quotientMap a χ) (1 : k) • z (d χ)) = z X := by
    calc
      _ = ∑ χ ∈ d.support, adjoint G B (t ≫ i.hom.hom) (z (d χ)) := by
        apply Finset.sum_congr rfl
        intro χ hχ
        exact (hwt χ).symm
      _ = adjoint G B (t ≫ i.hom.hom)
          (z (∑ χ ∈ d.support, (d χ : Additive (lieKernel G k)))) := by
        rw [map_sum, map_sum]
      _ = z X := by rw [hsum, hinv]
  have hconstant (q : Q) (Y : Additive (lieKernel G k)) :
      Lie.kernelCoefficient G k Q q (z Y) = if (0 : Q) = q then Y else 0 := by
    have h := Lie.kernelCoefficient_monomial G q (0 : Q) (1 : k) Y
    rw [hf] at h
    change Lie.kernelCoefficient G k Q q ((1 : B) • z Y) = _ at h
    simpa only [one_smul] using h
  have hzero (b : characterLattice T) (hb : b ∉ AddSubgroup.zmultiples a) :
      (d b : Additive (lieKernel G k)) = 0 := by
    have hbq : Diagonalizable.quotientMap a b ≠ 0 := by
      intro h
      exact hb ((QuotientAddGroup.eq_zero_iff b).mp h)
    let p : Additive (lieKernel G k) →ₗ[k] Additive (lieKernel G k) :=
      (W b).subtype.comp
        ((DirectSum.component k (characterLattice T) (fun χ => W χ) b).comp
          (DirectSum.decomposeLinearEquiv W).toLinearMap)
    have hp (χ : characterLattice T) :
        p (d χ) = if χ = b then (d χ : Additive (lieKernel G k)) else 0 := by
      change (DirectSum.decompose W (d χ : Additive (lieKernel G k)) b :
        Additive (lieKernel G k)) = _
      by_cases hχ : χ = b
      · subst χ
        rw [ite_eq_left rfl]
        exact DirectSum.decompose_of_mem_same W (d b).property
      · rw [ite_eq_right hχ]
        exact DirectSum.decompose_of_mem_ne W (d χ).property hχ
    let F := p.comp (Lie.kernelCoefficient G k Q (Diagonalizable.quotientMap a b))
    have hterm (χ : characterLattice T) :
        F (AddMonoidAlgebra.single (Diagonalizable.quotientMap a χ) (1 : k) • z (d χ)) =
          if χ = b then (d b : Additive (lieKernel G k)) else 0 := by
      change p (Lie.kernelCoefficient G k Q (Diagonalizable.quotientMap a b)
        (AddMonoidAlgebra.single (Diagonalizable.quotientMap a χ) (1 : k) • z (d χ))) = _
      have hm := Lie.kernelCoefficient_monomial G (Diagonalizable.quotientMap a b)
        (Diagonalizable.quotientMap a χ) (1 : k) (d χ : Additive (lieKernel G k))
      rw [hf] at hm
      rw [hm]
      by_cases hχ : χ = b
      · subst χ
        simpa only [ite_true, one_smul] using hp b
      · by_cases hq : Diagonalizable.quotientMap a χ = Diagonalizable.quotientMap a b
        · simp only [ite_eq_left hq, one_smul, hp, ite_eq_right hχ]
        · simp only [ite_eq_right hq, map_zero, ite_eq_right hχ]
    have hconst : F (z X) = 0 := by
      change p (Lie.kernelCoefficient G k Q (Diagonalizable.quotientMap a b) (z X)) = 0
      rw [hconstant, ite_eq_right (Ne.symm hbq), map_zero]
    have hleft :
        F (∑ χ ∈ d.support,
          AddMonoidAlgebra.single (Diagonalizable.quotientMap a χ) (1 : k) • z (d χ)) =
        (d b : Additive (lieKernel G k)) := by
      rw [map_sum]
      calc
        _ = F (AddMonoidAlgebra.single (Diagonalizable.quotientMap a b) (1 : k) • z (d b)) := by
          apply Finset.sum_eq_single b
          · intro χ hχ hχb
            rw [hterm, ite_eq_right hχb]
          · intro hbs
            have hd : d b = 0 := not_not.mp (fun hn => hbs (DFinsupp.mem_support_iff.mpr hn))
            rw [hterm, ite_eq_left rfl, hd, ZeroMemClass.coe_zero]
        _ = (d b : Additive (lieKernel G k)) := by rw [hterm, ite_eq_left rfl]
    exact hleft.symm.trans ((congrArg F haction).trans hconst)
  rw [← hsum]
  apply Submodule.sum_mem
  intro χ hχ
  by_cases hχa : χ ∈ AddSubgroup.zmultiples a
  · obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp hχa
    exact Submodule.mem_iSup_of_mem n (hn ▸ (d χ).property)
  · rw [hzero χ hχa]
    exact Submodule.zero_mem _

end RelativeRoot

end Langlands.GroupScheme
