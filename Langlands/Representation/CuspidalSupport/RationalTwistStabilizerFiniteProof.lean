import Langlands.Representation.CuspidalSupport.RationalTwistStabilizerFiniteStatement
import Langlands.Representation.CuspidalSupport.RationalNormKernelCentralFiniteIndex
import Langlands.Representation.Plancherel.TwistStabilizerComparison
import Langlands.Representation.Schur.RationalPoints

/-! # Finite unramified twist stabilizers (Renard V.2.7) -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

/-- Renard V.2.7: the unramified stabilizer of any irreducible smooth complex
representation of the actual rational-point group is finite. -/
theorem rationalTwistStabilizerFinite :
    RationalTwistStabilizerFiniteStatement.{uF, uV} := by
  intro F _ _ _ _ G hG
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := hG.smooth
  let : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
  have : IsTopologicalGroup (GroupScheme.rationalPoints G) :=
    rationalPoint_isTopologicalGroup F G
  intro A hA
  let ν := fun chi => (rationalNormCharacters G chi).toMul
  let Z := Subgroup.center (GroupScheme.rationalPoints G)
  have : (commonNormKernel ν ⊔ Z).FiniteIndex :=
    rationalCommonNormKernel_sup_center_finiteIndex F G hG
  have : Finite (centralTrivialUnramifiedCharacters ν Z) :=
    finite_centralTrivialUnramifiedCharacters ν Z
  apply (Set.toFinite (centralTrivialUnramifiedCharacters ν Z :
    Set (unramifiedCharacters ν))).subset
  intro χ hχ
  apply (mem_centralTrivialUnramifiedCharacters ν Z χ).mpr
  intro z
  obtain ⟨iso⟩ := hχ
  let e : A.representation.Equiv (twist χ.val.toMonoidHom A.representation) :=
    SmoothRep.equivOfIso iso.symm
  let T : A.representation.IntertwiningMap A.representation :=
    { toLinearMap := A.representation z
      isIntertwining' := fun g => by
        change A.representation (z : GroupScheme.rationalPoints G) * A.representation g =
          A.representation g * A.representation (z : GroupScheme.rationalPoints G)
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp z.property g] }
  obtain ⟨c, hc, -⟩ := Schur.rationalPoint_scalarEndomorphism F G hG A hA T
  have act (x : A) : A.representation z x = c • x :=
    congrArg (fun f : A.representation.IntertwiningMap A.representation => f x) hc
  have := hA
  have : Nontrivial A :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GroupScheme.rationalPoints G))
      A.representation.asModule
  obtain ⟨v, hv⟩ := exists_ne (0 : A)
  have hc0 : c ≠ 0 := by
    intro h
    have hact := act (A.representation (z : GroupScheme.rationalPoints G)⁻¹ v)
    rw [h, zero_smul, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one] at hact
    exact hv hact
  have hev : e v ≠ 0 := by
    intro h
    apply hv
    apply e.toLinearEquiv.injective
    change e.toLinearEquiv v = 0 at h
    simpa only [map_zero] using h
  have he := Representation.IntertwiningMap.isIntertwining
    A.representation (twist χ.val.toMonoidHom A.representation)
    e.toIntertwiningMap (z : GroupScheme.rationalPoints G) v
  change e (A.representation z v) =
    (χ.val z : ℂ) • A.representation z (e v) at he
  rw [act, map_smul, act, smul_smul] at he
  have hscalar : c = (χ.val z : ℂ) * c := smul_left_injective ℂ hev he
  apply Units.ext
  exact mul_right_cancel₀ hc0 (by simpa using hscalar.symm)

end Langlands.CuspidalSupport
