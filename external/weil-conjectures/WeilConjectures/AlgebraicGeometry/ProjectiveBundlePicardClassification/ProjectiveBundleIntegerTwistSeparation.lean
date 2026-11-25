/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveBundleQuotientGeometry.ProjectiveBundleQuotientData
public import WeilConjectures.AlgebraicGeometry.Locally.LocallyConstantLineTwist
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import WeilConjectures.AlgebraicGeometry.ProjectiveBundlePicardClassification.ProjectiveBundleFiberDegree

/-!
# Integer twists separate on every nonempty base neighbourhood

## References

* EGA II, Remark 4.2.7
* Stacks, Tag 0BXJ
* EGA II, Remark 4.2.7, printed p.75
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.ProjectiveBundlePicardClassification

open Scheme.Modules ProjectiveBundleQuotientGeometry

private theorem invertible_integerLinePower {X : Scheme.{u}} (A : X.Modules)
    (hA : A.IsInvertible) (m : ℤ) : (integerLinePower A hA m).IsInvertible := by
  have : A.IsInvertible := hA
  have hnat (M : X.Modules) [M.IsInvertible] (n : ℕ) :
      (tensorPowNat M n).IsInvertible := by
    induction n with
    | zero => exact isInvertible_tensorUnit
    | succ n ih =>
      have := ih
      exact IsInvertible.tensorObj M (tensorPowNat M n)
  cases m with
  | ofNat n => exact hnat A n
  | negSucc n => exact hnat (dual A) (n + 1)

/-- Integer twists which agree above a neighbourhood containing a base point have equal degrees.
-/
theorem projective_bundle_integer_twist_separation (S : Scheme.{u}) (E : S.Modules)
    [E.IsQuasicoherent] (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] (hr : 2 ≤ r)
    (D : TautologicalQuotient E) (U : S.Opens) (s : S) (hs : s ∈ U) (m n : ℤ)
    (e : Nonempty ((tensorPullback
      ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U).ι).obj
        (integerLinePower D.line D.invertible m) ≅
      (tensorPullback
        ((SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom ⁻¹ᵁ U).ι).obj
        (integerLinePower D.line D.invertible n))) : m = n := by
  let p := (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom
  let V := p ⁻¹ᵁ U
  let f := p.fiberι s
  have hf : Set.range f ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι, p.range_fiberι]
    intro x hx
    change p x ∈ U
    have hx' : p x = s := hx
    rw [hx']
    exact hs
  let g := IsOpenImmersion.lift V.ι f hf
  have hg : g ≫ V.ι = f := IsOpenImmersion.lift_fac V.ι f hf
  let c : tensorPullback f ≅ tensorPullback V.ι ⋙ tensorPullback g :=
    eqToIso (congrArg (fun h ↦ tensorPullback h) hg.symm) ≪≫
      tensorPullbackSectionComp g V.ι
  obtain ⟨e⟩ := e
  have ef : Nonempty
      ((tensorPullback f).obj (integerLinePower D.line D.invertible m) ≅
        (tensorPullback f).obj (integerLinePower D.line D.invertible n)) :=
    ⟨c.app _ ≪≫ (tensorPullback g).mapIso e ≪≫ (c.app _).symm⟩
  obtain ⟨d, _, hd⟩ := projective_bundle_fiber_degree S E r hr D
    (integerLinePower D.line D.invertible m)
    (invertible_integerLinePower D.line D.invertible m) s
  exact (hd m ⟨Iso.refl _⟩).trans (hd n ef).symm

end AlgebraicGeometry.ProjectiveBundlePicardClassification
