/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs
public import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Sites.LocallySurjective
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits

/-!
# Local support of an open extension

## References

* Stacks Project, Tags 00WK and 09AE
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

/-- Locally a section of an open extension is zero or its test object factors
through the open. Take the image sieve of the sheafification unit. If a test object
does not factor, the comma category computing the presheaf extension is empty, so
its value is zero and its representative maps to zero. -/
theorem openExtension_localSupport (R : Type (u + 1)) [Ring R]
    {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]
    (F : Sheaf (ProEt.topology U) (ModuleCat.{u + 1} R)) (Q : X.ProEt)
    (s : ((openImmersionLowerShriek (ModuleCat.{u + 1} R) j).obj F).obj.obj (op Q)) :
    ∃ S : Sieve Q, S ∈ ProEt.topology X Q ∧
      ∀ (Z : X.ProEt) (f : Z ⟶ Q), S f →
        (∃ g : Z.left ⟶ U, g ≫ j = Z.hom) ∨
          ((openImmersionLowerShriek (ModuleCat.{u + 1} R) j).obj F).obj.map f.op s = 0 := by
  classical
  let : (ProEt.topology X).PreservesSheafification (forget (ModuleCat.{u + 1} R)) :=
    inferInstance
  let L := MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale j)
  let P := L.op.lan.obj F.obj
  let η := toSheafify (ProEt.topology X) P
  have : Presheaf.IsLocallySurjective (ProEt.topology X) η :=
    Presheaf.isLocallySurjective_toSheafify' (ProEt.topology X) P
  refine ⟨Presheaf.imageSieve η s, Presheaf.imageSieve_mem _ _ _, ?_⟩
  intro Z f hf
  by_cases hz : ∃ g : Z.left ⟶ U, g ≫ j = Z.hom
  · exact Or.inl hz
  · right
    have : IsEmpty (CostructuredArrow L.op (op Z)) := by
      refine ⟨fun c ↦ hz ⟨c.hom.unop.left ≫ c.left.unop.hom, ?_⟩⟩
      have hw : c.hom.unop.left ≫ (c.left.unop.hom ≫ j) = Z.hom :=
        MorphismProperty.Over.w c.hom.unop
      exact (Category.assoc _ _ _).trans hw
    have hI := (isColimitEquivIsInitialOfIsEmpty _ _)
      (L.op.isPointwiseLeftKanExtensionLeftKanExtensionUnit F.obj (op Z))
    have : Subsingleton (P.obj (op Z)) := ModuleCat.subsingleton_of_isZero hI.isZero
    obtain ⟨t, ht⟩ := hf
    exact ht.symm.trans ((congrArg (η.app (op Z)) (Subsingleton.elim t 0)).trans
      (map_zero (η.app (op Z)).hom))

end AlgebraicGeometry.ProEtale
