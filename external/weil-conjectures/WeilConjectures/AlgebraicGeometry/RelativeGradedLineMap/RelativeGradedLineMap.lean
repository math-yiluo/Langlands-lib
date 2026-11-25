/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.RelativeProj.Basic
public import WeilConjectures.AlgebraicGeometry.Tensor.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.AlgebraicSpace.SpaceLineModuleProjInput

/-! # Relative graded maps into tensor powers of a line module

## References

* Stacks Project, Constructions, Tag 01O9
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- A graded algebra map on affine base opens into tensor powers of an invertible module. -/
structure RelativeGradedLineMap {Z S : Scheme.{u}} (h : Z ⟶ S)
    (A : S.GradedAlgebraData) (L : Z.Modules) where
  component (V : S.affineOpens) (n : ℕ) :
    A.grading V n →+ Γ(L.tensorPow n, h ⁻¹ᵁ V.1)
  smul (V : S.affineOpens) (n : ℕ) (r : Γ(S, V.1)) (a : A.grading V n) :
    component V n (r • a) = h.app V.1 r • component V n a
  one (V : S.affineOpens) :
    component V 0 ⟨1, SetLike.one_mem_graded (A.grading V)⟩ =
      unitSectionsEquiv (h ⁻¹ᵁ V.1) 1
  mul (V : S.affineOpens) (m n : ℕ) (a : A.grading V m) (b : A.grading V n) :
    component V (m + n) ⟨a * b, SetLike.mul_mem_graded a.property b.property⟩ =
      (L.tensorPowAddIso m n).inv.app (h ⁻¹ᵁ V.1)
        (tmulSection (component V m a) (component V n b))
  restriction {V W : S.affineOpens} (q : V ≤ W) (n : ℕ) (a : A.grading W n) :
    component V n ⟨A.res q a, (A.res q).map_mem a.property⟩ =
      (L.tensorPow n).val.map (homOfLE (h.preimage_mono q)).op (component W n a)

/-- Pull the component of a graded line map to a scheme chart. -/
noncomputable def RelativeGradedLineMap.evaluate
    {Z S : Scheme.{u}} {h : Z ⟶ S} {A : S.GradedAlgebraData} {L : Z.Modules}
    (ψ : RelativeGradedLineMap h A L) {W : Scheme.{u}} (j : W ⟶ Z)
    (V : S.affineOpens) (q : (⊤ : W.Opens) ≤ j ⁻¹ᵁ (h ⁻¹ᵁ V.1))
    (n : ℕ) (a : A.grading V n) :
    Γ(((tensorPullback j).obj L).tensorPow n, ⊤) :=
  (boundaryPullbackPowIso j L n).hom.app ⊤
    (((tensorPullback j).obj (L.tensorPow n)).val.map (homOfLE q).op
      (((tensorPullbackSectionAdjunction j).unit.app (L.tensorPow n)).app (h ⁻¹ᵁ V.1)
        (ψ.component V n a)))

/-- Positive-degree images generate the line module everywhere. -/
def RelativeGradedLineMap.GeneratesEverywhere
    {Z S : Scheme.{u}} {h : Z ⟶ S} {A : S.GradedAlgebraData} {L : Z.Modules}
    (ψ : RelativeGradedLineMap h A L) : Prop :=
  ∀ x : Z, ∃ (V : S.affineOpens) (hx : x ∈ h ⁻¹ᵁ V.1) (n : ℕ), 0 < n ∧
    ∃ a : A.grading V n,
      (TopCat.Presheaf.germ (L.tensorPow n).val.presheaf (h ⁻¹ᵁ V.1) x hx)
          (ψ.component V n a) ∉
        (IsLocalRing.maximalIdeal (Z.presheaf.stalk x)) •
          (⊤ : Submodule (Z.presheaf.stalk x)
            ↑(TopCat.Presheaf.stalk (L.tensorPow n).val.presheaf x))

/-- The usual homogeneous-fraction characterization of the canonical map to relative Proj. -/
def RelativeGradedLineMap.IsCanonicalMap
    {Z S : Scheme.{u}} {h : Z ⟶ S} {A : S.GradedAlgebraData} {L : Z.Modules}
    (ψ : RelativeGradedLineMap h A L) (r : Z ⟶ A.relProj) : Prop :=
  r ≫ A.relProjHom = h ∧
    ∀ (W : Scheme.{u}) (j : W ⟶ Z), IsOpenImmersion j →
      ∀ (V : S.affineOpens)
        (q : (⊤ : W.Opens) ≤ j ⁻¹ᵁ (h ⁻¹ᵁ V.1))
        (e : (tensorPullback j).obj L ≅ SheafOfModules.unit W.ringCatSheaf)
        (α : A.obj V →+* Γ(W, ⊤)),
        (∀ (n : ℕ) (a : A.grading V n), α a =
          (unitSectionsEquiv ⊤).symm
            ((AlgebraicSpace.trivializedPower e n).hom.app ⊤
              (ψ.evaluate j V q n a))) →
        ∀ hα : Ideal.map α (HomogeneousIdeal.irrelevant (A.grading V)).toIdeal = ⊤,
          j ≫ r = Proj.fromOfGlobalSections (A.grading V) α hα ≫ A.relProjι V

end AlgebraicGeometry.Scheme.Modules
