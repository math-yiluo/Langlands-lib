/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyBoundary
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.BoundaryHorseshoeGlobalLift
import WeilConjectures.AlgebraicGeometry.BoundaryHorseshoeBoundaryIdentification

/-! # A global representative for a horseshoe boundary

Source: Stacks Project, Homology, Tag 0117; Derived Categories, Tags 013T and 015B.
(blueprint: lem-sc-boundary-horseshoe-representative).
-/

@[expose] public section

universe u wC wD
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
/-- A boundary class is represented by the differential of a global lift through the
middle horseshoe resolution. No cover or Cech comparison is involved.
Source: Stacks Project, Homology, Tag 0117 (snake construction); Derived Categories,
Tags 013T and 015B (resolution and derived-triangle compatibility).
(blueprint: lem-sc-boundary-horseshoe-representative).

Proof:
1. Each horseshoe row splits because its first term is injective. Applying global
sections preserves its splitting identities and hence gives short exact rows.
Lift the augmentation of q in IC^0(X) to a section b in IB^0(X).
2. Naturality of beta and the augmentation identity imply beta(d b) = d(aug q) = 0.
Exactness of the degree-one global row lifts d b uniquely to a section a in IA^1(X).
The degree-two inclusion is monic and alpha is a chain map, so d a = 0.
3. The concrete snake formula on the global horseshoe complexes sends the class of
aug q to [a]. The degree-zero resolution identification sends toRightDerivedZero(q)
to [aug q]. The horseshoe/derived-triangle compatibility identifies this snake map
with moduleCohomologyBoundary. Transport by isoRightDerivedObj gives the last equation.
The argument includes q = 0 and zero objects: all lifts may then be zero. -/
theorem boundary_horseshoe_representative (X : Scheme.{u})
    [HasDerivedCategory.{wC} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wD} (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))]
    [EnoughInjectives X.Modules]
    [EnoughInjectives (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [(RingedSpace.globalSectionsFunctor X.toRingedSpace).Additive]
    (S : ShortComplex X.Modules)
    (IA : InjectiveResolution S.X₁) (IB : InjectiveResolution S.X₂)
    (IC : InjectiveResolution S.X₃)
    (α : IA.cocomplex ⟶ IB.cocomplex) (β : IB.cocomplex ⟶ IC.cocomplex)
    (hαβ : α ≫ β = 0)
    (hιA : IA.ι ≫ α = (CochainComplex.single₀ X.Modules).map S.f ≫ IB.ι)
    (hιB : IB.ι ≫ β = (CochainComplex.single₀ X.Modules).map S.g ≫ IC.ι)
    (hrows : ∀ k : ℕ, ((ShortComplex.mk α β hαβ).map
      (HomologicalComplex.eval X.Modules (ComplexShape.up ℕ) k)).ShortExact)
    (hS : S.ShortExact) (q : S.X₃.val.obj (op ⊤)) :
    ∃ (b : (IB.cocomplex.X 0).val.obj (op ⊤))
      (a : (RingedSpace.globalSectionsComplex IA).cycles 1),
      (β.f 0).val.app (op ⊤) b = (IC.ι.f 0).val.app (op ⊤) q ∧
      (α.f 1).val.app (op ⊤)
        ((RingedSpace.globalSectionsComplex IA).iCycles 1 a) =
          (IB.cocomplex.d 0 1).val.app (op ⊤) b ∧
      (IA.isoRightDerivedObj (RingedSpace.globalSectionsFunctor X.toRingedSpace) 1).hom
        (RingedSpace.moduleCohomologyBoundary X.toRingedSpace S hS 0
          ((RingedSpace.globalSectionsFunctor X.toRingedSpace).toRightDerivedZero.app S.X₃ q)) =
        (RingedSpace.globalSectionsComplex IA).homologyπ 1 a := by
  obtain ⟨b, a, hb, ha⟩ := boundary_horseshoe_global_lift X S IA IB IC α β hαβ hιA hιB hrows hS q
  exact ⟨b, a, hb, ha,
    boundary_horseshoe_boundary_identification X S IA IB IC α β hαβ hιA hιB hrows hS q b a hb ha⟩

end AlgebraicGeometry.Scheme.Modules
