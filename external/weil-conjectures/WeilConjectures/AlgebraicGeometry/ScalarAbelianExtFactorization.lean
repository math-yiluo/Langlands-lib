/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ScalarUnitCohomologyComparisonFamily
import WeilConjectures.AlgebraicGeometry.Cohomology.MayerVietorisExtFunctorSquare
import WeilConjectures.CategoryTheory.ExtExactFunctorIdentityComparison
import Mathlib.CategoryTheory.Sites.Adjunction
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-! # Forgetting scalar Ext classes

Source: Stacks Project, Tag 03FD; constant-sheaf adjunction.
(blueprint: new-sc-scalar-abelian-ext-factorization).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open TopologicalSpace Opposite
namespace AlgebraicGeometry.Scheme
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Modules
attribute [local instance] Sheaf.monoidalCategory
local instance (k : Type u) [Field k] (X : Scheme.{u}) : HasExt.{u + 1} (KSheaf X k) :=
  HasExt.standard _
/-- The exact functor forgetting the k-action on scalar sheaves.
Source: Stacks Project, Tag 03FD.
(blueprint: new-sc-scalar-abelian-ext-factorization). -/
noncomputable def scalarAbelianForget (k : Type u) [Field k] (X : Scheme.{u}) :
    KSheaf X k ⥤ Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  sheafCompose _ (forget₂ (ModuleCat.{u} k) AddCommGrpCat.{u})
instance (k : Type u) [Field k] (X : Scheme.{u}) :
    (scalarAbelianForget k X).Additive where
  map_add := by intros; rfl
noncomputable instance (k : Type u) [Field k] (X : Scheme.{u}) :
    PreservesFiniteColimits (scalarAbelianForget k X) := by
  let r : ℤ →+* k := Int.castRingHom k
  let U := ModuleCat.restrictScalars.{u} r
  let V := forget₂ (ModuleCat.{u} ℤ) AddCommGrpCat.{u}
  have : U.IsLeftAdjoint :=
    (ModuleCat.restrictCoextendScalarsAdj.{0, 0, u} r).isLeftAdjoint
  have : (U ⋙ V).IsLeftAdjoint := inferInstance
  have : (forget₂ (ModuleCat.{u} k) AddCommGrpCat.{u}).IsLeftAdjoint :=
    inferInstanceAs (U ⋙ V).IsLeftAdjoint
  let J := Opens.grothendieckTopology X
  let G := forget₂ (ModuleCat.{u} k) AddCommGrpCat.{u}
  let e : Sheaf.composeAndSheafify J G ≅ sheafCompose J G :=
    Functor.isoWhiskerLeft (sheafCompose J G)
      (sheafificationNatIso J AddCommGrpCat.{u}).symm ≪≫
      Functor.rightUnitor (sheafCompose J G)
  have : (Sheaf.composeAndSheafify J G).IsLeftAdjoint := inferInstance
  have : (sheafCompose J G).IsLeftAdjoint := Functor.isLeftAdjoint_of_iso e
  exact inferInstanceAs (PreservesFiniteColimits (sheafCompose J G))
instance (k : Type u) [Field k] (X : Scheme.{u}) :
    PreservesFiniteLimits (scalarAbelianForget k X) := by
  have : PreservesFiniteLimits (scalarAbelianForget k X ⋙ sheafToPresheaf _ _) :=
    inferInstanceAs (PreservesFiniteLimits (sheafToPresheaf _ _ ⋙
      (Functor.whiskeringRight _ _ _).obj (forget₂ (ModuleCat.{u} k) AddCommGrpCat.{u})))
  exact preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf _ _)
/-- The integer-unit class of the section 1 in the scalar tensor unit.
It is constructed from the constant-sheaf adjunction, without choosing sections.
Source: Stacks Project, Tag 03FD; constant-sheaf adjunction.
(blueprint: new-sc-scalar-abelian-ext-factorization). -/
noncomputable def scalarAbelianUnitClass (k : Type u) [Field k] (X : Scheme.{u}) :
    Sheaf.H.{u} ((scalarAbelianForget k X).obj (𝟙_ (KSheaf X k))) 0 :=
  (Sheaf.H.equiv₀ _ isTerminalTop).symm
    ((constantScalarUnitIso (X := X) (k := k)).hom.hom.app (op ⊤)
      (((constantSheafAdj (Opens.grothendieckTopology X) (ModuleCat.{u} k)
        isTerminalTop).unit.app (ModuleCat.of k k)) (1 : k)))
/-- Forget a scalar Ext class and precompose with the integer-unit class.
Source: Stacks Project, Tag 03FD.
(blueprint: new-sc-scalar-abelian-ext-factorization). -/
noncomputable def scalarAbelianExtComparison (k : Type u) [Field k] (X : Scheme.{u})
    (F : KSheaf X k) (n : ℕ) (x : Abelian.Ext.{u + 1} (𝟙_ (KSheaf X k)) F n) :
    Sheaf.H.{u} ((scalarAbelianForget k X).obj F) n :=
  (scalarAbelianUnitClass k X).comp (x.mapExactFunctor (scalarAbelianForget k X)) (zero_add n)
/-- On a single scheme the module-to-abelian comparison factors through scalar Ext.
Source: Stacks Project, Tag 03FD; the constant-sheaf adjunction.
(blueprint: new-sc-scalar-abelian-ext-factorization).

Proof: Unfold the two explicit comparison maps. Forgetting the k-action after
restricting scalars is the module-to-abelian functor on objects and morphisms.
Exact-functor composition therefore identifies their Ext maps, with independent
Ext universes. Move the scalar-unit precomposition through the forgetful Ext map.
Under the constant-integer sections adjunction the composite of its integer-unit
class with the forgotten scalarUnitMorphism is the section scalarMap f top 1.
This is 1 because scalarMap is a ring homomorphism. It is precisely the unit class
in scalarUnitAbelianComparison. Associativity of Yoneda composition gives the
factorization. No inverse-image functor, morphism of schemes, or bijectivity of
scalarUnitAbelianComparison is used. For a zero class or an empty scheme the same
additive formulas give zero on both sides. -/
theorem scalar_unit_abelian_ext_factorization (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    (x : scalarCohomology f (SheafOfModules.unit X.ringCatSheaf) 1) :
    scalarUnitAbelianComparison X x =
      scalarAbelianExtComparison k X (scalarSheaf f (SheafOfModules.unit X.ringCatSheaf)) 1
        (scalarCohomologyExtEquiv f (SheafOfModules.unit X.ringCatSheaf) 1 x) := by
  let : EnoughInjectives (SheafOfModules.{u} X.ringCatSheaf) :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  let : HasExt.{u} (SheafOfModules.{u} X.ringCatSheaf) := hasExt_of_enoughInjectives _
  let T := SheafOfModules.toSheaf.{u} X.ringCatSheaf
  have : PreservesFiniteColimits T :=
    SheafOfModules.preservesFiniteColimits_toSheaf X.ringCatSheaf
  let U := scalarAbelianForget k X
  let s : Sheaf.H (T.obj (SheafOfModules.unit X.ringCatSheaf)) 0 :=
    (Sheaf.H.equiv₀ _ isTerminalTop).symm (1 : Γ(X, ⊤))
  have hunit : (scalarAbelianUnitClass k X).comp
      (Abelian.Ext.mk₀ (U.map (scalarUnitMorphism f))) (zero_add 0) = s := by
    apply (Sheaf.H.equiv₀ _ isTerminalTop).injective
    change (Sheaf.H.equiv₀ _ isTerminalTop)
      (Sheaf.H.map (U.map (scalarUnitMorphism f)) 0 (scalarAbelianUnitClass k X)) = _
    rw [← Sheaf.H.equiv₀_naturality]
    dsimp only [U, T, scalarAbelianUnitClass, s]
    simp only [AddEquiv.apply_symm_apply]
    change (scalarUnitMorphism f).hom.app (op ⊤)
      ((constantScalarUnitIso (X := X) (k := k)).hom.hom.app (op ⊤)
        (((constantSheafAdj (Opens.grothendieckTopology X) (ModuleCat.{u} k)
          isTerminalTop).unit.app (ModuleCat.of k k)) (1 : k))) =
      (Sheaf.H.equiv₀ (T.obj (SheafOfModules.unit X.ringCatSheaf)) isTerminalTop)
        ((Sheaf.H.equiv₀ (T.obj (SheafOfModules.unit X.ringCatSheaf))
          isTerminalTop).symm (1 : Γ(X, ⊤)))
    rw [AddEquiv.apply_symm_apply]
    let adj := constantSheafAdj (Opens.grothendieckTopology X) (ModuleCat.{u} k)
      isTerminalTop
    let g := (adj.homEquiv (ModuleCat.of k k)
      (scalarSheaf f (SheafOfModules.unit X.ringCatSheaf))).symm (scalarUnitLinear f)
    have he := congrArg (fun m ↦ m (1 : k))
      ((adj.homEquiv (ModuleCat.of k k)
        (scalarSheaf f (SheafOfModules.unit X.ringCatSheaf))).apply_symm_apply
          (scalarUnitLinear f))
    rw [Adjunction.homEquiv_unit] at he
    change g.hom.app (op ⊤) (adj.unit.app (ModuleCat.of k k) (1 : k)) = _ at he
    have hi := congrArg (fun m ↦ m (adj.unit.app (ModuleCat.of k k) (1 : k)))
      (congrArg (fun m ↦ m.hom.app (op ⊤))
        (constantScalarUnitIso (X := X) (k := k)).hom_inv_id)
    change (constantScalarUnitIso (X := X) (k := k)).inv.hom.app (op ⊤)
      ((constantScalarUnitIso (X := X) (k := k)).hom.hom.app (op ⊤)
        (adj.unit.app (ModuleCat.of k k) (1 : k))) = _ at hi
    unfold scalarUnitMorphism
    change g.hom.app (op ⊤)
      ((constantScalarUnitIso (X := X) (k := k)).inv.hom.app (op ⊤)
        ((constantScalarUnitIso (X := X) (k := k)).hom.hom.app (op ⊤)
          (adj.unit.app (ModuleCat.of k k) (1 : k)))) = (1 : Γ(X, ⊤))
    rw [hi]
    change g.hom.app (op ⊤) (adj.unit.app (ModuleCat.of k k) (1 : k)) =
      (1 : Γ(X, ⊤))
    rw [he]
    exact (scalarMap f ⊤).map_one
  have hmap (a : Abelian.Ext.{u} (SheafOfModules.unit X.ringCatSheaf)
      (SheafOfModules.unit X.ringCatSheaf) 1) :
      (a.mapExactFunctor (scalarFunctor f)).mapExactFunctor U = a.mapExactFunctor T := by
    have h := Abelian.Ext.mapExactFunctor_square.{u, u + 1, u, u}
      (scalarFunctor f) T U (𝟭 _) (Iso.refl _) 1 a
    simpa using h.trans (by simp)
  unfold scalarCohomologyExtEquiv scalarCohomologyExtMap scalarExtMap
  change s.comp
    ((moduleExtEquiv (SheafOfModules.unit X.ringCatSheaf) 1 x).mapExactFunctor T) (zero_add 1) =
    (scalarAbelianUnitClass k X).comp
      (((Abelian.Ext.mk₀ (scalarUnitMorphism f)).comp
        ((moduleExtEquiv (SheafOfModules.unit X.ringCatSheaf) 1 x).mapExactFunctor
          (scalarFunctor f)) (zero_add 1)).mapExactFunctor U) (zero_add 1)
  rw [Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀, hmap]
  rw [← Abelian.Ext.comp_assoc _ _ _ (zero_add 0) (zero_add 1) (zero_add 1), hunit]

end AlgebraicGeometry.Scheme
