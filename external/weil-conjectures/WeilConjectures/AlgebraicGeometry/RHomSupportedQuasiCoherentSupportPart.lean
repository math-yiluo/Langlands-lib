/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.Algebra.Homology.DerivedInternalHom
import WeilConjectures.AlgebraicGeometry.DerivedInternalHomRestrictOpen


/-! # SupportPart of derived internal Hom

Source: Stacks Project, Tag 0A9C proof
(blueprint: lem-sc-rhom-supported-qcoherent-support-part).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry

open scoped ZeroObject

private theorem homObj_zero_target
    {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u})
    (P : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
    (Z : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
    (hZ : IsZero Z) : IsZero (SheafOfModules.homObj (R := R) P Z) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  rw [← SheafOfModules.homObjMap_id (R := R) (M := P) (N := Z), hZ.eq_zero_of_tgt (𝟙 Z)]
  apply SheafOfModules.hom_ext
  ext X φ : 3
  change (PresheafOfModules.restrictOver R.obj X.unop).map (𝟙 P.val) ≫ φ ≫
    (PresheafOfModules.restrictOver R.obj X.unop).map 0 = 0
  ext W x
  rfl

private theorem homComplex_zero_target
    {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u})
    (P : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ) :
    IsZero (homComplex (R := R) P 0) := by
  obtain ⟨π, hπ, _, _⟩ := Classical.choose_spec
    (homComplex_exists (C := C) (J := J) (R := R))
  apply (IsZero.iff_id_eq_zero _).mpr
  apply HomologicalComplex.hom_ext
  intro n
  apply (hπ P 0 n).some.hom_ext
  intro j
  exact (homObj_zero_target J R _ _
    ((HomologicalComplex.eval _ _ (j.as + n)).map_isZero (isZero_zero _))).eq_of_tgt _ _

private theorem derivedInternalHom_zero_target
    {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))]
    (K L : DerivedCategory (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)))
    (hL : IsZero L) : IsZero ((derivedInternalHom J R).obj (op K, L)) := by
  let A := SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)
  let P := DerivedCategory.Q.objPreimage K
  let Z : CochainComplex A ℤ := 0
  have hZ : IsZero Z := isZero_zero _
  have : Z.IsKInjective :=
    ⟨fun f _ ↦ ⟨Homotopy.ofEq (hZ.eq_zero_of_tgt f)⟩⟩
  obtain ⟨e⟩ := derivedInternalHom_obj_iso J R K L P Z
    (DerivedCategory.Q.objObjPreimageIso K)
    ((DerivedCategory.Q.map_isZero hZ).iso hL)
  exact (DerivedCategory.Q.map_isZero (homComplex_zero_target J R P)).of_iso e


/-- Internal Hom preserves support in its second argument.

Source: Stacks Project, Tag 0A9C proof
(blueprint: lem-sc-rhom-supported-qcoherent-support-part).

Proof: Let U be the open complement of T. Exact restriction commutes with cohomology,
so the hypothesis makes every cohomology object of L restricted to U zero. Cohomology
detects zero in the derived category, hence L restricted to U is a zero object.
Derived internal Hom commutes with restriction to U. Internal Hom into a zero object
is zero: represent the first argument by any complex and the second by the zero
K-injective complex; every term of its Hom complex is a product of zero module sheaves.
Consequently every cohomology sheaf of RHom(K,L) restricts to zero on U. This argument
also covers U empty, T empty, and T equal to X; it requires no pseudo-coherence
or perfectness assumption. -/
theorem rhom_supported_quasiCoherent_support_part
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (K L : schemeDerivedCategory X)
    (T : Set X) (hT : IsClosed T)
    (hzero : ∀ n : ℤ,
      IsZero ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace)
        ⟨Tᶜ, hT.isOpen_compl⟩).obj ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj L))) :
    ∀ n : ℤ,
      IsZero ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace)
        ⟨Tᶜ, hT.isOpen_compl⟩).obj ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj
            ((derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
              X.toRingedSpace.sheaf).obj (op K, L)))) := by
  let U : X.Opens := ⟨Tᶜ, hT.isOpen_compl⟩
  let C := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let D := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)
  let : Category.{w} (@DerivedCategory (SheafOfModules.{u}
      ((sheafCompose ((Opens.grothendieckTopology X.toRingedSpace).over U)
        (forget₂ CommRingCat RingCat)).obj (X.toRingedSpace.sheaf.over U))) _ _
      (inferInstanceAs (HasDerivedCategory.{w} D))) :=
    inferInstanceAs (Category.{w} (DerivedCategory D))
  let F := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U
  have hLzero : IsZero (F.mapDerivedCategory.obj L) := by
    have hh (n : ℤ) : IsZero
        ((DerivedCategory.homologyFunctor D n).obj (F.mapDerivedCategory.obj L)) :=
      (hzero n).of_iso ((F.mapDerivedCategoryHomologyFunctorIso n).app L).symm
    have hi : IsIso (0 : F.mapDerivedCategory.obj L ⟶ 0) :=
      (DerivedCategory.isIso_iff D _).mpr (fun n ↦
        IsZero.isIso (hh n) ((DerivedCategory.homologyFunctor D n).map_isZero
          (isZero_zero _)) _)
    exact (isZero_zero _).of_iso (asIso (0 : F.mapDerivedCategory.obj L ⟶ 0))
  obtain ⟨e⟩ := derivedInternalHom_restrict_open X.toRingedSpace U K L
  have hRzero : IsZero (F.mapDerivedCategory.obj
      ((derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
        X.toRingedSpace.sheaf).obj (op K, L))) :=
    (@derivedInternalHom_zero_target.{u, w} (Over U) _
      ((Opens.grothendieckTopology X.toRingedSpace).over U)
      (X.toRingedSpace.sheaf.over U) (inferInstanceAs (HasDerivedCategory.{w} D))
      _ _ hLzero).of_iso e.symm
  intro n
  exact ((DerivedCategory.homologyFunctor D n).map_isZero hRzero).of_iso
    ((F.mapDerivedCategoryHomologyFunctorIso n).app _)

end AlgebraicGeometry
