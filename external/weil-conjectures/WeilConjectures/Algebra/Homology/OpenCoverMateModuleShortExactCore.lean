/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Geometry.RingedSpace.Basic
import WeilConjectures.Algebra.Homology.OpenExtensionCounitStalk
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat


@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace SheafOfModules
private theorem biprod_cover_shortExact
    {C : Type*} [Category* C] [Abelian C] {A B D E : C}
    (i : A ⟶ B) (j : A ⟶ D) (b : B ⟶ E) (d : D ⟶ E) (a : A ⟶ E)
    (hi : i ≫ b = a) (hj : j ≫ d = a)
    (hz : biprod.lift i (-j) ≫ biprod.desc b d = 0)
    (p q : Prop) (hpq : p ∨ q)
    (hb : p → IsIso b) (hd : q → IsIso d) (ha : p ∧ q → IsIso a)
    (hB : ¬p → IsZero B) (hD : ¬q → IsZero D)
    (hA : ¬(p ∧ q) → IsZero A) :
    (ShortComplex.mk (biprod.lift i (-j)) (biprod.desc b d) hz).ShortExact := by
  classical
  let S := ShortComplex.mk (biprod.lift i (-j)) (biprod.desc b d) hz
  by_cases hp : p
  · have := hb hp
    by_cases hq : q
    · have := hd hq
      have := ha ⟨hp, hq⟩
      have hi' : inv a ≫ i = inv b := by
        apply (cancel_mono b).mp
        simp [Category.assoc, hi]
      have hj' : inv a ≫ j = inv d := by
        apply (cancel_mono d).mp
        simp [Category.assoc, hj]
      have sp : S.Splitting :=
        { r := biprod.fst ≫ b ≫ inv a
          s := inv d ≫ biprod.inr
          f_r := by simp [S, ← Category.assoc, hi]
          s_g := by simp [S, Category.assoc]
          id := by
            apply biprod.hom_ext <;> apply biprod.hom_ext'
            all_goals simp [S, Category.assoc, hi', hj'] }
      exact sp.shortExact
    · have hAz := hA (fun h => hq h.2)
      have hDz := hD hq
      have sp : S.Splitting :=
        { r := 0
          s := inv b ≫ biprod.inl
          f_r := by simpa [S] using hAz.eq_of_src (0 : A ⟶ A) (𝟙 A)
          s_g := by simp [S, Category.assoc]
          id := by
            apply biprod.hom_ext <;> apply biprod.hom_ext'
            all_goals first | exact hDz.eq_of_src _ _ | exact hDz.eq_of_tgt _ _ |
              simp [S, Category.assoc] }
      exact sp.shortExact
  · have hq : q := hpq.resolve_left hp
    have := hd hq
    have hAz := hA (fun h => hp h.1)
    have hBz := hB hp
    have sp : S.Splitting :=
      { r := 0
        s := inv d ≫ biprod.inr
        f_r := by simpa [S] using hAz.eq_of_src (0 : A ⟶ A) (𝟙 A)
        s_g := by simp [S, Category.assoc]
        id := by
          apply biprod.hom_ext <;> apply biprod.hom_ext'
          all_goals first | exact hBz.eq_of_src _ _ | exact hBz.eq_of_tgt _ _ |
            simp [S, Category.assoc] }
    exact sp.shortExact

/-- Given the two canonical counit compatibility equations, the open-cover mate
sequence is short exact. The proof uses the extension-by-zero stalk calculation,
then reflects exactness, monicity and epimorphicity through module stalks.
Source: Stacks Project, Tag 08BU and Tag 00A7.
(blueprint: lem-sc-open-cover-mate-module-short-exact-core). -/
theorem open_cover_mate_module_shortExact_core (X : AlgebraicGeometry.RingedSpace.{u})
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (_hR : R = (sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf)
    (U V : Opens X) (_hcover : U ⊔ V = ⊤)
    [(overFunctor.{u} R U).Additive] [(overFunctor.{u} R V).Additive]
    [(overFunctor.{u} R (U ⊓ V)).Additive]
    (SU : SheafOfModules.{u} (R.over U) ⥤ SheafOfModules.{u} R)
    (SV : SheafOfModules.{u} (R.over V) ⥤ SheafOfModules.{u} R)
    (SW : SheafOfModules.{u} (R.over (U ⊓ V)) ⥤ SheafOfModules.{u} R)
    [SU.Additive] [SV.Additive] [SW.Additive]
    (aU : SU ⊣ overFunctor.{u} R U) (aV : SV ⊣ overFunctor.{u} R V)
    (aW : SW ⊣ overFunctor.{u} R (U ⊓ V))
    (F : SheafOfModules.{u} R)
    (iU iV : (SW.obj ((overFunctor.{u} R (U ⊓ V)).obj F)) ⟶ _)
    (hU : iU ≫ aU.counit.app F = aW.counit.app F)
    (hV : iV ≫ aV.counit.app F = aW.counit.app F)
    (hz : biprod.lift iU (-iV) ≫
      biprod.desc (aU.counit.app F) (aV.counit.app F) = 0) :
    (ShortComplex.mk (biprod.lift iU (-iV))
      (biprod.desc (aU.counit.app F) (aV.counit.app F)) hz).ShortExact := by
  classical
  let Q := toSheaf R
  have : PreservesFiniteColimits Q :=
    (CategoryTheory.moduleSheaves_colimits_forgetful R).2.2.1
  let T (x : X) := Q ⋙ TopCat.Sheaf.forget AddCommGrpCat.{u} X.carrier ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  have hstalk (x : X) : (TopCat.Sheaf.forget AddCommGrpCat.{u} X.carrier ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).Additive := inferInstance
  have hT (x : X) : (T x).Additive := inferInstance
  have hbp (x : X) : PreservesBinaryBiproducts (T x) :=
    preservesBinaryBiproducts_of_preservesBinaryProducts (T x)
  have detect (S : ShortComplex (SheafOfModules.{u} R)) :
      S.Exact ↔ ∀ x : X, (S.map (T x)).Exact := by
    rw [← S.exact_map_iff_of_faithful Q,
      TopCat.Sheaf.exact_iff_stalkFunctor_map_exact]
    rfl
  let S := ShortComplex.mk (biprod.lift iU (-iV))
    (biprod.desc (aU.counit.app F) (aV.counit.app F)) hz
  have hs (x : X) : (S.map (T x)).ShortExact := by
    obtain ⟨hb, hB⟩ := open_extension_counit_stalk X R _hR U SU aU F x
    obtain ⟨hd, hD⟩ := open_extension_counit_stalk X R _hR V SV aV F x
    obtain ⟨ha, hA⟩ := open_extension_counit_stalk X R _hR (U ⊓ V) SW aW F x
    have hpq : x ∈ U ∨ x ∈ V := by
      change x ∈ U ⊔ V
      rw [_hcover]
      trivial
    have hzi : biprod.lift ((T x).map iU) (-((T x).map iV)) ≫
        biprod.desc ((T x).map (aU.counit.app F)) ((T x).map (aV.counit.app F)) = 0 := by
      simp only [biprod.lift_desc, Preadditive.neg_comp, ← Functor.map_comp,
        hU, hV, add_neg_cancel]
    have hlocal := biprod_cover_shortExact ((T x).map iU) ((T x).map iV)
      ((T x).map (aU.counit.app F)) ((T x).map (aV.counit.app F))
      ((T x).map (aW.counit.app F))
      (by rw [← Functor.map_comp, hU]) (by rw [← Functor.map_comp, hV])
      hzi (x ∈ U) (x ∈ V) hpq hb hd ha hB hD hA
    let S' := ShortComplex.mk (biprod.lift ((T x).map iU) (-((T x).map iV)))
      (biprod.desc ((T x).map (aU.counit.app F)) ((T x).map (aV.counit.app F))) hzi
    have e : S.map (T x) ≅ S' := ShortComplex.isoMk (Iso.refl _)
      ((T x).mapBiprod _ _) (Iso.refl _)
      (by simpa [S, S'] using (biprod.map_lift_mapBiprod (T x) _ _ iU (-iV)).symm)
      (by simpa [S, S'] using
        biprod.mapBiprod_hom_desc (T x) _ _ (aU.counit.app F) (aV.counit.app F))
    exact ShortComplex.shortExact_of_iso e.symm hlocal
  refine ShortComplex.ShortExact.mk' ((detect S).mpr (fun x => (hs x).exact)) ?_ ?_
  · let S₀ := ShortComplex.mk (0 : S.X₁ ⟶ S.X₁) S.f (by simp)
    apply (S₀.exact_iff_mono rfl).mp
    apply (detect S₀).mpr
    intro x
    apply ((S₀.map (T x)).exact_iff_mono (by simp [S₀])).mpr
    exact (hs x).mono_f
  · let S₀ := ShortComplex.mk S.g (0 : S.X₃ ⟶ S.X₃) (by simp)
    apply (S₀.exact_iff_epi rfl).mp
    apply (detect S₀).mpr
    intro x
    apply ((S₀.map (T x)).exact_iff_epi (by simp [S₀])).mpr
    exact (hs x).epi_g
/-- Compatibility of nested mates with counits.
Source: Stacks Project, Tag 08BU.
(blueprint: lem-sc-open-cover-mate-module-counit-compatibility). -/
theorem open_cover_mate_module_counit_compatibility (X : AlgebraicGeometry.RingedSpace.{u})
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (_hR : R = (sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf)
    (U V : Opens X) (_hcover : U ⊔ V = ⊤)
    [(overFunctor.{u} R U).Additive] [(overFunctor.{u} R V).Additive]
    [(overFunctor.{u} R (U ⊓ V)).Additive]
    (SU : SheafOfModules.{u} (R.over U) ⥤ SheafOfModules.{u} R)
    (SV : SheafOfModules.{u} (R.over V) ⥤ SheafOfModules.{u} R)
    (SW : SheafOfModules.{u} (R.over (U ⊓ V)) ⥤ SheafOfModules.{u} R)
    [SU.Additive] [SV.Additive] [SW.Additive]
    (aU : SU ⊣ overFunctor.{u} R U) (aV : SV ⊣ overFunctor.{u} R V)
    (aW : SW ⊣ overFunctor.{u} R (U ⊓ V)) (F : SheafOfModules.{u} R) :
    let cU := overFunctorMap.{u} R (homOfLE inf_le_left : U ⊓ V ⟶ U)
    let cV := overFunctorMap.{u} R (homOfLE inf_le_right : U ⊓ V ⟶ V)
    let iU := (aW.homEquiv _ _).symm (cU.inv.app F ≫
      (overMap.{u} R (homOfLE inf_le_left : U ⊓ V ⟶ U)).map
        (aU.unit.app ((overFunctor.{u} R U).obj F)) ≫ cU.hom.app
          (SU.obj ((overFunctor.{u} R U).obj F)))
    let iV := (aW.homEquiv _ _).symm (cV.inv.app F ≫
      (overMap.{u} R (homOfLE inf_le_right : U ⊓ V ⟶ V)).map
        (aV.unit.app ((overFunctor.{u} R V).obj F)) ≫ cV.hom.app
          (SV.obj ((overFunctor.{u} R V).obj F)))
    iU ≫ aU.counit.app F = aW.counit.app F ∧
      iV ≫ aV.counit.app F = aW.counit.app F := by
  dsimp
  constructor
  · apply (aW.homEquiv _ _).injective
    rw [CategoryTheory.Adjunction.homEquiv_naturality_right,
      Equiv.apply_symm_apply]
    rw [CategoryTheory.Adjunction.homEquiv_unit, aW.right_triangle_components]
    simp only [Category.assoc]
    rw [← (overFunctorMap.{u} R (homOfLE inf_le_left : U ⊓ V ⟶ U)).hom.naturality]
    simp only [Functor.comp_map, ← Functor.map_comp_assoc]
    rw [aU.right_triangle_components]
    simp
  · apply (aW.homEquiv _ _).injective
    rw [CategoryTheory.Adjunction.homEquiv_naturality_right,
      Equiv.apply_symm_apply]
    rw [CategoryTheory.Adjunction.homEquiv_unit, aW.right_triangle_components]
    simp only [Category.assoc]
    rw [← (overFunctorMap.{u} R (homOfLE inf_le_right : U ⊓ V ⟶ V)).hom.naturality]
    simp only [Functor.comp_map, ← Functor.map_comp_assoc]
    rw [aV.right_triangle_components]
    simp

end SheafOfModules
