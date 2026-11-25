/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Geometry.RingedSpace.Basic
import WeilConjectures.CategoryTheory.LocalizedModuleAdjunctionExact
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.Algebra.Homology.OpenCoverAdjunctionTriangle
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # Hom identifications for the open-cover triangle

Source: Stacks Project, Tags 08BU, 08BT and 08BW.
(blueprint: lem-sc-open-hom-triangle-realization).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace Pretriangulated

noncomputable section

namespace SheafOfModules

/-- Restrict derived Hom along an inclusion of opens, using the composition and
localization comparison isomorphisms.
Source: Stacks Project, Tag 08BW (blueprint: lem-sc-open-hom-triangle-realization). -/
def openHomRestriction {S : Type u} [TopologicalSpace S]
    (R : Sheaf (Opens.grothendieckTopology S) RingCat.{u})
    {W U : Opens S} (i : W ⟶ U)
    [(overFunctor.{u} R U).Additive]
    [PreservesFiniteLimits (overFunctor.{u} R U)]
    [PreservesFiniteColimits (overFunctor.{u} R U)]
    [(overFunctor.{u} R W).Additive]
    [PreservesFiniteLimits (overFunctor.{u} R W)]
    [PreservesFiniteColimits (overFunctor.{u} R W)]
    [(overMap.{u} R i).Additive]
    [PreservesFiniteLimits (overMap.{u} R i)]
    [PreservesFiniteColimits (overMap.{u} R i)]
    [HasDerivedCategory.{w} (SheafOfModules.{u} R)]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (R.over U))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (R.over W))]
    {E F : DerivedCategory (SheafOfModules.{u} R)}
    (f : (overFunctor.{u} R U).mapDerivedCategory.obj E ⟶
      (overFunctor.{u} R U).mapDerivedCategory.obj F) :
    (overFunctor.{u} R W).mapDerivedCategory.obj E ⟶
      (overFunctor.{u} R W).mapDerivedCategory.obj F :=
  let A := overFunctor.{u} R U
  let B := overMap.{u} R i
  letI : PreservesFiniteLimits (A ⋙ B) := comp_preservesFiniteLimits A B
  letI : PreservesFiniteColimits (A ⋙ B) := comp_preservesFiniteColimits A B
  let e := Functor.mapDerivedCategoryCompIso A B ≪≫
    Functor.mapDerivedCategoryNatIso (overFunctorMap.{u} R i)
  e.inv.app E ≫ (overMap.{u} R i).mapDerivedCategory.map f ≫ e.hom.app F

private theorem restriction_has_left_adjoint (X : AlgebraicGeometry.RingedSpace.{u})
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (hR : R = (sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf)
    (U : Opens X) [(overFunctor.{u} R U).Additive]
    [PreservesFiniteLimits (overFunctor.{u} R U)]
    [PreservesFiniteColimits (overFunctor.{u} R U)]
    [HasDerivedCategory.{w} (SheafOfModules.{u} R)]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (R.over U))] :
    ∃ L : DerivedCategory (SheafOfModules.{u} (R.over U)) ⥤
      DerivedCategory (SheafOfModules.{u} R),
      Nonempty (L ⊣ (overFunctor.{u} R U).mapDerivedCategory) := by
  classical
  subst R
  have hJ : (Opens.grothendieckTopology X).toPrecoverage.toGrothendieck =
      Opens.grothendieckTopology X := by
    apply le_antisymm
    · exact GrothendieckTopology.toGrothendieck_toPrecoverage_le _
    · intro V S hS
      simpa only [Sieve.generate_sieve] using
        Precoverage.generate_mem_toGrothendieck
          ((GrothendieckTopology.arrows_mem_toPrecoverage_iff _ S).mpr hS)
  have h := localizedModule_adjunction_exact
    (Opens.grothendieckTopology X).toPrecoverage
  rw [hJ] at h
  obtain ⟨_, _, hlim, hcolim, ⟨adj⟩⟩ := h X.sheaf U
  let G := extensionByZeroPresheaf.{u}
    ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf) U ⋙
    PresheafOfModules.sheafification.{u} (𝟙 _)
  let : PreservesFiniteLimits G := hlim
  let : PreservesFiniteColimits G := hcolim
  let : G.Additive := adj.left_adjoint_additive
  let F := overFunctor.{u}
    ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf) U
  let : CatCommSq (G.mapHomologicalComplex (ComplexShape.up ℤ))
      DerivedCategory.Q DerivedCategory.Q G.mapDerivedCategory :=
    ⟨G.mapDerivedCategoryFactors.symm⟩
  let : CatCommSq (F.mapHomologicalComplex (ComplexShape.up ℤ))
      DerivedCategory.Q DerivedCategory.Q F.mapDerivedCategory :=
    ⟨F.mapDerivedCategoryFactors.symm⟩
  exact ⟨G.mapDerivedCategory, ⟨(adj.mapHomologicalComplex (ComplexShape.up ℤ)).localization
    DerivedCategory.Q (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
    DerivedCategory.Q (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
    G.mapDerivedCategory F.mapDerivedCategory⟩⟩

private def biprodHomAddEquiv {C : Type*} [Category C] [Preadditive C]
    [HasBinaryBiproducts C] (A B F : C) :
    (A ⊞ B ⟶ F) ≃+ ((A ⟶ F) × (B ⟶ F)) where
  toFun g := (biprod.inl ≫ g, biprod.inr ≫ g)
  invFun p := biprod.desc p.1 p.2
  left_inv g := by ext <;> simp
  right_inv p := by simp
  map_add' g h := by simp [Preadditive.comp_add]

private def postcompAddEquiv {C : Type*} [Category C] [Preadditive C]
    (A : C) {B D : C} (e : B ≅ D) : (A ⟶ B) ≃+ (A ⟶ D) where
  toFun g := g ≫ e.hom
  invFun g := g ≫ e.inv
  left_inv g := by simp
  right_inv g := by simp
  map_add' g h := by simp [Preadditive.add_comp]

private theorem nested_transpose {C D H : Type*}
    [Category C] [Category D] [Category H]
    (RU : C ⥤ D) (RW : C ⥤ H) (T : D ⥤ H)
    (LU : D ⥤ C) (LW : H ⥤ C) (adjU : LU ⊣ RU) (adjW : LW ⊣ RW)
    (c : RU ⋙ T ≅ RW) (E F : C) (g : LU.obj (RU.obj E) ⟶ F) :
    adjW.homEquiv (RW.obj E) F
      ((adjW.homEquiv (RW.obj E) (LU.obj (RU.obj E))).symm
        (c.inv.app E ≫ T.map (adjU.unit.app (RU.obj E)) ≫
          c.hom.app (LU.obj (RU.obj E))) ≫ g) =
      c.inv.app E ≫ T.map (adjU.homEquiv (RU.obj E) F g) ≫ c.hom.app F := by
  rw [adjW.homEquiv_naturality_right, Equiv.apply_symm_apply,
    adjU.homEquiv_unit, T.map_comp]
  simp only [Category.assoc]
  rw [← c.hom.naturality g]
  rfl

private theorem assemble_open_triangle
    {C DU DV DW : Type*} [Category C] [Category DU] [Category DV] [Category DW]
    [Preadditive C] [Preadditive DU] [Preadditive DV] [Preadditive DW]
    [HasBinaryBiproducts C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    [HasShift DW ℤ]
    (RU : C ⥤ DU) (RV : C ⥤ DV) (RW : C ⥤ DW)
    (TU : DU ⥤ DW) (TV : DV ⥤ DW)
    [RU.Additive] [RV.Additive] [RW.Additive] [RW.CommShift ℤ]
    (LU : DU ⥤ C) (LV : DV ⥤ C) (LW : DW ⥤ C)
    (adjU : LU ⊣ RU) (adjV : LV ⊣ RV) (adjW : LW ⊣ RW)
    (cU : RU ⋙ TU ≅ RW) (cV : RV ⋙ TV ≅ RW) (E F : C)
    (hT :
      let κU := (adjW.homEquiv (RW.obj E) (LU.obj (RU.obj E))).symm
        (cU.inv.app E ≫ TU.map (adjU.unit.app (RU.obj E)) ≫ cU.hom.app (LU.obj (RU.obj E)))
      let κV := (adjW.homEquiv (RW.obj E) (LV.obj (RV.obj E))).symm
        (cV.inv.app E ≫ TV.map (adjV.unit.app (RV.obj E)) ≫ cV.hom.app (LV.obj (RV.obj E)))
      ∃ δ : E ⟶ (LW.obj (RW.obj E))⟦(1 : ℤ)⟧,
        Triangle.mk (biprod.lift κU (-κV))
          (biprod.desc (adjU.counit.app E) (adjV.counit.app E)) δ ∈ distTriang _) :
    ∃ (A B : C) (a : A ⟶ B) (b : B ⟶ E) (δ : E ⟶ A⟦(1 : ℤ)⟧),
      Triangle.mk a b δ ∈ distTriang _ ∧
      ∃ (eB : (B ⟶ F) ≃+ ((RU.obj E ⟶ RU.obj F) × (RV.obj E ⟶ RV.obj F)))
        (eA : (A ⟶ F) ≃+ (RW.obj E ⟶ RW.obj F))
        (_eN : (A⟦(1 : ℤ)⟧ ⟶ F) ≃+ (RW.obj E ⟶ (RW.obj F)⟦(-1 : ℤ)⟧)),
        (∀ f : E ⟶ F, eB (b ≫ f) = (RU.map f, RV.map f)) ∧
        (∀ g : B ⟶ F, eA (a ≫ g) =
          (cU.inv.app E ≫ TU.map (eB g).1 ≫ cU.hom.app F) -
            (cV.inv.app E ≫ TV.map (eB g).2 ≫ cV.hom.app F)) := by
  let : LU.Additive := adjU.left_adjoint_additive
  let : LV.Additive := adjV.left_adjoint_additive
  let : LW.Additive := adjW.left_adjoint_additive
  let κU := (adjW.homEquiv (RW.obj E) (LU.obj (RU.obj E))).symm
    (cU.inv.app E ≫ TU.map (adjU.unit.app (RU.obj E)) ≫ cU.hom.app (LU.obj (RU.obj E)))
  let κV := (adjW.homEquiv (RW.obj E) (LV.obj (RV.obj E))).symm
    (cV.inv.app E ≫ TV.map (adjV.unit.app (RV.obj E)) ≫ cV.hom.app (LV.obj (RV.obj E)))
  obtain ⟨δ, hδ⟩ := hT
  let eB := (biprodHomAddEquiv (LU.obj (RU.obj E)) (LV.obj (RV.obj E)) F).trans
    (AddEquiv.prodCongr (adjU.homAddEquiv (RU.obj E) F)
      (adjV.homAddEquiv (RV.obj E) F))
  let eA := adjW.homAddEquiv (RW.obj E) F
  let : (shiftEquiv C (1 : ℤ)).functor.Additive :=
    (inferInstance : (shiftFunctor C (1 : ℤ)).Additive)
  let eN := ((shiftEquiv C (1 : ℤ)).toAdjunction.homAddEquiv (LW.obj (RW.obj E)) F).trans
    ((adjW.homAddEquiv (RW.obj E) (F⟦(-1 : ℤ)⟧)).trans
      (postcompAddEquiv (RW.obj E) ((RW.commShiftIso (-1 : ℤ)).app F)))
  refine ⟨LW.obj (RW.obj E), LU.obj (RU.obj E) ⊞ LV.obj (RV.obj E),
    biprod.lift κU (-κV), biprod.desc (adjU.counit.app E) (adjV.counit.app E),
    δ, hδ, eB, eA, eN, ?_, ?_⟩
  · intro f
    apply Prod.ext
    · change adjU.homEquiv _ _ (biprod.inl ≫ _ ≫ f) = RU.map f
      rw [biprod.inl_desc_assoc, adjU.homEquiv_naturality_right]
      rw [adjU.homEquiv_unit]
      simp only [adjU.right_triangle_components, Category.id_comp]
    · change adjV.homEquiv _ _ (biprod.inr ≫ _ ≫ f) = RV.map f
      rw [biprod.inr_desc_assoc, adjV.homEquiv_naturality_right]
      rw [adjV.homEquiv_unit]
      simp only [adjV.right_triangle_components, Category.id_comp]
  · intro g
    change adjW.homAddEquiv _ _ (biprod.lift κU (-κV) ≫ g) = _
    rw [biprod.lift_eq, Preadditive.add_comp, map_add, Preadditive.neg_comp,
      Preadditive.neg_comp, map_neg]
    simp only [Category.assoc]
    rw [Adjunction.homAddEquiv_apply, Adjunction.homAddEquiv_apply]
    rw [nested_transpose RU RW TU LU LW adjU adjW cU E F,
      nested_transpose RV RW TV LV LW adjV adjW cV E F]
    rw [sub_eq_add_neg]
    rfl

-- The original existential binder eN is used only through its asserted existence.
set_option linter.unusedVariables false in
/-- The open-cover triangle, together with its additive Hom identifications.
The equality hR records that R is exactly the underlying ring sheaf of X; keeping R
as an explicit parameter avoids repeatedly unfolding that large expression.
This statement supplies the geometric triangle and the map identifications, not exactness
of Hom. The latter follows separately from the pretriangulated-category axioms.

Source: Stacks Project, Tags 08BU (triangle), 08BT (adjunction), and 08BW (identifications).
(blueprint: lem-sc-open-hom-triangle-realization).

Proof: Represent E by a complex K. In each degree use the short exact sequence
0 → j_{U∩V,!} K|_{U∩V} → j_{U,!} K|_U ⊕ j_{V,!} K|_V → K → 0,
where the first map has components the canonical extension maps and minus the
canonical extension map, and the second is the pair of counits. Exactness follows
on stalks: on the intersection the sequence is M → M ⊕ M → M with maps
m ↦ (m,-m) and (m,n) ↦ m+n; on just one open it is 0 → M → M;
outside both opens there is nothing since U ∪ V is the whole space. Apply the
short-exact-complex triangle construction and transport along Q K ≅ E. Take A
to be derived extension by zero from the overlap, B the biproduct of the two
extensions, and b the pair of derived counits. The additive adjunction bijections
and the biproduct Hom bijection give eB and eA. For eN first use the shift
bijection Hom(A[1],F) ≃ Hom(A,F[-1]), then the overlap adjunction and restriction's
shift comparison. The adjunction triangle identity gives eB(b ≫ f) equal to the
pair of restrictions of f. Naturality of the adjunction for nested opens identifies
precomposition with each component of a with openHomRestriction: write η_W for the
unit and κ for the canonical extension map from W to U. The transpose of κ ≫ g_U
is η_W ≫ R_W(κ) ≫ R_W(g_U). The sectionwise extension-by-zero construction gives
η_W ≫ R_W(κ) = c_E.inv ≫ R_{W,U}(η_U) ≫ c_{L_U E_U}.hom,
where c is the nested restriction comparison. Naturality of c moves R_W(g_U)
past its last factor, leaving c_E.inv ≫ R_{W,U}(η_U ≫ R_U(g_U)) ≫ c_F.hom.
This is exactly restriction of the U transpose. The identity holds termwise on
complexes and passes through localization using the derived comparison isos.
Apply it on both opens, then use additivity and
the minus sign in the V component to obtain the asserted difference identity. For U or V
empty the extension term vanishes, and for U = V = top the stalk
sequence is the same split sequence, so both degenerate cases remain valid. -/
theorem open_hom_triangle_realization (X : AlgebraicGeometry.RingedSpace.{u})
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (hR : R = (sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj X.sheaf)
    (U V : Opens X) (hcover : U ⊔ V = ⊤)
    [(overFunctor.{u} R U).Additive]
    [PreservesFiniteLimits (overFunctor.{u} R U)]
    [PreservesFiniteColimits (overFunctor.{u} R U)]
    [(overFunctor.{u} R V).Additive]
    [PreservesFiniteLimits (overFunctor.{u} R V)]
    [PreservesFiniteColimits (overFunctor.{u} R V)]
    [(overFunctor.{u} R (U ⊓ V)).Additive]
    [PreservesFiniteLimits (overFunctor.{u} R (U ⊓ V))]
    [PreservesFiniteColimits (overFunctor.{u} R (U ⊓ V))]
    [(overMap.{u} R (homOfLE inf_le_left : U ⊓ V ⟶ U)).Additive]
    [PreservesFiniteLimits (overMap.{u} R (homOfLE inf_le_left : U ⊓ V ⟶ U))]
    [PreservesFiniteColimits (overMap.{u} R (homOfLE inf_le_left : U ⊓ V ⟶ U))]
    [(overMap.{u} R (homOfLE inf_le_right : U ⊓ V ⟶ V)).Additive]
    [PreservesFiniteLimits (overMap.{u} R (homOfLE inf_le_right : U ⊓ V ⟶ V))]
    [PreservesFiniteColimits (overMap.{u} R (homOfLE inf_le_right : U ⊓ V ⟶ V))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} R)]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (R.over U))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (R.over V))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (R.over (U ⊓ V)))]
    (E F : DerivedCategory (SheafOfModules.{u} R)) :
    let RU := (overFunctor.{u} R U).mapDerivedCategory
    let RV := (overFunctor.{u} R V).mapDerivedCategory
    let RW := (overFunctor.{u} R (U ⊓ V)).mapDerivedCategory
    ∃ (A B : DerivedCategory (SheafOfModules.{u} R))
      (a : A ⟶ B) (b : B ⟶ E) (δ : E ⟶ A⟦(1 : ℤ)⟧),
      Triangle.mk a b δ ∈ distTriang _ ∧
      ∃ (eB : (B ⟶ F) ≃+ ((RU.obj E ⟶ RU.obj F) × (RV.obj E ⟶ RV.obj F)))
        (eA : (A ⟶ F) ≃+ (RW.obj E ⟶ RW.obj F))
        (eN : (A⟦(1 : ℤ)⟧ ⟶ F) ≃+ (RW.obj E ⟶ (RW.obj F)⟦(-1 : ℤ)⟧)),
        (∀ f : E ⟶ F, eB (b ≫ f) = (RU.map f, RV.map f)) ∧
        (∀ g : B ⟶ F, eA (a ≫ g) =
          openHomRestriction R (homOfLE inf_le_left) (eB g).1 -
            openHomRestriction R (homOfLE inf_le_right) (eB g).2) := by
  classical
  let RU := (overFunctor.{u} R U).mapDerivedCategory
  let RV := (overFunctor.{u} R V).mapDerivedCategory
  let RW := (overFunctor.{u} R (U ⊓ V)).mapDerivedCategory
  have hU := restriction_has_left_adjoint.{u, w} X R hR U
  have hV := restriction_has_left_adjoint.{u, w} X R hR V
  have hW := restriction_has_left_adjoint.{u, w} X R hR (U ⊓ V)
  let LU := hU.choose
  let LV := hV.choose
  let LW := hW.choose
  let adjU := hU.choose_spec.some
  let adjV := hV.choose_spec.some
  let adjW := hW.choose_spec.some
  exact assemble_open_triangle RU RV RW
    (overMap.{u} R (homOfLE inf_le_left : U ⊓ V ⟶ U)).mapDerivedCategory
    (overMap.{u} R (homOfLE inf_le_right : U ⊓ V ⟶ V)).mapDerivedCategory
    LU LV LW adjU adjV adjW
    (openRestrictionComparison R (homOfLE inf_le_left : U ⊓ V ⟶ U))
    (openRestrictionComparison R (homOfLE inf_le_right : U ⊓ V ⟶ V)) E F
    (open_cover_adjunction_triangle.{u, w} X R hR U V hcover E LU LV LW adjU adjV adjW)

end SheafOfModules
