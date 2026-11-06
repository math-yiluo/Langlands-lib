import Langlands.Cohomology.ExtResolutionMap
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction

/-! # The actual Ext adjunction through injective resolutions -/

noncomputable section
universe v wC wD
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open Langlands.Cohomology.DerivedComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 2048
set_option maxHeartbeats 800000

namespace Langlands.Cohomology.ExtAdjunctionResolution

variable {C D : Type*} [Category.{v} C] [Abelian C] [Category.{v} D] [Abelian D]
  {F : C ⥤ D} [F.Additive] {G : D ⥤ C} [G.Additive] (adj : F ⊣ G) (X : C)

/-- The actual additive Hom adjunction as a natural isomorphism in the coefficient. -/
def homAdjunctionIso :
    G ⋙ preadditiveCoyoneda.obj (op X) ≅ preadditiveCoyoneda.obj (op (F.obj X)) :=
  NatIso.ofComponents (fun Y => (adj.homAddEquiv X Y).symm.toAddCommGrpIso)
    (by intro Y Z a; ext f; exact adj.homEquiv_naturality_right_symm f a)

variable [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G] [G.PreservesInjectiveObjects]
  [HasExt.{wC} C] [HasExt.{wD} D]
  {Y : D} (I : InjectiveResolution Y) {n : ℕ}
  (f : F.obj X ⟶ I.cocomplex.X n)
  (hf : f ≫ I.cocomplex.d n (n + 1) = 0)

/-- The published Ext adjunction sends a resolution cocycle to its actual adjunct. -/
lemma extEquiv_extMk :
    adj.extEquiv (I.extMk f (n + 1) rfl hf) =
      (mapInjectiveResolution G I).extMk (adj.homEquiv X _ f) (n + 1) rfl
        (by
          rw [Adjunction.homEquiv_unit]
          change (adj.unit.app X ≫ G.map f) ≫ G.map (I.cocomplex.d n (n + 1)) = 0
          rw [Category.assoc, ← G.map_comp, hf, G.map_zero, comp_zero]) := by
  rw [Adjunction.extEquiv_apply, ExtResolutionMap.extMk_mapExactFunctor,
    InjectiveResolution.mk₀_comp_extMk]
  rfl

/-- The actual adjunct map between the Hom complexes of a resolution and its image. -/
def adjunctionResolutionHomMap :
    ((preadditiveCoyoneda.obj (op (F.obj X))).mapHomologicalComplex (.up ℕ)).obj I.cocomplex ⟶
      ((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex (.up ℕ)).obj
        (mapInjectiveResolution G I).cocomplex :=
  (Functor.mapHomologicalComplexCompIso (homAdjunctionIso adj X) _).inv.app I.cocomplex

/-- On resolution homology, the existing Ext adjunction is the actual adjunct
map on the coefficients in every degree. -/
lemma extAddEquivHomology_symm_adjunction (n : ℕ)
    (a : (((preadditiveCoyoneda.obj (op (F.obj X))).mapHomologicalComplex (.up ℕ)).obj
      I.cocomplex).homology n) :
    (ExtRightDerived.extAddEquivHomology X (mapInjectiveResolution G I) n).symm
        (HomologicalComplex.homologyMap (adjunctionResolutionHomMap adj X I) n a) =
      adj.extEquiv ((ExtRightDerived.extAddEquivHomology (F.obj X) I n).symm a) := by
  let K := ((preadditiveCoyoneda.obj (op (F.obj X))).mapHomologicalComplex (.up ℕ)).obj I.cocomplex
  let L := ((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex (.up ℕ)).obj
    (mapInjectiveResolution G I).cocomplex
  let ψ := adjunctionResolutionHomMap adj X I
  obtain ⟨c, rfl⟩ := (AddCommGrpCat.epi_iff_surjective (K.homologyπ n)).1 inferInstance a
  change (ExtRightDerived.extAddEquivHomology X (mapInjectiveResolution G I) n).symm
    ((K.homologyπ n ≫ HomologicalComplex.homologyMap ψ n) c) = _
  erw [HomologicalComplex.homologyπ_naturality]
  change (ExtRightDerived.extAddEquivHomology X (mapInjectiveResolution G I) n).symm
    (L.homologyπ n (HomologicalComplex.cyclesMap ψ n c)) = _
  rw [ExtRightDerived.extAddEquivHomology_symm_homologyπ,
    ExtRightDerived.extAddEquivHomology_symm_homologyπ, extEquiv_extMk]
  congr 1
  exact ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i ψ n) c

end Langlands.Cohomology.ExtAdjunctionResolution

namespace Langlands.Cohomology.ExtRightDerived

variable {C : Type*} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
  [HasExt.{wC} C] (X : C) {Y : C} (I : InjectiveResolution Y) (n : ℕ)

/-- The unchanged Ext/right-derived comparison is computed on any actual
injective resolution, with its specified canonical derived comparison. -/
lemma extAddEquivRightDerived_eq_of_resolution (a : Ext.{wC} X Y n) :
    extAddEquivRightDerived X Y n a =
      (I.isoRightDerivedObj (preadditiveCoyoneda.obj (op X)) n).inv
        (extAddEquivHomology X I n a) := by
  let J := injectiveResolution Y
  let φ : InjectiveResolution.Hom I J (𝟙 Y) :=
    ⟨InjectiveResolution.desc (𝟙 Y) J I, by
      simp [InjectiveResolution.desc_commutes_zero]⟩
  have ht := extAddEquivHomology_naturality X (𝟙 Y) I J φ n a
  simp only [Ext.comp_mk₀_id] at ht
  change (J.isoRightDerivedObj (preadditiveCoyoneda.obj (op X)) n).inv
    (extAddEquivHomology X J n a) = _
  rw [ht]
  have hr := InjectiveResolution.isoRightDerivedObj_inv_naturality (𝟙 Y) I J φ.hom
    (by simp) (preadditiveCoyoneda.obj (op X)) n
  simp only [CategoryTheory.Functor.map_id, Category.comp_id] at hr
  exact (ConcreteCategory.congr_hom hr (extAddEquivHomology X I n a)).symm

end Langlands.Cohomology.ExtRightDerived
