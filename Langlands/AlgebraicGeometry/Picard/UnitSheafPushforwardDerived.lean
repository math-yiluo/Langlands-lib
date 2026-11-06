import Langlands.AlgebraicGeometry.Picard.UnitSheafPushforwardNaturality
import Langlands.Cohomology.AbelianSheafDerivedSectionsResolution
import Langlands.Cohomology.AcyclicResolution.ExactComparison
import Langlands.AlgebraicGeometry.Modules.HigherDirectImageOpenRestriction

/-! # Actual Ext and derived-sections pushforward under a homeomorphism -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace
open Langlands.Cohomology Langlands.Cohomology.AcyclicResolution
open Langlands.Cohomology.DerivedComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxRecDepth 2048
set_option maxHeartbeats 800000

namespace Langlands.AlgebraicGeometry.Picard.UnitSheafPushforward

variable {X Y : TopCat.{u}} (e : X ≅ Y)


local instance : (TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom).IsEquivalence :=
  (sheafPushforwardEquivalence (C := AddCommGrpCat.{u}) e).isEquivalence_functor
local instance : (TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.inv).IsEquivalence :=
  (sheafPushforwardEquivalence (C := AddCommGrpCat.{u}) e).isEquivalence_inverse
local instance : (TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom).Additive := Functor.additive_of_preserves_binary_products _
local instance : (TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.inv).Additive := Functor.additive_of_preserves_binary_products _

private abbrev pushforwardAdjunction : (TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.inv) ⊣ (TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom) :=
  (sheafPushforwardEquivalence (C := AddCommGrpCat.{u}) e).symm.toAdjunction

/-- Actual sections of an abelian-sheaf pushforward are actual sections on its source. -/
def pushforwardSectionsIso :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom) ⋙ AbelianSheafDerivedSections.globalSections Y ≅
      AbelianSheafDerivedSections.globalSections X :=
  NatIso.ofComponents (fun _ => Iso.refl _)

/-- The inverse of the published Ext-defined cohomology equivalence uses the
forward exact adjunction and the actual constant-sheaf isomorphism. -/
lemma cohomologyPushforwardEquiv_symm_apply
    (F : X.Sheaf AddCommGrpCat.{u}) (n : ℕ) (a : Sheaf.H.{u} F n) :
    (cohomologyPushforwardEquiv e F n).symm a =
      (pushforwardAdjunction e).extEquiv
        ((Ext.mk₀ ((constantInversePushforwardIso e).hom.app
          (AddCommGrpCat.of (ULift ℤ)))).comp a (zero_add n)) := by
  apply (cohomologyPushforwardEquiv e F n).injective
  rw [AddEquiv.apply_symm_apply, cohomologyPushforwardEquiv_apply,
    AddEquiv.symm_apply_apply]
  rw [← Ext.comp_assoc _ _ _ (zero_add 0) (zero_add n) (zero_add n),
    Ext.mk₀_comp_mk₀, Iso.inv_hom_id_app, Ext.mk₀_id_comp]

private lemma homGlobalSectionsIso_mk₀ (Z : TopCat.{u})
    (F : Z.Sheaf AddCommGrpCat.{u})
    (a : AbelianSheafDerivedSections.constantIntegers Z ⟶ F) :
    (AbelianSheafDerivedSections.homGlobalSectionsIso Z).hom.app F a =
      Sheaf.H.equiv₀ F (isTerminalTop (α := Opens Z)) (Ext.mk₀ a) := by
  simp only [Sheaf.H.equiv₀, AddEquiv.trans_apply, ← Ext.addEquiv₀_symm_apply,
    AddEquiv.apply_symm_apply, Adjunction.homAddEquiv_apply]
  rfl

private lemma adjunct_sections (F : X.Sheaf AddCommGrpCat.{u})
    (a : AbelianSheafDerivedSections.constantIntegers X ⟶ F) :
    (AbelianSheafDerivedSections.homGlobalSectionsIso Y).hom.app ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom).obj F)
      ((pushforwardAdjunction e).homEquiv _ _
        ((constantInversePushforwardIso e).hom.app
          (AddCommGrpCat.of (ULift ℤ)) ≫ a)) =
      (AbelianSheafDerivedSections.homGlobalSectionsIso X).hom.app F a := by
  have h := cohomologyPushforwardEquiv_equiv₀ e F
    ((cohomologyPushforwardEquiv e F 0).symm (Ext.mk₀ a))
  rw [AddEquiv.apply_symm_apply, cohomologyPushforwardEquiv_symm_apply,
    Ext.mk₀_comp_mk₀, Adjunction.extEquiv_mk₀] at h
  rw [homGlobalSectionsIso_mk₀, homGlobalSectionsIso_mk₀]
  exact h.symm

variable {F : X.Sheaf AddCommGrpCat.{u}} (I : InjectiveResolution F)

/-- The actual coefficient map on Hom resolutions induced by inverse cohomology
pushforward, before taking homology. -/
def pushforwardResolutionHomMap :
    ((preadditiveCoyoneda.obj (op (AbelianSheafDerivedSections.constantIntegers X))).mapHomologicalComplex
      (.up ℕ)).obj I.cocomplex ⟶
    ((preadditiveCoyoneda.obj (op (AbelianSheafDerivedSections.constantIntegers Y))).mapHomologicalComplex
      (.up ℕ)).obj
      (mapInjectiveResolution (TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom) I).cocomplex where
  f _ := AddCommGrpCat.ofHom
    { toFun := fun a => (pushforwardAdjunction e).homEquiv _ _
        ((constantInversePushforwardIso e).hom.app (AddCommGrpCat.of (ULift ℤ)) ≫ a)
      map_zero' := by
        change (pushforwardAdjunction e).homAddEquiv _ _ (_ ≫ 0) = 0
        rw [comp_zero, map_zero]
      map_add' := by
        intro a b
        change (pushforwardAdjunction e).homAddEquiv _ _ (_ ≫ (a + b)) = _
        rw [Preadditive.comp_add, map_add]
        rfl }
  comm' i j _ := by
    ext a
    change ((pushforwardAdjunction e).homEquiv _ _
      ((constantInversePushforwardIso e).hom.app (AddCommGrpCat.of (ULift ℤ)) ≫ a)) ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom).map (I.cocomplex.d i j) =
      (pushforwardAdjunction e).homEquiv _ _
        ((constantInversePushforwardIso e).hom.app (AddCommGrpCat.of (ULift ℤ)) ≫
          (a ≫ I.cocomplex.d i j))
    exact (by simpa only [Category.assoc] using
      ((pushforwardAdjunction e).homEquiv_naturality_right
        ((constantInversePushforwardIso e).hom.app (AddCommGrpCat.of (ULift ℤ)) ≫ a)
        (I.cocomplex.d i j)).symm)

private lemma pushforwardResolutionHomMap_sections :
    pushforwardResolutionHomMap e I ≫
      (NatTrans.mapHomologicalComplex (AbelianSheafDerivedSections.homGlobalSectionsIso Y).hom _).app
        (mapInjectiveResolution (TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom) I).cocomplex =
    (NatTrans.mapHomologicalComplex (AbelianSheafDerivedSections.homGlobalSectionsIso X).hom _).app
        I.cocomplex ≫
      (Functor.mapHomologicalComplexCompIso (pushforwardSectionsIso e) _).inv.app I.cocomplex := by
  apply HomologicalComplex.hom_ext
  intro j
  ext a
  exact adjunct_sections e (I.cocomplex.X j) a

set_option maxHeartbeats 2400000 in
private lemma extAddEquivHomology_symm_pushforward (n : ℕ)
    (a : (((preadditiveCoyoneda.obj (op (AbelianSheafDerivedSections.constantIntegers X))).mapHomologicalComplex
      (.up ℕ)).obj I.cocomplex).homology n) :
    (ExtRightDerived.extAddEquivHomology (AbelianSheafDerivedSections.constantIntegers Y)
        (mapInjectiveResolution (TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom) I) n).symm
      (HomologicalComplex.homologyMap (pushforwardResolutionHomMap e I) n a) =
    (cohomologyPushforwardEquiv e F n).symm
      ((ExtRightDerived.extAddEquivHomology (AbelianSheafDerivedSections.constantIntegers X) I n).symm a) := by
  let K := ((preadditiveCoyoneda.obj (op (AbelianSheafDerivedSections.constantIntegers X))).mapHomologicalComplex
    (.up ℕ)).obj I.cocomplex
  let J := mapInjectiveResolution (TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom) I
  let L := ((preadditiveCoyoneda.obj (op (AbelianSheafDerivedSections.constantIntegers Y))).mapHomologicalComplex
    (.up ℕ)).obj J.cocomplex
  let ψ := pushforwardResolutionHomMap e I
  obtain ⟨c, rfl⟩ := (AddCommGrpCat.epi_iff_surjective (K.homologyπ n)).1 inferInstance a
  change (ExtRightDerived.extAddEquivHomology (AbelianSheafDerivedSections.constantIntegers Y) J n).symm
    ((K.homologyπ n ≫ HomologicalComplex.homologyMap ψ n) c) = _
  erw [HomologicalComplex.homologyπ_naturality]
  change (ExtRightDerived.extAddEquivHomology (AbelianSheafDerivedSections.constantIntegers Y) J n).symm
    (L.homologyπ n (HomologicalComplex.cyclesMap ψ n c)) = _
  rw [ExtRightDerived.extAddEquivHomology_symm_homologyπ,
    ExtRightDerived.extAddEquivHomology_symm_homologyπ,
    cohomologyPushforwardEquiv_symm_apply, InjectiveResolution.mk₀_comp_extMk]
  rw [ExtAdjunctionResolution.extEquiv_extMk
    (F := TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.inv)
    (G := TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom)
    (pushforwardAdjunction e) (AbelianSheafDerivedSections.constantIntegers Y) I]
  congr 1
  exact ConcreteCategory.congr_hom (HomologicalComplex.cyclesMap_i ψ n) c

private lemma extAddEquivHomology_pushforward (n : ℕ) (a : Sheaf.H.{u} F n) :
    ExtRightDerived.extAddEquivHomology (AbelianSheafDerivedSections.constantIntegers Y)
        (mapInjectiveResolution (TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom) I) n
      ((cohomologyPushforwardEquiv e F n).symm a) =
    HomologicalComplex.homologyMap (pushforwardResolutionHomMap e I) n
      (ExtRightDerived.extAddEquivHomology (AbelianSheafDerivedSections.constantIntegers X) I n a) := by
  apply (ExtRightDerived.extAddEquivHomology (AbelianSheafDerivedSections.constantIntegers Y)
    (mapInjectiveResolution (TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom) I) n).symm.injective
  rw [AddEquiv.symm_apply_apply, extAddEquivHomology_symm_pushforward, AddEquiv.symm_apply_apply]

/-- The existing inverse Ext-defined pushforward map on actual sheaf cohomology
is the identity sections comparison on the mapped injective-resolution complex. -/
lemma resolutionGlobalSectionsHomologyEquiv_pushforward (n : ℕ) (a : Sheaf.H.{u} F n) :
    AbelianSheafDerivedSections.resolutionGlobalSectionsHomologyEquiv Y
      (mapInjectiveResolution (TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom) I) n
      ((cohomologyPushforwardEquiv e F n).symm a) =
    HomologicalComplex.homologyMap
      ((Functor.mapHomologicalComplexCompIso (pushforwardSectionsIso e) _).inv.app I.cocomplex) n
      (AbelianSheafDerivedSections.resolutionGlobalSectionsHomologyEquiv X I n a) := by
  simp only [AbelianSheafDerivedSections.resolutionGlobalSectionsHomologyEquiv, AddEquiv.trans_apply]
  rw [extAddEquivHomology_pushforward]
  have hs := congrArg (HomologicalComplex.homologyFunctor AddCommGrpCat.{u} (.up ℕ) n).map
    (pushforwardResolutionHomMap_sections e I)
  simp only [Functor.map_comp] at hs
  exact ConcreteCategory.congr_hom hs
    (ExtRightDerived.extAddEquivHomology (AbelianSheafDerivedSections.constantIntegers X) I n a)

/-- The canonical comparison of actual degreewise derived sections under the
homeomorphism, using the identity comparison on actual sections. -/
def pushforwardDerivedComparison (F : X.Sheaf AddCommGrpCat.{u}) (n : ℕ) :
    ((AbelianSheafDerivedSections.globalSections X).rightDerived n).obj F ⟶
      ((AbelianSheafDerivedSections.globalSections Y).rightDerived n).obj
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom).obj F) :=
  compComparison (F := TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom)
    (AbelianSheafDerivedSections.globalSections Y) (pushforwardSectionsIso e) F
    (fun q => Langlands.AlgebraicGeometry.Modules.DerivedSections.isZero_rightDerived_succ_of_preservesHomology
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom) F q) n

private lemma comparisonOfInjectiveResolution
    {C D : Type*} [Category* C] [Abelian C] [HasInjectiveResolutions C]
    [Category* D] [Abelian D] (G : C ⥤ D) [G.Additive]
    {A : C} (J : InjectiveResolution A) (n : ℕ) :
    resolutionComparison G J.ι n = (J.isoRightDerivedObj G n).inv := by
  rw [resolutionComparison_eq G J.ι J (𝟙 _) (Category.comp_id _) n]
  simp only [comparison, CategoryTheory.Functor.map_id, Category.id_comp]

/-- The existing inverse Ext-defined pushforward equivalence is exactly the
canonical comparison on right-derived actual global sections. -/
lemma cohomologyPushforwardEquiv_symm_HAddEquiv (n : ℕ) (a : Sheaf.H.{u} F n) :
    AbelianSheafDerivedSections.HAddEquiv Y
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom).obj F) n
      ((cohomologyPushforwardEquiv e F n).symm a) =
    pushforwardDerivedComparison e F n (AbelianSheafDerivedSections.HAddEquiv X F n a) := by
  let I := injectiveResolution F
  let J := mapInjectiveResolution (TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom) I
  have hc := resolutionComparison_compComparison
    (F := TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom)
    (AbelianSheafDerivedSections.globalSections Y) (pushforwardSectionsIso e) I.ι
    (fun q => Langlands.AlgebraicGeometry.Modules.DerivedSections.isZero_rightDerived_succ_of_preservesHomology
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom) F q) n
  change resolutionComparison (AbelianSheafDerivedSections.globalSections X) I.ι n ≫
      pushforwardDerivedComparison e F n =
    HomologicalComplex.homologyMap
        ((Functor.mapHomologicalComplexCompIso (pushforwardSectionsIso e) _).inv.app I.cocomplex) n ≫
      resolutionComparison (AbelianSheafDerivedSections.globalSections Y) J.ι n at hc
  rw [comparisonOfInjectiveResolution, comparisonOfInjectiveResolution] at hc
  rw [AbelianSheafDerivedSections.HAddEquiv_eq_of_resolution Y J n,
    AbelianSheafDerivedSections.HAddEquiv_eq_of_resolution X I n,
    resolutionGlobalSectionsHomologyEquiv_pushforward e I n a]
  exact (ConcreteCategory.congr_hom hc
    (AbelianSheafDerivedSections.resolutionGlobalSectionsHomologyEquiv X I n a)).symm

/-- The forward square retains the published actual Ext-defined pushforward
and the canonical derived-sections comparison, with no chosen replacement maps. -/
lemma cohomologyPushforwardEquiv_HAddEquiv (n : ℕ)
    (a : Sheaf.H.{u} ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom).obj F) n) :
    pushforwardDerivedComparison e F n
        (AbelianSheafDerivedSections.HAddEquiv X F n (cohomologyPushforwardEquiv e F n a)) =
      AbelianSheafDerivedSections.HAddEquiv Y
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} e.hom).obj F) n a := by
  rw [← cohomologyPushforwardEquiv_symm_HAddEquiv e n, AddEquiv.symm_apply_apply]

end Langlands.AlgebraicGeometry.Picard.UnitSheafPushforward
