import Langlands.AlgebraicGeometry.ModuleDualPullback
import Langlands.AlgebraicGeometry.ModuleDualLocalFree
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-! # The dual pullback comparison is invertible for finite local bases -/

open CategoryTheory CategoryTheory.Functor AlgebraicGeometry Opposite TopologicalSpace
open Langlands.SchemeModule

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

universe u

noncomputable section

namespace Langlands.Scheme.Modules

variable {X Y Z : AlgebraicGeometry.Scheme.{u}}

section Locality

/-- A morphism of module sheaves is invertible if it is invertible after restriction to the
members of an open cover. -/
lemma isIso_of_isIso_restrict {P Q : X.Modules} (φ : P ⟶ Q)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      IsIso ((AlgebraicGeometry.Scheme.Modules.restrictFunctor U.ι).map φ)) :
    IsIso φ := by
  let F : TopCat.Sheaf Ab X := ⟨P.presheaf, P.isSheaf⟩
  let G : TopCat.Sheaf Ab X := ⟨Q.presheaf, Q.isSheaf⟩
  let ψ : F ⟶ G := ⟨(AlgebraicGeometry.Scheme.Modules.toPresheaf X).map φ⟩
  have hs : ∀ x : X, IsIso ((TopCat.Presheaf.stalkFunctor Ab x).map ψ.1) := by
    intro x
    obtain ⟨U, hx, hU⟩ := h x
    have e := AlgebraicGeometry.Scheme.Modules.restrictStalkNatIso U.ι (⟨x, hx⟩ : U.toScheme)
    have h1 : IsIso ((AlgebraicGeometry.Scheme.Modules.restrictFunctor U.ι ⋙
        AlgebraicGeometry.Scheme.Modules.toPresheaf U.toScheme ⋙
        TopCat.Presheaf.stalkFunctor Ab.{u} (⟨x, hx⟩ : U.toScheme)).map φ) :=
      inferInstanceAs (IsIso ((AlgebraicGeometry.Scheme.Modules.toPresheaf U.toScheme ⋙
        TopCat.Presheaf.stalkFunctor Ab.{u} (⟨x, hx⟩ : U.toScheme)).map
          ((AlgebraicGeometry.Scheme.Modules.restrictFunctor U.ι).map φ)))
    exact (NatIso.isIso_map_iff e φ).mp h1
  have : IsIso ψ := TopCat.Presheaf.isIso_of_stalkFunctor_map_iso ψ
  have : IsIso ((AlgebraicGeometry.Scheme.Modules.toPresheaf X).map φ) :=
    inferInstanceAs (IsIso ((sheafToPresheaf _ _).map ψ))
  exact isIso_of_reflects_iso φ (AlgebraicGeometry.Scheme.Modules.toPresheaf X)

end Locality

section Retract

instance isIso_dualMap {M N : X.Modules} (a : M ⟶ N) [IsIso a] : IsIso (dualMap a) :=
  ⟨dualMap (inv a), by rw [← dualMap_comp, IsIso.inv_hom_id, dualMap_id],
    by rw [← dualMap_comp, IsIso.hom_inv_id, dualMap_id]⟩

private lemma dualMap_sum {M N : X.Modules} {J : Type*} (s : Finset J) (a : J → (M ⟶ N)) :
    dualMap (∑ k ∈ s, a k) = ∑ k ∈ s, dualMap (a k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert k s hk ih => rw [Finset.sum_insert hk, Finset.sum_insert hk, dualMap_add, ih]

/-- If a module is a finite retract-sum of modules with invertible comparison, then its
comparison is invertible. -/
lemma isIso_dualPullbackComparison_of_sum (f : X ⟶ Y) {P : Y.Modules} {J : Type*}
    [Fintype J] (N : J → Y.Modules) (ι : ∀ k, N k ⟶ P) (π : ∀ k, P ⟶ N k)
    (hsum : ∑ k, π k ≫ ι k = 𝟙 P) (hN : ∀ k, IsIso (dualPullbackComparison f (N k))) :
    IsIso (dualPullbackComparison f P) := by
  refine ⟨∑ k, dualMap ((AlgebraicGeometry.Scheme.Modules.pullback f).map (ι k)) ≫
      inv (dualPullbackComparison f (N k)) ≫
      (AlgebraicGeometry.Scheme.Modules.pullback f).map (dualMap (π k)), ?_, ?_⟩
  · rw [Preadditive.comp_sum]
    have hk : ∀ k, dualPullbackComparison f P ≫
        dualMap ((AlgebraicGeometry.Scheme.Modules.pullback f).map (ι k)) ≫
        inv (dualPullbackComparison f (N k)) ≫
        (AlgebraicGeometry.Scheme.Modules.pullback f).map (dualMap (π k)) =
        (AlgebraicGeometry.Scheme.Modules.pullback f).map (dualMap (π k ≫ ι k)) := by
      intro k
      rw [← Category.assoc, ← dualPullbackComparison_naturality, Category.assoc,
        IsIso.hom_inv_id_assoc, ← CategoryTheory.Functor.map_comp, dualMap_comp]
    simp only [hk]
    rw [← CategoryTheory.Functor.map_sum, ← dualMap_sum, hsum, dualMap_id,
      CategoryTheory.Functor.map_id]
  · rw [Preadditive.sum_comp]
    have hk : ∀ k, (dualMap ((AlgebraicGeometry.Scheme.Modules.pullback f).map (ι k)) ≫
        inv (dualPullbackComparison f (N k)) ≫
        (AlgebraicGeometry.Scheme.Modules.pullback f).map (dualMap (π k))) ≫
        dualPullbackComparison f P =
        dualMap ((AlgebraicGeometry.Scheme.Modules.pullback f).map (π k ≫ ι k)) := by
      intro k
      rw [Category.assoc, Category.assoc, dualPullbackComparison_naturality,
        IsIso.inv_hom_id_assoc, ← dualMap_comp, ← CategoryTheory.Functor.map_comp]
    simp only [hk]
    rw [← dualMap_sum, ← CategoryTheory.Functor.map_sum, hsum, CategoryTheory.Functor.map_id,
      dualMap_id]

/-- Invertibility of the comparison is invariant under isomorphism of the module. -/
lemma isIso_dualPullbackComparison_of_iso (f : X ⟶ Y) {N P : Y.Modules} (e : N ≅ P)
    (hN : IsIso (dualPullbackComparison f N)) : IsIso (dualPullbackComparison f P) := by
  have h := dualPullbackComparison_naturality f e.hom
  have : IsIso (dualPullbackComparison f P ≫
      dualMap ((AlgebraicGeometry.Scheme.Modules.pullback f).map e.hom)) := by
    rw [← h]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    (dualMap ((AlgebraicGeometry.Scheme.Modules.pullback f).map e.hom))

end Retract

section SectionsEquiv

lemma internalHomSectionsEquiv_id (M : X.Modules) (U : X.Opens) :
    internalHomSectionsEquiv M M U (𝟙 (M.over U)) = 𝟙 _ := by
  ext V x
  rfl

lemma internalHomSectionsEquiv_comp {M N P : X.Modules} (U : X.Opens)
    (a : LocalHom M N U) (b : LocalHom N P U) :
    internalHomSectionsEquiv M P U (a ≫ b) =
      internalHomSectionsEquiv M N U a ≫ internalHomSectionsEquiv N P U b := by
  ext V x
  rfl

lemma internalHomSectionsEquiv_sum {M N : X.Modules} (U : X.Opens) {J : Type*}
    (s : Finset J) (a : J → LocalHom M N U) :
    internalHomSectionsEquiv M N U (∑ k ∈ s, a k) =
      ∑ k ∈ s, internalHomSectionsEquiv M N U (a k) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, internalHomSectionsEquiv_zero]
  | @insert k s hk ih =>
    rw [Finset.sum_insert hk, Finset.sum_insert hk, internalHomSectionsEquiv_add, ih]

lemma localHomPullback_id (f : X ⟶ Y) (M : Y.Modules) (U : Y.Opens) :
    localHomPullback f U (𝟙 (M.over U)) = 𝟙 _ := by
  apply (internalHomSectionsEquiv _ _ _).injective
  rw [internalHomSectionsEquiv_localHomPullback, internalHomSectionsEquiv_id]
  simp only [CategoryTheory.Functor.map_id]
  erw [internalHomSectionsEquiv_id, Category.id_comp]
  exact Iso.hom_inv_id_app _ _

end SectionsEquiv

section Unit

variable (X) in
/-- The identity local endomorphisms of the structure module form a global section of its
dual. -/
def unitDualSection : (dual (structureModule X)).sections :=
  PresheafOfModules.sectionsMk
    (fun U => (𝟙 _ : LocalHom (structureModule X) (structureModule X) U.unop))
    (fun _ _ _ => rfl)

variable (X) in
/-- The structure module maps to its dual, sending a function to multiplication by it. -/
def unitToDual : structureModule X ⟶ dual (structureModule X) :=
  (SheafOfModules.unitHomEquiv _).symm (unitDualSection X)

lemma unitToDual_app (U : X.Opens) (r : Γ(X, U)) :
    (unitToDual X).app U r =
      r • (𝟙 _ : LocalHom (structureModule X) (structureModule X) U) := rfl

instance isIso_unitToDual : IsIso (unitToDual X) := by
  rw [AlgebraicGeometry.Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro U
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun r s hrs => ?_, fun h => ?_⟩
  · have h1 := congrArg (fun k : LocalHom (structureModule X) (structureModule X) U =>
      (LocalHom.app k (𝟙 U)).hom (1 : Γ(X, U))) hrs
    change X.presheaf.map (𝟙 U).op r * 1 = X.presheaf.map (𝟙 U).op s * 1 at h1
    simpa using h1
  · let h' : LocalHom (structureModule X) (structureModule X) U := h
    let c : Γ(X, U) := (LocalHom.app h' (𝟙 U)).hom (1 : Γ(X, U))
    refine ⟨c, ?_⟩
    change (c • (𝟙 _ : LocalHom (structureModule X) (structureModule X) U)) = h'
    refine LocalHom.ext _ _ (fun V i => ?_)
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    let y : Γ(X, V) := x
    have hn : (LocalHom.app h' i).hom (X.presheaf.map i.op (1 : Γ(X, U))) =
        X.presheaf.map i.op c :=
      internalHomEval_restrict (structureModule X) (structureModule X) i h' (1 : Γ(X, U))
    have h2 : (LocalHom.app h' i).hom (1 : Γ(X, V)) = X.presheaf.map i.op c := by
      rw [map_one] at hn
      exact hn
    have h1 : (LocalHom.app h' i).hom (y * 1) =
        y • (LocalHom.app h' i).hom (1 : Γ(X, V)) :=
      (LocalHom.app h' i).hom.map_smul y (1 : Γ(X, V))
    change X.presheaf.map i.op c * y = (LocalHom.app h' i).hom y
    calc X.presheaf.map i.op c * y = y * X.presheaf.map i.op c := mul_comm _ _
      _ = y • (LocalHom.app h' i).hom (1 : Γ(X, V)) := by rw [h2]; rfl
      _ = (LocalHom.app h' i).hom (y * 1) := h1.symm
      _ = (LocalHom.app h' i).hom y := by rw [mul_one]

lemma pullback_unitToDual_comp (g : X ⟶ Y) :
    (AlgebraicGeometry.Scheme.Modules.pullback g).map (unitToDual Y) ≫
        dualPullbackComparison g (structureModule Y) =
      (pullbackUnitIso g).hom ≫ unitToDual X ≫ dualMap (pullbackUnitIso g).hom := by
  apply ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv
    _ _).injective
  rw [Adjunction.homEquiv_naturality_left, homEquiv_dualPullbackComparison,
    Adjunction.homEquiv_naturality_right]
  erw [pullbackUnitAdjunction X Y g]
  apply (SheafOfModules.unitHomEquiv _).injective
  refine PresheafOfModules.sections_ext _ _ (fun U => ?_)
  change localDualPullback g (structureModule Y) U.unop
      ((1 : Γ(Y, U.unop)) • (𝟙 _ : LocalHom (structureModule Y) (structureModule Y) U.unop)) =
    (pullbackUnitIso g).hom.over (g ⁻¹ᵁ U.unop) ≫
      ((g.app U.unop (1 : Γ(Y, U.unop))) •
        (𝟙 _ : LocalHom (structureModule X) (structureModule X) (g ⁻¹ᵁ U.unop))) ≫
      (SheafOfModules.overFunctor X.ringCatSheaf (g ⁻¹ᵁ U.unop)).map (𝟙 (structureModule X))
  rw [one_smul, map_one, one_smul, localDualPullback, localHomPullback_id]
  simp
  exact (Category.comp_id _).symm

/-- The comparison is invertible for the structure module. -/
instance isIso_dualPullbackComparison_unit (g : X ⟶ Y) :
    IsIso (dualPullbackComparison g (structureModule Y)) := by
  have : IsIso ((AlgebraicGeometry.Scheme.Modules.pullback g).map (unitToDual Y) ≫
      dualPullbackComparison g (structureModule Y)) := by
    rw [pullback_unitToDual_comp g]
    infer_instance
  exact IsIso.of_isIso_comp_left
    ((AlgebraicGeometry.Scheme.Modules.pullback g).map (unitToDual Y)) _

end Unit

section OpenImmersion

/-- Pullback along an isomorphism of schemes is fully faithful. -/
def pullbackFullyFaithfulOfIsIso (g : X ⟶ Y) [IsIso g] :
    (AlgebraicGeometry.Scheme.Modules.pullback g).FullyFaithful :=
  (CategoryTheory.Equivalence.mk (AlgebraicGeometry.Scheme.Modules.pullback g)
    (AlgebraicGeometry.Scheme.Modules.pullback (inv g))
    ((AlgebraicGeometry.Scheme.Modules.pullbackId Y).symm ≪≫
      AlgebraicGeometry.Scheme.Modules.pullbackCongr (IsIso.inv_hom_id g).symm ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullbackComp (inv g) g).symm)
    (AlgebraicGeometry.Scheme.Modules.pullbackComp g (inv g) ≪≫
      AlgebraicGeometry.Scheme.Modules.pullbackCongr (IsIso.hom_inv_id g) ≪≫
      AlgebraicGeometry.Scheme.Modules.pullbackId X)).fullyFaithfulFunctor

/-- Local functional pullback is bijective over an open on which the morphism restricts to
an isomorphism. -/
lemma localDualPullback_bijective (f : X ⟶ Y) (M : Y.Modules) (U : Y.Opens)
    [IsIso (f ∣_ U)] : Function.Bijective (localDualPullback f M U) := by
  let d := (SheafOfModules.overFunctor X.ringCatSheaf (f ⁻¹ᵁ U)).mapIso (pullbackUnitIso f)
  let e5 : LocalHom ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M)
      ((AlgebraicGeometry.Scheme.Modules.pullback f).obj (structureModule Y)) (f ⁻¹ᵁ U) ≃
      LocalHom ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M) (structureModule X)
        (f ⁻¹ᵁ U) :=
    { toFun := fun k => k ≫ d.hom
      invFun := fun k => k ≫ d.inv
      left_inv := fun k => by simp
      right_inv := fun k => by simp }
  let e := (internalHomSectionsEquiv M (structureModule Y) U).trans
    ((pullbackFullyFaithfulOfIsIso (f ∣_ U)).homEquiv.trans
      ((Iso.homCongr ((restrictPullbackNatIso f U).app M).symm
        ((restrictPullbackNatIso f U).app (structureModule Y)).symm).trans
        ((internalHomSectionsEquiv _ _ _).symm.trans e5)))
  exact e.bijective

/-- An open immersion restricts to an isomorphism over the image of an open. -/
lemma isIso_morphismRestrict_image (j : X ⟶ Y) [IsOpenImmersion j] (W : X.Opens) :
    IsIso (j ∣_ (j ''ᵁ W)) := by
  rw [isIso_iff_isOpenImmersion_and_epi_base]
  refine ⟨inferInstance, ?_⟩
  rw [TopCat.epi_iff_surjective]
  rintro ⟨y, hy⟩
  obtain ⟨x, hx, rfl⟩ := hy
  exact ⟨⟨x, ⟨x, hx, rfl⟩⟩, Subtype.ext (morphismRestrict_base_coe j _ _)⟩

/-- The comparison is invertible for an open immersion and an arbitrary module. -/
instance isIso_dualPullbackComparison_of_isOpenImmersion (j : X ⟶ Y) [IsOpenImmersion j]
    (N : Y.Modules) : IsIso (dualPullbackComparison j N) := by
  have hφ : IsIso ((AlgebraicGeometry.Scheme.Modules.restrictFunctor j).map
      (dualPushforwardComparison j N)) := by
    rw [AlgebraicGeometry.Scheme.Modules.Hom.isIso_iff_isIso_app]
    intro W
    rw [ConcreteCategory.isIso_iff_bijective]
    have := isIso_morphismRestrict_image j W
    exact localDualPullback_bijective j N (j ''ᵁ W)
  have key : ((AlgebraicGeometry.Scheme.Modules.restrictAdjunction j).leftAdjointUniq
        (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction j)).hom.app (dual N) ≫
        dualPullbackComparison j N =
      (AlgebraicGeometry.Scheme.Modules.restrictFunctor j).map
          (dualPushforwardComparison j N) ≫
        (AlgebraicGeometry.Scheme.Modules.restrictAdjunction j).counit.app _ := by
    rw [dualPullbackComparison, Adjunction.homEquiv_counit, ← Category.assoc,
      ← NatTrans.naturality, Category.assoc, Adjunction.leftAdjointUniq_hom_app_counit]
  have : IsIso (((AlgebraicGeometry.Scheme.Modules.restrictAdjunction j).leftAdjointUniq
        (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction j)).hom.app (dual N) ≫
        dualPullbackComparison j N) := by
    rw [key]
    infer_instance
  exact IsIso.of_isIso_comp_left
    (((AlgebraicGeometry.Scheme.Modules.restrictAdjunction j).leftAdjointUniq
      (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction j)).hom.app (dual N))
    (dualPullbackComparison j N)

end OpenImmersion

section LocalBasis

/-- The comparison is invertible for the restriction of a module that is free of finite rank
on the open. -/
lemma isIso_dualPullbackComparison_restrict_of_free {U : Y.Opens} {M : Y.Modules}
    {I : Type u} [Fintype I]
    (e : SheafOfModules.free (R := Y.ringCatSheaf.over U) I ≅ M.over U)
    {Z : AlgebraicGeometry.Scheme.{u}} (g : Z ⟶ U.toScheme) :
    IsIso (dualPullbackComparison g
      ((AlgebraicGeometry.Scheme.Modules.restrictFunctor U.ι).obj M)) := by
  have hunit : IsIso (dualPullbackComparison g
      ((AlgebraicGeometry.Scheme.Modules.restrictFunctor U.ι).obj (structureModule Y))) :=
    isIso_dualPullbackComparison_of_iso g
      (AlgebraicGeometry.Scheme.Modules.restrictUnitIso U.ι).symm
      (isIso_dualPullbackComparison_unit g)
  refine isIso_dualPullbackComparison_of_sum g
    (fun _ : I => (AlgebraicGeometry.Scheme.Modules.restrictFunctor U.ι).obj (structureModule Y))
    (fun k => internalHomSectionsEquiv (structureModule Y) M U
      (SheafOfModules.ιFree k ≫ e.hom))
    (fun k => internalHomSectionsEquiv M (structureModule Y) U
      (e.inv ≫ freeCoordinate U I k)) ?_ (fun _ => hunit)
  have htot : ∑ k : I, (e.inv ≫ freeCoordinate U I k) ≫ (SheafOfModules.ιFree k ≫ e.hom) =
      𝟙 (M.over U) := by
    simp only [Category.assoc]
    rw [← Preadditive.comp_sum]
    have h2 : ∑ k : I, freeCoordinate U I k ≫ SheafOfModules.ιFree k ≫ e.hom =
        (∑ k : I, freeCoordinate U I k ≫ SheafOfModules.ιFree k) ≫ e.hom := by
      rw [Preadditive.sum_comp]
      simp only [Category.assoc]
    rw [h2, freeCoordinate_total, Category.id_comp, Iso.inv_hom_id]
  simp only [← internalHomSectionsEquiv_comp]
  rw [← internalHomSectionsEquiv_sum, htot, internalHomSectionsEquiv_id]

/-- The comparison is invertible if it is so after restriction to the members of an open
cover of the target, for every base morphism into them. -/
lemma isIso_dualPullbackComparison_of_local (f : X ⟶ Y) (M : Y.Modules)
    (h : ∀ y : Y, ∃ U : Y.Opens, y ∈ U ∧ ∀ {Z : AlgebraicGeometry.Scheme.{u}}
      (g : Z ⟶ U.toScheme), IsIso (dualPullbackComparison g
        ((AlgebraicGeometry.Scheme.Modules.restrictFunctor U.ι).obj M))) :
    IsIso (dualPullbackComparison f M) := by
  apply isIso_of_isIso_restrict
  intro x
  obtain ⟨U, hU, hg⟩ := h (f x)
  refine ⟨f ⁻¹ᵁ U, hU, ?_⟩
  rw [NatIso.isIso_map_iff (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback
    (f ⁻¹ᵁ U).ι)]
  have hU' : IsIso (dualPullbackComparison (f ∣_ U)
      ((AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj M)) :=
    isIso_dualPullbackComparison_of_iso (f ∣_ U)
      ((AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback U.ι).app M) (hg (f ∣_ U))
  have h3 : IsIso (dualPullbackComparison ((f ⁻¹ᵁ U).ι ≫ f) M) := by
    rw [← morphismRestrict_ι f U, dualPullbackComparison_comp]
    infer_instance
  rw [dualPullbackComparison_comp] at h3
  have h4 : IsIso ((AlgebraicGeometry.Scheme.Modules.pullback (f ⁻¹ᵁ U).ι).map
        (dualPullbackComparison f M) ≫
      dualPullbackComparison (f ⁻¹ᵁ U).ι ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M) ≫
      dualMap ((AlgebraicGeometry.Scheme.Modules.pullbackComp (f ⁻¹ᵁ U).ι f).inv.app M)) :=
    IsIso.of_isIso_comp_left
      ((AlgebraicGeometry.Scheme.Modules.pullbackComp (f ⁻¹ᵁ U).ι f).inv.app (dual M)) _
  exact IsIso.of_isIso_comp_right _
    (dualPullbackComparison (f ⁻¹ᵁ U).ι ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M) ≫
      dualMap ((AlgebraicGeometry.Scheme.Modules.pullbackComp (f ⁻¹ᵁ U).ι f).inv.app M))

/-- The dual pullback comparison is invertible for a module with a finite local basis. -/
theorem isIso_dualPullbackComparison_of_localGeneratorsData (f : X ⟶ Y) {M : Y.Modules}
    (q : SheafOfModules.LocalGeneratorsData.{u} M) [q.IsLocallyFreeData] [q.IsFiniteType] :
    IsIso (dualPullbackComparison f M) := by
  apply isIso_dualPullbackComparison_of_local
  intro y
  obtain ⟨i, hi⟩ := ((Opens.coversTop_iff _ q.X).mp q.coversTop).exists_mem y
  refine ⟨q.X i, hi, fun g => ?_⟩
  have : (q.generators i).IsFiniteType :=
    SheafOfModules.LocalGeneratorsData.IsFiniteType.isFiniteType i
  let : Fintype (q.generators i).I := Fintype.ofFinite _
  exact isIso_dualPullbackComparison_restrict_of_free (asIso (q.generators i).π) g

end LocalBasis

end Langlands.Scheme.Modules
