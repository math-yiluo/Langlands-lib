/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Modules.ExteriorPower
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Mathlib.LinearAlgebra.TensorProduct.Map
import WeilConjectures.AlgebraicGeometry.Modules.ExteriorSheafLocalFreeComparison
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-! # Section comparisons on a common free chart for a split sequence
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped TensorProduct
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
private noncomputable def smallerFrame {X : Scheme.{v}} (M : X.Modules)
    (U V : X.Opens) (h : V ≤ U) (I : Type v)
    (e : M.over U ≅ SheafOfModules.free I) :
    M.over V ≅ SheafOfModules.free I :=
  (overIsoFreeEquiv M V I).symm
    (restrictCompIso M U.ι (X.homOfLE h) V.ι (by simp) ≪≫
      (restrictFunctor (X.homOfLE h)).mapIso (overIsoFreeEquiv M U I e) ≪≫
      restrictFreeIso _ I)

set_option backward.isDefEq.respectTransparency false in
private theorem commonFrames {X : Scheme.{v}} (A C : X.Modules) (r s : ℕ)
    [A.IsFiniteLocallyFreeOfRank r] [C.IsFiniteLocallyFreeOfRank s]
    (U : X.Opens) (x : X) (hx : x ∈ U) :
    ∃ (V : X.Opens), V ≤ U ∧ x ∈ V ∧
      Nonempty (A.over V ≅ SheafOfModules.free (ULift.{v} (Fin r))) ∧
      Nonempty (C.over V ≅ SheafOfModules.free (ULift.{v} (Fin s))) := by
  obtain ⟨I, UA, hA, eA⟩ :=
    SheafOfModules.isFiniteLocallyFreeOfRank_iff_exists_over_iso_free (M := A) (r := r) |>.mp
      (inferInstanceAs (A.IsFiniteLocallyFreeOfRank r))
  obtain ⟨J, UC, hC, eC⟩ :=
    SheafOfModules.isFiniteLocallyFreeOfRank_iff_exists_over_iso_free (M := C) (r := s) |>.mp
      (inferInstanceAs (C.IsFiniteLocallyFreeOfRank s))
  obtain ⟨i, hi⟩ := ((Opens.coversTop_iff _ _).mp hA).exists_mem x
  obtain ⟨j, hj⟩ := ((Opens.coversTop_iff _ _).mp hC).exists_mem x
  refine ⟨U ⊓ UA i ⊓ UC j, inf_le_left.trans inf_le_left, ⟨⟨hx, hi⟩, hj⟩, ?_, ?_⟩
  · exact ⟨smallerFrame A _ _ (inf_le_left.trans inf_le_right) _ (eA i).some⟩
  · exact ⟨smallerFrame C _ _ inf_le_right _ (eC j).some⟩

private theorem transportedSplit
    {C D E : Type*} [Category C] [Category D] [Category E]
    [HasZeroMorphisms D] [HasZeroMorphisms E]
    [HasBinaryBiproducts D] [HasBinaryBiproducts E]
    (G : C ⥤ D) (F : D ⥤ E) (H : C ⥤ E) [F.Full] [F.Faithful]
    [F.PreservesZeroMorphisms] [PreservesBinaryBiproducts F] (i : G ⋙ F ≅ H)
    {A B Q : C} (f : A ⟶ B) (g : B ⟶ Q)
    (e : H.obj B ≅ H.obj A ⊞ H.obj Q)
    (hf : H.map f ≫ e.hom = biprod.inl) (hg : e.hom ≫ biprod.snd = H.map g) :
    ∃ eO : G.obj B ≅ G.obj A ⊞ G.obj Q,
      G.map f ≫ eO.hom = biprod.inl ∧ eO.hom ≫ biprod.snd = G.map g := by
  let d := (biprod.mapIso (i.app A) (i.app Q)).symm ≪≫
    (F.mapBiprod (G.obj A) (G.obj Q)).symm
  let eO := F.preimageIso (i.app B ≪≫ e ≪≫ d)
  have hn (f : A ⟶ B) :
      F.map (G.map f) ≫ (i.app B).hom =
        (i.app A).hom ≫ H.map f := i.hom.naturality f
  have hb : (F.mapBiprod (G.obj A) (G.obj Q)).inv ≫
      F.map biprod.snd = biprod.snd := by
    rw [← cancel_epi (F.mapBiprod (G.obj A) (G.obj Q)).hom]
    rw [Iso.hom_inv_id_assoc]
    exact (biprod.lift_snd _ _).symm
  refine ⟨eO, ?_, ?_⟩
  · apply F.map_injective
    simp only [Functor.map_comp, eO, Functor.preimageIso, Functor.map_preimage]
    dsimp only [Iso.trans_hom, Iso.symm_hom, d]
    rw [← Category.assoc, hn]
    rw [Category.assoc, ← Category.assoc (H.map f), hf]
    simp
  · apply F.map_injective
    simp only [Functor.map_comp, eO, Functor.preimageIso, Functor.map_preimage]
    dsimp only [Iso.trans_hom, Iso.symm_hom, d]
    simp only [Category.assoc, hb]
    rw [← cancel_mono (i.app Q).hom]
    simp only [biprod.mapIso_inv, Category.assoc]
    erw [biprod.map_snd_assoc]
    rw [Iso.inv_hom_id, Category.comp_id]
    rw [hg]
    exact (i.hom.naturality g).symm

set_option backward.isDefEq.respectTransparency false in
private theorem overSplit {X : Scheme.{v}} (S : ShortComplex X.Modules) (U : X.Opens)
    (e : S.X₂.restrict U.ι ≅ S.X₁.restrict U.ι ⊞ S.X₃.restrict U.ι)
    (hf : (restrictFunctor U.ι).map S.f ≫ e.hom = biprod.inl)
    (hg : e.hom ≫ biprod.snd = (restrictFunctor U.ι).map S.g) :
    ∃ eO : S.X₂.over U ≅ S.X₁.over U ⊞ S.X₃.over U,
      (SheafOfModules.overFunctor X.ringCatSheaf U).map S.f ≫ eO.hom = biprod.inl ∧
      eO.hom ≫ biprod.snd = (SheafOfModules.overFunctor X.ringCatSheaf U).map S.g := by
  let F := (overEquiv U).functor
  have : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBinaryProducts F
  exact transportedSplit (SheafOfModules.overFunctor X.ringCatSheaf U) F
    (restrictFunctor U.ι) (overFunctorEquiv U) S.f S.g e hf hg

set_option backward.isDefEq.respectTransparency false in
private noncomputable def middleFrame {X : Scheme.{v}} (S : ShortComplex X.Modules)
    (U V : X.Opens) (h : V ≤ U) (r s : ℕ)
    (e : S.X₂.over U ≅ S.X₁.over U ⊞ S.X₃.over U)
    (a : S.X₁.over V ≅ SheafOfModules.free (ULift.{v} (Fin r)))
    (c : S.X₃.over V ≅ SheafOfModules.free (ULift.{v} (Fin s))) :
    S.X₂.over V ≅ SheafOfModules.free (ULift.{v} (Fin (r + s))) := by
  let F := SheafOfModules.overMap X.ringCatSheaf (homOfLE h)
  have : F.PreservesZeroMorphisms := ⟨fun _ _ ↦ rfl⟩
  have : PreservesBinaryBiproducts F :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  let i := SheafOfModules.overFunctorMap X.ringCatSheaf (homOfLE h)
  exact (i.app S.X₂).symm ≪≫ F.mapIso e ≪≫ F.mapBiprod _ _ ≪≫
    biprod.mapIso (i.app S.X₁ ≪≫ a) (i.app S.X₃ ≪≫ c) ≪≫
    biprod.isoCoprod _ _ ≪≫ SheafOfModules.freeSumIso _ _ ≪≫
    SheafOfModules.freeFunctor.mapIso
      ((Equiv.sumCongr Equiv.ulift Equiv.ulift).trans
        (finSumFinEquiv.trans Equiv.ulift.symm)).toIso

private theorem mappedSplit
    {C D : Type*} [Category C] [Category D] [HasZeroMorphisms C] [HasZeroMorphisms D]
    [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms] [PreservesBinaryBiproducts F]
    {A B Q : C} (f : A ⟶ B) (g : B ⟶ Q) (e : B ≅ A ⊞ Q)
    (hf : f ≫ e.hom = biprod.inl) (hg : e.hom ≫ biprod.snd = g) :
    ∃ d : F.obj B ≅ F.obj A ⊞ F.obj Q,
      F.map f ≫ d.hom = biprod.inl ∧ d.hom ≫ biprod.snd = F.map g := by
  refine ⟨F.mapIso e ≪≫ F.mapBiprod A Q, ?_, ?_⟩
  · dsimp only [Iso.trans_hom, Functor.mapIso_hom]
    rw [← Category.assoc, ← F.map_comp, hf]
    apply biprod.hom_ext <;> simp [← F.map_comp]
  · dsimp only [Iso.trans_hom, Functor.mapIso_hom]
    rw [Category.assoc, Functor.mapBiprod_hom, biprod.lift_snd, ← F.map_comp, hg]

private theorem moduleSplit {R : Type*} [CommRing R] {A B Q : ModuleCat.{v} R}
    (f : A ⟶ B) (g : B ⟶ Q) (e : B ≅ A ⊞ Q)
    (hf : f ≫ e.hom = biprod.inl) (hg : e.hom ≫ biprod.snd = g) :
    ∃ d : B ≃ₗ[R] (A × Q), (∀ z, d (f z) = (z, 0)) ∧ (∀ z, (d z).2 = g z) := by
  let d := e ≪≫ ModuleCat.biprodIsoProd A Q
  have hp : (ModuleCat.biprodIsoProd A Q).hom ≫
      ModuleCat.ofHom (LinearMap.snd R A Q) = biprod.snd := by
    rw [← cancel_epi (ModuleCat.biprodIsoProd A Q).inv]
    simp
  refine ⟨d.toLinearEquiv, ?_, ?_⟩
  · have he : f ≫ d.hom = ModuleCat.ofHom (LinearMap.inl R A Q) := by
      dsimp only [d, Iso.trans_hom]
      rw [← Category.assoc, hf]
      apply (cancel_mono (ModuleCat.biprodIsoProd A Q).inv).mp
      simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      apply biprod.hom_ext <;> simp <;> rfl
    exact fun z ↦ CategoryTheory.congr_fun he z
  · have he : d.hom ≫ ModuleCat.ofHom (LinearMap.snd R A Q) = g := by
      dsimp only [d, Iso.trans_hom]
      rw [Category.assoc, hp, hg]
    exact fun z ↦ CategoryTheory.congr_fun he z

set_option backward.isDefEq.respectTransparency false in
private theorem evaluateSplit {X : Scheme.{v}} (S : ShortComplex X.Modules)
    (U W : X.Opens) (h : W ≤ U)
    (e : S.X₂.over U ≅ S.X₁.over U ⊞ S.X₃.over U)
    (hf : (SheafOfModules.overFunctor X.ringCatSheaf U).map S.f ≫ e.hom = biprod.inl)
    (hg : e.hom ≫ biprod.snd = (SheafOfModules.overFunctor X.ringCatSheaf U).map S.g) :
    ∃ eW : S.X₂.val.obj (op W) ≃ₗ[X.presheaf.obj (op W)]
        (S.X₁.val.obj (op W) × S.X₃.val.obj (op W)),
      (∀ z, eW (S.f.val.app (op W) z) = (z, 0)) ∧
      (∀ z, (eW z).2 = S.g.val.app (op W) z) := by
  let E := SheafOfModules.evaluation.{v} (X.ringCatSheaf.over U)
    (op (Over.mk (homOfLE h)))
  have : E.Additive := by
    dsimp only [E, SheafOfModules.evaluation]
    infer_instance
  have : PreservesBinaryBiproducts E :=
    preservesBinaryBiproducts_of_preservesBinaryProducts E
  obtain ⟨d, hfd, hgd⟩ := mappedSplit E
    ((SheafOfModules.overFunctor X.ringCatSheaf U).map S.f)
    ((SheafOfModules.overFunctor X.ringCatSheaf U).map S.g) e hf hg
  exact moduleSplit _ _ d hfd hgd

private theorem tensorSections_bijective_of_generator {X : Scheme.{v}} (M N : X.Modules)
    (V W : X.Opens) (h : W ≤ V) (t : Γ(N, V)) (ht : IsFreeGenerator t) :
    Function.Bijective (tensorSectionsMap M N W) := by
  have ha := TensorProduct.bijective_tmul_right_of_bijective_smul
    (A := Γ(M, W)) (ht.map h).bijective
  have hb := ht.bijective_tmulSection_right (M := M) h
  exact (Function.Bijective.of_comp_iff (tensorSectionsMap M N W) ha).mp hb

set_option backward.isDefEq.respectTransparency false in
private theorem topExterior_generator {X : Scheme.{v}} (M : X.Modules)
    (V : X.Opens) (r : ℕ)
    (e : M.over V ≅ SheafOfModules.free (ULift.{v} (Fin r))) :
    ∃ t : Γ(exteriorPower M r, V), IsFreeGenerator t := by
  classical
  let : Unique (Set.powersetCard (Fin r) r) :=
    { default := ⟨Finset.univ, by simp⟩
      uniq a := Subtype.ext (Finset.eq_univ_of_card a.val (by simp)) }
  obtain ⟨d⟩ := (exteriorSheaf_local_free_comparison X M r V r e).1
  exact exists_isFreeGenerator_of_iso (d ≪≫ SheafOfModules.freeUniqueIso _)

-- The unchanged statement names existential witnesses not used in later conjuncts.
set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency false in
/-- A common free chart identifies the sectionwise exterior and tensor constructions
with their sheaf counterparts, and evaluates a sheaf splitting as a module splitting. -/
theorem determinant_split_chart_comparison {X : Scheme.{v}}
    (S : ShortComplex X.Modules) (r s : ℕ)
    [S.X₁.IsFiniteLocallyFreeOfRank r] [S.X₃.IsFiniteLocallyFreeOfRank s]
    (U : X.Opens)
    (e : S.X₂.restrict U.ι ≅ S.X₁.restrict U.ι ⊞ S.X₃.restrict U.ι)
    (hf : (restrictFunctor U.ι).map S.f ≫ e.hom = biprod.inl)
    (hg : e.hom ≫ biprod.snd = (restrictFunctor U.ι).map S.g) :
    ∀ x ∈ U, ∃ (V : X.Opens) (hVU : V ≤ U), x ∈ V ∧
      ∀ (W : X.Opens), W ≤ V →
        ∃ (a : Module.Basis (Fin r) (X.presheaf.obj (op W)) (S.X₁.val.obj (op W)))
          (c : Module.Basis (Fin s) (X.presheaf.obj (op W)) (S.X₃.val.obj (op W)))
          (eW : S.X₂.val.obj (op W) ≃ₗ[X.presheaf.obj (op W)]
            (S.X₁.val.obj (op W) × S.X₃.val.obj (op W))),
          (∀ z, eW (S.f.val.app (op W) z) = (z, 0)) ∧
          (∀ z, (eW z).2 = S.g.val.app (op W) z) ∧
          Function.Bijective
            (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
              ((S.X₂.val.exteriorPower (R := X.presheaf) (r + s)))).app (op W)) ∧
          Function.Bijective
            ((tensorSectionsMap (exteriorPower S.X₁ r) (exteriorPower S.X₃ s) W).comp
              (TensorProduct.map (R := X.presheaf.obj (op W))
                (R₂ := X.presheaf.obj (op W)) (σ₁₂ := RingHom.id _)
                (((PresheafOfModules.sheafificationAdjunction
                  (𝟙 X.ringCatSheaf.obj)).unit.app
                  (S.X₁.val.exteriorPower (R := X.presheaf) r)).app (op W)).hom
                (((PresheafOfModules.sheafificationAdjunction
                  (𝟙 X.ringCatSheaf.obj)).unit.app
                  (S.X₃.val.exteriorPower (R := X.presheaf) s)).app (op W)).hom)) := by
  classical
  intro x hx
  obtain ⟨V, hVU, hxV, ⟨aV⟩, ⟨cV⟩⟩ := commonFrames S.X₁ S.X₃ r s U x hx
  obtain ⟨eO, hfO, hgO⟩ := overSplit S U e hf hg
  let bV := middleFrame S U V hVU r s eO aV cV
  have hB := (exteriorSheaf_local_free_comparison X S.X₂ (r + s) V (r + s) bV).2
  have hA := (exteriorSheaf_local_free_comparison X S.X₁ r V r aV).2
  have hC := (exteriorSheaf_local_free_comparison X S.X₃ s V s cV).2
  obtain ⟨t, ht⟩ := topExterior_generator S.X₃ V s cV
  refine ⟨V, hVU, hxV, ?_⟩
  intro W hWV
  let a := ((Pi.basisFun _ (ULift.{v} (Fin r))).map
    (SheafOfModules.sectionsLinearEquivOfIsoFree aV
      (op (Over.mk (homOfLE hWV)))).symm).reindex Equiv.ulift
  let c := ((Pi.basisFun _ (ULift.{v} (Fin s))).map
    (SheafOfModules.sectionsLinearEquivOfIsoFree cV
      (op (Over.mk (homOfLE hWV)))).symm).reindex Equiv.ulift
  obtain ⟨eW, hfW, hgW⟩ := evaluateSplit S U W (hWV.trans hVU) eO hfO hgO
  refine ⟨a, c, eW, hfW, hgW, hB W (homOfLE hWV), ?_⟩
  exact (tensorSections_bijective_of_generator _ _ V W hWV t ht).comp
    (TensorProduct.map_bijective (hA W (homOfLE hWV)) (hC W (homOfLE hWV)))

end AlgebraicGeometry.Scheme.Modules
