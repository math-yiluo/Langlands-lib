/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassCoefficients
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.PowerSystemOrdinaryCokernel
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced
import Mathlib.Algebra.Homology.HomologySequenceLemmas
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.Algebra.FreeAbelianGroup.Finsupp
import Mathlib.Algebra.Homology.HomotopyCategory.ShortExact

/-! # Flat resolutions adapted to simultaneous prime-power reduction -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u u₁ v₁ u₂ v₂ w₁ w₂
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [local irreducible] HasDerivedCategory.standard

private def freeSheaf (T : Scheme.{u}) : DiagonalAb T ⥤ DiagonalAb T :=
  sheafToPresheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1} ⋙
    (Functor.whiskeringRight _ AddCommGrpCat.{u + 1} AddCommGrpCat.{u + 1}).obj
      (forget AddCommGrpCat ⋙ AddCommGrpCat.free) ⋙
        presheafToSheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}

private def freeSheafπ (T : Scheme.{u}) (X : DiagonalAb T) :
    (freeSheaf T).obj X ⟶ X :=
  (presheafToSheaf (Scheme.ProEt.topology T) AddCommGrpCat).map
    (Functor.whiskerLeft X.obj AddCommGrpCat.adj.counit) ≫
      (sheafificationAdjunction (Scheme.ProEt.topology T) AddCommGrpCat).counit.app X

private theorem freeSheafπ_naturality (T : Scheme.{u}) {X Y : DiagonalAb T} (f : X ⟶ Y) :
    (freeSheaf T).map f ≫ freeSheafπ T Y = freeSheafπ T X ≫ f := by
  dsimp only [freeSheaf, freeSheafπ, Functor.comp_map, Functor.whiskeringRight,
    sheafToPresheaf, ObjectProperty.ι]
  rw [← Category.assoc, ← Functor.map_comp]
  have h : Functor.whiskerRight f.hom (forget AddCommGrpCat ⋙ AddCommGrpCat.free) ≫
      Functor.whiskerLeft Y.obj AddCommGrpCat.adj.counit =
    Functor.whiskerLeft X.obj AddCommGrpCat.adj.counit ≫ f.hom := by
    apply NatTrans.ext
    funext U
    exact AddCommGrpCat.adj.counit.naturality (f.hom.app U)
  change (presheafToSheaf (Scheme.ProEt.topology T) AddCommGrpCat).map
    (Functor.whiskerRight f.hom _ ≫ _) ≫ _ = _
  have hcn : (presheafToSheaf (Scheme.ProEt.topology T) AddCommGrpCat).map f.hom ≫
      (sheafificationAdjunction (Scheme.ProEt.topology T) AddCommGrpCat).counit.app Y =
    (sheafificationAdjunction (Scheme.ProEt.topology T) AddCommGrpCat).counit.app X ≫ f :=
      (sheafificationAdjunction (Scheme.ProEt.topology T) AddCommGrpCat).counit.naturality f
  rw [h, Functor.map_comp, Category.assoc, hcn]
  exact (Category.assoc _ _ _).symm

private theorem freeSheafπ_epi (T : Scheme.{u}) (X : DiagonalAb T) :
    Epi (freeSheafπ T X) := by
  have h (A : AddCommGrpCat.{u + 1}) : Epi (AddCommGrpCat.adj.counit.app A) := by
    apply (AddCommGrpCat.epi_iff_surjective _).2
    intro a
    refine ⟨AddCommGrpCat.adj.unit.app ((forget AddCommGrpCat).obj A) a, ?_⟩
    exact ConcreteCategory.congr_hom (AddCommGrpCat.adj.right_triangle_components A) a
  have : Epi (Functor.whiskerLeft X.obj AddCommGrpCat.adj.counit) := by
    exact (NatTrans.epi_iff_epi_app _).2 (fun U ↦ h (X.obj.obj U))
  dsimp only [freeSheafπ]
  exact epi_comp'
    ((presheafToSheaf (Scheme.ProEt.topology T) AddCommGrpCat).map_epi
      (Functor.whiskerLeft X.obj AddCommGrpCat.adj.counit))
    (inferInstanceAs (Epi
      ((sheafificationAdjunction (Scheme.ProEt.topology T) AddCommGrpCat).counit.app X)))

private theorem freeSheaf_mono (T : Scheme.{u}) (X : DiagonalAb T) (m : ℕ) (hm : m ≠ 0) :
    Mono (m • 𝟙 ((freeSheaf T).obj X)) := by
  let A := X.obj ⋙ forget AddCommGrpCat ⋙ AddCommGrpCat.free
  have : Mono (m • 𝟙 A) := by
    apply (NatTrans.mono_iff_mono_app _).2
    intro U
    apply (AddCommGrpCat.mono_iff_injective _).2
    change Function.Injective (fun a : FreeAbelianGroup (X.obj.obj U) ↦ m • a)
    intro a b hab
    apply (FreeAbelianGroup.equivFinsupp _).injective
    exact nsmul_right_injective hm
      (by simpa only [map_nsmul] using
        congrArg (FreeAbelianGroup.equivFinsupp (X.obj.obj U)) hab)
  let F := presheafToSheaf (Scheme.ProEt.topology T) AddCommGrpCat.{u + 1}
  have hmono := F.map_mono (m • 𝟙 A)
  have hmap : F.map (m • 𝟙 A) = m • 𝟙 (F.obj A) :=
    (F.map_nsmul).trans (congrArg (fun f ↦ m • f) (F.map_id A))
  rw [hmap] at hmono
  exact hmono

private def freeTower (T : Scheme.{u}) : Ab T ⥤ Ab T :=
  (Functor.whiskeringRight ℕᵒᵖ (DiagonalAb T) (DiagonalAb T)).obj (freeSheaf T)

private def freeTowerπ (T : Scheme.{u}) (X : Ab T) : (freeTower T).obj X ⟶ X where
  app n := freeSheafπ T (X.obj n)
  naturality _ _ f := freeSheafπ_naturality T (X.map f)

private theorem freeTowerπ_naturality (T : Scheme.{u}) {X Y : Ab T} (f : X ⟶ Y) :
    (freeTower T).map f ≫ freeTowerπ T Y = freeTowerπ T X ≫ f := by
  apply NatTrans.ext
  funext n
  exact freeSheafπ_naturality T (f.app n)

private theorem freeTowerπ_epi (T : Scheme.{u}) (X : Ab T) : Epi (freeTowerπ T X) := by
  exact (NatTrans.epi_iff_epi_app _).2 (fun n ↦ freeSheafπ_epi T (X.obj n))

private theorem freeTower_mono (T : Scheme.{u}) (X : Ab T) (m : ℕ) (hm : m ≠ 0) :
    Mono (m • 𝟙 ((freeTower T).obj X)) := by
  exact (NatTrans.mono_iff_mono_app _).2 (fun n ↦ freeSheaf_mono T (X.obj n) m hm)

private def coverD (T : Scheme.{u}) (K : CochainComplex (Ab T) ℤ) (i : ℤ) :
    (freeTower T).obj (K.X i) ⊞ (freeTower T).obj (K.X (i - 1)) ⟶
      (freeTower T).obj (K.X (i + 1)) ⊞ (freeTower T).obj (K.X (i + 1 - 1)) :=
  biprod.fst ≫ (freeTower T).map (eqToHom (by congr 1; omega)) ≫ biprod.inr

private theorem coverD_sq (T : Scheme.{u}) (K : CochainComplex (Ab T) ℤ) (i : ℤ) :
    coverD T K i ≫ coverD T K (i + 1) = 0 := by
  simp [coverD, Category.assoc]

private def cover (T : Scheme.{u}) (K : CochainComplex (Ab T) ℤ) :
    CochainComplex (Ab T) ℤ :=
  CochainComplex.of
    (fun i ↦ (freeTower T).obj (K.X i) ⊞ (freeTower T).obj (K.X (i - 1)))
    (coverD T K) (coverD_sq T K)

private def coverπF (T : Scheme.{u}) (K : CochainComplex (Ab T) ℤ) (i : ℤ) :
    (cover T K).X i ⟶ K.X i :=
  biprod.desc (freeTowerπ T (K.X i)) (freeTowerπ T (K.X (i - 1)) ≫ K.d (i - 1) i)

private theorem coverπF_comm (T : Scheme.{u}) (K : CochainComplex (Ab T) ℤ) (i : ℤ) :
    coverπF T K i ≫ K.d i (i + 1) =
      (cover T K).d i (i + 1) ≫ coverπF T K (i + 1) := by
  dsimp only [cover, coverπF]
  rw [CochainComplex.of_d]
  apply biprod.hom_ext'
  · simp only [Category.assoc, biprod.inl_desc_assoc, coverD, biprod.inl_fst_assoc,
      biprod.inr_desc]
    rw [← Category.assoc, freeTowerπ_naturality, Category.assoc]
    rw [K.eqToHom_comp_d (i := i) (i' := i + 1 - 1) (j := i + 1)
      (by rfl) (by change i + 1 - 1 + 1 = i + 1; omega)]
  · simp [coverD, Category.assoc]

private def coverπ (T : Scheme.{u}) (K : CochainComplex (Ab T) ℤ) : cover T K ⟶ K :=
  CochainComplex.ofHom (coverπF T K) (coverπF_comm T K)

private theorem coverπ_epi (T : Scheme.{u}) (K : CochainComplex (Ab T) ℤ) :
    Epi (coverπ T K) := by
  apply HomologicalComplex.epi_of_epi_f
  intro i
  have : Epi (freeTowerπ T (K.X i)) := freeTowerπ_epi T _
  apply epi_of_epi_fac (show biprod.inl ≫ (coverπ T K).f i = freeTowerπ T (K.X i) by
    simp [coverπ, coverπF])

private theorem nsmul_mono_of_mono {C : Type*} [Category C] [Preadditive C]
    {X Y : C} (f : X ⟶ Y) [Mono f] (m : ℕ) [Mono (m • 𝟙 Y)] :
    Mono (m • 𝟙 X) := by
  apply mono_of_mono_fac (show (m • 𝟙 X) ≫ f = f ≫ (m • 𝟙 Y) by
    simp only [Preadditive.nsmul_comp, Preadditive.comp_nsmul,
      Category.comp_id, Category.id_comp])

private theorem nsmul_mono_biprod {C : Type*} [Category C] [Preadditive C]
    (X Y : C) [HasBinaryBiproduct X Y] (m : ℕ)
    [Mono (m • 𝟙 X)] [Mono (m • 𝟙 Y)] : Mono (m • 𝟙 (X ⊞ Y)) := by
  have h : m • 𝟙 (X ⊞ Y) = biprod.map (m • 𝟙 X) (m • 𝟙 Y) := by
    apply biprod.hom_ext' <;> apply biprod.hom_ext <;> simp
  rw [h]
  infer_instance

private theorem cover_mono (T : Scheme.{u}) (K : CochainComplex (Ab T) ℤ)
    (i : ℤ) (m : ℕ) (hm : m ≠ 0) : Mono (m • 𝟙 ((cover T K).X i)) := by
  have := freeTower_mono T (K.X i) m hm
  have := freeTower_mono T (K.X (i - 1)) m hm
  exact nsmul_mono_biprod _ _ m

private theorem torsionFree_resolution (T : Scheme.{u}) (K : CochainComplex (Ab T) ℤ) :
    ∃ (P : CochainComplex (Ab T) ℤ) (q : P ⟶ K),
      QuasiIso q ∧ ∀ (i : ℤ) (m : ℕ), m ≠ 0 → Mono (m • 𝟙 (P.X i)) := by
  let q := coverπ T K
  have : Epi q := coverπ_epi T K
  let S := ShortComplex.mk (kernel.ι q) q (kernel.condition q)
  have hS : S.ShortExact := { exact := ShortComplex.exact_kernel q }
  refine ⟨CochainComplex.mappingCone S.f, CochainComplex.mappingCone.descShortComplex S,
    CochainComplex.mappingCone.quasiIso_descShortComplex hS, ?_⟩
  intro i m hm
  have := cover_mono T K i m hm
  have := cover_mono T K (i + 1) m hm
  have := nsmul_mono_of_mono ((kernel.ι q).f (i + 1)) m
  let e := HomologicalComplex.homotopyCofiber.XIsoBiprod S.f i (i + 1) rfl
  have := nsmul_mono_biprod ((kernel q).X (i + 1)) ((cover T K).X i) m
  exact nsmul_mono_of_mono e.hom m

private theorem initial_of_full_essSurj
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B) [F.Full] [F.EssSurj] :
    F.Initial := by
  classical
  constructor
  intro Y
  let e := F.objObjPreimageIso Y
  let Z : CostructuredArrow F Y := CostructuredArrow.mk e.hom
  have lift (X : CostructuredArrow F Y) : Nonempty (X ⟶ Z) := by
    refine ⟨CostructuredArrow.homMk (F.preimage (X.hom ≫ e.inv)) ?_⟩
    simp [Z, e]
  let : Nonempty (CostructuredArrow F Y) := ⟨Z⟩
  apply zigzag_isConnected
  intro X X'
  exact (Zigzag.of_hom (lift X).some).trans (Zigzag.of_inv (lift X').some)

private def pointwise_precomp_full
    {A C D H : Type*} [Category A] [Category C] [Category D] [Category H]
    (P : A ⥤ C) [P.Full] [P.EssSurj] (Q : C ⥤ D) (F : C ⥤ H) (L : D ⥤ H)
    (α : Q ⋙ L ⟶ F)
    (h : (Functor.RightExtension.mk L α).IsPointwiseRightKanExtension) :
    (Functor.RightExtension.mk L
      ((Functor.associator P Q L).hom ≫ Functor.whiskerLeft P α)).IsPointwiseRightKanExtension := by
  intro Y
  let p := StructuredArrow.pre Y P Q
  let : p.Initial := initial_of_full_essSurj p
  apply IsLimit.ofIsoLimit ((Functor.Initial.isLimitWhiskerEquiv p _).symm (h Y))
  refine Cone.ext (Iso.refl _) ?_
  intro X
  dsimp [Functor.RightExtension.coneAt, Functor.RightExtension.mk, p]
  simp only [Category.id_comp]

private def pointwise_change_iso
    {C D H : Type*} [Category C] [Category D] [Category H]
    {Q Q' : C ⥤ D} {F F' : C ⥤ H} (L : D ⥤ H)
    (i : Q ≅ Q') (j : F ≅ F') (α : Q ⋙ L ⟶ F)
    (h : (Functor.RightExtension.mk L α).IsPointwiseRightKanExtension) :
    (Functor.RightExtension.mk L
      (Functor.whiskerRight i.inv L ≫ α ≫ j.hom)).IsPointwiseRightKanExtension := by
  intro Y
  let Φ : StructuredArrow Y Q' ≌ StructuredArrow Y Q := Comma.mapRightIso _ i.symm
  let k : Φ.functor ⋙ StructuredArrow.proj Y Q ⋙ F ≅
      StructuredArrow.proj Y Q' ⋙ F' :=
    NatIso.ofComponents (fun X ↦ j.app X.right) (by
      intro X X' f
      exact j.hom.naturality f.right)
  apply IsLimit.ofIsoLimit
    ((IsLimit.postcomposeHomEquiv k _).symm ((h Y).whiskerEquivalence Φ))
  refine Cone.ext (Iso.refl _) ?_
  intro X
  dsimp [Functor.RightExtension.coneAt, Functor.RightExtension.mk, Φ, k]
  simp only [Functor.map_comp, Category.id_comp]
  change ((L.map X.hom ≫ L.map (i.inv.app X.right)) ≫ α.app X.right) ≫
      j.hom.app X.right = _
  exact (Category.assoc _ _ _).trans (Category.assoc _ _ _)

private theorem counit_computes_of_resolving
    {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasDerivedCategory.{w₁} C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasDerivedCategory.{w₂} D]
    {E : C ⥤ D} {G : D ⥤ C} [E.Additive] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (r : DerivedExtension E G) (S : Set (CochainComplex C ℤ))
    (hres : ∀ K : CochainComplex C ℤ,
      ∃ (P : CochainComplex C ℤ) (q : P ⟶ K), S P ∧ QuasiIso q)
    (hinv : ∀ {P Q : CochainComplex C ℤ} (q : P ⟶ Q),
      S P → S Q → QuasiIso q → QuasiIso ((E.mapHomologicalComplex (.up ℤ)).map q))
    (P : CochainComplex C ℤ) (hP : S P) : IsIso (r.epsilon.app P) := by
  let H := E.mapHomotopyCategory (.up ℤ) ⋙ DerivedCategory.Qh (C := D)
  let Sc : Set (HomotopyCategory C (.up ℤ)) := fun X ↦
    ∃ K : CochainComplex C ℤ, S K ∧ (HomotopyCategory.quotient C (.up ℤ)).obj K = X
  have hresc (X : HomotopyCategory C (.up ℤ)) :
      ∃ (X' : HomotopyCategory C (.up ℤ)) (s : X' ⟶ X),
        X' ∈ Sc ∧ HomotopyCategory.quasiIso C (.up ℤ) s := by
    obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
    obtain ⟨L, q, hL, hq⟩ := hres K
    exact ⟨_, (HomotopyCategory.quotient C (.up ℤ)).map q, ⟨L, hL, rfl⟩,
      (HomotopyCategory.quotient_map_mem_quasiIso_iff q).2 hq⟩
  have hinvc (X X' : HomotopyCategory C (.up ℤ)) (s : X ⟶ X')
      (hX : X ∈ Sc) (hX' : X' ∈ Sc) (hs : HomotopyCategory.quasiIso C (.up ℤ) s) :
      IsIso (H.map s) := by
    obtain ⟨K, hK, rfl⟩ := hX
    obtain ⟨L, hL, rfl⟩ := hX'
    obtain ⟨q, rfl⟩ := (HomotopyCategory.quotient C (.up ℤ)).map_surjective s
    have hq := (HomotopyCategory.quotient_map_mem_quasiIso_iff q).1 hs
    have hEq := hinv q hK hL hq
    change IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient D (.up ℤ)).map
        ((E.mapHomologicalComplex (.up ℤ)).map q)))
    exact Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso D (.up ℤ)) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 hEq)
  obtain ⟨hpw, L, ε, hu, _, hc⟩ :=
    Functor.leftDerived_from_resolvingClass C (DerivedCategory D) H Sc hresc hinvc
  let : H.HasPointwiseLeftDerivedFunctor (HomotopyCategory.quasiIso C (.up ℤ)) := hpw
  let : L.IsLeftDerivedFunctor ε (HomotopyCategory.quasiIso C (.up ℤ)) := hu
  let q := HomotopyCategory.quotient C (.up ℤ)
  let α := (Functor.associator q DerivedCategory.Qh L).hom ≫ Functor.whiskerLeft q ε
  have hα := pointwise_precomp_full q DerivedCategory.Qh H L ε
    (Functor.isPointwiseRightKanExtensionOfHasPointwiseLeftDerivedFunctor L ε
      (HomotopyCategory.quasiIso C (.up ℤ)))
  let i := DerivedCategory.quotientCompQhIso C
  let j : q ⋙ H ≅ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (E.mapHomotopyCategoryFactors (.up ℤ)) _ ≪≫
      Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (DerivedCategory.quotientCompQhIso D)
  let β : DerivedCategory.Q ⋙ L ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q :=
    Functor.whiskerRight i.inv L ≫ α ≫ j.hom
  have hβ := pointwise_change_iso L i j α hα
  let : L.IsLeftDerivedFunctor β (HomologicalComplex.quasiIso C (.up ℤ)) :=
    ⟨hβ.isRightKanExtension⟩
  let : r.derived.IsLeftDerivedFunctor r.epsilon
      (HomologicalComplex.quasiIso C (.up ℤ)) := r.universal
  have : IsIso (β.app P) := by
    have := hc (q.obj P) ⟨P, hP, rfl⟩
    dsimp [β, α]
    infer_instance
  let γ := r.derived.leftDerivedLift r.epsilon
    (HomologicalComplex.quasiIso C (.up ℤ)) L β
  have : IsIso γ :=
    (Functor.isLeftDerivedFunctor_iff_isIso_leftDerivedLift r.derived r.epsilon
      (HomologicalComplex.quasiIso C (.up ℤ)) L β).1 inferInstance
  have he : γ.app (DerivedCategory.Q.obj P) ≫ r.epsilon.app P = β.app P :=
    Functor.leftDerived_fac_app r.derived r.epsilon
      (HomologicalComplex.quasiIso C (.up ℤ)) L β P
  exact IsIso.of_isIso_fac_left he

private def unitShortComplex
    {A : Type*} [Category A] [HasZeroMorphisms A] {V W : A ⥤ A}
    (μ : V ⟶ 𝟭 A) (η : 𝟭 A ⟶ W) (hz : ∀ P, μ.app P ≫ η.app P = 0) (P : A) :
    ShortComplex A :=
  ShortComplex.mk (μ.app P) (η.app P) (hz P)

private theorem quasiIso_map_of_shortExact
    {C : Type u₁} [Category.{v₁} C] [Abelian C]
    {D : Type u₂} [Category.{v₂} D] [Abelian D]
    (E : C ⥤ D) (G : D ⥤ C) [E.Additive] [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] [G.Faithful]
    (V : CochainComplex C ℤ ⥤ CochainComplex C ℤ) (μ : V ⟶ 𝟭 _)
    (η : 𝟭 _ ⟶ E.mapHomologicalComplex (.up ℤ) ⋙ G.mapHomologicalComplex (.up ℤ))
    (hz : ∀ P, μ.app P ≫ η.app P = 0)
    {P Q : CochainComplex C ℤ} (f : P ⟶ Q)
    (hP : (unitShortComplex μ η hz P).ShortExact)
    (hQ : (unitShortComplex μ η hz Q).ShortExact)
    (hV : QuasiIso (V.map f)) (hf : QuasiIso f) :
    QuasiIso ((E.mapHomologicalComplex (.up ℤ)).map f) := by
  let φ : unitShortComplex μ η hz P ⟶ unitShortComplex μ η hz Q :=
    { τ₁ := V.map f
      τ₂ := f
      τ₃ := (G.mapHomologicalComplex (.up ℤ)).map
        ((E.mapHomologicalComplex (.up ℤ)).map f)
      comm₁₂ := μ.naturality f
      comm₂₃ := η.naturality f }
  have hφ₃ := HomologicalComplex.HomologySequence.quasiIso_τ₃ φ hP hQ hV hf
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology
    ((E.mapHomologicalComplex (.up ℤ)).map f) G).1 hφ₃

private theorem forget_faithful (T : Scheme.{u})
    (B : ℕᵒᵖ ⥤ Sheaf (Scheme.ProEt.topology T) CommRingCat.{u + 1})
    (F : Forget T B) : F.F.Faithful := by
  constructor
  intro M N f g h
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  obtain ⟨⟨n, V⟩⟩ := U
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hfg := congrArg (fun z ↦ (((z.app (op n)).hom.app (op V)).hom)) h
  have hh := (F.morphisms f n (op V)).symm.trans
    (hfg.heq.trans (F.morphisms g n (op V)))
  exact congrArg (fun z ↦ z x) (eq_of_heq hh)

private theorem powerComplex_zero (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    (r : Reduction T (Rrings l T)) (P : CochainComplex (Ab T) ℤ) :
    (NatTrans.mapHomologicalComplex (PowerTransition.multiplication l) (.up ℤ)).app P ≫
      (r.model.adjunction.mapHomologicalComplex (.up ℤ)).unit.app P = 0 := by
  apply HomologicalComplex.Hom.ext
  funext i
  exact (powerSystem_ordinary_cokernel l T r (P.X i)).choose

private def powerShortComplex (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    (r : Reduction T (Rrings l T)) (P : CochainComplex (Ab T) ℤ) :
    ShortComplex (CochainComplex (Ab T) ℤ) :=
  unitShortComplex
    (NatTrans.mapHomologicalComplex (PowerTransition.multiplication l) (.up ℤ))
    (r.model.adjunction.mapHomologicalComplex (.up ℤ)).unit (powerComplex_zero l T r) P

private theorem powerShortComplex_exact (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    (r : Reduction T (Rrings l T)) (P : CochainComplex (Ab T) ℤ)
    (hP : ∀ (i : ℤ) (n : ℕ), Mono (l ^ (n + 1) • 𝟙 ((P.X i).obj (op n)))) :
    (powerShortComplex l T r P).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  change (ShortComplex.mk ((PowerTransition.multiplication l).app (P.X i))
    (r.model.adjunction.unit.app (P.X i)) _).ShortExact
  obtain ⟨hz, ⟨hc⟩⟩ := powerSystem_ordinary_cokernel l T r (P.X i)
  have : Mono ((PowerTransition.multiplication l).app (P.X i)) :=
    (NatTrans.mono_iff_mono_app _).2 (fun n ↦ hP i n.unop)
  have : Epi (r.model.adjunction.unit.app (P.X i)) := Cofork.IsColimit.epi hc
  exact { exact := ShortComplex.exact_of_g_is_cokernel _ hc }

private theorem reduction_preserves_regular_quasiIso (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    (r : Reduction T (Rrings l T)) {P Q : CochainComplex (Ab T) ℤ} (f : P ⟶ Q)
    (hP : ∀ (i : ℤ) (n : ℕ), Mono (l ^ (n + 1) • 𝟙 ((P.X i).obj (op n))))
    (hQ : ∀ (i : ℤ) (n : ℕ), Mono (l ^ (n + 1) • 𝟙 ((Q.X i).obj (op n))))
    (hf : QuasiIso f) :
    QuasiIso ((r.ordinary.mapHomologicalComplex (.up ℤ)).map f) := by
  have : r.forget.F.Faithful := forget_faithful T (Rrings l T) r.forget
  have : QuasiIso f := hf
  exact quasiIso_map_of_shortExact r.ordinary r.forget.F
    ((PowerTransition.functor (C := DiagonalAb T) l).mapHomologicalComplex (.up ℤ))
    (NatTrans.mapHomologicalComplex (PowerTransition.multiplication l) (.up ℤ))
    (r.model.adjunction.mapHomologicalComplex (.up ℤ)).unit (powerComplex_zero l T r) f
    (powerShortComplex_exact l T r P hP) (powerShortComplex_exact l T r Q hQ)
    (PowerTransition.quasiIso_map l f) hf

/-- Every abelian tower complex has a reduction-acyclic resolution with torsion-free terms.

Source: Stacks 06YS, 06YY, 06XN, 05SE; blueprint latest,
`sk-prop-sp-tower-geometric-classes.proof.md`, clause (2), K-flat computation.
(blueprint: lem-sfb-power-system-acyclic-resolution).

Proof: sheafify the free abelian presheaf on the sections of a sheaf, and apply this
construction at every level of a tower. Its evaluation map is epic and its nonzero
integer multiples are monic, since sheafification is exact. Cover a complex K by the
complex with terms F(K^i) ⊕ F(K^(i-1)), differential (x,y) ↦ (0,x), and augmentation
(x,y) ↦ ε(x) + d ε(y). The cone of the inclusion of its augmentation kernel maps
quasi-isomorphically to K. Its terms are sums of subobjects of free sheaves, so all
nonzero integer multiples are monic. In particular the positive prime powers are
monic after evaluation. On complexes with this regularity, the ordinary adjunction
unit is the cokernel of the variable-power map. The associated short exact sequence
and its homology sequence show that ordinary reduction preserves quasi-isomorphisms
between regular complexes, since twisting transitions preserves quasi-isomorphisms
and the exact faithful forgetful functor detects them. Apply the resolving-class
construction on the homotopy category and transport its universal pair to complexes.
Uniqueness of universal derived functors identifies its invertible counit components
with those of the supplied reduction r. -/
theorem powerSystem_acyclic_resolution (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    (r : Reduction T (Rrings l T)) (K : CochainComplex (Ab T) ℤ) :
    ∃ (P : CochainComplex (Ab T) ℤ) (q : P ⟶ K),
      QuasiIso q ∧ (∀ (i : ℤ) (n : ℕ),
        Mono (l ^ (n + 1) • 𝟙 ((P.X i).obj (op n)))) ∧
      IsIso (r.model.epsilon.app P) := by
  let S : Set (CochainComplex (Ab T) ℤ) := fun P ↦
    ∀ (i : ℤ) (n : ℕ), Mono (l ^ (n + 1) • 𝟙 ((P.X i).obj (op n)))
  have hres (K : CochainComplex (Ab T) ℤ) :
      ∃ (P : CochainComplex (Ab T) ℤ) (q : P ⟶ K), S P ∧ QuasiIso q := by
    obtain ⟨P, q, hq, hP⟩ := torsionFree_resolution T K
    refine ⟨P, q, ?_, hq⟩
    intro i n
    let ev := (evaluation ℕᵒᵖ (DiagonalAb T)).obj (op n)
    have := hP i (l ^ (n + 1)) (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)
    have hmono := ev.map_mono (l ^ (n + 1) • 𝟙 (P.X i))
    have hmap : ev.map (l ^ (n + 1) • 𝟙 (P.X i)) =
        l ^ (n + 1) • 𝟙 (ev.obj (P.X i)) :=
      (ev.map_nsmul).trans (congrArg (fun f ↦ l ^ (n + 1) • f) (ev.map_id (P.X i)))
    rw [hmap] at hmono
    exact hmono
  obtain ⟨P, q, hP, hq⟩ := hres K
  refine ⟨P, q, hq, hP, ?_⟩
  exact counit_computes_of_resolving r.model S hres
    (fun f hP hQ hf ↦ reduction_preserves_regular_quasiIso l T r f hP hQ hf) P hP

end AlgebraicGeometry.ProEtale.SpTowerClasses
