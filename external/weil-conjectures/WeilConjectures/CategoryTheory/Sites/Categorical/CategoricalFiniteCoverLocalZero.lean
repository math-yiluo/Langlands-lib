/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Sites.CechComplexFunctor
public import WeilConjectures.CategoryTheory.Sites.CechComplex
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify

/-! # Locally zero generalized sections of a presheaf with zero sheafification

Source: Stacks Project, Tags 00W1 and 00WB, expressed using exact filtered
colimits of local restriction kernels rather than underlying elements.
-/

@[expose] public section

universe u' u w v

open CategoryTheory Limits Opposite

namespace CategoryTheory.Presheaf

variable {C : Type (u + 1)} [Category.{u} C]
  {A : Type u'} [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A]
  (J : GrothendieckTopology C) [HasSheafify J A]
  [∀ V : C, HasFiniteProducts (Over V)]

omit [HasSheafify J A] [∀ V : C, HasFiniteProducts (Over V)] in
private theorem kills_kernel_colimit
    {I : Type w} [Category.{v} I] [IsConnected I]
    [HasColimitsOfShape I A] [HasExactColimitsOfShape I A]
    {X : A} (D : I ⥤ A) (α : (Functor.const I).obj X ⟶ D)
    (c : Cocone D) (hc : IsColimit c) (a : X ⟶ c.pt)
    (ha : ∀ i, a = α.app i ≫ c.ι.app i) {T : A} (b : X ⟶ T)
    (h : ∀ i {E : A} (x : E ⟶ X), x ≫ α.app i = 0 → x ≫ b = 0)
    {E : A} (x : E ⟶ X) (hx : x ≫ a = 0) : x ≫ b = 0 := by
  let K := ShortComplex.kernelSequence α
  let k : colimit K.X₁ ⟶ X :=
    colimit.desc K.X₁ { pt := X, ι := kernel.ι α }
  have hk (i : I) : colimit.ι K.X₁ i ≫ k = K.f.app i :=
    colimit.ι_desc _ i
  have he := colim.exact_mapShortComplex (ShortComplex.kernelSequence_exact α)
    (colimit.isColimit K.X₁) (isColimitConstCocone I X) hc k a
    (fun i ↦ by
      change colimit.ι K.X₁ i ≫ k = K.f.app i ≫ 𝟙 _
      simpa only [Category.comp_id] using hk i)
    (fun i ↦ by
      change 𝟙 _ ≫ a = α.app i ≫ c.ι.app i
      simpa only [Category.id_comp] using ha i)
  have hkb : k ≫ b = 0 := by
    apply colimit.hom_ext
    intro i
    rw [← Category.assoc, hk, comp_zero]
    apply h i (K.f.app i)
    exact NatTrans.congr_app K.zero i
  exact he.comp_eq_zero hx hkb

omit [HasSheafify J A] [∀ V : C, HasFiniteProducts (Over V)] in
private theorem kills_kernel_toPlus
    (P : Cᵒᵖ ⥤ A) (V : C) {T : A} (b : P.obj (op V) ⟶ T)
    (h : ∀ (S : J.Cover V) {E : A} (x : E ⟶ P.obj (op V)),
      x ≫ S.toMultiequalizer P = 0 → x ≫ b = 0)
    {E : A} (x : E ⟶ P.obj (op V))
    (hx : x ≫ (J.toPlus P).app (op V) = 0) : x ≫ b = 0 := by
  let D := J.diagram P V
  let α : (Functor.const (J.Cover V)ᵒᵖ).obj (P.obj (op V)) ⟶ D :=
    { app S := S.unop.toMultiequalizer P
      naturality S R f := by
        apply Multiequalizer.hom_ext
        intro i
        simp [D, GrothendieckTopology.Cover.Arrow.map] }
  exact kills_kernel_colimit D α _ (colimit.isColimit D) ((J.toPlus P).app (op V))
    (fun S ↦ (J.toMultiequalizer_ι_diagram P S.unop).symm) b
    (fun S ↦ h S.unop) x hx

private theorem finite_basis_cover
    (B : C → Prop)
    (hcov : ∀ V, B V → ∀ R ∈ J V, ∃ (n : ℕ) (U : Fin n → Over V),
      (∀ (k : ℕ) (y : Fin (k + 1) → Fin n), B (cechNerveObj U y).left) ∧
      (∀ a, R (U a).hom) ∧
      Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈ J V)
    (V : C) (hV : B V) (S : J.Cover V) :
    ∃ (n : ℕ) (U : Fin n → Over V), (∀ i, B (U i).left) ∧
      (∀ i, S.1 (U i).hom) ∧
      Sieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (U i).hom) ∈ J V := by
  obtain ⟨n, U, hUB, hUS, hU⟩ := hcov V hV S.1 S.2
  let W (i : Fin n) := cechNerveObj U (fun _ : Fin 1 ↦ i)
  refine ⟨n, W, fun i ↦ hUB 0 _, ?_, ?_⟩
  · intro i
    have hr := S.1.downward_closed (hUS i) (Pi.π (fun _ : Fin 1 ↦ U i) 0).left
    rwa [Over.w] at hr
  · apply J.superset_covering (S := Sieve.ofArrows _ _) _ hU
    intro Z f hf
    obtain ⟨i, g, rfl⟩ := Sieve.ofArrows.exists hf
    let d : U i ⟶ W i := Pi.lift fun _ ↦ 𝟙 _
    apply (Sieve.mem_ofArrows_iff _ _ _).2
    refine ⟨i, g ≫ d.left, ?_⟩
    rw [Category.assoc, Over.w d]

omit [HasSheafify J A] [∀ V : C, HasFiniteProducts (Over V)] in
private theorem isZero_matching_of_generators
    (P : Cᵒᵖ ⥤ A) {V : C} {n : ℕ} (U : Fin n → Over V)
    (hU : Sieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (U i).hom) ∈ J V)
    (hP : ∀ i, IsZero (P.obj (op (U i).left))) :
    IsZero (multiequalizer (GrothendieckTopology.Cover.index
      (⟨Sieve.ofArrows (fun i ↦ (U i).left)
        (fun i ↦ (U i).hom), hU⟩ : J.Cover V) P)) := by
  let S : J.Cover V := ⟨Sieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (U i).hom), hU⟩
  apply (IsZero.iff_id_eq_zero _).2
  apply Multiequalizer.hom_ext
  intro I
  obtain ⟨i, g, hg⟩ := Sieve.ofArrows.exists I.hf
  let a : S.Arrow := ⟨(U i).left, (U i).hom, Sieve.ofArrows_mk _ _ i⟩
  have he := Multiequalizer.condition (S.index P)
    { fst := I, snd := a, r.Z := I.Y, r.g₁ := 𝟙 I.Y, r.g₂ := g, r.w := by simpa [a] using hg }
  change Multiequalizer.ι (S.index P) I ≫ P.map (𝟙 I.Y).op =
    Multiequalizer.ι (S.index P) a ≫ P.map g.op at he
  change 𝟙 (multiequalizer (S.index P)) ≫ Multiequalizer.ι (S.index P) I =
    0 ≫ Multiequalizer.ι (S.index P) I
  simp only [Category.id_comp, zero_comp]
  change Multiequalizer.ι (S.index P) I ≫ P.map (𝟙 (op I.Y)) =
    Multiequalizer.ι (S.index P) a ≫ P.map g.op at he
  rw [P.map_id] at he
  change Multiequalizer.ι (S.index P) I ≫ 𝟙 ((S.index P).left I) =
    Multiequalizer.ι (S.index P) a ≫ P.map g.op at he
  simpa only [Category.comp_id,
    (hP i).eq_zero_of_tgt (Multiequalizer.ι (S.index P) a), zero_comp] using he

omit [HasSheafify J A] [∀ V : C, HasFiniteProducts (Over V)] in
private theorem plus_isZero_on_basis
    (B : C → Prop)
    (hcov : ∀ V, B V → ∀ S : J.Cover V, ∃ (n : ℕ) (U : Fin n → Over V),
      (∀ i, B (U i).left) ∧ (∀ i, S.1 (U i).hom) ∧
      Sieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (U i).hom) ∈ J V)
    (P : Cᵒᵖ ⥤ A) (hP : ∀ V, B V → IsZero (P.obj (op V)))
    (V : C) (hV : B V) : IsZero ((J.plusObj P).obj (op V)) := by
  apply (IsZero.iff_id_eq_zero _).2
  apply colimit.hom_ext
  intro S
  obtain ⟨n, U, hUB, hUS, hU⟩ := hcov V hV S.unop
  let R : J.Cover V := ⟨Sieve.ofArrows (fun i ↦ (U i).left)
    (fun i ↦ (U i).hom), hU⟩
  have hRS : R ≤ S.unop := by
    intro Z f hf
    obtain ⟨i, g, rfl⟩ := Sieve.ofArrows.exists hf
    exact S.unop.1.downward_closed (hUS i) g
  have hR := isZero_matching_of_generators J P U hU (fun i ↦ hP _ (hUB i))
  have he : colimit.ι (J.diagram P V) S = 0 := by
    rw [← colimit.w (J.diagram P V) (homOfLE hRS).op]
    have hz : colimit.ι (J.diagram P V) (op R) = 0 := hR.eq_zero_of_src _
    rw [hz, comp_zero]
  change colimit.ι (J.diagram P V) S ≫ 𝟙 (colimit (J.diagram P V)) =
    colimit.ι (J.diagram P V) S ≫ 0
  simpa only [Category.comp_id, comp_zero] using he

omit [HasSheafify J A] [∀ V : C, HasFiniteProducts (Over V)] in
private theorem matching_ι_of_factor
    (P : Cᵒᵖ ⥤ A) {V : C} (S : J.Cover V) (I K : S.Arrow)
    (g : K.Y ⟶ I.Y) (hg : K.f = g ≫ I.f) :
    Multiequalizer.ι (S.index P) K = Multiequalizer.ι (S.index P) I ≫ P.map g.op := by
  have he := Multiequalizer.condition (S.index P)
    { fst := K, snd := I, r.Z := K.Y, r.g₁ := 𝟙 K.Y, r.g₂ := g,
      r.w := by simpa using hg }
  change Multiequalizer.ι (S.index P) K ≫ P.map (𝟙 (op K.Y)) =
    Multiequalizer.ι (S.index P) I ≫ P.map g.op at he
  rw [P.map_id] at he
  change Multiequalizer.ι (S.index P) K ≫ 𝟙 ((S.index P).left K) =
    Multiequalizer.ι (S.index P) I ≫ P.map g.op at he
  simpa only [Category.comp_id] using he

omit [HasSheafify J A] [∀ V : C, HasFiniteProducts (Over V)] in
private theorem plus_isZero_of_toPlus_zero
    (P : Cᵒᵖ ⥤ A) (hη : J.toPlus P = 0) (V : C)
    (hfin : ∀ S : J.Cover V, ∃ (n : ℕ) (U : Fin n → Over V),
      (∀ i, S.1 (U i).hom) ∧
      Sieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (U i).hom) ∈ J V) :
    IsZero ((J.plusObj P).obj (op V)) := by
  classical
  apply (IsZero.iff_id_eq_zero _).2
  apply colimit.hom_ext
  intro S
  change colimit.ι (J.diagram P V) S ≫ 𝟙 (colimit (J.diagram P V)) =
    colimit.ι (J.diagram P V) S ≫ 0
  simp only [Category.comp_id, comp_zero]
  obtain ⟨n, U, hUS, hU⟩ := hfin S.unop
  let I := ∀ i : Fin n, (J.Cover (U i).left)ᵒᵖ
  have : IsFiltered I := inferInstanceAs
    (IsFiltered (∀ i : Fin n, (J.Cover (U i).left)ᵒᵖ))
  have : IsConnected I := IsFiltered.isConnected I
  let F : I ⥤ Discrete (Fin n) ⥤ A :=
    Functor.pi (fun i ↦ J.diagram P (U i).left) ⋙
      (piEquivalenceFunctorDiscrete (Fin n) A).functor
  let D := limit F.flip
  let e := colimitLimitIso F.flip
  let cD : Cocone D :=
    { pt := limit (colimit F)
      ι := (colimit.cocone D).ι ≫ (Functor.const I).map e.hom }
  have hcD : IsColimit cD :=
    (colimit.isColimit D).ofIsoColimit (Cocone.ext e (fun t ↦ by simp [cD]))
  let p (i : Fin n) : multiequalizer (S.unop.index P) ⟶ P.obj (op (U i).left) :=
    Multiequalizer.ι (S.unop.index P) ⟨(U i).left, (U i).hom, hUS i⟩
  let q (i : Fin n) :
      (Functor.const I).obj (multiequalizer (S.unop.index P)) ⟶ F.flip.obj ⟨i⟩ :=
    { app t := p i ≫ (t i).unop.toMultiequalizer P
      naturality t s f := by
        change 𝟙 _ ≫ (p i ≫ (s i).unop.toMultiequalizer P) =
          (p i ≫ (t i).unop.toMultiequalizer P) ≫ (J.diagram P (U i).left).map (f i)
        rw [Category.id_comp, Category.assoc]
        congr 1
        apply Multiequalizer.hom_ext
        intro a
        simp [GrothendieckTopology.Cover.Arrow.map] }
  let α : (Functor.const I).obj (multiequalizer (S.unop.index P)) ⟶ D :=
    limit.lift F.flip { pt := _, π := Discrete.natTrans fun i ↦ q i.as }
  have hα (t : I) (i : Fin n) :
      α.app t ≫ (limit.π F.flip ⟨i⟩).app t = p i ≫ (t i).unop.toMultiequalizer P :=
    NatTrans.congr_app (limit.lift_π
      { pt := _, π := Discrete.natTrans fun i ↦ q i.as } ⟨i⟩) t
  have ha (t : I) : (0 : multiequalizer (S.unop.index P) ⟶ cD.pt) =
      α.app t ≫ cD.ι.app t := by
    apply limit.hom_ext
    intro i
    let ei : (colimit F).obj i ≅ (J.plusObj P).obj (op (U i.as).left) :=
      colimitObjIsoColimitCompEvaluation F i ≪≫
        Functor.Final.colimitIso
          (CategoryTheory.Pi.eval (fun i ↦ (J.Cover (U i).left)ᵒᵖ) i.as)
          (J.diagram P (U i.as).left)
    apply (cancel_mono ei.hom).1
    change (0 ≫ limit.π (colimit F) i) ≫ ei.hom =
      ((α.app t ≫ (colimit.ι D t ≫ e.hom)) ≫ limit.π (colimit F) i) ≫ ei.hom
    simp only [zero_comp, Category.assoc]
    change 0 = α.app t ≫ (colimit.ι (limit F.flip) t ≫
      (colimitLimitIso F.flip).hom ≫ limit.π (colimit F.flip.flip) i ≫ ei.hom)
    rw [ι_colimitLimitIso_limit_π_assoc F.flip t i, ← Category.assoc, hα]
    change 0 = (p i.as ≫ (t i.as).unop.toMultiequalizer P) ≫
      (colimit.ι F t).app i ≫ ei.hom
    simp only [ei, Iso.trans_hom, Category.assoc,
      colimitObjIsoColimitCompEvaluation_ι_app_hom_assoc]
    change 0 = p i.as ≫ (t i.as).unop.toMultiequalizer P ≫
      colimit.ι (CategoryTheory.Pi.eval (fun i ↦ (J.Cover (U i).left)ᵒᵖ) i.as ⋙
        J.diagram P (U i.as).left) t ≫
      (Functor.Final.colimitIso
        (CategoryTheory.Pi.eval (fun i ↦ (J.Cover (U i).left)ᵒᵖ) i.as)
        (J.diagram P (U i.as).left)).hom
    rw [Functor.Final.ι_colimitIso_hom]
    change 0 = p i.as ≫ (t i.as).unop.toMultiequalizer P ≫
      colimit.ι (J.diagram P (U i.as).left) (op (t i.as).unop)
    rw [J.toMultiequalizer_ι_diagram]
    have hz := NatTrans.congr_app hη (op (U i.as).left)
    change (J.toPlus P).app (op (U i.as).left) = 0 at hz
    rw [hz, comp_zero]
  have hb : ∀ t {E : A} (x : E ⟶ multiequalizer (S.unop.index P)),
      x ≫ α.app t = 0 → x ≫ colimit.ι (J.diagram P V) S = 0 := by
    intro t E x hx
    let R : J.Cover V := ⟨Sieve.generate (Presieve.bindOfArrows
      (fun i ↦ (U i).left) (fun i ↦ (U i).hom) (fun i ↦ (t i).unop.1.arrows)),
      J.bindOfArrows hU (fun i ↦ by simp)⟩
    have hRS : R ≤ S.unop := by
      apply (Sieve.generate_le_iff _ _).2
      intro Z f hf
      cases hf with
      | mk i g hg => exact S.unop.1.downward_closed (hUS i) g
    have hm : x ≫ (J.diagram P V).map (homOfLE hRS).op = 0 := by
      apply Multiequalizer.hom_ext
      intro a
      obtain ⟨Z, g, f, hf, hgf⟩ := a.hf
      cases hf with
      | mk i f hf =>
        have hz := congrArg (fun z ↦ z ≫ (limit.π F.flip ⟨i⟩).app t) hx
        rw [Category.assoc, hα, zero_comp] at hz
        have hz' := congrArg (fun z ↦ z ≫
          Multiequalizer.ι ((t i).unop.index P) ⟨Z, f, hf⟩) hz
        simp only [Category.assoc, GrothendieckTopology.Cover.toMultiequalizer_ι,
          zero_comp] at hz'
        have he := matching_ι_of_factor J P S.unop
          ⟨(U i).left, (U i).hom, hUS i⟩
          ⟨a.Y, a.f, hRS _ a.hf⟩ (g ≫ f) (by simpa only [Category.assoc] using hgf.symm)
        simp only [Category.assoc, GrothendieckTopology.diagram_map,
          Multiequalizer.lift_ι, zero_comp]
        change x ≫ Multiequalizer.ι (S.unop.index P)
          ⟨a.Y, a.f, hRS _ a.hf⟩ = 0
        rw [he]
        change x ≫ p i ≫ P.map (g ≫ f).op = 0
        rw [op_comp, P.map_comp]
        simpa only [Category.assoc, zero_comp] using
          congrArg (fun z ↦ z ≫ P.map g.op) hz'
    rw [← colimit.w (J.diagram P V) (homOfLE hRS).op, ← Category.assoc, hm, zero_comp]
  have he := kills_kernel_colimit D α cD hcD 0 ha
    (colimit.ι (J.diagram P V) S) hb (𝟙 _) (by simp)
  simpa only [Category.id_comp] using he

omit [HasSheafify J A] [∀ V : C, HasFiniteProducts (Over V)] in
private theorem mono_toPlus_plus_of_finite_basis
    (P : Cᵒᵖ ⥤ A) (V : C)
    (hfin : ∀ S : J.Cover V, ∃ (n : ℕ) (U : Fin n → Over V),
      (∀ i, S.1 (U i).hom) ∧
      Sieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (U i).hom) ∈ J V) :
    Mono ((J.toPlus (J.plusObj P)).app (op V)) := by
  let K := kernel (J.toPlus P)
  have : Mono (J.plusMap (kernel.ι (J.toPlus P))) :=
    inferInstanceAs (Mono ((J.plusFunctor A).map (kernel.ι (J.toPlus P))))
  have hη : J.toPlus K = 0 := by
    apply (cancel_mono (J.plusMap (kernel.ι (J.toPlus P)))).1
    rw [zero_comp, ← J.toPlus_naturality, kernel.condition]
  have hK := plus_isZero_of_toPlus_zero J K hη V hfin
  let F := J.plusFunctor A ⋙ (evaluation _ _).obj (op V)
  have : PreservesFiniteLimits F := inferInstanceAs
    (PreservesFiniteLimits (J.plusFunctor A ⋙ (evaluation _ _).obj (op V)))
  have hk := isLimitOfHasKernelOfPreservesLimit F (J.toPlus P)
  have hm : Mono (F.map (J.toPlus P)) := Preadditive.mono_of_isZero_kernel' _ hk hK
  change Mono ((J.plusMap (J.toPlus P)).app (op V)) at hm
  rwa [J.plusMap_toPlus] at hm

omit [HasSheafify J A] [∀ V : C, HasFiniteProducts (Over V)] in
private theorem plus_map_mono_on_basis
    (B : C → Prop)
    (hcov : ∀ V, B V → ∀ S : J.Cover V, ∃ (n : ℕ) (U : Fin n → Over V),
      (∀ i, B (U i).left) ∧ (∀ i, S.1 (U i).hom) ∧
      Sieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (U i).hom) ∈ J V)
    {P Q : Cᵒᵖ ⥤ A} (f : P ⟶ Q)
    (hf : ∀ V, B V → Mono (f.app (op V))) (V : C) (hV : B V) :
    Mono ((J.plusMap f).app (op V)) := by
  have hK : ∀ W, B W → IsZero ((kernel f).obj (op W)) := by
    intro W hW
    have := hf W hW
    let F := (evaluation Cᵒᵖ A).obj (op W)
    exact (isZero_kernel_of_mono (f.app (op W))).of_iso (PreservesKernel.iso F f)
  have hz := plus_isZero_on_basis J B hcov (kernel f) hK V hV
  let F := J.plusFunctor A ⋙ (evaluation _ _).obj (op V)
  have : PreservesFiniteLimits F := inferInstanceAs
    (PreservesFiniteLimits (J.plusFunctor A ⋙ (evaluation _ _).obj (op V)))
  exact Preadditive.mono_of_isZero_kernel' _ (isLimitOfHasKernelOfPreservesLimit F f) hz

omit [HasSheafify J A] [∀ V : C, HasFiniteProducts (Over V)] in
private noncomputable def plusUnderSucc (Q : Cᵒᵖ ⥤ A) : SmallObject.SuccStruct (Under Q) where
  X₀ := Under.mk (𝟙 Q)
  succ X := Under.mk (X.hom ≫ J.toPlus X.right)
  toSucc X := Under.homMk (J.toPlus X.right) rfl

private def monoOnBasisUnder (B : C → Prop) (Q : Cᵒᵖ ⥤ A) : ObjectProperty (Under Q) :=
  fun X ↦ ∀ V, B V → Mono (X.hom.app (op V))

omit [HasSheafify J A] [∀ V : C, HasFiniteProducts (Over V)] in
private theorem monoOnBasisUnder_iso (B : C → Prop) (Q : Cᵒᵖ ⥤ A) :
    (monoOnBasisUnder B Q).IsClosedUnderIsomorphisms where
  of_iso e h V hV := by
    have := h V hV
    have he := Under.w e.hom
    have heV := NatTrans.congr_app he (op V)
    rw [NatTrans.comp_app] at heV
    rw [← heV]
    infer_instance

omit [HasSheafify J A] [∀ V : C, HasFiniteProducts (Over V)] in
private theorem monoOnBasisUnder_colimits
    (B : C → Prop) (Q : Cᵒᵖ ⥤ A)
    (I : Type (u + 1)) [SmallCategory I] [IsFiltered I] :
    (monoOnBasisUnder B Q).IsClosedUnderColimitsOfShape I := by
  have : IsConnected I := IsFiltered.isConnected I
  have := monoOnBasisUnder_iso B Q
  apply ObjectProperty.IsClosedUnderColimitsOfShape.mk'
  rintro _ ⟨F, hF⟩ V hV
  let E := Under.forget Q ⋙ (evaluation _ _).obj (op V)
  let α : (Functor.const I).obj (Q.obj (op V)) ⟶ F ⋙ E :=
    { app i := (F.obj i).hom.app (op V)
      naturality i j f := by
        change 𝟙 _ ≫ (F.obj j).hom.app (op V) =
          (F.obj i).hom.app (op V) ≫ (F.map f).right.app (op V)
        simpa only [Category.id_comp, NatTrans.comp_app] using
          (NatTrans.congr_app (Under.w (F.map f)) (op V)).symm }
  have : ∀ i, Mono (α.app i) := fun i ↦ hF i V hV
  have : Mono α := NatTrans.mono_of_mono_app α
  exact colim.map_mono' α (isColimitConstCocone I _) (isColimitOfPreserves E
    (colimit.isColimit F)) ((colimit F).hom.app (op V)) (fun i ↦ by
      change 𝟙 _ ≫ (colimit F).hom.app (op V) =
        (F.obj i).hom.app (op V) ≫ (colimit.ι F i).right.app (op V)
      simpa only [Category.id_comp, NatTrans.comp_app] using
        (NatTrans.congr_app (Under.w (colimit.ι F i)) (op V)).symm)

omit [HasSheafify J A] [∀ V : C, HasFiniteProducts (Over V)] in
private theorem isSheaf_plusUnderIteration
    (Q : Cᵒᵖ ⥤ A) (κ : Cardinal.{u + 1}) [Fact κ.IsRegular]
    [OrderBot κ.ord.ToType]
    {G : A} (hG : IsDetector G) [IsCardinalPresentable G κ]
    (hC : HasCardinalLT (Arrow C) κ) :
    Presheaf.IsSheaf J ((plusUnderSucc J Q).iteration κ.ord.ToType).right := by
  have : NoMaxOrder κ.ord.ToType := Cardinal.noMaxOrder (Fact.out : κ.IsRegular).aleph0_le
  have : IsConnected κ.ord.ToType := IsFiltered.isConnected κ.ord.ToType
  let Φ := plusUnderSucc J Q
  let F := Φ.iterationFunctor κ.ord.ToType ⋙ Under.forget Q
  let hc := isColimitOfPreserves (Under.forget Q) (Φ.isColimitIterationCocone κ.ord.ToType)
  let e (i : κ.ord.ToType) : F.obj (Order.succ i) ≅ J.plusObj (F.obj i) :=
    (Under.forget Q).mapIso (Φ.iterationFunctorObjSuccIso i (not_isMax i))
  have hs (i : κ.ord.ToType) :
      F.map (homOfLE (Order.le_succ i)) = J.toPlus (F.obj i) ≫ (e i).inv := by
    change (Under.forget Q).map
      ((Φ.iterationFunctor κ.ord.ToType).map (homOfLE (Order.le_succ i))) = _
    rw [Φ.iterationFunctor_map_succ i (not_isMax i), Functor.map_comp]
    rfl
  rw [Presheaf.isSheaf_iff_multiequalizer]
  intro X S
  have := S.preservesColimitsOfShape_multiequalizerFunctor hG κ κ.ord.ToType hC
  refine IsColimit.isIso_of_interleave
    (isColimitOfPreserves ((evaluation _ _).obj (op X)) hc)
    (isColimitOfPreserves (S.multiequalizerFunctor A) hc)
    (Functor.whiskerLeft F (S.toMultiequalizerNatTrans A))
    (fun i ↦ colimit.ι (J.diagram (F.obj i) X) (op S) ≫ (e i).inv.app (op X))
    (fun i ↦ ?_) (fun i ↦ ?_) _ (fun i ↦ ?_)
  · simp only [Functor.comp_map, evaluation_obj_map, Functor.whiskerLeft_app,
      GrothendieckTopology.Cover.toMultiequalizerNatTrans_app,
      J.toMultiequalizer_ι_diagram_assoc]
    exact (NatTrans.congr_app (hs i) (op X)).symm
  · rw [Functor.comp_map, hs, Functor.map_comp,
      ← J.ι_diagram_toMultiequalizer_plusObj (F.obj i),
      Functor.whiskerLeft_app, GrothendieckTopology.Cover.toMultiequalizerNatTrans_app,
      Category.assoc, Category.assoc]
    exact congrArg (_ ≫ ·) (S.toMultiequalizer_naturality (e i).inv)
  · exact (S.toMultiequalizerNatTrans A).naturality _

omit [HasSheafify J A] [∀ V : C, HasFiniteProducts (Over V)] in
private theorem mono_plusUnderIteration
    (B : C → Prop)
    (hcov : ∀ V, B V → ∀ S : J.Cover V, ∃ (n : ℕ) (U : Fin n → Over V),
      (∀ i, B (U i).left) ∧ (∀ i, S.1 (U i).hom) ∧
      Sieve.ofArrows (fun i ↦ (U i).left) (fun i ↦ (U i).hom) ∈ J V)
    (Q : Cᵒᵖ ⥤ A) (hQ : ∀ V, B V → Mono ((J.toPlus Q).app (op V)))
    (κ : Cardinal.{u + 1}) [Fact κ.IsRegular] [OrderBot κ.ord.ToType] :
    ∀ V, B V → Mono (((plusUnderSucc J Q).iteration κ.ord.ToType).hom.app (op V)) := by
  have : IsConnected κ.ord.ToType := IsFiltered.isConnected κ.ord.ToType
  have := monoOnBasisUnder_iso B Q
  have := monoOnBasisUnder_colimits B Q κ.ord.ToType
  apply (plusUnderSucc J Q).prop_iteration κ.ord.ToType (monoOnBasisUnder B Q)
  · intro V hV
    change Mono (𝟙 (Q.obj (op V)))
    infer_instance
  · intro X hX V hV
    have := hQ V hV
    have := plus_map_mono_on_basis J B hcov X.hom hX V hV
    change Mono ((X.hom ≫ J.toPlus X.right).app (op V))
    rw [J.toPlus_naturality, NatTrans.comp_app]
    infer_instance
  · intro j hj
    have : Nonempty (Set.Iio j) := ⟨⟨⊥, hj.bot_lt⟩⟩
    exact monoOnBasisUnder_colimits B Q (Set.Iio j)

/-- A map from a presheaf with zero sheafification vanishes if it vanishes on
all generalized sections killed by restriction to a finite basis cover.
Source: Stacks Project, Section 7.10 (Tag 00W1), the filtered-colimit equality
description before Lemma 7.10.8 and Theorem 7.10.10 (Tag 00WB), extended using
AB5 to Grothendieck abelian coefficients.
(blueprint: stage3-categorical-finite-cover-local-zero).

Proof: AB5 computes the kernel of the plus unit as the filtered union of the
kernels of the matching-family restriction maps. Each covering sieve has a finite
refinement as in hcov. Its matching restriction kills every one-fold nerve restriction,
so the hypothesis on b shows that b kills the kernel of the plus unit.

We show that this kernel already equals the kernel of sheafification at B-objects.
First, if a presheaf K has zero plus unit, its plus object vanishes at every object
whose covering sieves have finite refinements. Given a matching family over S, choose
finite generators U of a covering subsieve. Take the filtered product of the cover
categories of the U. AB5 commutes that filtered colimit with the finite product of
matching objects. The induced map from the S-matching object to this colimit is zero,
since each component factors through the zero plus unit of K. Its kernel is the union
of the kernels at finite stages. For each stage, compose its chosen covers with U:
the corresponding kernel vanishes on this composite cover, hence vanishes in plus.
Consequently every colimit inclusion defining plus K is zero. This includes empty U.

Apply this to the kernel of P → P⁺. Naturality and preservation of monomorphisms by
plus show that the kernel's own plus unit is zero. Left exactness of plus then makes
P⁺ → P⁺⁺ monic at B-objects. Also, plus preserves maps monic at B-objects: their
kernels vanish on B, and so do their plus objects. For this last assertion refine
covers by the one-fold nerve family. Its members satisfy B literally, and its sieve
is still covering by the diagonals into singleton products. Thus no invariance of B
under isomorphisms is needed.

Starting with Q = P⁺, iterate plus in the category of objects under Q. The property
that Q → R is monic at all B-objects is preserved at successors by naturality and
the preceding preservation result, and at nonempty filtered colimits by AB5. Hence
Q → R remains monic through the iteration. Choose a regular cardinal larger than
the arrow cardinal of C at which a separator of A is presentable. The colimit of
the iteration is a sheaf: matching-family objects preserve colimits of this shape,
and the maps from matching families to the successor plus stage interleave the
sheaf-condition maps with the transition maps. Their colimit maps are isomorphisms.
This is the source library's convergence argument, applied to the iteration under Q;
it also works when C's hom universe is smaller than its object universe.

Finally P → Q → R factors through the zero sheafification of P, hence is zero.
Since Q(V) → R(V) is monic, the plus unit of P at V is zero. Its kernel is therefore
all of P(V), and the first paragraph gives b = 0. -/
theorem hom_eq_zero_of_sheafification_zero
    (B : C → Prop)
    (hcov : ∀ V, B V → ∀ R ∈ J V, ∃ (n : ℕ) (U : Fin n → Over V),
      (∀ (k : ℕ) (y : Fin (k + 1) → Fin n), B (Presheaf.cechNerveObj U y).left) ∧
      (∀ a, R (U a).hom) ∧
      Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈ J V)
    (P : Cᵒᵖ ⥤ A) (hP : IsZero ((presheafToSheaf J A).obj P))
    (V : C) (hV : B V) {T : A} (b : P.obj (op V) ⟶ T)
    (h : ∀ {n : ℕ} (U : Fin n → Over V),
      (∀ (k : ℕ) (y : Fin (k + 1) → Fin n), B (Presheaf.cechNerveObj U y).left) →
      Sieve.ofArrows (fun a ↦ (U a).left) (fun a ↦ (U a).hom) ∈ J V →
      ∀ {E : A} (x : E ⟶ P.obj (op V)),
        x ≫ cechAugmentation U Over.mkIdTerminal ((Over.forget V).op ⋙ P) = 0 →
        x ≫ b = 0) : b = 0 := by
  have hk : ∀ {E : A} (x : E ⟶ P.obj (op V)),
      x ≫ (J.toPlus P).app (op V) = 0 → x ≫ b = 0 := by
    apply kills_kernel_toPlus J P V b
    intro S E x hx
    obtain ⟨n, U, hUB, hUS, hU⟩ := hcov V hV S.1 S.2
    apply h U hUB hU x
    apply Pi.hom_ext
    intro y
    rw [Category.assoc, cechAugmentation_π, zero_comp]
    simp only [Functor.comp_map, Functor.op_map, Over.forget_map, Quiver.Hom.unop_op,
      Over.mkIdTerminal_from_left]
    change x ≫ P.map (cechNerveObj U y).hom.op = 0
    have hr : S.1 (cechNerveObj U y).hom := by
      have hr := S.1.downward_closed (hUS (y 0))
        (Pi.π (fun l : Fin 1 ↦ U (y l)) 0).left
      rw [Over.w] at hr
      exact hr
    have hz := congrArg (fun f ↦ f ≫ Multiequalizer.ι (S.index P)
      ⟨(cechNerveObj U y).left, (cechNerveObj U y).hom, hr⟩) hx
    simpa only [Category.assoc, GrothendieckTopology.Cover.toMultiequalizer_ι,
      zero_comp] using hz
  let G := separator A
  obtain ⟨κ₀, _, _⟩ :=
    Functor.IsAccessible.exists_cardinal (F := coyoneda.obj (Opposite.op G))
  let κ := Order.succ (max (max κ₀ (Cardinal.mk (Arrow C))) Cardinal.aleph0)
  have hκ : κ.IsRegular := Cardinal.isRegular_succ (le_max_right _ _)
  have : Fact κ.IsRegular := ⟨hκ⟩
  have hle : max (max κ₀ (Cardinal.mk (Arrow C))) Cardinal.aleph0 < κ :=
    Order.lt_succ_of_not_isMax (not_isMax _)
  have : IsCardinalPresentable G κ :=
    isCardinalPresentable_of_le G
      ((le_max_left _ _).trans (le_max_left _ _) |>.trans hle.le)
  have hC : HasCardinalLT (Arrow C) κ := (hasCardinalLT_iff_cardinal_mk_lt _ _).2
    (((le_max_right _ _).trans (le_max_left _ _)).trans_lt hle)
  have : Nonempty κ.ord.ToType := by simpa using hκ.ne_zero
  have := WellFoundedLT.toOrderBot κ.ord.ToType
  let Q := J.plusObj P
  let R := (plusUnderSucc J Q).iteration κ.ord.ToType
  have hR : Presheaf.IsSheaf J R.right :=
    isSheaf_plusUnderIteration J Q κ (isSeparator_separator A).isDetector hC
  have hcov' := finite_basis_cover J B hcov
  have hQ : ∀ W, B W → Mono ((J.toPlus Q).app (op W)) := by
    intro W hW
    apply mono_toPlus_plus_of_finite_basis J P W
    intro S
    obtain ⟨n, U, _, hUS, hU⟩ := hcov' W hW S
    exact ⟨n, U, hUS, hU⟩
  have := mono_plusUnderIteration J B hcov' Q hQ κ V hV
  have hf : J.toPlus P ≫ R.hom = 0 := by
    rw [← toSheafify_sheafifyLift J (J.toPlus P ≫ R.hom) hR]
    have hz : IsZero (sheafify J P) := (sheafToPresheaf J A).map_isZero hP
    rw [hz.eq_zero_of_src (sheafifyLift J (J.toPlus P ≫ R.hom) hR), comp_zero]
  have hη : (J.toPlus P).app (op V) = 0 := by
    apply (cancel_mono (R.hom.app (op V))).1
    simpa only [NatTrans.comp_app, zero_comp, zero_app] using NatTrans.congr_app hf (op V)
  simpa only [Category.id_comp] using hk (𝟙 _) (by rw [hη, comp_zero])

end CategoryTheory.Presheaf
