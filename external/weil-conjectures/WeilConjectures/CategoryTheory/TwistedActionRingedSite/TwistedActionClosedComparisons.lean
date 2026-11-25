/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TwistedActionRingedSiteDataSupplement
import WeilConjectures.CategoryTheory.TwistedActionRingedSite.TwistedActionHomEvaluationComparisons

/-! # Tensor and internal Hom on the twisted action site

Source: steps 9--13 of the agent-formulated twisted variant of Stacks Tag 00W0.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

namespace CategoryTheory.TwistedActionRingedSite

private theorem tensorMap_comp
    {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}
    {S : Sheaf K CommRingCat.{u}} {M M' M'' N N' N'' : Modules S}
    (f : M ⟶ M') (g : N ⟶ N') (f' : M' ⟶ M'') (g' : N' ⟶ N'') :
    tensorMap f g ≫ tensorMap f' g' = tensorMap (f ≫ f') (g ≫ g') :=
  tensorHom_comp_tensorHom f g f' g'

private theorem tensorMap_second_comp
    {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}
    {S : Sheaf K CommRingCat.{u}} {M M' N N' N'' : Modules S}
    (f : M ⟶ M') (g : N ⟶ N') (g' : N' ⟶ N'') :
    tensorMap f (g ≫ g') = tensorMap f g ≫ tensorMap (𝟙 M') g' := by
  rw [tensorMap_comp (S := S), Category.comp_id]

private theorem tensorMap_exchange
    {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}
    {S : Sheaf K CommRingCat.{u}} {M M' N N' : Modules S}
    (f : M ⟶ M') (g : N ⟶ N') :
    tensorMap f (𝟙 N) ≫ tensorMap (𝟙 M') g = tensorMap f g := by
  rw [tensorMap_comp (S := S), Category.comp_id, Category.id_comp]

private theorem tensorMap_exchange_assoc
    {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}
    {S : Sheaf K CommRingCat.{u}} {M M' N N' Q : Modules S}
    (f : M ⟶ M') (g : N ⟶ N') (k : tensorObj M' N' ⟶ Q) :
    tensorMap f (𝟙 N) ≫ tensorMap (𝟙 M') g ≫ k = tensorMap f g ≫ k := by
  rw [← Category.assoc, tensorMap_exchange (S := S)]

private theorem tensorMap_id_comp
    {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}
    {S : Sheaf K CommRingCat.{u}} {M N N' N'' : Modules S}
    (f : N ⟶ N') (g : N' ⟶ N'') :
    tensorMap (𝟙 M) f ≫ tensorMap (𝟙 M) g = tensorMap (𝟙 M) (f ≫ g) := by
  rw [tensorMap_comp (S := S), Category.id_comp]

private theorem tensorMap_id_comp_assoc
    {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}
    {S : Sheaf K CommRingCat.{u}} {M N N' N'' Q : Modules S}
    (f : N ⟶ N') (g : N' ⟶ N'') (k : tensorObj M N'' ⟶ Q) :
    tensorMap (𝟙 M) f ≫ tensorMap (𝟙 M) g ≫ k = tensorMap (𝟙 M) (f ≫ g) ≫ k := by
  rw [← Category.assoc, tensorMap_id_comp (S := S)]

private theorem transpose_evaluation
    {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}
    {S : Sheaf K CommRingCat.{u}} (M N : Modules S) :
    SheafOfModules.tensorHomEquiv (R := S) M _ N (evaluationMap M N) = 𝟙 _ :=
  (SheafOfModules.tensorHomEquiv (R := S) M _ N).apply_symm_apply _

private theorem evaluation_naturality
    {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}
    {S : Sheaf K CommRingCat.{u}} {M M' N N' : Modules S}
    (f : M' ⟶ M) (g : N ⟶ N') :
    tensorMap (𝟙 M') (SheafOfModules.homObjMap (R := S) f g) ≫ evaluationMap M' N' =
      tensorMap f (𝟙 _) ≫ evaluationMap M N ≫ g := by
  apply (SheafOfModules.tensorHomEquiv (R := S) M' _ N').injective
  have h₁ := SheafOfModules.tensorHomEquiv_whiskerLeft_comp (R := S) M'
    (SheafOfModules.homObjMap (R := S) f g) (evaluationMap M' N')
  have h₂ := SheafOfModules.tensorHomEquiv_whiskerRight_comp (R := S) f
    (evaluationMap M N ≫ g)
  have h₃ := SheafOfModules.tensorHomEquiv_comp_homObjMap (R := S) M
    (evaluationMap M N) g
  rw [transpose_evaluation, Category.comp_id] at h₁
  rw [transpose_evaluation, Category.id_comp] at h₃
  have h₄ := h₂.trans (congrArg
    (fun z ↦ z ≫ SheafOfModules.homObjMap (R := S) f (𝟙 N')) h₃)
  rw [SheafOfModules.homObjMap_comp_homObjMap (R := S)] at h₄
  simp only [Category.comp_id] at h₄
  simpa only [tensorMap, id_tensorHom, tensorHom_id] using h₁.trans h₄.symm

private theorem evaluation_injective
    {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}
    {S : Sheaf K CommRingCat.{u}} (M N T : Modules S)
    (f g : T ⟶ SheafOfModules.homObj (R := S) M N)
    (h : tensorMap (𝟙 M) f ≫ evaluationMap M N =
      tensorMap (𝟙 M) g ≫ evaluationMap M N) : f = g := by
  have hh := congrArg (SheafOfModules.tensorHomEquiv (R := S) M T N) h
  simpa only [tensorMap, id_tensorHom,
    SheafOfModules.tensorHomEquiv_whiskerLeft_comp, transpose_evaluation,
    Category.comp_id] using hh

private theorem evaluation_precomp
    {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}
    {S : Sheaf K CommRingCat.{u}} {M M' N N' T : Modules S}
    (f : M' ⟶ M) (g : N ⟶ N') (k : T ⟶ SheafOfModules.homObj (R := S) M N) :
    tensorMap f k ≫ evaluationMap M N ≫ g =
      tensorMap (𝟙 M') (k ≫ SheafOfModules.homObjMap (R := S) f g) ≫
        evaluationMap M' N' := by
  calc
    _ = tensorMap (𝟙 M') k ≫
        (tensorMap f (𝟙 _) ≫ evaluationMap M N ≫ g) := by
      simp only [tensorMap, ← Category.assoc, tensorHom_comp_tensorHom,
        Category.id_comp, Category.comp_id]
    _ = _ := by
      rw [← evaluation_naturality]
      simp only [tensorMap, ← Category.assoc, tensorHom_comp_tensorHom, Category.comp_id]

private theorem evaluation_conjugate
    {D : Type u} [SmallCategory D] {K : GrothendieckTopology D}
    {S : Sheaf K CommRingCat.{u}} {M M' N N' T : Modules S}
    (e : M' ≅ M) (g : N ⟶ N') (k : T ⟶ SheafOfModules.homObj (R := S) M' N) :
    tensorMap e.hom (k ≫ SheafOfModules.homObjMap (R := S) e.inv g) ≫
        evaluationMap M N' = tensorMap (𝟙 M') k ≫ evaluationMap M' N ≫ g := by
  calc
    _ = tensorMap e.hom k ≫
        (tensorMap (𝟙 M) (SheafOfModules.homObjMap (R := S) e.inv g) ≫
          evaluationMap M N') := by
      simp only [tensorMap, ← Category.assoc, tensorHom_comp_tensorHom, Category.comp_id]
    _ = _ := by
      rw [evaluation_naturality]
      simp only [tensorMap, ← Category.assoc, tensorHom_comp_tensorHom,
        Iso.hom_inv_id, Category.comp_id]

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
    (s : C ≌ C) [s.functor.IsContinuous J J] [s.inverse.IsContinuous J J]
    (R : Sheaf J CommRingCat.{u})
    (a : (s.inverse.sheafPushforwardContinuous CommRingCat.{u} J J).obj R ≅ R)

omit [s.functor.IsContinuous J J] in
private theorem hom_naturality_of_evaluation (P : RestrictionPresentation J s R a)
    (T : TensorComparisons J s R a P) (H : HomEvaluationComparisons J s R a P T) :
    let := P.category
    ∀ {M M' N N' : Modules P.coefficient} (f : M' ⟶ M) (g : N ⟶ N'),
      (P.modules.functor.map (SheafOfModules.homObjMap (R := P.coefficient) f g)).hom.f ≫
          (H.hom M' N').hom =
        (H.hom M N).hom ≫ SheafOfModules.homObjMap (R := R)
          (P.modules.functor.map f).hom.f (P.modules.functor.map g).hom.f := by
  dsimp only
  let := P.category
  intro M M' N N' f g
  let U : Modules P.coefficient ⥤ Modules R :=
    { P.modules.functor ⋙ forgetPairs (sigma J s R a) with
      obj M := (P.modules.functor.obj M).obj.a
      map f := (P.modules.functor.map f).hom.f }
  let h : ∀ M N : Modules P.coefficient,
      U.obj (SheafOfModules.homObj (R := P.coefficient) M N) ≅
        SheafOfModules.homObj (R := R) (U.obj M) (U.obj N) := H.hom
  have he (M N : Modules P.coefficient) : U.map (evaluationMap M N) =
      (T.tensor M (SheafOfModules.homObj (R := P.coefficient) M N)).hom ≫
        tensorMap (𝟙 (U.obj M)) (h M N).hom ≫ evaluationMap (U.obj M) (U.obj N) :=
    H.evaluation M N
  let k := SheafOfModules.homObjMap (R := P.coefficient) f g
  change U.map k ≫ (h M' N').hom =
    (h M N).hom ≫ SheafOfModules.homObjMap (R := R) (U.map f) (U.map g)
  apply evaluation_injective (U.obj M') (U.obj N') (U.obj _)
  apply (cancel_epi (T.tensor M' (SheafOfModules.homObj (R := P.coefficient) M N)).hom).mp
  have ht₁ := T.tensor_naturality (𝟙 M') k
  have ht₂ := T.tensor_naturality f
    (𝟙 (SheafOfModules.homObj (R := P.coefficient) M N))
  change U.map (tensorMap (𝟙 M') k) ≫ (T.tensor M' _).hom =
    (T.tensor M' _).hom ≫ tensorMap (U.map (𝟙 M')) (U.map k) at ht₁
  change U.map (tensorMap f (𝟙 _)) ≫ (T.tensor M _).hom =
    (T.tensor M' _).hom ≫ tensorMap (U.map f) (U.map (𝟙 _)) at ht₂
  simp only [Functor.map_id] at ht₁ ht₂
  calc
    _ = U.map (tensorMap (𝟙 M') k) ≫ U.map (evaluationMap M' N') := by
      simp only [tensorMap_second_comp (S := R), Category.assoc]
      rw [← Category.assoc, ← ht₁, Category.assoc, ← he M' N']
    _ = U.map (tensorMap f (𝟙 _) ≫ evaluationMap M N ≫ g) := by
      rw [← U.map_comp, evaluation_naturality (S := P.coefficient)]
    _ = (T.tensor M' _).hom ≫ tensorMap (U.map f) (h M N).hom ≫
        evaluationMap (U.obj M) (U.obj N) ≫ U.map g := by
      rw [U.map_comp (tensorMap f (𝟙 _)) (evaluationMap M N ≫ g),
        U.map_comp (evaluationMap M N) g, he M N]
      simp only [Category.assoc]
      rw [← Category.assoc, ht₂]
      simpa only [Category.assoc] using congrArg
        (fun z ↦ (T.tensor M' (SheafOfModules.homObj (R := P.coefficient) M N)).hom ≫
          z ≫ evaluationMap (U.obj M) (U.obj N) ≫ U.map g)
        (tensorMap_exchange (S := R) (U.map f) (h M N).hom)
    _ = _ := by rw [evaluation_precomp (S := R)]

omit [s.functor.IsContinuous J J] in
private theorem hom_action_of_evaluation (P : RestrictionPresentation J s R a)
    (T : TensorComparisons J s R a P) (H : HomEvaluationComparisons J s R a P T) :
    let := P.category
    ∀ M N : Modules P.coefficient,
      (P.modules.functor.obj (SheafOfModules.homObj (R := P.coefficient) M N)).obj.str ≫
          (H.hom M N).hom =
        (sigma J s R a).map (H.hom M N).hom ≫
          (H.sigmaHom (P.modules.functor.obj M).obj.a
            (P.modules.functor.obj N).obj.a).hom ≫
          SheafOfModules.homObjMap (R := R) (pairIso (P.modules.functor.obj M)).inv
            (P.modules.functor.obj N).obj.str := by
  dsimp only
  let := P.category
  intro M N
  let U : Modules P.coefficient ⥤ Modules R :=
    { P.modules.functor ⋙ forgetPairs (sigma J s R a) with
      obj M := (P.modules.functor.obj M).obj.a
      map f := (P.modules.functor.map f).hom.f }
  have he (M N : Modules P.coefficient) : U.map (evaluationMap M N) =
      (T.tensor M (SheafOfModules.homObj (R := P.coefficient) M N)).hom ≫
        tensorMap (𝟙 _) (H.hom M N).hom ≫ evaluationMap (U.obj M) (U.obj N) :=
    H.evaluation M N
  let L := SheafOfModules.homObj (R := P.coefficient) M N
  let m : (sigma J s R a).obj (U.obj M) ≅ U.obj M := pairIso (P.modules.functor.obj M)
  let n : (sigma J s R a).obj (U.obj N) ≅ U.obj N := pairIso (P.modules.functor.obj N)
  let l : (sigma J s R a).obj (U.obj L) ≅ U.obj L := pairIso (P.modules.functor.obj L)
  change l.hom ≫ (H.hom M N).hom =
    (sigma J s R a).map (H.hom M N).hom ≫ (H.sigmaHom (U.obj M) (U.obj N)).hom ≫
      SheafOfModules.homObjMap (R := R) m.inv n.hom
  apply evaluation_injective (U.obj M) (U.obj N) ((sigma J s R a).obj (U.obj L))
  apply (cancel_epi (tensorMap m.hom (𝟙 ((sigma J s R a).obj (U.obj L))))).mp
  apply (cancel_epi ((sigma J s R a).map (T.tensor M L).hom ≫
    (T.sigmaTensor (U.obj M) (U.obj L)).hom)).mp
  have ht := T.tensor_action M L
  change (pairIso (P.modules.functor.obj (tensorObj M L))).hom ≫ (T.tensor M L).hom =
    (sigma J s R a).map (T.tensor M L).hom ≫
      (T.sigmaTensor (U.obj M) (U.obj L)).hom ≫ tensorMap m.hom l.hom at ht
  have hn := (P.modules.functor.map (evaluationMap M N)).hom.h
  change (sigma J s R a).map (U.map (evaluationMap M N)) ≫ n.hom =
    (pairIso (P.modules.functor.obj (tensorObj M L))).hom ≫
      U.map (evaluationMap M N) at hn
  have hs := T.sigmaTensor_naturality (𝟙 (U.obj M)) (H.hom M N).hom
  simp only [Functor.map_id] at hs
  have hse := H.sigmaHom_evaluation (U.obj M) (U.obj N)
  calc
    _ = (pairIso (P.modules.functor.obj (tensorObj M L))).hom ≫
        U.map (evaluationMap M N) := by
      calc
        _ = (sigma J s R a).map (T.tensor M L).hom ≫
            (T.sigmaTensor (U.obj M) (U.obj L)).hom ≫ tensorMap m.hom l.hom ≫
              tensorMap (𝟙 _) (H.hom M N).hom ≫ evaluationMap (U.obj M) (U.obj N) := by
          rw [tensorMap_second_comp (S := R) (𝟙 (U.obj M)) l.hom (H.hom M N).hom]
          simp only [Category.assoc, tensorMap_exchange_assoc (S := R)]
        _ = (pairIso (P.modules.functor.obj (tensorObj M L))).hom ≫
            (T.tensor M L).hom ≫ tensorMap (𝟙 _) (H.hom M N).hom ≫
              evaluationMap (U.obj M) (U.obj N) := by
          simpa only [Category.assoc] using congrArg
            (fun z ↦ z ≫ tensorMap (𝟙 _) (H.hom M N).hom ≫
              evaluationMap (U.obj M) (U.obj N)) ht.symm
        _ = _ := by rw [← he M N]
    _ = (sigma J s R a).map (U.map (evaluationMap M N)) ≫ n.hom := hn.symm
    _ = (sigma J s R a).map (T.tensor M L).hom ≫
        (T.sigmaTensor (U.obj M) (U.obj L)).hom ≫
        tensorMap (𝟙 _) ((sigma J s R a).map (H.hom M N).hom ≫
          (H.sigmaHom (U.obj M) (U.obj N)).hom) ≫
        evaluationMap ((sigma J s R a).obj (U.obj M))
          ((sigma J s R a).obj (U.obj N)) ≫ n.hom := by
      rw [he M N,
        (sigma J s R a).map_comp (T.tensor M L).hom
          (tensorMap (𝟙 _) (H.hom M N).hom ≫ evaluationMap (U.obj M) (U.obj N)),
        (sigma J s R a).map_comp (tensorMap (𝟙 _) (H.hom M N).hom)
          (evaluationMap (U.obj M) (U.obj N)), hse]
      simpa only [Category.assoc, tensorMap_id_comp_assoc (S := R)] using
        congrArg (fun z ↦ (sigma J s R a).map (T.tensor M L).hom ≫ z ≫
          tensorMap (𝟙 _) (H.sigmaHom (U.obj M) (U.obj N)).hom ≫
          evaluationMap ((sigma J s R a).obj (U.obj M))
            ((sigma J s R a).obj (U.obj N)) ≫ n.hom) hs
    _ = _ := by
      simpa only [Category.assoc, tensorMap_exchange_assoc (S := R)] using
        congrArg (fun z ↦ (sigma J s R a).map (T.tensor M L).hom ≫
          (T.sigmaTensor (U.obj M) (U.obj L)).hom ≫ z)
          (evaluation_conjugate (S := R) m n.hom
            ((sigma J s R a).map (H.hom M N).hom ≫
              (H.sigmaHom (U.obj M) (U.obj N)).hom)).symm

/-- Restriction of tensor and internal Hom along a displayed action-site presentation.
Source: steps 9--13 of the twisted action-site argument, Stacks 03EK and 04TT
(blueprint: lem-sf-twisted-action-closed-comparisons).

Proof: sheafification commutes with translation, since the site equivalence identifies
maps into translated sheaves before and after sheafification. Its universal property
therefore extends the presheaf action uniquely to the sheafification. Apply this to the
sectionwise tensor presheaf: restriction gives the ordinary tensor presheaf on C, whose
action sends each pure tensor to the tensor of its translated factors. The resulting
comparison preserves the displayed pure tensors and identifies the diagonal action.
For the tensor unit this is precisely coefficient restriction and the chosen ring action.
For internal Hom use the equivalence of localized action sites with the base slices:
a slice arrow of degree n is normalized by its inverse n-th power. The slice relation
forces every map's degree, so this normalization is fully faithful and essentially
surjective, and preserves coverings in both directions. Restriction of module sheaves
on the slices is consequently an equivalence. Sections of internal Hom on each slice
are thus all local linear maps, with no extra equivariance condition. Their restriction
maps commute with normalization, giving a sheaf isomorphism. Translating a local map
conjugates it by the target and source actions, giving the stated contragredient formula.
The translation comparison is uniquely determined by preservation of evaluation.
Naturality follows by composition of local maps. Symmetry interchanges the pure factors,
and evaluation sends a local map and an argument to its value, so both agree under the
comparisons. Equality before sheafification gives equality afterward by uniqueness.
The induction data are retained exactly; neither induction nor its exactness is used
in any comparison. Zero modules and the zero coefficient ring satisfy the same formulas.
-/
theorem closedComparisons [HasPullbacks C] (P : OrbitPresentation J s R a) :
    Nonempty {Q : Presentation J s R a // Q.toOrbitPresentation = P} := by
  let := P.category
  obtain ⟨T⟩ := tensorComparisons J s R a P.toRestrictionPresentation
  obtain ⟨H⟩ := homEvaluationComparisons J s R a P.toRestrictionPresentation T
  exact ⟨⟨{
    toOrbitPresentation := P
    tensor := T.tensor
    sigmaTensor := T.sigmaTensor
    tensor_pure := T.tensor_pure
    sigmaTensor_pure := T.sigmaTensor_pure
    tensor_action := T.tensor_action
    unit := T.unit
    unit_sections := T.unit_sections
    sigmaUnit := T.sigmaUnit
    sigmaUnit_sections := T.sigmaUnit_sections
    unit_action := T.unit_action
    tensor_naturality := T.tensor_naturality
    symmetry := T.symmetry
    hom := H.hom
    sigmaHom := H.sigmaHom
    sigmaHom_evaluation := H.sigmaHom_evaluation
    evaluation := H.evaluation
    hom_action := hom_action_of_evaluation J s R a P.toRestrictionPresentation T H
    hom_naturality := hom_naturality_of_evaluation J s R a P.toRestrictionPresentation T H
    }, rfl⟩⟩

end CategoryTheory.TwistedActionRingedSite
