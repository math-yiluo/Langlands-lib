/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CoefficientConstructibleEtaleModules
import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Adjunction.Mates
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Over
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf

/-! # The comparison counit on a constant etale chart

Source: Stacks Project, Tags 099R, 099T and 099Y, comparison and localization.
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory AlgebraicGeometry

-- The universe-polymorphic `hasSheafify_of_essentiallySmall` gets stuck on the universe of
-- `ModuleCat.{max v (u + 1)}`; Mathlib's concrete-category instance applies instead.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

open CategoryTheory.Limits Opposite

section Localization

universe w
variable {C D : Type w} [SmallCategory C] [SmallCategory D]
  [HasFiniteLimits C] [HasFiniteLimits D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (G : C ⥤ D) [G.IsContinuous J K] [PreservesFiniteLimits G]
  (R : Type w) [CommRing R] (V : C)
  [(Over.post (X := V) G).IsContinuous (J.over V) (K.over (G.obj V))]

private noncomputable def restrictionSquare :
    G.sheafPushforwardContinuous (ModuleCat.{w} R) J K ⋙
        J.overPullback (ModuleCat.{w} R) V ≅
      K.overPullback (ModuleCat.{w} R) (G.obj V) ⋙
        (Over.post (X := V) G).sheafPushforwardContinuous (ModuleCat.{w} R)
          (J.over V) (K.over (G.obj V)) :=
  NatIso.ofComponents (fun _ ↦ ObjectProperty.isoMk _ (Iso.refl _))

private theorem restrictionSquare_mate_isIso :
    IsIso ((mateEquiv
      ((Over.forgetAdjStar (G.obj V)).sheafPushforwardContinuous
        (E := ModuleCat.{w} R) (K.over (G.obj V)) K)
      ((Over.forgetAdjStar V).sheafPushforwardContinuous
        (E := ModuleCat.{w} R) (J.over V) J))
      (restrictionSquare J K G R V).hom) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro H
  suffices IsIso ((sheafToPresheaf J (ModuleCat.{w} R)).map
      (((mateEquiv
        ((Over.forgetAdjStar (G.obj V)).sheafPushforwardContinuous
          (E := ModuleCat.{w} R) (K.over (G.obj V)) K)
        ((Over.forgetAdjStar V).sheafPushforwardContinuous
          (E := ModuleCat.{w} R) (J.over V) J))
        (restrictionSquare J K G R V).hom).app H)) from
    isIso_of_reflects_iso _ (sheafToPresheaf J (ModuleCat.{w} R))
  rw [NatTrans.isIso_iff_isIso_app]
  intro T
  change IsIso (H.obj.map
    (((Over.star (G.obj V)).map (G.map
      ((Over.forgetAdjStar V).counit.app T.unop))).op) ≫
    H.obj.map (((Over.forgetAdjStar (G.obj V)).unit.app
      ((Over.post G).obj ((Over.star V).obj T.unop))).op))
  rw [← H.obj.map_comp, ← op_comp]
  let e : (Over.post G).obj ((Over.star V).obj T.unop) ≅
      (Over.star (G.obj V)).obj (G.obj T.unop) :=
    Over.isoMk (PreservesLimitPair.iso G V T.unop) (by
      simp [PreservesLimitPair.iso_hom, Over.post, Over.star_obj_hom])
  have he : (Over.forgetAdjStar (G.obj V)).unit.app
        ((Over.post G).obj ((Over.star V).obj T.unop)) ≫
      (Over.star (G.obj V)).map (G.map ((Over.forgetAdjStar V).counit.app T.unop)) =
        e.hom := by
    apply Over.OverMorphism.ext
    apply prod.hom_ext <;>
      simp [e, PreservesLimitPair.iso_hom, Over.forgetAdjStar_unit_app_left,
        Over.post, Over.star_obj_hom]
  rw [he]
  infer_instance

private theorem localizedCounit_isIso
    (H : Sheaf K (ModuleCat.{w} R))
    (h : IsIso ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      (Over.post (X := V) G) (ModuleCat.{w} R) (J.over V)
      (K.over (G.obj V))).counit.app (H.over (G.obj V)))) :
    IsIso ((K.overPullback (ModuleCat.{w} R) (G.obj V)).map
      ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous G
        (ModuleCat.{w} R) J K).counit.app H)) := by
  let a := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous G
    (ModuleCat.{w} R) J K
  let b := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Over.post (X := V) G) (ModuleCat.{w} R) (J.over V) (K.over (G.obj V))
  let c := (Over.forgetAdjStar (G.obj V)).sheafPushforwardContinuous
    (E := ModuleCat.{w} R) (K.over (G.obj V)) K
  let d := (Over.forgetAdjStar V).sheafPushforwardContinuous
    (E := ModuleCat.{w} R) (J.over V) J
  let β := restrictionSquare J K G R V
  let δ := mateEquiv c d β.hom
  have hd : IsIso δ := restrictionSquare_mate_isIso J K G R V
  let α := ((mateEquiv a b).symm β.hom)
  have ha : IsIso α := by
    have he := iterated_mateEquiv_conjugateEquiv_symm a b d c δ
    have hb : (mateEquiv c d).symm δ = β.hom := Equiv.symm_apply_apply _ _
    rw [hb] at he
    have he' := he
    change α = (conjugateEquiv (a.comp c) (d.comp b)).symm δ at he'
    rw [he']
    infer_instance
  have hh : IsIso (b.counit.app (H.over (G.obj V))) := h
  have he := mateEquiv_counit_symm a b β.hom H
  have hc : IsIso (α.app
      ((G.sheafPushforwardContinuous (ModuleCat.{w} R) J K).obj H) ≫
        (K.overPullback (ModuleCat.{w} R) (G.obj V)).map (a.counit.app H)) := by
    rw [← he]
    infer_instance
  exact IsIso.of_isIso_comp_left (α.app _) _

end Localization

section Constants

universe w
variable {C D : Type w} [SmallCategory C] [SmallCategory D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (G : C ⥤ D) [G.IsContinuous J K]
  (R : Type w) [CommRing R]

private noncomputable def constantDirect (M : ModuleCat.{w} R) :
    (constantSheaf J (ModuleCat.{w} R)).obj M ⟶
      (G.sheafPushforwardContinuous (ModuleCat.{w} R) J K).obj
        ((constantSheaf K (ModuleCat.{w} R)).obj M) :=
  ((sheafificationAdjunction J (ModuleCat.{w} R)).homEquiv _ _).symm
    (Functor.whiskerLeft G.op (toSheafify K ((Functor.const Dᵒᵖ).obj M)))

private theorem constantDirect_unit (M : ModuleCat.{w} R) :
    toSheafify J ((Functor.const Cᵒᵖ).obj M) ≫
        (constantDirect J K G R M).hom =
      Functor.whiskerLeft G.op (toSheafify K ((Functor.const Dᵒᵖ).obj M)) :=
  ((sheafificationAdjunction J (ModuleCat.{w} R)).homEquiv _ _).apply_symm_apply _

private theorem sheafifiedMap_isIso
    {M : ModuleCat.{w} R} {P : Sheaf K (ModuleCat.{w} R)}
    (t : (Functor.const Dᵒᵖ).obj M ⟶ P.obj)
    [Presheaf.IsLocallyInjective K t] [Presheaf.IsLocallySurjective K t] :
    IsIso (((sheafificationAdjunction K (ModuleCat.{w} R)).homEquiv _ _).symm t) := by
  let k := ((sheafificationAdjunction K (ModuleCat.{w} R)).homEquiv _ _).symm t
  have h : toSheafify K ((Functor.const Dᵒᵖ).obj M) ≫ k.hom = t :=
    ((sheafificationAdjunction K (ModuleCat.{w} R)).homEquiv _ _).apply_symm_apply t
  refine (Sheaf.isLocallyBijective_iff_isIso k).1 ⟨?_, ?_⟩
  · change Presheaf.IsLocallyInjective K k.hom
    rw [← Presheaf.comp_isLocallyInjective_iff K (toSheafify K _), h]
    infer_instance
  · change Presheaf.IsLocallySurjective K k.hom
    rw [← Presheaf.comp_isLocallySurjective_iff K (toSheafify K _), h]
    infer_instance

private theorem constantDirect_isIso_of_functions
    (M : ModuleCat.{w} R) (P : Sheaf K (ModuleCat.{w} R))
    (t : (Functor.const Dᵒᵖ).obj M ⟶ P.obj)
    [Presheaf.IsLocallyInjective K t] [Presheaf.IsLocallySurjective K t]
    [Presheaf.IsLocallyInjective J (Functor.whiskerLeft G.op t)]
    [Presheaf.IsLocallySurjective J (Functor.whiskerLeft G.op t)] :
    IsIso (constantDirect J K G R M) := by
  let k := ((sheafificationAdjunction K (ModuleCat.{w} R)).homEquiv _ _).symm t
  let j : (constantSheaf J (ModuleCat.{w} R)).obj M ⟶
      (G.sheafPushforwardContinuous (ModuleCat.{w} R) J K).obj P :=
    ((sheafificationAdjunction J (ModuleCat.{w} R)).homEquiv _ _).symm
      (Functor.whiskerLeft G.op t)
  have hk : IsIso k := sheafifiedMap_isIso K R t
  have hj : IsIso j := sheafifiedMap_isIso J R
    (P := (G.sheafPushforwardContinuous (ModuleCat.{w} R) J K).obj P)
    (Functor.whiskerLeft G.op t)
  have he : constantDirect J K G R M ≫
      (G.sheafPushforwardContinuous (ModuleCat.{w} R) J K).map k = j := by
    have hjunit : toSheafify J ((Functor.const Cᵒᵖ).obj M) ≫ j.hom =
        Functor.whiskerLeft G.op t :=
      ((sheafificationAdjunction J (ModuleCat.{w} R)).homEquiv _ _).apply_symm_apply _
    apply ((sheafificationAdjunction J (ModuleCat.{w} R)).homEquiv _ _).injective
    simp only [Adjunction.homEquiv_unit]
    change toSheafify J _ ≫ ((constantDirect J K G R M).hom ≫
      Functor.whiskerLeft G.op k.hom) = toSheafify J _ ≫ j.hom
    rw [hjunit, ← Category.assoc, constantDirect_unit, ← Functor.whiskerLeft_comp]
    exact congrArg (Functor.whiskerLeft G.op)
      (((sheafificationAdjunction K (ModuleCat.{w} R)).homEquiv _ _).apply_symm_apply t)
  have hc : IsIso (constantDirect J K G R M ≫
      (G.sheafPushforwardContinuous (ModuleCat.{w} R) J K).map k) := by
    rw [he]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((G.sheafPushforwardContinuous (ModuleCat.{w} R) J K).map k)

private theorem constantInverse_isIso
    {L : Sheaf J (ModuleCat.{w} R) ⥤ Sheaf K (ModuleCat.{w} R)}
    (adj : L ⊣ G.sheafPushforwardContinuous (ModuleCat.{w} R) J K)
    {T : C} (hT : IsTerminal T) (hGT : IsTerminal (G.obj T))
    (M : ModuleCat.{w} R) :
    IsIso ((adj.homEquiv _ _).symm (constantDirect J K G R M)) := by
  let a := constantSheafAdj J (ModuleCat.{w} R) hT
  let b := constantSheafAdj K (ModuleCat.{w} R) hGT
  let c := (a.comp adj).ofNatIsoRight
    (G.sheafPushforwardContinuousCompSheafSectionsObjIso (ModuleCat.{w} R) J K (op T))
  have he : (adj.homEquiv _ _).symm (constantDirect J K G R M) =
      (c.leftAdjointUniq b).hom.app M := by
    apply (c.homEquiv _ _).injective
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app,
      Adjunction.homEquiv_ofNatIsoRight_apply]
    change (a.comp adj).homEquiv _ _
      ((adj.homEquiv _ _).symm (constantDirect J K G R M)) ≫ 𝟙 _ = _
    rw [Category.comp_id, Adjunction.comp_homEquiv]
    change a.homEquiv _ _ (adj.homEquiv _ _
      ((adj.homEquiv _ _).symm (constantDirect J K G R M))) = _
    rw [Equiv.apply_symm_apply]
    change ((constantPresheafAdj (ModuleCat.{w} R) hT).comp
      (sheafificationAdjunction J (ModuleCat.{w} R))).homEquiv _ _
        (constantDirect J K G R M) = _
    rw [Adjunction.comp_homEquiv]
    change (constantPresheafAdj (ModuleCat.{w} R) hT).homEquiv _ _
      ((sheafificationAdjunction J (ModuleCat.{w} R)).homEquiv _ _
        (((sheafificationAdjunction J (ModuleCat.{w} R)).homEquiv _ _).symm _)) = _
    rw [Equiv.apply_symm_apply]
    change 𝟙 M ≫ _ = _
    rw [Category.id_comp]
    rfl
  rw [he]
  infer_instance

private theorem constantCounit_isIso
    {L : Sheaf J (ModuleCat.{w} R) ⥤ Sheaf K (ModuleCat.{w} R)}
    (adj : L ⊣ G.sheafPushforwardContinuous (ModuleCat.{w} R) J K)
    {T : C} (hT : IsTerminal T) (hGT : IsTerminal (G.obj T))
    (M : ModuleCat.{w} R) [IsIso (constantDirect J K G R M)] :
    IsIso (adj.counit.app ((constantSheaf K (ModuleCat.{w} R)).obj M)) := by
  have hi := constantInverse_isIso J K G R adj hT hGT M
  rw [Adjunction.homEquiv_counit] at hi
  exact IsIso.of_isIso_comp_left (L.map (constantDirect J K G R M)) _

end Constants

section Functions

variable (X : Scheme.{u}) (R : Type (max v (u + 1))) [CommRing R]
  (M : ModuleCat.{max v (u + 1)} R) [TopologicalSpace M] [DiscreteTopology M]

private instance functions_continuousConstSMul {S N : Type*} [SMul S N]
    [TopologicalSpace N] [DiscreteTopology N] : ContinuousConstSMul S N where
  continuous_const_smul _ := continuous_of_discreteTopology

private def functionsPresheaf : Scheme.{u}ᵒᵖ ⥤ ModuleCat.{max v (u + 1)} R where
  obj U := ModuleCat.of R C(U.unop, M)
  map f := ModuleCat.ofHom
    { toFun := fun s ↦ s.comp f.unop.base.hom
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  map_id U := by ext s x; rfl
  map_comp f g := by ext s x; rfl

private theorem functionsPresheaf_isSheaf :
    Presheaf.IsSheaf Scheme.fpqcTopology (functionsPresheaf.{u, v} R M) := by
  have : ReflectsLimitsOfSize.{u, u + 1} (forget (ModuleCat.{max v (u + 1)} R)) :=
    reflectsLimitsOfSize_shrink.{u + 1, max v (u + 1), u, max v (u + 1)} _
  apply Presheaf.isSheaf_of_isSheaf_comp Scheme.fpqcTopology
    (functionsPresheaf.{u, v} R M) (forget (ModuleCat.{max v (u + 1)} R))
  exact AlgebraicGeometry.isSheaf_fpqcTopology_continuousMapPresheaf M

private def constantsToFunctions :
    (Functor.const Scheme.{u}ᵒᵖ).obj M ⟶ functionsPresheaf.{u, v} R M where
  app U := ModuleCat.ofHom
    { toFun := fun m ↦ ContinuousMap.const U.unop m
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  naturality _ _ _ := rfl

private theorem pro_constants_locallyInjective :
    Presheaf.IsLocallyInjective (Scheme.ProEt.topology X)
      (Functor.whiskerLeft (Scheme.ProEt.forget X ⋙ Over.forget X).op
        (constantsToFunctions.{u, v} R M)) := by
  constructor
  intro U a b h
  by_cases hab : a = b
  · subst b
    exact (Scheme.ProEt.topology X).superset_covering (fun _ _ _ ↦ rfl)
      ((Scheme.ProEt.topology X).top_mem _)
  · have : IsEmpty U.unop.left :=
      ⟨fun x ↦ hab (congrArg (fun f : C(U.unop.left, M) ↦ f x) h)⟩
    exact (Scheme.ProEt.topology X).superset_covering bot_le
      (Scheme.ProEt.bot_mem_topology _)

private theorem pro_constants_locallySurjective :
    Presheaf.IsLocallySurjective (Scheme.ProEt.topology X)
      (Functor.whiskerLeft (Scheme.ProEt.forget X ⋙ Over.forget X).op
        (constantsToFunctions.{u, v} R M)) := by
  constructor
  intro U s₀
  let s : C(U.left, M) := s₀
  let O (x : U.left) : U.left.Opens :=
    ⟨s ⁻¹' {s x}, (isOpen_discrete _).preimage s.continuous⟩
  apply Scheme.ProEt.mem_topology_of_openImmersion _ (fun x ↦ (O x).ι)
  · intro x
    exact ⟨x, ⟨⟨x, rfl⟩, rfl⟩⟩
  · intro x
    refine ⟨s x, ContinuousMap.ext fun y ↦ ?_⟩
    exact y.property.symm

private theorem etale_constants_locallyInjective :
    Presheaf.IsLocallyInjective X.smallEtaleTopology
      (Functor.whiskerLeft
        (Scheme.toProEt X ⋙ Scheme.ProEt.forget X ⋙ Over.forget X).op
        (constantsToFunctions.{u, v} R M)) := by
  constructor
  intro U a b h
  by_cases hab : a = b
  · subst b
    exact X.smallEtaleTopology.superset_covering (fun _ _ _ ↦ rfl)
      (X.smallEtaleTopology.top_mem _)
  · have : IsEmpty U.unop.left :=
      ⟨fun x ↦ hab (congrArg (fun f : C(U.unop.left, M) ↦ f x) h)⟩
    refine X.smallEtaleTopology.superset_covering ?_
      ((Scheme.ofArrows_mem_smallEtaleTopology_iff (Z := PEmpty.elim) (W := U.unop)
        (fun i : PEmpty.{1} ↦ i.elim)).2 (Set.eq_univ_of_forall fun x ↦ isEmptyElim x))
    rw [Sieve.ofArrows, Sieve.generate_le_iff]
    rintro _ _ ⟨i⟩
    exact i.elim

private theorem etale_constants_locallySurjective :
    Presheaf.IsLocallySurjective X.smallEtaleTopology
      (Functor.whiskerLeft
        (Scheme.toProEt X ⋙ Scheme.ProEt.forget X ⋙ Over.forget X).op
        (constantsToFunctions.{u, v} R M)) := by
  constructor
  intro U s₀
  let s : C(U.left, M) := s₀
  let O (x : U.left) : U.left.Opens :=
    ⟨s ⁻¹' {s x}, (isOpen_discrete _).preimage s.continuous⟩
  let W (x : U.left) : X.Etale := Scheme.Etale.mk ((O x).ι ≫ U.hom)
  let f (x : U.left) : W x ⟶ U := MorphismProperty.Over.homMk (O x).ι rfl
  refine X.smallEtaleTopology.superset_covering ?_
    ((Scheme.ofArrows_mem_smallEtaleTopology_iff f).2 ?_)
  · rw [Sieve.ofArrows, Sieve.generate_le_iff]
    rintro _ _ ⟨x⟩
    refine ⟨s x, ContinuousMap.ext fun y ↦ ?_⟩
    exact y.property.symm
  · exact Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.2 ⟨x, ⟨x, rfl⟩, rfl⟩

end Functions

namespace AlgebraicGeometry.ProEtale

/-- On an etale chart where F is constant, the restriction of the comparison
counit is invertible. There is no finite-presentation assumption, no covering
family, and no assumption on F away from this single chart.

Source: Stacks Project, Tags 099R, 099T and 099Y, comparison with etale localization
and the constant model case of lemma-compare-locally-constant
(auxiliary; not a blueprint node).

Proof: restriction commutes with comparison direct image on sections. Its mate
under the restriction/star adjunctions is induced by the product comparison
isomorphism, since the inclusion preserves finite limits. Iterated mates and the
mate counit identity identify the restricted global counit with the slice counit.
On both slice sites the sheaf of continuous functions into discrete M is the
constant sheaf: the constant-functions map is locally injective, including the
empty scheme, and locally surjective by the open fibres of a continuous function.
These properties descend through AsSmall and restriction to a slice. Consequently
the canonical direct-image map between constant sheaves is invertible. Its adjoint
is also invertible by uniqueness of left adjoints to evaluation at the terminal
object. The adjunction formula then makes the slice counit invertible on constant
M, and naturality transports this along the given chart isomorphism. -/
theorem coefficientComparison_counit_isIso_of_constant_over (X : Scheme.{u})
    (A : Type (max v (u + 1))) [CommRing A]
    (F : Sheaf (Scheme.coefficientProEtaleModelTopology.{u, v} X)
      (ModuleCat.{max v (u + 1)} A))
    (V : Scheme.smallModelComparisonEtaleSite.{u, v} X)
    (M : ModuleCat.{max v (u + 1)} A)
    (e : F.over ((Scheme.smallModelComparisonInclusion.{u, v} X).obj V) ≅
      (constantSheaf ((Scheme.coefficientProEtaleModelTopology.{u, v} X).over
        ((Scheme.smallModelComparisonInclusion.{u, v} X).obj V))
        (ModuleCat.{max v (u + 1)} A)).obj M) :
    IsIso (((Scheme.coefficientProEtaleModelTopology.{u, v} X).overPullback
      (ModuleCat.{max v (u + 1)} A)
      ((Scheme.smallModelComparisonInclusion.{u, v} X).obj V)).map
        ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
          (Scheme.smallModelComparisonInclusion.{u, v} X) (ModuleCat.{max v (u + 1)} A)
          (Scheme.smallModelComparisonEtaleTopology.{u, v} X)
          (Scheme.coefficientProEtaleModelTopology.{u, v} X)).counit.app F)) := by
  classical
  let J := Scheme.smallModelComparisonEtaleTopology.{u, v} X
  let K := Scheme.coefficientProEtaleModelTopology.{u, v} X
  let G := Scheme.smallModelComparisonInclusion.{u, v} X
  have : PreservesFiniteLimits
      (AsSmall.down : Scheme.smallModelComparisonEtaleSite.{u, v} X ⥤ X.Etale) :=
    inferInstanceAs (PreservesFiniteLimits
      (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.Etale)).inverse)
  have : PreservesFiniteLimits
      (AsSmall.up : X.ProEt ⥤ Scheme.coefficientProEtaleSiteModel.{u, v} X) :=
    inferInstanceAs (PreservesFiniteLimits
      (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.ProEt)).functor)
  have hp : PreservesFiniteLimits G := by dsimp [G]; infer_instance
  have : RepresentablyFlat (Over.post (X := V) G) := flat_of_preservesFiniteLimits _
  have hc : (Over.post (X := V) G).IsContinuous (J.over V) (K.over (G.obj V)) :=
    Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
      ((CoverPreserving.of_isContinuous G J K).overPost V)
  apply localizedCounit_isIso J K G A V F
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    (Over.post (X := V) G) (ModuleCat.{max v (u + 1)} A)
    (J.over V) (K.over (G.obj V))
  rw [NatTrans.isIso_app_iff_of_iso adj.counit e]
  suffices IsIso (constantDirect (J.over V) (K.over (G.obj V))
      (Over.post (X := V) G) A M) from
    constantCounit_isIso (J.over V) (K.over (G.obj V))
      (Over.post (X := V) G) A adj Over.mkIdTerminal
      (Over.mkIdTerminal.isTerminalObj (Over.post (X := V) G)) M
  let : TopologicalSpace M := ⊥
  let : DiscreteTopology M := ⟨rfl⟩
  have : (AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, v} X ⥤
      X.ProEt).IsEquivalence :=
    (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.ProEt)).isEquivalence_inverse
  have : (AsSmall.down : Scheme.smallModelComparisonEtaleSite.{u, v} X ⥤
      X.Etale).IsEquivalence :=
    (AsSmall.equiv.{u, u + 1, max v (u + 1)} (C := X.Etale)).isEquivalence_inverse
  let H₀ : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max v (u + 1)} A) :=
    ⟨(Scheme.ProEt.forget X ⋙ Over.forget X).op ⋙ functionsPresheaf.{u, v} A M,
      Functor.op_comp_isSheaf_of_isSheaf _ _ _ _
        ((functionsPresheaf_isSheaf.{u, v} A M).of_le
          Scheme.proetaleTopology_le_fpqcTopology)⟩
  let H := ((AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, v} X ⥤
    X.ProEt).sheafPushforwardContinuous (ModuleCat.{max v (u + 1)} A) K
      (Scheme.ProEt.topology X)).obj H₀
  let t₀ := Functor.whiskerLeft (Scheme.ProEt.forget X ⋙ Over.forget X).op
    (constantsToFunctions.{u, v} A M)
  let t := Functor.whiskerLeft (Over.forget (G.obj V)).op
    (Functor.whiskerLeft AsSmall.down.op t₀)
  have ht₀i : Presheaf.IsLocallyInjective (Scheme.ProEt.topology X) t₀ :=
    pro_constants_locallyInjective X A M
  have ht₀s : Presheaf.IsLocallySurjective (Scheme.ProEt.topology X) t₀ :=
    pro_constants_locallySurjective X A M
  have hmi := Presheaf.isLocallyInjective_whisker K (Scheme.ProEt.topology X)
    (AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, v} X ⥤ X.ProEt) t₀
  have hms := Presheaf.isLocallySurjective_whisker K (Scheme.ProEt.topology X)
    (AsSmall.down : Scheme.coefficientProEtaleSiteModel.{u, v} X ⥤ X.ProEt) t₀
  have hti : Presheaf.IsLocallyInjective (K.over (G.obj V)) t :=
    Presheaf.isLocallyInjective_whisker (K.over (G.obj V)) K (Over.forget (G.obj V)) _
  have hts : Presheaf.IsLocallySurjective (K.over (G.obj V)) t :=
    Presheaf.isLocallySurjective_whisker (K.over (G.obj V)) K (Over.forget (G.obj V)) _
  have hei := etale_constants_locallyInjective X A M
  have hes := etale_constants_locallySurjective X A M
  have hemi := Presheaf.isLocallyInjective_whisker J X.smallEtaleTopology
    (AsSmall.down : Scheme.smallModelComparisonEtaleSite.{u, v} X ⥤ X.Etale)
    (Functor.whiskerLeft
      (Scheme.toProEt X ⋙ Scheme.ProEt.forget X ⋙ Over.forget X).op
      (constantsToFunctions.{u, v} A M))
  have hems := Presheaf.isLocallySurjective_whisker J X.smallEtaleTopology
    (AsSmall.down : Scheme.smallModelComparisonEtaleSite.{u, v} X ⥤ X.Etale)
    (Functor.whiskerLeft
      (Scheme.toProEt X ⋙ Scheme.ProEt.forget X ⋙ Over.forget X).op
      (constantsToFunctions.{u, v} A M))
  have hgi : Presheaf.IsLocallyInjective (J.over V)
      (Functor.whiskerLeft (Over.post (X := V) G).op t) := by
    change Presheaf.IsLocallyInjective (J.over V)
      (Functor.whiskerLeft (Over.forget V).op
        (Functor.whiskerLeft AsSmall.down.op
          (Functor.whiskerLeft
            (Scheme.toProEt X ⋙ Scheme.ProEt.forget X ⋙ Over.forget X).op
            (constantsToFunctions.{u, v} A M))))
    exact Presheaf.isLocallyInjective_whisker (J.over V) J (Over.forget V) _
  have hgs : Presheaf.IsLocallySurjective (J.over V)
      (Functor.whiskerLeft (Over.post (X := V) G).op t) := by
    change Presheaf.IsLocallySurjective (J.over V)
      (Functor.whiskerLeft (Over.forget V).op
        (Functor.whiskerLeft AsSmall.down.op
          (Functor.whiskerLeft
            (Scheme.toProEt X ⋙ Scheme.ProEt.forget X ⋙ Over.forget X).op
            (constantsToFunctions.{u, v} A M))))
    exact Presheaf.isLocallySurjective_whisker (J.over V) J (Over.forget V) _
  exact constantDirect_isIso_of_functions (J.over V) (K.over (G.obj V))
    (Over.post (X := V) G) A M (H.over (G.obj V)) t

end AlgebraicGeometry.ProEtale
