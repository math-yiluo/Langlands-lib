/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent

/-! # Locality of quasi-coherence and finite type on a binary union

Source: Stacks Project, Modules, Tags 01BE and 01B5; Properties, Lemma 01PF.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry SheafOfModules

section SiteHelpers

universe u₁ u₂ v₁ v₂

open SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

private theorem finiteType_of_data {M : SheafOfModules.{u} R}
    (q : M.LocalGeneratorsData) [hq : q.IsFiniteType] : M.IsFiniteType := by
  have : q.shrink.IsFiniteType :=
    ⟨fun i ↦ hq.isFiniteType i.2.choose⟩
  exact ⟨q.shrink, this⟩

private theorem finiteType_of_iso {M N : SheafOfModules.{u} R} (e : M ≅ N)
    [M.IsFiniteType] : N.IsFiniteType := by
  obtain ⟨q, hq⟩ := IsFiniteType.exists_localGeneratorsData M
  let q' : N.LocalGeneratorsData :=
    { I := q.I
      X := q.X
      coversTop := q.coversTop
      generators i := (q.generators i).ofEpi (e.hom.over (q.X i)) }
  have : q'.IsFiniteType := ⟨fun i ↦ by
    have := hq.isFiniteType i
    exact inferInstanceAs ((q.generators i).ofEpi _).IsFiniteType⟩
  exact finiteType_of_data q'

variable {D : Type u₂} [Category.{v₂} D] {K : GrothendieckTopology D}
  {S : Sheaf K RingCat.{u}}
  [∀ X, HasSheafify (K.over X) AddCommGrpCat.{u}]
  [∀ X, (K.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]

set_option backward.isDefEq.respectTransparency false in
private theorem finiteType_pushforward
    (G : D ⥤ C) [G.IsContinuous K J] [G.IsCocontinuous K J]
    (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{u} K J).obj R)
    (η : (pushforward.{u} φ).obj (unit R) ≅ unit S)
    [∀ X, (Over.post G).IsContinuous (K.over X) (J.over (G.obj X))]
    (h : ∀ (X : D) (Y : C) (f : G.obj X ⟶ Y),
      PreservesColimitsOfSize.{u, u}
        (pushforward.{u} (R := R.over Y) (F := Over.post (X := X) G ⋙ Over.map f)
          (((Over.forget X).sheafPushforwardContinuous RingCat.{u} (K.over X) K).map φ)))
    {M : SheafOfModules.{u} R} [M.IsFiniteType] :
    ((pushforward.{u} φ).obj M).IsFiniteType := by
  obtain ⟨P, hP⟩ := IsFiniteType.exists_localGeneratorsData M
  let Q : ((pushforward.{u} φ).obj M).LocalGeneratorsData :=
    { I := Σ (X : D) (i : P.I), G.obj X ⟶ P.X i
      X i := i.1
      coversTop Y := by
        refine K.superset_covering ?_ (G.cover_lift K _ (P.coversTop (G.obj Y)))
        intro Z g ⟨i, ⟨v⟩⟩
        exact ⟨⟨Z, i, v⟩, ⟨𝟙 _⟩⟩
      generators i := by
        let overS : SheafOfModules.{u} S ⥤ SheafOfModules.{u} (S.over i.1) :=
          pushforward (𝟙 _)
        let G' := Over.post (X := i.1) G ⋙ Over.map i.2.2
        let ψ : S.over i.1 ⟶
            (G'.sheafPushforwardContinuous RingCat.{u} (K.over i.1)
              (J.over (P.X i.2.1))).obj (R.over (P.X i.2.1)) :=
          ((Over.forget i.1).sheafPushforwardContinuous RingCat.{u} (K.over i.1) K).map φ
        let e : (pushforward.{u} (F := G') ψ).obj (unit (R.over (P.X i.2.1))) ≅
            unit (S.over i.1) := overS.mapIso η
        letI : PreservesColimitsOfSize.{u, u} (pushforward.{u} (F := G') ψ) := h _ _ _
        exact (P.generators i.2.1).map (pushforward.{u} (F := G') ψ) e.symm }
  have : Q.IsFiniteType := ⟨fun i ↦ by
    have := hP.isFiniteType i.2.1
    dsimp [Q]
    infer_instance⟩
  exact finiteType_of_data Q

private theorem finiteType_pushforward_leftAdjoint
    (G : D ⥤ C) [G.IsContinuous K J] [G.IsCocontinuous K J]
    (φ : S ⟶ (G.sheafPushforwardContinuous RingCat.{u} K J).obj R)
    (η : (pushforward.{u} φ).obj (unit R) ≅ unit S) [G.IsLeftAdjoint] [IsIso φ]
    [∀ X, (Over.post G).IsContinuous (K.over X) (J.over (G.obj X))]
    [HasPullbacks C] [HasPullbacks D]
    {M : SheafOfModules.{u} R} [M.IsFiniteType] :
    ((pushforward.{u} φ).obj M).IsFiniteType := by
  apply +allowSynthFailures finiteType_pushforward G φ η _
  intro X Y f
  let G' := Over.post (X := X) G ⋙ Over.map f
  have : G'.IsContinuous (K.over X) (J.over Y) :=
    Functor.isContinuous_comp _ _ _ (J.over _) _
  have : G'.IsCocontinuous (K.over X) (J.over Y) := isCocontinuous_comp _ _ _ (J.over _)
  let a : S.over X ⟶
      (G'.sheafPushforwardContinuous RingCat.{u} (K.over X) (J.over Y)).obj (R.over Y) :=
    ((Over.forget X).sheafPushforwardContinuous RingCat.{u} (K.over X) K).map φ
  have : (pushforward.{u} a).IsLeftAdjoint := isLeftAdjoint_pushforward_of_isIso a
  infer_instance

section Locality

variable [HasPullbacks C] [HasBinaryProducts C]
  [∀ X Y, HasSheafify ((J.over X).over Y) AddCommGrpCat.{u}]
  [∀ X Y, ((J.over X).over Y).WEqualsLocallyBijective AddCommGrpCat.{u}]

omit [HasPullbacks C] [HasBinaryProducts C] in
private theorem finiteType_of_cover (M : SheafOfModules.{u} R) {I : Type v}
    (X : I → C) (hX : J.CoversTop X) [∀ i, (M.over (X i)).IsFiniteType] :
    M.IsFiniteType := by
  choose D hD using fun i ↦ IsFiniteType.exists_localGeneratorsData (M.over (X i))
  let q : M.LocalGeneratorsData :=
    { I := (i : I) × (D i).I
      X ij := ((D ij.1).X ij.2).left
      coversTop := hX.over (fun i ↦ (D i).coversTop)
      generators i := by
        let e := pushforwardPushforwardEquivalence (Over.iteratedSliceEquiv ((D i.1).X i.2))
          (S := (R.over _).over _) (R := R.over _) (𝟙 _) (𝟙 _)
          (by ext : 2; exact R.1.map_id _) (by ext : 2; exact R.1.map_id _)
        exact (((D i.1).generators i.2).map e.inverse (.refl _)).ofEpi
          (e.fullyFaithfulFunctor.preimageIso
            (by exact e.counitIso.app ((M.over (X i.1)).over ((D i.1).X i.2)))).hom }
  have : q.IsFiniteType := ⟨fun i ↦ by
    have := (hD i.1).isFiniteType i.2
    dsimp [q]
    infer_instance⟩
  exact finiteType_of_data q

-- Keep the ring sheaf abstract during iterated-slice transport, and perform
-- the cover argument separately so the slice instances need not be reconstructed.
private theorem localProperties_over_of_overMap
    (X : TopCat.{u}) (R : Sheaf (_root_.Opens.grothendieckTopology X) RingCat.{u})
    {A B : TopologicalSpace.Opens X} (f : A ⟶ B)
    (M : SheafOfModules.{u} (R.over B))
    (hq : ((overMap R f).obj M).IsQuasicoherent)
    (hf : ((overMap R f).obj M).IsFiniteType) :
    (M.over (Over.mk f)).IsQuasicoherent ∧ (M.over (Over.mk f)).IsFiniteType := by
  let J := _root_.Opens.grothendieckTopology X
  have := hq
  have := hf
  let E := Over.iteratedSliceEquiv (Over.mk f)
  have : E.inverse.IsDenseSubsite (J.over A)
      ((J.over B).over (Over.mk f)) := by
    refine { functorPushforward_mem_iff := ?_ }
    intro T S
    simp only [E, GrothendieckTopology.mem_over_iff, Sieve.overEquiv,
      RelIso.coe_fn_mk, Equiv.coe_fn_mk]
    dsimp [Over.iteratedSliceEquiv]
    rw [← Sieve.functorPushforward_comp, ← Sieve.functorPushforward_comp]
    rfl
  have : E.functor.IsContinuous
      ((J.over B).over (Over.mk f)) (J.over A) := by
    infer_instance
  have : E.functor.IsCocontinuous
      ((J.over B).over (Over.mk f)) (J.over A) := by
    infer_instance
  have (T : Over (Over.mk f)) :
      (Over.post (X := T) E.functor).IsContinuous
        (((J.over B).over (Over.mk f)).over T)
        ((J.over A).over (E.functor.obj T)) := by
    apply Functor.isContinuous_of_coverPreserving
      (compatiblePreservingOfFlat _ _) _
    exact (Functor.IsDenseSubsite.coverPreserving
      ((J.over B).over (Over.mk f))
      (J.over A) E.functor).overPost T
  let S := (R.over B).over (Over.mk f)
  let φ : S ⟶ (E.functor.sheafPushforwardContinuous RingCat
      ((J.over B).over (Over.mk f)) (J.over A)).obj
        (R.over A) := 𝟙 _
  let e : (SheafOfModules.pushforward φ).obj ((overMap R f).obj M) ≅
      M.over (Over.mk f) :=
    (SheafOfModules.fullyFaithfulForget _).preimageIso
      (PresheafOfModules.isoMk (fun _ ↦ Iso.refl _))
  have hqc := isQuasicoherent_pushforward_of_isLeftAdjoint E.functor φ
    (Iso.refl _) (M := (overMap R f).obj M)
  have hft := finiteType_pushforward_leftAdjoint E.functor φ
    (Iso.refl _) (M := (overMap R f).obj M)
  exact ⟨(isQuasicoherent S).prop_of_iso e hqc,
    finiteType_of_iso (R := S) e⟩

end Locality

end SiteHelpers



namespace AlgebraicGeometry.Scheme.Modules

set_option backward.defeqAttrib.useBackward true in
-- Transport across iterated slice sites requires additional elaboration.
set_option backward.isDefEq.respectTransparency false in
/-- Quasi-coherence and finite type descend from the two members of a binary open cover.
Source: Stacks Project, Modules, Definitions 01BE and 01B5, and Properties, Lemma 01PF.
(blueprint: lem-weil-pbc-module-binary-local-properties).

Proof: Choose local presentations and finite generating families for the two restricted
modules. An object of the slice site Over W or Over V is an open T contained in that
member. The iterated-slice equivalence identifies its further restriction with the
restriction of G directly to T in Over (W union V), and identifies the structure
modules and their free modules. Transport each presentation and generating family
through this equivalence. Index these data by the disjoint union of the two local
index types, and use their underlying opens as objects of Over (W union V).
Every point of an open T in W union V belongs to W or V; the local cover for that
member supplies a smaller neighbourhood on which the transported data apply.
Thus these neighbourhoods cover the terminal object of the union site. The combined
presentations witness quasi-coherence, and the combined finite generating families
witness finite type. Empty members contribute vacuous data and cause no exception. -/
theorem module_binary_local_properties
    (X : Scheme.{u}) (W V : X.Opens)
    (G : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over (W ⊔ V)))
    (hW : ((SheafOfModules.overMap (moduleRings X.toRingedSpace)
      (homOfLE (show W ≤ W ⊔ V from le_sup_left))).obj G).IsQuasicoherent ∧
      ((SheafOfModules.overMap (moduleRings X.toRingedSpace)
        (homOfLE (show W ≤ W ⊔ V from le_sup_left))).obj G).IsFiniteType)
    (hV : ((SheafOfModules.overMap (moduleRings X.toRingedSpace)
      (homOfLE (show V ≤ W ⊔ V from le_sup_right))).obj G).IsQuasicoherent ∧
      ((SheafOfModules.overMap (moduleRings X.toRingedSpace)
        (homOfLE (show V ≤ W ⊔ V from le_sup_right))).obj G).IsFiniteType) :
    G.IsQuasicoherent ∧ G.IsFiniteType := by
  let R := moduleRings X.toRingedSpace
  let J := _root_.Opens.grothendieckTopology X
  let U : ULift.{u} Bool → Over (W ⊔ V) := fun b ↦
    if b.down then Over.mk (homOfLE (le_sup_left : W ≤ W ⊔ V))
    else Over.mk (homOfLE (le_sup_right : V ≤ W ⊔ V))
  have hc : (J.over (W ⊔ V)).CoversTop U := by
    intro T
    rw [GrothendieckTopology.mem_over_iff]
    intro x hx
    have hxu : x ∈ W ⊔ V := T.hom.le hx
    rcases hxu with hxW | hxV
    · let A : Over (W ⊔ V) := Over.mk
        (homOfLE (inf_le_left.trans T.hom.le : T.left ⊓ W ≤ W ⊔ V))
      refine ⟨T.left ⊓ W, homOfLE inf_le_left, ?_, ⟨hx, hxW⟩⟩
      rw [Sieve.overEquiv_iff]
      change Sieve.ofObjects U T (Over.homMk (homOfLE inf_le_left) : A ⟶ T)
      exact ⟨⟨true⟩, ⟨Over.homMk (homOfLE inf_le_right)⟩⟩
    · let A : Over (W ⊔ V) := Over.mk
        (homOfLE (inf_le_left.trans T.hom.le : T.left ⊓ V ≤ W ⊔ V))
      refine ⟨T.left ⊓ V, homOfLE inf_le_left, ?_, ⟨hx, hxV⟩⟩
      rw [Sieve.overEquiv_iff]
      change Sieve.ofObjects U T (Over.homMk (homOfLE inf_le_left) : A ⟶ T)
      exact ⟨⟨false⟩, ⟨Over.homMk (homOfLE inf_le_right)⟩⟩
  have hp (b : ULift.{u} Bool) : (G.over (U b)).IsQuasicoherent ∧ (G.over (U b)).IsFiniteType := by
    rcases b with ⟨b⟩
    cases b
    · exact localProperties_over_of_overMap X.toTopCat R (homOfLE le_sup_right) G hV.1 hV.2
    · exact localProperties_over_of_overMap X.toTopCat R (homOfLE le_sup_left) G hW.1 hW.2
  have (b : ULift.{u} Bool) : (G.over (U b)).IsQuasicoherent := (hp b).1
  have (b : ULift.{u} Bool) : (G.over (U b)).IsFiniteType := (hp b).2
  exact ⟨IsQuasicoherent.of_coversTop G U hc, finiteType_of_cover G U hc⟩

end AlgebraicGeometry.Scheme.Modules
