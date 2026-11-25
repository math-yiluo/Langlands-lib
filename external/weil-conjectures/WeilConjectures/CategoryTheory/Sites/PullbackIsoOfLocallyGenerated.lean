/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.CategoryTheory.Sites.Continuous
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# Isomorphy of the counit-type map for locally generated sheaves

Let `P : C ⥤ D` be a continuous functor between sites `(C, J)` and `(D, K)` and let
`L ⊣ P_*` be an adjunction, where `P_* = P.sheafPushforwardContinuous A J K` and
`A = ModuleCat R`. Given sheaves `F` on `C`, `G` on `D` and `η : F ⟶ P_* G`, we show that the
adjoint morphism `L F ⟶ G` is an isomorphism provided that

* (LS) every section of `G` is locally of the form `G.map φ.op (η t)` for a section `t` of `F`;
* (WD) whenever `G.map φ.op (η t) = 0`, this relation holds locally already in `F`, i.e.
  locally `φ` factors as `φ' ≫ P.map a` with `F.map a.op t = 0`;

and `P` preserves binary products. Indeed, for every sheaf `H` the map
`(G ⟶ H) → (F ⟶ P_* H)`, `x ↦ η ≫ P_* x`, is bijective: a morphism `ψ : F ⟶ P_* H` is glued
to a morphism `G ⟶ H` using the sheaf property of `H`.

## Main results

- `CategoryTheory.isIso_homEquiv_symm_of_locally_generated`.

The auxiliary construction is carried out at the level of presheaves in the namespace
`CategoryTheory.LocallyGenerated`.
-/

@[expose] public section

namespace CategoryTheory

open Opposite Limits

universe w v₁ v₂ u₁ u₂ u

namespace LocallyGenerated

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {K : GrothendieckTopology D} {P : C ⥤ D} {R : Type u} [Ring R]
  {F : Cᵒᵖ ⥤ ModuleCat.{w} R} {G H : Dᵒᵖ ⥤ ModuleCat.{w} R}

/-- Every section of `G` is locally of the form `G.map φ.op (η t)`. -/
def SectionsLocallyPulledBack (K : GrothendieckTopology D) (η : F ⟶ P.op ⋙ G) : Prop :=
  ∀ (U : D) (s : G.obj (op U)), ∃ S ∈ K U, ∀ ⦃U' : D⦄ (u : U' ⟶ U), S u →
    ∃ (V : C) (t : F.obj (op V)) (φ : U' ⟶ P.obj V), G.map u.op s = G.map φ.op (η.app (op V) t)

/-- Relations among pulled back sections hold locally already in `F`. -/
def RelationsLocal (K : GrothendieckTopology D) (η : F ⟶ P.op ⋙ G) : Prop :=
  ∀ (V : C) (t : F.obj (op V)) (U : D) (φ : U ⟶ P.obj V),
    G.map φ.op (η.app (op V) t) = 0 → ∃ S ∈ K U, ∀ ⦃U' : D⦄ (u : U' ⟶ U), S u →
      ∃ (V' : C) (a : V' ⟶ V) (φ' : U' ⟶ P.obj V'), F.map a.op t = 0 ∧ φ' ≫ P.map a = u ≫ φ

/-- Any two objects `V₁`, `V₂` admit a common "refinement" `V` through which pairs of maps
`U ⟶ P.obj V₁`, `U ⟶ P.obj V₂` factor (e.g. `V = V₁ ⨯ V₂` if `P` preserves it). -/
def HasPairLifts (P : C ⥤ D) : Prop :=
  ∀ V₁ V₂ : C, ∃ (V : C) (p₁ : V ⟶ V₁) (p₂ : V ⟶ V₂), ∀ ⦃U : D⦄ (φ₁ : U ⟶ P.obj V₁)
    (φ₂ : U ⟶ P.obj V₂), ∃ φ : U ⟶ P.obj V, φ ≫ P.map p₁ = φ₁ ∧ φ ≫ P.map p₂ = φ₂

/-- A functor preserving binary products of a category with binary products has pair lifts. -/
lemma hasPairLifts_of_preservesLimitsOfShape [HasBinaryProducts C]
    [PreservesLimitsOfShape (Discrete WalkingPair) P] : HasPairLifts P := by
  intro V₁ V₂
  refine ⟨V₁ ⨯ V₂, prod.fst, prod.snd, fun U φ₁ φ₂ ↦ ?_⟩
  obtain ⟨φ, h₁, h₂⟩ := BinaryFan.IsLimit.lift'
    (isLimitOfHasBinaryProductOfPreservesLimit P V₁ V₂) φ₁ φ₂
  exact ⟨φ, h₁, h₂⟩

/-- Naturality of `η : F ⟶ P.op ⋙ G`, phrased with `G.map (P.map a).op`. -/
lemma app_map (η : F ⟶ P.op ⋙ G) {V V' : C} (a : V' ⟶ V) (t : F.obj (op V)) :
    η.app (op V') (F.map a.op t) = G.map (P.map a).op (η.app (op V) t) :=
  NatTrans.naturality_apply η a.op t

/-- Separatedness of `H`, phrased with the module-valued restriction maps. -/
lemma ext_of_isSeparated (hH : Presieve.IsSeparated K (H ⋙ forget (ModuleCat.{w} R))) {U : D}
    {S : Sieve U} (hS : S ∈ K U) {a b : H.obj (op U)}
    (h : ∀ ⦃U' : D⦄ (u : U' ⟶ U), S u → H.map u.op a = H.map u.op b) : a = b :=
  (hH S hS).ext h

/-- If `G.map φ.op (η t) = 0`, then also `H.map φ.op (ψ t) = 0`. -/
lemma map_eq_zero (η : F ⟶ P.op ⋙ G) (ψ : F ⟶ P.op ⋙ H) (hWD : RelationsLocal K η)
    (hH : Presieve.IsSeparated K (H ⋙ forget (ModuleCat.{w} R)))
    {V : C} (t : F.obj (op V)) {U : D} (φ : U ⟶ P.obj V)
    (h : G.map φ.op (η.app (op V) t) = 0) : H.map φ.op (ψ.app (op V) t) = 0 := by
  obtain ⟨S, hS, hS'⟩ := hWD V t U φ h
  refine ext_of_isSeparated hH hS fun U' u hu ↦ ?_
  obtain ⟨V', a, φ', ha, hφ'⟩ := hS' u hu
  rw [map_zero, ← Functor.map_comp_apply, ← op_comp, ← hφ', op_comp, Functor.map_comp_apply,
    ← app_map ψ a t, ha, map_zero, map_zero]

/-- Two local presentations of the same section of `G` induce the same section of `H`. -/
lemma map_eq_map (η : F ⟶ P.op ⋙ G) (ψ : F ⟶ P.op ⋙ H) (hP : HasPairLifts P)
    (hWD : RelationsLocal K η) (hH : Presieve.IsSeparated K (H ⋙ forget (ModuleCat.{w} R)))
    {V₁ V₂ : C} (t₁ : F.obj (op V₁)) (t₂ : F.obj (op V₂)) {U : D} (φ₁ : U ⟶ P.obj V₁)
    (φ₂ : U ⟶ P.obj V₂) (h : G.map φ₁.op (η.app (op V₁) t₁) = G.map φ₂.op (η.app (op V₂) t₂)) :
    H.map φ₁.op (ψ.app (op V₁) t₁) = H.map φ₂.op (ψ.app (op V₂) t₂) := by
  obtain ⟨V, p₁, p₂, hp⟩ := hP V₁ V₂
  obtain ⟨φ, rfl, rfl⟩ := hp φ₁ φ₂
  have := map_eq_zero η ψ hWD hH (F.map p₁.op t₁ - F.map p₂.op t₂) φ (by
    rw [map_sub, app_map, app_map, map_sub, ← Functor.map_comp_apply, ← Functor.map_comp_apply,
      ← op_comp, ← op_comp, h, sub_self])
  rwa [map_sub, app_map, app_map, map_sub, ← Functor.map_comp_apply, ← Functor.map_comp_apply,
    ← op_comp, ← op_comp, sub_eq_zero] at this

/-- Every section `s` of `G` determines a section of `H` whose restrictions are computed by
`ψ` on any local presentation of `s`. -/
lemma exists_section (η : F ⟶ P.op ⋙ G) (ψ : F ⟶ P.op ⋙ H) (hP : HasPairLifts P)
    (hLS : SectionsLocallyPulledBack K η) (hWD : RelationsLocal K η)
    (hH : Presieve.IsSheaf K (H ⋙ forget (ModuleCat.{w} R))) {U : D} (s : G.obj (op U)) :
    ∃ x : H.obj (op U), ∀ ⦃U' : D⦄ (u : U' ⟶ U) ⦃V : C⦄ (t : F.obj (op V))
      (φ : U' ⟶ P.obj V), G.map u.op s = G.map φ.op (η.app (op V) t) →
        H.map u.op x = H.map φ.op (ψ.app (op V) t) := by
  obtain ⟨S, hS, hS'⟩ := hLS U s
  choose V t φ hφ using hS'
  let x : Presieve.FamilyOfElements (H ⋙ forget (ModuleCat.{w} R)) S.arrows :=
    fun _ u hu ↦ H.map (φ u hu).op (ψ.app _ (t u hu))
  have hx : x.Compatible := by
    intro Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ hg
    have := map_eq_map η ψ hP hWD hH.isSeparated (t f₁ h₁) (t f₂ h₂) (g₁ ≫ φ f₁ h₁)
      (g₂ ≫ φ f₂ h₂) (by
        rw [op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply, ← hφ, ← hφ,
          ← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, hg])
    simpa [x] using this
  refine ⟨(hH S hS).amalgamate x hx, fun U' u V₀ t₀ φ₀ h ↦ ?_⟩
  refine (hH.isSeparated _ (K.pullback_stable u hS)).ext fun U'' v hv ↦ ?_
  replace hv : S.arrows (v ≫ u) := hv
  have h₁ : H.map (v ≫ u).op ((hH S hS).amalgamate x hx) =
      H.map (φ _ hv).op (ψ.app _ (t _ hv)) := (hH S hS).valid_glue hx (v ≫ u) hv
  have h₂ := map_eq_map η ψ hP hWD hH.isSeparated (t _ hv) t₀ (φ _ hv) (v ≫ φ₀) (by
    rw [← hφ, op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply, h])
  rw [op_comp, Functor.map_comp_apply] at h₁ h₂
  exact h₁.trans h₂

/-- The section of `H` glued from `ψ` along the local presentations of `s`. -/
noncomputable def liftApp (η : F ⟶ P.op ⋙ G) (ψ : F ⟶ P.op ⋙ H) (hP : HasPairLifts P)
    (hLS : SectionsLocallyPulledBack K η) (hWD : RelationsLocal K η)
    (hH : Presieve.IsSheaf K (H ⋙ forget (ModuleCat.{w} R))) {U : D} (s : G.obj (op U)) :
    H.obj (op U) :=
  (exists_section η ψ hP hLS hWD hH s).choose

/-- The defining property of `liftApp`. -/
lemma map_liftApp (η : F ⟶ P.op ⋙ G) (ψ : F ⟶ P.op ⋙ H) (hP : HasPairLifts P)
    (hLS : SectionsLocallyPulledBack K η) (hWD : RelationsLocal K η)
    (hH : Presieve.IsSheaf K (H ⋙ forget (ModuleCat.{w} R))) {U U' : D} (s : G.obj (op U))
    (u : U' ⟶ U) {V : C} (t : F.obj (op V)) (φ : U' ⟶ P.obj V)
    (h : G.map u.op s = G.map φ.op (η.app (op V) t)) :
    H.map u.op (liftApp η ψ hP hLS hWD hH s) = H.map φ.op (ψ.app (op V) t) :=
  (exists_section η ψ hP hLS hWD hH s).choose_spec u t φ h

/-- `liftApp` is additive. -/
lemma liftApp_add (η : F ⟶ P.op ⋙ G) (ψ : F ⟶ P.op ⋙ H) (hP : HasPairLifts P)
    (hLS : SectionsLocallyPulledBack K η) (hWD : RelationsLocal K η)
    (hH : Presieve.IsSheaf K (H ⋙ forget (ModuleCat.{w} R))) {U : D} (s₁ s₂ : G.obj (op U)) :
    liftApp η ψ hP hLS hWD hH (s₁ + s₂) =
      liftApp η ψ hP hLS hWD hH s₁ + liftApp η ψ hP hLS hWD hH s₂ := by
  obtain ⟨S₁, hS₁, hS₁'⟩ := hLS U s₁
  obtain ⟨S₂, hS₂, hS₂'⟩ := hLS U s₂
  refine ext_of_isSeparated hH.isSeparated (K.intersection_covering hS₁ hS₂) fun U' u hu ↦ ?_
  obtain ⟨V₁, t₁, φ₁, h₁⟩ := hS₁' u hu.1
  obtain ⟨V₂, t₂, φ₂, h₂⟩ := hS₂' u hu.2
  obtain ⟨V, p₁, p₂, hp⟩ := hP V₁ V₂
  obtain ⟨φ, rfl, rfl⟩ := hp φ₁ φ₂
  rw [map_add, map_liftApp η ψ hP hLS hWD hH _ u t₁ _ h₁, map_liftApp η ψ hP hLS hWD hH _ u t₂ _ h₂,
    map_liftApp η ψ hP hLS hWD hH _ u (F.map p₁.op t₁ + F.map p₂.op t₂) φ
      (by
        rw [map_add, h₁, h₂, map_add, app_map, app_map, map_add, ← Functor.map_comp_apply,
          ← Functor.map_comp_apply, ← op_comp, ← op_comp])]
  rw [map_add, app_map, app_map, map_add, ← Functor.map_comp_apply, ← Functor.map_comp_apply,
    ← op_comp, ← op_comp]

/-- `liftApp` is `R`-linear. -/
lemma liftApp_smul (η : F ⟶ P.op ⋙ G) (ψ : F ⟶ P.op ⋙ H) (hP : HasPairLifts P)
    (hLS : SectionsLocallyPulledBack K η) (hWD : RelationsLocal K η)
    (hH : Presieve.IsSheaf K (H ⋙ forget (ModuleCat.{w} R))) {U : D} (r : R)
    (s : G.obj (op U)) :
    liftApp η ψ hP hLS hWD hH (r • s) = r • liftApp η ψ hP hLS hWD hH s := by
  obtain ⟨S, hS, hS'⟩ := hLS U s
  refine ext_of_isSeparated hH.isSeparated hS fun U' u hu ↦ ?_
  obtain ⟨V, t, φ, h⟩ := hS' u hu
  rw [map_smul, map_liftApp η ψ hP hLS hWD hH _ u t _ h,
    map_liftApp η ψ hP hLS hWD hH _ u (r • t) φ (by simp [h])]
  simp

/-- `liftApp` commutes with restrictions. -/
lemma liftApp_map (η : F ⟶ P.op ⋙ G) (ψ : F ⟶ P.op ⋙ H) (hP : HasPairLifts P)
    (hLS : SectionsLocallyPulledBack K η) (hWD : RelationsLocal K η)
    (hH : Presieve.IsSheaf K (H ⋙ forget (ModuleCat.{w} R))) {U₁ U₂ : D} (f : U₂ ⟶ U₁)
    (s : G.obj (op U₁)) :
    liftApp η ψ hP hLS hWD hH (G.map f.op s) = H.map f.op (liftApp η ψ hP hLS hWD hH s) := by
  obtain ⟨S, hS, hS'⟩ := hLS U₂ (G.map f.op s)
  refine ext_of_isSeparated hH.isSeparated hS fun U' u hu ↦ ?_
  obtain ⟨V, t, φ, h⟩ := hS' u hu
  rw [map_liftApp η ψ hP hLS hWD hH _ u t _ h, ← Functor.map_comp_apply, ← op_comp,
    map_liftApp η ψ hP hLS hWD hH _ _ t _ (by rw [op_comp, Functor.map_comp_apply, h])]

/-- The morphism `G ⟶ H` glued from `ψ : F ⟶ P.op ⋙ H`. -/
noncomputable def lift (η : F ⟶ P.op ⋙ G) (ψ : F ⟶ P.op ⋙ H) (hP : HasPairLifts P)
    (hLS : SectionsLocallyPulledBack K η) (hWD : RelationsLocal K η)
    (hH : Presieve.IsSheaf K (H ⋙ forget (ModuleCat.{w} R))) : G ⟶ H where
  app U := ModuleCat.ofHom
    { toFun := liftApp η ψ hP hLS hWD hH (U := U.unop)
      map_add' := liftApp_add η ψ hP hLS hWD hH
      map_smul' := liftApp_smul η ψ hP hLS hWD hH }
  naturality U₁ U₂ f := by
    ext s
    exact liftApp_map η ψ hP hLS hWD hH f.unop s

/-- The components of `lift`. -/
@[simp]
lemma lift_app_apply (η : F ⟶ P.op ⋙ G) (ψ : F ⟶ P.op ⋙ H) (hP : HasPairLifts P)
    (hLS : SectionsLocallyPulledBack K η) (hWD : RelationsLocal K η)
    (hH : Presieve.IsSheaf K (H ⋙ forget (ModuleCat.{w} R))) (U : Dᵒᵖ) (s : G.obj U) :
    (lift η ψ hP hLS hWD hH).app U s = liftApp η ψ hP hLS hWD hH (U := U.unop) s :=
  rfl

/-- `lift η ψ` is a preimage of `ψ` under `x ↦ η ≫ P.op ◁ x`. -/
lemma lift_fac (η : F ⟶ P.op ⋙ G) (ψ : F ⟶ P.op ⋙ H) (hP : HasPairLifts P)
    (hLS : SectionsLocallyPulledBack K η) (hWD : RelationsLocal K η)
    (hH : Presieve.IsSheaf K (H ⋙ forget (ModuleCat.{w} R))) :
    η ≫ Functor.whiskerLeft P.op (lift η ψ hP hLS hWD hH) = ψ := by
  ext V t
  simpa using map_liftApp η ψ hP hLS hWD hH (η.app V t) (𝟙 _) t (𝟙 _) rfl

/-- Morphisms out of `G` are determined by their composition with `η`. -/
lemma hom_ext (η : F ⟶ P.op ⋙ G) (hLS : SectionsLocallyPulledBack K η)
    (hH : Presieve.IsSeparated K (H ⋙ forget (ModuleCat.{w} R))) {x y : G ⟶ H}
    (h : η ≫ Functor.whiskerLeft P.op x = η ≫ Functor.whiskerLeft P.op y) : x = y := by
  ext U s
  obtain ⟨S, hS, hS'⟩ := hLS U.unop s
  refine ext_of_isSeparated hH hS fun U' u hu ↦ ?_
  obtain ⟨V, t, φ, h'⟩ := hS' u hu
  have := congr_arg (fun f ↦ H.map φ.op (f.app (op V) t)) h
  simpa [← NatTrans.naturality_apply, h'] using this

end LocallyGenerated

/-- Let `P : C ⥤ D` be a continuous functor preserving binary products, with `C` having binary
products, and let `L ⊣ P.sheafPushforwardContinuous _ J K` be an adjunction. If
`η : F ⟶ P_* G` is such that every section of `G` is locally pulled back from `F` along `η`
and relations between such pulled back sections hold locally in `F`, then the adjoint morphism
`L F ⟶ G` of `η` is an isomorphism. -/
theorem isIso_homEquiv_symm_of_locally_generated {C : Type u₁} [Category.{v₁} C] {D : Type u₂}
    [Category.{v₂} D] {J : GrothendieckTopology C} {K : GrothendieckTopology D} (P : C ⥤ D)
    [P.IsContinuous J K] [HasBinaryProducts C] [PreservesLimitsOfShape (Discrete WalkingPair) P]
    {R : Type u} [Ring R] [K.HasSheafCompose (forget (ModuleCat.{w} R))]
    {F : Sheaf J (ModuleCat.{w} R)} {G : Sheaf K (ModuleCat.{w} R)}
    (η : F ⟶ (P.sheafPushforwardContinuous (ModuleCat.{w} R) J K).obj G)
    (hLS : ∀ (U : D) (s : G.obj.obj (op U)), ∃ S ∈ K U, ∀ ⦃U' : D⦄ (u : U' ⟶ U), S u →
      ∃ (V : C) (t : F.obj.obj (op V)) (φ : U' ⟶ P.obj V),
        G.obj.map u.op s = G.obj.map φ.op (η.hom.app (op V) t))
    (hWD : ∀ (V : C) (t : F.obj.obj (op V)) (U : D) (φ : U ⟶ P.obj V),
      G.obj.map φ.op (η.hom.app (op V) t) = 0 → ∃ S ∈ K U, ∀ ⦃U' : D⦄ (u : U' ⟶ U), S u →
        ∃ (V' : C) (a : V' ⟶ V) (φ' : U' ⟶ P.obj V'),
          F.obj.map a.op t = 0 ∧ φ' ≫ P.map a = u ≫ φ)
    {L : Sheaf J (ModuleCat.{w} R) ⥤ Sheaf K (ModuleCat.{w} R)}
    (adj : L ⊣ P.sheafPushforwardContinuous (ModuleCat.{w} R) J K) :
    IsIso ((adj.homEquiv F G).symm η) := by
  rw [isIso_iff_coyoneda_map_bijective]
  intro T
  have hT := (isSheaf_iff_isSheaf_of_type _ _).1 ((sheafCompose K (forget _)).obj T).2
  rw [← (adj.homEquiv F T).bijective.of_comp_iff']
  have e : (adj.homEquiv F T) ∘ (fun x ↦ (adj.homEquiv F G).symm η ≫ x) =
      fun x ↦ η ≫ (P.sheafPushforwardContinuous _ J K).map x := by
    ext x : 1
    simp [Adjunction.homEquiv_naturality_right]
  rw [e]
  have hP := LocallyGenerated.hasPairLifts_of_preservesLimitsOfShape (P := P)
  refine ⟨fun x y h ↦ Sheaf.hom_ext
    (LocallyGenerated.hom_ext η.hom hLS hT.isSeparated (congr_arg (·.hom) h)), fun ψ ↦ ?_⟩
  exact ⟨ObjectProperty.homMk (LocallyGenerated.lift η.hom ψ.hom hP hLS hWD hT),
    Sheaf.hom_ext (LocallyGenerated.lift_fac η.hom ψ.hom hP hLS hWD hT)⟩

end CategoryTheory
