import Langlands.Shimura.RestrictedLevelColimit
import Langlands.Shimura.LevelHeckeModule

/-! # Colimits over levels of presheaves of modules carrying a further action -/

noncomputable section

universe v w t u'' uH

set_option autoImplicit false

namespace Langlands.Shimura.RestrictedLevelColimit

open CategoryTheory CategoryTheory.Limits Opposite CompactOpenLevel LevelHecke

variable {G : Type v} [Group G] [TopologicalSpace G] {P : ObjectProperty (CompactOpenLevel G)}
  {R : Type t} [CommRing R] {Γ : Type u''} [Monoid Γ]

/-! ## The action of `Γ` on the underlying presheaf -/

section Presheaf

variable (F : P.FullSubcategoryᵒᵖ ⥤ Action (ModuleCat.{w} R) Γ)

/-- The underlying presheaf of modules of a level-trivial presheaf of modules with an action of
`Γ` is level-trivial. -/
theorem isLevelTrivial_forget (hF : IsLevelTrivial F) :
    IsLevelTrivial (F ⋙ Action.forget (ModuleCat.{w} R) Γ) := fun K k hk => by
  change (F.map (restrictedSelfArrow P K k hk).op).hom = 𝟙 _
  rw [hF K k hk]
  rfl

/-- The action of `γ ∈ Γ` at every level, as an endomorphism of the underlying presheaf of
modules. -/
def actionNatTrans (γ : Γ) :
    F ⋙ Action.forget (ModuleCat.{w} R) Γ ⟶ F ⋙ Action.forget (ModuleCat.{w} R) Γ where
  app U := (F.obj U).ρ γ
  naturality _ _ a := ((F.map a).comm γ).symm

@[simp] theorem actionNatTrans_app (γ : Γ) (U : P.FullSubcategoryᵒᵖ) :
    (actionNatTrans F γ).app U = (F.obj U).ρ γ := rfl

/-- A level-trivial presheaf of modules with an action of `Γ`, as a level-trivial presheaf of
modules with an action of `Γ` by endomorphisms of presheaves. -/
def levelTrivialAction (hF : IsLevelTrivial F) :
    Action (levelTrivialProperty P (ModuleCat.{w} R)).FullSubcategory Γ where
  V := ⟨F ⋙ Action.forget (ModuleCat.{w} R) Γ, isLevelTrivial_forget F hF⟩
  ρ :=
    { toFun γ := ObjectProperty.homMk (actionNatTrans F γ)
      map_one' := ObjectProperty.hom_ext _ (NatTrans.ext (funext fun U => (F.obj U).ρ.map_one))
      map_mul' γ δ :=
        ObjectProperty.hom_ext _ (NatTrans.ext (funext fun U => (F.obj U).ρ.map_mul γ δ)) }

end Presheaf

/-! ## The colimit as a smooth representation with a commuting action of `Γ` -/

section Colimit

variable [IsTopologicalGroup G] [IsConjStable P]
  [HasColimitsOfShape (RestrictedOrdered P)ᵒᵖ (ModuleCat.{w} R)]
  (F : P.FullSubcategoryᵒᵖ ⥤ Action (ModuleCat.{w} R) Γ) (hF : IsLevelTrivial F)

/-- The colimit over levels satisfying `P` of a level-trivial presheaf of modules with an action
of `Γ`: a smooth representation of `G`, on which `Γ` acts by morphisms of smooth
representations, through its action at every level. -/
def smoothRepAction : Action (SmoothRep.{t, v, w} R G) Γ :=
  ((smoothFunctor P R).mapAction Γ).obj (levelTrivialAction F hF)

theorem smoothRepAction_V :
    (smoothRepAction F hF).V =
      smoothRep (F ⋙ Action.forget (ModuleCat.{w} R) Γ) (isLevelTrivial_forget F hF) := rfl

/-- The action of `γ ∈ Γ` on a vector coming from level `U` is its action at level `U`. -/
theorem smoothRepAction_ρ_ι_apply (γ : Γ) (U : P.FullSubcategory) (x : (F.obj (op U)).V) :
    ((smoothRepAction F hF).ρ γ).hom.hom
        ((ι (F ⋙ Action.forget (ModuleCat.{w} R) Γ) U).hom x) =
      (ι (F ⋙ Action.forget (ModuleCat.{w} R) Γ) U).hom (((F.obj (op U)).ρ γ).hom x) :=
  congrArg (fun f => ModuleCat.Hom.hom f x) (ι_map (actionNatTrans F γ) U)

/-- The action of `g ∈ G` on a vector coming from level `U`: it comes from the conjugate level
`g U g⁻¹`, through the transition map of the arrow `g U g⁻¹ ⟶ U` with element `g`. -/
theorem smoothRepAction_representation_ι_apply (g : G) (U : P.FullSubcategory)
    (x : (F.obj (op U)).V) :
    (smoothRepAction F hF).V.obj.ρ g ((ι (F ⋙ Action.forget (ModuleCat.{w} R) Γ) U).hom x) =
      (ι (F ⋙ Action.forget (ModuleCat.{w} R) Γ) (restrictedConj P g U)).hom
        ((F.map (restrictedConjArrow P g U).op).hom.hom x) :=
  translate_ι_apply (F ⋙ Action.forget (ModuleCat.{w} R) Γ) g U x

/-- The actions of `G` and of `Γ` on the colimit commute. -/
theorem smoothRepAction_comm (γ : Γ) (g : G) (z : (smoothRepAction F hF).V) :
    ((smoothRepAction F hF).ρ γ).hom.hom ((smoothRepAction F hF).V.obj.ρ g z) =
      (smoothRepAction F hF).V.obj.ρ g (((smoothRepAction F hF).ρ γ).hom.hom z) :=
  Representation.IntertwiningMap.isIntertwining _ _ ((smoothRepAction F hF).ρ γ).hom.hom g z

/-! ### Fixed vectors -/

/-- Vectors coming from level `U` are fixed by `U`. -/
theorem ι_apply_mem_fixedVectors (U : P.FullSubcategory) (x : (F.obj (op U)).V) :
    (show (smoothRepAction F hF).V.obj.V from
        (ι (F ⋙ Action.forget (ModuleCat.{w} R) Γ) U).hom x) ∈
      fixedVectors (smoothRepAction F hF).V.obj.ρ U.obj.subgroup :=
  (Representation.mem_invariants _ _).mpr fun k =>
    translate_ι_apply_of_mem (F ⋙ Action.forget (ModuleCat.{w} R) Γ) (isLevelTrivial_forget F hF)
      k.property x

/-- The linear map from level `U` into the `U`-fixed vectors of the colimit. -/
def fixedLegLinear (U : P.FullSubcategory) :
    (F.obj (op U)).V →ₗ[R] fixedVectors (smoothRepAction F hF).V.obj.ρ U.obj.subgroup :=
  LinearMap.codRestrict _ (ι (F ⋙ Action.forget (ModuleCat.{w} R) Γ) U).hom
    (ι_apply_mem_fixedVectors F hF U)

@[simp] theorem fixedLegLinear_apply_coe (U : P.FullSubcategory) (x : (F.obj (op U)).V) :
    (fixedLegLinear F hF U x : (smoothRepAction F hF).V.obj.V) =
      (ι (F ⋙ Action.forget (ModuleCat.{w} R) Γ) U).hom x := rfl

/-- The map from level `U` into the `U`-fixed vectors of the colimit, equivariant for `Γ`. -/
def fixedLeg (U : P.FullSubcategory) :
    F.obj (op U) ⟶ (fixedVectorsActionFunctor R Γ U.obj.subgroup).obj (smoothRepAction F hF) where
  hom := ModuleCat.ofHom (fixedLegLinear F hF U)
  comm γ := by
    ext x
    exact Subtype.ext (smoothRepAction_ρ_ι_apply F hF γ U x).symm

theorem fixedLeg_hom (U : P.FullSubcategory) :
    (fixedLeg F hF U).hom = ModuleCat.ofHom (fixedLegLinear F hF U) := rfl

/-- The fixed-vector comparison at level `U` for a presheaf of modules `F₀`: the inclusion
`ι F₀ U` of level `U` into the colimit is injective, and its image is the set of vectors fixed
by every element of `U`. -/
def FixedVectorComparison (F₀ : P.FullSubcategoryᵒᵖ ⥤ ModuleCat.{w} R) (U : P.FullSubcategory) :
    Prop :=
  Function.Injective (ι F₀ U).hom ∧
    Set.range (ι F₀ U).hom = {z | ∀ u ∈ U.obj.subgroup, (translate F₀ u).hom z = z}

theorem fixedVectorComparison_iff_bijective (U : P.FullSubcategory) :
    FixedVectorComparison (F ⋙ Action.forget (ModuleCat.{w} R) Γ) U ↔
      Function.Bijective (fixedLegLinear F hF U) := by
  constructor
  · rintro ⟨hinj, hrange⟩
    refine ⟨fun x y h => hinj ?_, fun z => ?_⟩
    · have h' := congrArg Subtype.val h
      rwa [fixedLegLinear_apply_coe, fixedLegLinear_apply_coe] at h'
    · have hz : (z : (smoothRepAction F hF).V.obj.V) ∈
          Set.range (ι (F ⋙ Action.forget (ModuleCat.{w} R) Γ) U).hom := by
        rw [hrange]
        intro u hu
        exact (Representation.mem_invariants _ _).mp z.property ⟨u, hu⟩
      obtain ⟨x, hx⟩ := hz
      exact ⟨x, Subtype.ext ((fixedLegLinear_apply_coe F hF U x).trans hx)⟩
  · rintro ⟨hinj, hsurj⟩
    refine ⟨fun x y h => hinj (Subtype.ext ?_), Set.ext fun z => ⟨?_, fun hz => ?_⟩⟩
    · rwa [fixedLegLinear_apply_coe, fixedLegLinear_apply_coe]
    · rintro ⟨x, rfl⟩ u hu
      exact translate_ι_apply_of_mem (F ⋙ Action.forget (ModuleCat.{w} R) Γ)
        (isLevelTrivial_forget F hF) hu x
    · obtain ⟨x, hx⟩ := hsurj ⟨z, (Representation.mem_invariants _ _).mpr fun k => hz k k.property⟩
      exact ⟨x, (fixedLegLinear_apply_coe F hF U x).symm.trans (congrArg Subtype.val hx)⟩

/-- Under the fixed-vector comparison, level `U` is isomorphic to the `U`-fixed vectors of the
colimit, compatibly with the actions of `Γ`. -/
def fixedLegIso (U : P.FullSubcategory)
    (h : FixedVectorComparison (F ⋙ Action.forget (ModuleCat.{w} R) Γ) U) :
    F.obj (op U) ≅ (fixedVectorsActionFunctor R Γ U.obj.subgroup).obj (smoothRepAction F hF) :=
  Action.mkIso
    (LinearEquiv.ofBijective (fixedLegLinear F hF U)
      ((fixedVectorComparison_iff_bijective F hF U).mp h)).toModuleIso
    (fixedLeg F hF U).comm

@[simp] theorem fixedLegIso_hom (U : P.FullSubcategory)
    (h : FixedVectorComparison (F ⋙ Action.forget (ModuleCat.{w} R) Γ) U) :
    (fixedLegIso F hF U h).hom = fixedLeg F hF U := rfl

/-! ### The Hecke algebra on fixed vectors -/

/-- The `K`-fixed vectors of the colimit, as a module over the Hecke algebra of `K`, with the
commuting action of `Γ`. -/
abbrev heckeModule (K : Subgroup G) : Action (ModuleCat.{w} (LevelHeckeAlgebra R K)) Γ :=
  (heckeModuleActionFunctor R Γ K).obj (smoothRepAction F hF)

/-- Each element of `Γ` commutes with the Hecke algebra on fixed vectors. -/
theorem heckeModule_ρ_smul (K : Subgroup G) (γ : Γ) (a : LevelHeckeAlgebra R K)
    (x : (heckeModule F hF K).V) :
    ((heckeModule F hF K).ρ γ).hom (a • x) = a • ((heckeModule F hF K).ρ γ).hom x :=
  heckeModuleActionFunctor_ρ_smul Γ K (smoothRepAction F hF) γ a x

/-- The double-coset element `[K g K]` acts on the `K`-fixed vectors as the double-coset
operator. -/
theorem doubleCoset_smul_heckeModule (K : CompactOpenLevel G) (g : G)
    (x : fixedVectors (smoothRepAction F hF).V.obj.ρ K.subgroup) :
    (doubleCoset K g : LevelHeckeAlgebra R K.subgroup) •
        (show (heckeModule F hF K.subgroup).V from x) =
      heckeOperator (smoothRepAction F hF).V.obj.ρ K K g x :=
  doubleCoset_smul _ K g x

end Colimit

/-! ## Restriction along a continuous homomorphism -/

section Pullback

variable {H : Type uH} [Group H] [TopologicalSpace H] (φ : H →* G) (hφ : Continuous φ)

variable (R) in
/-- Smooth representations of `G` restricted along a continuous homomorphism `φ : H →* G`,
keeping the carrier: `h ∈ H` acts as `φ h`. -/
def smoothRepPullback : SmoothRep.{t, v, w} R G ⥤ SmoothRep.{t, uH, w} R H :=
  (smoothRepProperty R H).lift (SmoothRep.toRep ⋙ Rep.resFunctor φ)
    (fun A => isSmooth_comp φ hφ A.isSmooth)

@[simp] theorem smoothRepPullback_obj_ρ (A : SmoothRep.{t, v, w} R G) (h : H) :
    ((smoothRepPullback R φ hφ).obj A).obj.ρ h = A.obj.ρ (φ h) := rfl

/-- The vectors of the restriction fixed by `K' ≤ H` are the vectors fixed by the image of
`K'` in `G`. -/
theorem fixedVectors_smoothRepPullback (A : SmoothRep.{t, v, w} R G) (K' : Subgroup H) :
    fixedVectors ((smoothRepPullback R φ hφ).obj A).obj.ρ K' =
      fixedVectors A.obj.ρ (K'.map φ) := by
  ext v
  simp only [fixedVectors, Representation.mem_invariants]
  constructor
  · rintro hv ⟨g, hg⟩
    obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.mp hg
    exact hv ⟨h, hh⟩
  · intro hv h
    exact hv ⟨φ h, Subgroup.mem_map_of_mem φ h.property⟩

variable (R Γ) in
/-- If `K'` maps onto `K` under `φ`, the `K'`-fixed vectors of the restriction along `φ` are
the `K`-fixed vectors, compatibly with the action of `Γ`. -/
def fixedVectorsPullbackIso (A : Action (SmoothRep.{t, v, w} R G) Γ) {K' : Subgroup H}
    {K : Subgroup G} (hK : K'.map φ = K) :
    (fixedVectorsActionFunctor R Γ K').obj (((smoothRepPullback R φ hφ).mapAction Γ).obj A) ≅
      (fixedVectorsActionFunctor R Γ K).obj A :=
  Action.mkIso
    (LinearEquiv.ofEq _ _ ((fixedVectors_smoothRepPullback φ hφ A.V K').trans
      (congrArg (fixedVectors A.V.obj.ρ) hK))).toModuleIso
    (fun _ => rfl)

@[simp] theorem fixedVectorsPullbackIso_hom_apply_coe (A : Action (SmoothRep.{t, v, w} R G) Γ)
    {K' : Subgroup H} {K : Subgroup G} (hK : K'.map φ = K)
    (x : fixedVectors ((smoothRepPullback R φ hφ).obj A.V).obj.ρ K') :
    Subtype.val (show fixedVectors A.V.obj.ρ K from
        (fixedVectorsPullbackIso R Γ φ hφ A hK).hom.hom x) = Subtype.val x := rfl

end Pullback

/-! ## The colimit restricted along a continuous homomorphism -/

section ColimitPullback

variable [IsTopologicalGroup G] [IsConjStable P]
  [HasColimitsOfShape (RestrictedOrdered P)ᵒᵖ (ModuleCat.{w} R)]
  (F : P.FullSubcategoryᵒᵖ ⥤ Action (ModuleCat.{w} R) Γ) (hF : IsLevelTrivial F)
  {H : Type uH} [Group H] [TopologicalSpace H] (φ : H →* G) (hφ : Continuous φ)

/-- The colimit with its action of `Γ`, as a smooth representation of `H` through the
continuous homomorphism `φ : H →* G`. -/
def smoothRepActionPullback : Action (SmoothRep.{t, uH, w} R H) Γ :=
  ((smoothRepPullback R φ hφ).mapAction Γ).obj (smoothRepAction F hF)

/-- If `K' ≤ H` maps onto the level `U` under `φ`, the map from level `U` into the `K'`-fixed
vectors of the restricted colimit, equivariant for `Γ`. -/
def fixedLegPullback (U : P.FullSubcategory) {K' : Subgroup H} (hK : K'.map φ = U.obj.subgroup) :
    F.obj (op U) ⟶ (fixedVectorsActionFunctor R Γ K').obj (smoothRepActionPullback F hF φ hφ) :=
  fixedLeg F hF U ≫ (fixedVectorsPullbackIso R Γ φ hφ (smoothRepAction F hF) hK).inv

/-- Under the fixed-vector comparison, level `U` is isomorphic to the `K'`-fixed vectors of the
restricted colimit, compatibly with the actions of `Γ`. -/
def fixedLegPullbackIso (U : P.FullSubcategory) {K' : Subgroup H}
    (hK : K'.map φ = U.obj.subgroup)
    (h : FixedVectorComparison (F ⋙ Action.forget (ModuleCat.{w} R) Γ) U) :
    F.obj (op U) ≅ (fixedVectorsActionFunctor R Γ K').obj (smoothRepActionPullback F hF φ hφ) :=
  fixedLegIso F hF U h ≪≫ (fixedVectorsPullbackIso R Γ φ hφ (smoothRepAction F hF) hK).symm

@[simp] theorem fixedLegPullbackIso_hom (U : P.FullSubcategory) {K' : Subgroup H}
    (hK : K'.map φ = U.obj.subgroup)
    (h : FixedVectorComparison (F ⋙ Action.forget (ModuleCat.{w} R) Γ) U) :
    (fixedLegPullbackIso F hF φ hφ U hK h).hom = fixedLegPullback F hF φ hφ U hK := rfl

end ColimitPullback

end Langlands.Shimura.RestrictedLevelColimit
