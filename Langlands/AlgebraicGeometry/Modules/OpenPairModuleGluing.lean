import Langlands.AlgebraicGeometry.Modules.OpenCoverModuleGluingProof

/-! # Gluing two module sheaves from one overlap identification -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

noncomputable section

namespace Langlands.Scheme.Modules.OpenPairModuleGluing

open AlgebraicGeometry.Scheme.Modules (pushforward restrictFunctor restrictFunctorIsoPullback
  restrictAdjunction pushforwardComp pushforwardCongr)
open OpenCoverModuleGluing (res_res res_bijective secFun)

variable {X Y Z : AlgebraicGeometry.Scheme.{u}} (f : Y ⟶ X) (g : Z ⟶ X)
  [IsOpenImmersion f] [IsOpenImmersion g] (M : Y.Modules) (N : Z.Modules)
  (φ : (Scheme.Modules.pullback (pullback.fst f g)).obj M ≅
    (Scheme.Modules.pullback (pullback.snd f g)).obj N)

/-- The given overlap isomorphism, expressed using restriction. -/
def overlap :
    M.restrict (pullback.fst f g) ≅ N.restrict (pullback.snd f g) :=
  (restrictFunctorIsoPullback _).app M ≪≫ φ ≪≫
    ((restrictFunctorIsoPullback _).app N).symm

/-- The common target of the two maps imposing the overlap relation. -/
def target : X.Modules :=
  (pushforward f).obj ((pushforward (pullback.fst f g)).obj
    (N.restrict (pullback.snd f g)))

/-- Restrict the left piece and apply the prescribed overlap identification. -/
def leftMap : (pushforward f).obj M ⟶ target f g N :=
  (pushforward f).map
    ((restrictAdjunction (pullback.fst f g)).unit.app M ≫
      (pushforward (pullback.fst f g)).map (overlap f g M N φ).hom)

/-- Compare the two iterated pushforwards from the overlap. -/
def pushforwardOverlap (P : (pullback f g).Modules) :
    (pushforward g).obj ((pushforward (pullback.snd f g)).obj P) ≅
      (pushforward f).obj ((pushforward (pullback.fst f g)).obj P) :=
  (pushforwardComp (pullback.snd f g) g).app P ≪≫
    (pushforwardCongr pullback.condition.symm).app P ≪≫
      ((pushforwardComp (pullback.fst f g) f).app P).symm

/-- Restrict the right piece and express its pushforward in the common target. -/
def rightMap : (pushforward g).obj N ⟶ target f g N :=
  (pushforward g).map ((restrictAdjunction (pullback.snd f g)).unit.app N) ≫
    (pushforwardOverlap f g (N.restrict (pullback.snd f g))).hom

/-- The actual module sheaf whose sections are compatible pairs. -/
def glued : X.Modules := pullback (leftMap f g M N φ) (rightMap f g N)

/-- Projection to the left pushed-forward piece. -/
def leftProj : glued f g M N φ ⟶ (pushforward f).obj M :=
  pullback.fst _ _

/-- Projection to the right pushed-forward piece. -/
def rightProj : glued f g M N φ ⟶ (pushforward g).obj N :=
  pullback.snd _ _

lemma leftMap_app (O : X.Opens) (x : Γ((pushforward f).obj M, O)) :
    (leftMap f g M N φ).app O x =
      (overlap f g M N φ).hom.app ((pullback.fst f g) ⁻¹ᵁ f ⁻¹ᵁ O)
        (M.presheaf.map
          (homOfLE ((pullback.fst f g).image_preimage_le (f ⁻¹ᵁ O))).op x) :=
  rfl

omit [IsOpenImmersion g] in
lemma rightMap_app (O : X.Opens) (y : Γ((pushforward g).obj N, O))
    (r : op (g ⁻¹ᵁ O) ⟶ op ((pullback.snd f g) ''ᵁ
      ((pullback.fst f g) ⁻¹ᵁ f ⁻¹ᵁ O))) :
    (rightMap f g N).app O y = N.presheaf.map r y := by
  simp only [rightMap, pushforwardOverlap, Scheme.Modules.Hom.comp_app, Iso.trans_hom,
    Iso.symm_hom, Iso.app_hom, Iso.app_inv, Scheme.Modules.pushforward_map_app,
    Scheme.Modules.restrictAdjunction_unit_app_app, Scheme.Modules.pushforwardComp_hom_app_app,
    Scheme.Modules.pushforwardComp_inv_app_app, Scheme.Modules.pushforwardCongr_hom_app_app]
  simp only [ConcreteCategory.comp_apply]
  exact res_res N _ _ r y

omit [IsOpenImmersion f] [IsOpenImmersion g] in
lemma preimage_overlap (O : X.Opens) :
    (pullback.fst f g) ⁻¹ᵁ f ⁻¹ᵁ O = (pullback.snd f g) ⁻¹ᵁ g ⁻¹ᵁ O := by
  rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, pullback.condition]

omit [IsOpenImmersion f] in
lemma le_image_fst {O : X.Opens} (hO : O ≤ g.opensRange) :
    f ⁻¹ᵁ O ≤ (pullback.fst f g) ''ᵁ ((pullback.fst f g) ⁻¹ᵁ f ⁻¹ᵁ O) := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Hom.opensRange_pullbackFst]
  exact le_inf (Scheme.Hom.preimage_mono _ hO) le_rfl

omit [IsOpenImmersion g] in
lemma image_snd_le (O : X.Opens) :
    (pullback.snd f g) ''ᵁ ((pullback.fst f g) ⁻¹ᵁ f ⁻¹ᵁ O) ≤ g ⁻¹ᵁ O := by
  rw [preimage_overlap]
  exact Scheme.Hom.image_preimage_le _ _

omit [IsOpenImmersion g] in
lemma le_image_snd {O : X.Opens} (hO : O ≤ f.opensRange) :
    g ⁻¹ᵁ O ≤ (pullback.snd f g) ''ᵁ ((pullback.fst f g) ⁻¹ᵁ f ⁻¹ᵁ O) := by
  rw [preimage_overlap, Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.Hom.opensRange_pullbackSnd]
  exact le_inf (Scheme.Hom.preimage_mono _ hO) le_rfl

lemma leftMap_bijective {O : X.Opens} (hO : O ≤ g.opensRange) :
    Function.Bijective ((leftMap f g M N φ).app O) := by
  have e : ⇑((leftMap f g M N φ).app O) =
      (overlap f g M N φ).hom.app _ ∘ M.presheaf.map
        (homOfLE ((pullback.fst f g).image_preimage_le (f ⁻¹ᵁ O))).op :=
    funext (leftMap_app f g M N φ O)
  rw [e]
  exact (ConcreteCategory.bijective_of_isIso _).comp (res_bijective _ _
    (le_antisymm (le_image_fst f g hO) (Scheme.Hom.image_preimage_le _ _)))

omit [IsOpenImmersion g] in
lemma rightMap_bijective {O : X.Opens} (hO : O ≤ f.opensRange) :
    Function.Bijective ((rightMap f g N).app O) := by
  have e : ⇑((rightMap f g N).app O) =
      N.presheaf.map (homOfLE (image_snd_le f g O)).op :=
    funext fun y ↦ rightMap_app f g N O y _
  rw [e]
  exact res_bijective _ _ (le_antisymm (le_image_snd f g hO) (image_snd_le f g O))

private lemma pullback_fst_bijective {A B H : X.Modules} (a : A ⟶ H) (b : B ⟶ H)
    (O : X.Opens) (hb : Function.Bijective (b.app O)) :
    Function.Bijective ((pullback.fst a b).app O) := by
  have : IsIso ((secFun O).map b) := (CategoryTheory.isIso_iff_bijective _).2 hb
  have : IsIso ((secFun O).map (pullback.fst a b)) :=
    ((IsPullback.of_hasPullback a b).map (secFun O)).isIso_fst_of_isIso
  exact (CategoryTheory.isIso_iff_bijective ((secFun O).map (pullback.fst a b))).1
    inferInstance

private lemma pullback_snd_bijective {A B H : X.Modules} (a : A ⟶ H) (b : B ⟶ H)
    (O : X.Opens) (ha : Function.Bijective (a.app O)) :
    Function.Bijective ((pullback.snd a b).app O) := by
  have : IsIso ((secFun O).map a) := (CategoryTheory.isIso_iff_bijective _).2 ha
  have : IsIso ((secFun O).map (pullback.snd a b)) :=
    ((IsPullback.of_hasPullback a b).map (secFun O)).isIso_snd_of_isIso
  exact (CategoryTheory.isIso_iff_bijective ((secFun O).map (pullback.snd a b))).1
    inferInstance

lemma leftProj_bijective {O : X.Opens} (hO : O ≤ f.opensRange) :
    Function.Bijective ((leftProj f g M N φ).app O) :=
  pullback_fst_bijective _ _ O (rightMap_bijective f g N hO)

lemma rightProj_bijective {O : X.Opens} (hO : O ≤ g.opensRange) :
    Function.Bijective ((rightProj f g M N φ).app O) :=
  pullback_snd_bijective _ _ O (leftMap_bijective f g M N φ hO)

section RestrictionProjection

variable {F : X.Modules} (π : F ⟶ (pushforward f).obj M)

/-- The restriction of a projection to a pushed-forward piece. -/
def restrictProj : F.restrict f ⟶ M :=
  (restrictFunctor f).map π ≫ (restrictAdjunction f).counit.app M

lemma restrictProj_app (W : Y.Opens) (y : Γ(F, f ''ᵁ W))
    (r : op (f ⁻¹ᵁ f ''ᵁ W) ⟶ op W) :
    (restrictProj f M π).app W y = M.presheaf.map r (π.app (f ''ᵁ W) y) := by
  rw [presheaf_map_subsingleton M.presheaf r (eqToHom (f.preimage_image_eq W).symm).op]
  rfl

lemma restrictProj_map_app (W : Y.Opens) {O : X.Opens} (hle : f ''ᵁ W ≤ O)
    (x : Γ(F, O)) (r : op (f ⁻¹ᵁ O) ⟶ op W) :
    (restrictProj f M π).app W (F.presheaf.map (homOfLE hle).op x) =
      M.presheaf.map r (π.app O x) := by
  rw [restrictProj_app f M π W _ (eqToHom (f.preimage_image_eq W).symm).op,
    ← OpenCoverHomGluing.hom_map_app]
  exact res_res M _ _ r _

lemma restrictProj_isIso
    (hπ : ∀ (O : X.Opens), O ≤ f.opensRange → Function.Bijective (π.app O)) :
    IsIso (restrictProj f M π) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro W
  apply (ConcreteCategory.isIso_iff_bijective _).2
  have e : ⇑((restrictProj f M π).app W) =
      M.presheaf.map (eqToHom (f.preimage_image_eq W).symm).op ∘ π.app (f ''ᵁ W) :=
    funext fun y ↦ restrictProj_app f M π W y _
  rw [e]
  exact (res_bijective _ _ (f.preimage_image_eq W)).comp (hπ _ (f.image_le_opensRange W))

end RestrictionProjection

/-- The actual pullback of the glued module to the left chart is the left piece. -/
def leftIso : (Scheme.Modules.pullback f).obj (glued f g M N φ) ≅ M :=
  haveI := restrictProj_isIso f M (leftProj f g M N φ)
    (fun _ hO ↦ leftProj_bijective f g M N φ hO)
  ((restrictFunctorIsoPullback f).app _).symm ≪≫
    asIso (restrictProj f M (leftProj f g M N φ))

/-- The actual pullback of the glued module to the right chart is the right piece. -/
def rightIso : (Scheme.Modules.pullback g).obj (glued f g M N φ) ≅ N :=
  haveI := restrictProj_isIso g N (rightProj f g M N φ)
    (fun _ hO ↦ rightProj_bijective f g M N φ hO)
  ((restrictFunctorIsoPullback g).app _).symm ≪≫
    asIso (restrictProj g N (rightProj f g M N φ))

lemma proj_condition_apply (O : X.Opens) (x : Γ(glued f g M N φ, O)) :
    (leftMap f g M N φ).app O ((leftProj f g M N φ).app O x) =
      (rightMap f g N).app O ((rightProj f g M N φ).app O x) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    ← Scheme.Modules.Hom.comp_app, ← Scheme.Modules.Hom.comp_app]
  exact congrArg (fun k : glued f g M N φ ⟶ target f g N => k.app O x)
    (pullback.condition (f := leftMap f g M N φ) (g := rightMap f g N))

/-- The relation imposed by the pullback holds after restriction to every overlap open. -/
lemma relation_restrict {O : X.Opens} {x : Γ((pushforward f).obj M, O)}
    {y : Γ((pushforward g).obj N, O)}
    (hr : (leftMap f g M N φ).app O x = (rightMap f g N).app O y)
    (A : (pullback f g).Opens)
    (hA : A ≤ (pullback.fst f g) ⁻¹ᵁ f ⁻¹ᵁ O)
    (r : op (f ⁻¹ᵁ O) ⟶ op ((pullback.fst f g) ''ᵁ A))
    (r' : op (g ⁻¹ᵁ O) ⟶ op ((pullback.snd f g) ''ᵁ A)) :
    (overlap f g M N φ).hom.app A (M.presheaf.map r x) =
      N.presheaf.map r' y := by
  have h := congrArg ((N.restrict (pullback.snd f g)).presheaf.map (homOfLE hA).op) hr
  rw [leftMap_app, rightMap_app f g N O y (homOfLE (image_snd_le f g O)).op,
    OpenCoverHomGluing.hom_map_app, Scheme.Modules.restrict_map,
    Scheme.Modules.restrict_map] at h
  exact (congrArg _ (res_res M _ _ r x).symm).trans (h.trans (res_res N _ _ r' y))

/-- The comparison maps are compatible on the overlap, read on iterated restrictions. -/
lemma restrict_compat :
    (restrictCompIso (pullback.fst f g) f (pullback.fst f g ≫ f) rfl).hom.app
        (glued f g M N φ) ≫
      (restrictFunctor (pullback.fst f g)).map
        (restrictProj f M (leftProj f g M N φ)) ≫ (overlap f g M N φ).hom =
    (restrictCompIso (pullback.snd f g) g (pullback.fst f g ≫ f)
        pullback.condition.symm).hom.app (glued f g M N φ) ≫
      (restrictFunctor (pullback.snd f g)).map
        (restrictProj g N (rightProj f g M N φ)) := by
  refine OpenCoverModuleGluing.restrict_square_ext _ _ _ _ pullback.condition _ _ _
    fun A x => ?_
  have hA : A ≤ (pullback.fst f g) ⁻¹ᵁ f ⁻¹ᵁ ((pullback.fst f g ≫ f) ''ᵁ A) :=
    ((pullback.fst f g ≫ f).preimage_image_eq A).ge
  rw [restrictProj_map_app f M _ _ _ x
      (homOfLE (OpenCoverModuleGluing.image_le_of_le_preimage _ hA)).op,
    restrictProj_map_app g N _ _ _ x
      (homOfLE ((Scheme.Hom.image_mono _ hA).trans (image_snd_le f g _))).op]
  exact relation_restrict f g M N φ (proj_condition_apply f g M N φ _ x) A hA _ _

lemma restrictFunctorIsoPullback_hom_leftIso_hom :
    (restrictFunctorIsoPullback f).hom.app (glued f g M N φ) ≫ (leftIso f g M N φ).hom =
      restrictProj f M (leftProj f g M N φ) :=
  Iso.hom_inv_id_app_assoc _ _ _

lemma restrictFunctorIsoPullback_hom_rightIso_hom :
    (restrictFunctorIsoPullback g).hom.app (glued f g M N φ) ≫ (rightIso f g M N φ).hom =
      restrictProj g N (rightProj f g M N φ) :=
  Iso.hom_inv_id_app_assoc _ _ _

/-- The actual pullback comparisons realize precisely the prescribed overlap isomorphism. -/
lemma compatible :
    (Scheme.Modules.pullback (pullback.fst f g)).map (leftIso f g M N φ).hom ≫ φ.hom =
      (squarePullbackIso g (pullback.fst f g) (pullback.snd f g) f pullback.condition
        (glued f g M N φ)).hom ≫
          (Scheme.Modules.pullback (pullback.snd f g)).map (rightIso f g M N φ).hom := by
  refine OpenCoverModuleGluing.pullback_compat_of_restrict _ _ _ _ pullback.condition _ _ _ ?_
  rw [restrictFunctorIsoPullback_hom_leftIso_hom,
    restrictFunctorIsoPullback_hom_rightIso_hom]
  exact restrict_compat f g M N φ

end Langlands.Scheme.Modules.OpenPairModuleGluing
