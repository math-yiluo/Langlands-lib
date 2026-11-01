import Langlands.AlgebraicGeometry.Modules.OpenCoverModuleGluingStatement
import Langlands.AlgebraicGeometry.Modules.OpenCoverHomGluing

/-! # Gluing actual module sheaves over a scheme open cover -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

noncomputable section

namespace Langlands.Scheme.Modules.OpenCoverModuleGluing

open AlgebraicGeometry.Scheme.Modules (pushforward restrictFunctor restrictFunctorIsoPullback
  restrictAdjunction pushforwardComp pushforwardCongr)

section Restriction

variable {T : AlgebraicGeometry.Scheme.{u}}

/-- Two composable restriction maps compose to any restriction map with the same ends. -/
lemma res_res (F : T.Modules) {A B C : T.Opensᵒᵖ} (p : A ⟶ B) (q : B ⟶ C) (r : A ⟶ C)
    (x : F.presheaf.obj A) :
    F.presheaf.map q (F.presheaf.map p x) = F.presheaf.map r x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp,
    presheaf_map_subsingleton F.presheaf (p ≫ q) r]

/-- A restriction map from an open to itself is the identity. -/
lemma res_self (F : T.Modules) {A : T.Opensᵒᵖ} (p : A ⟶ A) (x : F.presheaf.obj A) :
    F.presheaf.map p x = x := by
  rw [presheaf_map_subsingleton F.presheaf p (𝟙 _), CategoryTheory.Functor.map_id]
  rfl

/-- A restriction map between equal opens is bijective. -/
lemma res_bijective (F : T.Modules) {A B : T.Opens} (p : op A ⟶ op B) (h : A = B) :
    Function.Bijective (F.presheaf.map p) := by
  subst h
  rw [presheaf_map_subsingleton F.presheaf p (𝟙 _), CategoryTheory.Functor.map_id]
  exact ⟨fun x y hxy => hxy, fun y => ⟨y, rfl⟩⟩

end Restriction

variable {X : AlgebraicGeometry.Scheme.{u}} (𝒰 : X.OpenCover.{u})
  (M : ∀ i, (𝒰.X i).Modules)
  (φ : ∀ i j,
    (AlgebraicGeometry.Scheme.Modules.pullback (pullback.fst (𝒰.f i) (𝒰.f j))).obj (M i) ≅
      (AlgebraicGeometry.Scheme.Modules.pullback (pullback.snd (𝒰.f i) (𝒰.f j))).obj (M j))

/-- The overlap isomorphisms, read on restrictions instead of pullbacks. -/
def φr (i j : 𝒰.I₀) :
    (M i).restrict (pullback.fst (𝒰.f i) (𝒰.f j)) ≅
      (M j).restrict (pullback.snd (𝒰.f i) (𝒰.f j)) :=
  (restrictFunctorIsoPullback _).app (M i) ≪≫ φ i j ≪≫
    ((restrictFunctorIsoPullback _).app (M j)).symm

/-- The pushforward of a piece to the whole scheme. -/
def G (i : 𝒰.I₀) : X.Modules := (pushforward (𝒰.f i)).obj (M i)

/-- The pushforward of the restriction of the `j`-th piece to the overlap `(i, j)`. -/
def H (i j : 𝒰.I₀) : X.Modules :=
  (pushforward (𝒰.f i)).obj ((pushforward (pullback.fst (𝒰.f i) (𝒰.f j))).obj
    ((M j).restrict (pullback.snd (𝒰.f i) (𝒰.f j))))

/-- Restrict the `i`-th piece to the overlap and apply the overlap isomorphism. -/
def aMap (i j : 𝒰.I₀) : G 𝒰 M i ⟶ H 𝒰 M i j :=
  (pushforward (𝒰.f i)).map
    ((restrictAdjunction (pullback.fst (𝒰.f i) (𝒰.f j))).unit.app (M i) ≫
      (pushforward (pullback.fst (𝒰.f i) (𝒰.f j))).map (φr 𝒰 M φ i j).hom)

/-- The comparison of the two iterated pushforwards from the overlap. -/
def overlapIso (i j : 𝒰.I₀) (F : (pullback (𝒰.f i) (𝒰.f j)).Modules) :
    (pushforward (𝒰.f j)).obj ((pushforward (pullback.snd (𝒰.f i) (𝒰.f j))).obj F) ≅
      (pushforward (𝒰.f i)).obj ((pushforward (pullback.fst (𝒰.f i) (𝒰.f j))).obj F) :=
  (pushforwardComp (pullback.snd (𝒰.f i) (𝒰.f j)) (𝒰.f j)).app F ≪≫
    (pushforwardCongr (pullback.condition (f := 𝒰.f i) (g := 𝒰.f j)).symm).app F ≪≫
    ((pushforwardComp (pullback.fst (𝒰.f i) (𝒰.f j)) (𝒰.f i)).app F).symm

/-- Restrict the `j`-th piece to the overlap. -/
def bMap (i j : 𝒰.I₀) : G 𝒰 M j ⟶ H 𝒰 M i j :=
  (pushforward (𝒰.f j)).map
      ((restrictAdjunction (pullback.snd (𝒰.f i) (𝒰.f j))).unit.app (M j)) ≫
    (overlapIso 𝒰 i j ((M j).restrict (pullback.snd (𝒰.f i) (𝒰.f j)))).hom

lemma aMap_app (i j : 𝒰.I₀) (O : X.Opens) (x : Γ(G 𝒰 M i, O)) :
    (aMap 𝒰 M φ i j).app O x =
      (φr 𝒰 M φ i j).hom.app ((pullback.fst (𝒰.f i) (𝒰.f j)) ⁻¹ᵁ (𝒰.f i) ⁻¹ᵁ O)
        ((M i).presheaf.map
          (homOfLE ((pullback.fst (𝒰.f i) (𝒰.f j)).image_preimage_le _)).op x) :=
  rfl

lemma bMap_app (i j : 𝒰.I₀) (O : X.Opens) (y : Γ(G 𝒰 M j, O))
    (r : op ((𝒰.f j) ⁻¹ᵁ O) ⟶
      op ((pullback.snd (𝒰.f i) (𝒰.f j)) ''ᵁ
        ((pullback.fst (𝒰.f i) (𝒰.f j)) ⁻¹ᵁ (𝒰.f i) ⁻¹ᵁ O))) :
    (bMap 𝒰 M i j).app O y = (M j).presheaf.map r y := by
  simp only [bMap, overlapIso, Scheme.Modules.Hom.comp_app, Iso.trans_hom, Iso.symm_hom,
    Iso.app_hom, Iso.app_inv, Scheme.Modules.pushforward_map_app,
    Scheme.Modules.restrictAdjunction_unit_app_app, Scheme.Modules.pushforwardComp_hom_app_app,
    Scheme.Modules.pushforwardComp_inv_app_app, Scheme.Modules.pushforwardCongr_hom_app_app]
  simp only [ConcreteCategory.comp_apply]
  exact res_res (M j) _ _ r y

/-- The gluing diagram: the pieces pushed forward to `X`, compared on all ordered overlaps. -/
def index : MulticospanIndex (MulticospanShape.prod 𝒰.I₀) X.Modules where
  left := G 𝒰 M
  right p := H 𝒰 M p.1 p.2
  fst p := aMap 𝒰 M φ p.1 p.2
  snd p := bMap 𝒰 M p.1 p.2

/-- The glued module. -/
def glued : X.Modules := multiequalizer (index 𝒰 M φ)

/-- The projection of the glued module to the `k`-th pushed forward piece. -/
def proj (k : 𝒰.I₀) : glued 𝒰 M φ ⟶ G 𝒰 M k := Multiequalizer.ι (index 𝒰 M φ) k

lemma proj_condition (i j : 𝒰.I₀) :
    proj 𝒰 M φ i ≫ aMap 𝒰 M φ i j = proj 𝒰 M φ j ≫ bMap 𝒰 M i j :=
  Multiequalizer.condition (index 𝒰 M φ) (i, j)

lemma proj_condition_apply (i j : 𝒰.I₀) (O : X.Opens) (x : Γ(glued 𝒰 M φ, O)) :
    (aMap 𝒰 M φ i j).app O ((proj 𝒰 M φ i).app O x) =
      (bMap 𝒰 M i j).app O ((proj 𝒰 M φ j).app O x) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    ← Scheme.Modules.Hom.comp_app, ← Scheme.Modules.Hom.comp_app, proj_condition]

/-- Sections over an open, as a functor to types. -/
def secFun (O : X.Opens) : X.Modules ⥤ Type u :=
  Scheme.Modules.toPresheaf X ⋙ (evaluation _ _).obj (op O) ⋙ forget Ab

instance (O : X.Opens) : PreservesLimits (secFun (X := X) O) := by
  have h₁ : PreservesLimits (Scheme.Modules.toPresheaf X) := inferInstance
  have h₂ : PreservesLimits ((evaluation X.Opensᵒᵖ Ab.{u}).obj (op O)) := inferInstance
  have h₃ : PreservesLimits (forget Ab.{u}) := inferInstance
  have h₄ : PreservesLimits ((evaluation X.Opensᵒᵖ Ab.{u}).obj (op O) ⋙ forget Ab.{u}) :=
    comp_preservesLimits _ _
  exact comp_preservesLimits (Scheme.Modules.toPresheaf X) _

/-- Sections of the glued module are determined by their projections. -/
lemma proj_ext (O : X.Opens) (x y : Γ(glued 𝒰 M φ, O))
    (h : ∀ k, (proj 𝒰 M φ k).app O x = (proj 𝒰 M φ k).app O y) : x = y := by
  let hc := isLimitOfPreserves (secFun (X := X) O) (limit.isLimit (index 𝒰 M φ).multicospan)
  apply (Types.isLimitEquivSections hc).injective
  apply Subtype.ext
  funext j
  rcases j with k | p
  · exact h k
  · have hw := limit.w (index 𝒰 M φ).multicospan (WalkingMulticospan.Hom.fst p)
    change (secFun O).map (limit.π _ _) x = (secFun O).map (limit.π _ _) y
    rw [← hw, Functor.map_comp, types_comp_apply, types_comp_apply]
    exact congrArg _ (h p.1)

/-- Compatible families of sections of the pieces come from sections of the glued module. -/
lemma proj_exists (O : X.Opens) (s : ∀ k, Γ(G 𝒰 M k, O))
    (hs : ∀ i j, (aMap 𝒰 M φ i j).app O (s i) = (bMap 𝒰 M i j).app O (s j)) :
    ∃ x : Γ(glued 𝒰 M φ, O), ∀ k, (proj 𝒰 M φ k).app O x = s k := by
  let hc := isLimitOfPreserves (secFun (X := X) O) (limit.isLimit (index 𝒰 M φ).multicospan)
  let sec : ((index 𝒰 M φ).multicospan ⋙ secFun O).sections :=
    ⟨fun j => match j with
      | WalkingMulticospan.left k => s k
      | WalkingMulticospan.right p => (aMap 𝒰 M φ p.1 p.2).app O (s p.1), by
      rintro (a | b) (a' | b') (f | f | f)
      · simp only [WalkingMulticospan.Hom.id_eq_id]; rfl
      · rfl
      · exact (hs b'.1 b'.2).symm
      · simp only [WalkingMulticospan.Hom.id_eq_id]; rfl⟩
  exact ⟨(Types.isLimitEquivSections hc).symm sec, fun k =>
    Types.isLimitEquivSections_symm_apply hc sec (WalkingMulticospan.left k)⟩

section Bijective

/-- The two preimages of an open of `X` in an overlap agree. -/
lemma preimage_fst_eq (i j : 𝒰.I₀) (O : X.Opens) :
    pullback.fst (𝒰.f i) (𝒰.f j) ⁻¹ᵁ (𝒰.f i) ⁻¹ᵁ O =
      pullback.snd (𝒰.f i) (𝒰.f j) ⁻¹ᵁ (𝒰.f j) ⁻¹ᵁ O := by
  rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, pullback.condition]

lemma le_image_fst (i j : 𝒰.I₀) {O : X.Opens} (hO : O ≤ (𝒰.f j).opensRange) :
    (𝒰.f i) ⁻¹ᵁ O ≤ pullback.fst (𝒰.f i) (𝒰.f j) ''ᵁ
      (pullback.fst (𝒰.f i) (𝒰.f j) ⁻¹ᵁ (𝒰.f i) ⁻¹ᵁ O) := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Hom.opensRange_pullbackFst]
  exact le_inf (Scheme.Hom.preimage_mono _ hO) le_rfl

lemma image_snd_le (i j : 𝒰.I₀) (O : X.Opens) :
    pullback.snd (𝒰.f i) (𝒰.f j) ''ᵁ (pullback.fst (𝒰.f i) (𝒰.f j) ⁻¹ᵁ (𝒰.f i) ⁻¹ᵁ O) ≤
      (𝒰.f j) ⁻¹ᵁ O := by
  rw [preimage_fst_eq]
  exact Scheme.Hom.image_preimage_le _ _

lemma le_image_snd (i j : 𝒰.I₀) {O : X.Opens} (hO : O ≤ (𝒰.f i).opensRange) :
    (𝒰.f j) ⁻¹ᵁ O ≤ pullback.snd (𝒰.f i) (𝒰.f j) ''ᵁ
      (pullback.fst (𝒰.f i) (𝒰.f j) ⁻¹ᵁ (𝒰.f i) ⁻¹ᵁ O) := by
  rw [preimage_fst_eq, Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.Hom.opensRange_pullbackSnd]
  exact le_inf (Scheme.Hom.preimage_mono _ hO) le_rfl

lemma φr_app_bijective (i j : 𝒰.I₀) (B : (pullback (𝒰.f i) (𝒰.f j)).Opens) :
    Function.Bijective ((φr 𝒰 M φ i j).hom.app B) :=
  ConcreteCategory.bijective_of_isIso _

lemma aMap_bijective (i j : 𝒰.I₀) {O : X.Opens} (hO : O ≤ (𝒰.f j).opensRange) :
    Function.Bijective ((aMap 𝒰 M φ i j).app O) := by
  have e : ⇑((aMap 𝒰 M φ i j).app O) =
      (φr 𝒰 M φ i j).hom.app _ ∘ (M i).presheaf.map
        (homOfLE ((pullback.fst (𝒰.f i) (𝒰.f j)).image_preimage_le ((𝒰.f i) ⁻¹ᵁ O))).op :=
    funext (aMap_app 𝒰 M φ i j O)
  rw [e]
  exact (φr_app_bijective 𝒰 M φ i j _).comp (res_bijective _ _
    (le_antisymm (le_image_fst 𝒰 i j hO) (Scheme.Hom.image_preimage_le _ _)))

lemma bMap_bijective (i j : 𝒰.I₀) {O : X.Opens} (hO : O ≤ (𝒰.f i).opensRange) :
    Function.Bijective ((bMap 𝒰 M i j).app O) := by
  have e : ⇑((bMap 𝒰 M i j).app O) =
      (M j).presheaf.map (homOfLE (image_snd_le 𝒰 i j O)).op :=
    funext fun y => bMap_app 𝒰 M i j O y _
  rw [e]
  exact res_bijective _ _ (le_antisymm (le_image_snd 𝒰 i j hO) (image_snd_le 𝒰 i j O))

end Bijective

section Relation

/-- Sections of the pieces `i` and `j` over `O` that correspond under the overlap isomorphism. -/
def Rel (i j : 𝒰.I₀) (O : X.Opens) (x : Γ(G 𝒰 M i, O)) (y : Γ(G 𝒰 M j, O)) : Prop :=
  (aMap 𝒰 M φ i j).app O x = (bMap 𝒰 M i j).app O y

variable {𝒰 M φ}

lemma rel_map {i j : 𝒰.I₀} {O P : X.Opens} (h : P ≤ O) {x : Γ(G 𝒰 M i, O)}
    {y : Γ(G 𝒰 M j, O)} (hr : Rel 𝒰 M φ i j O x y) :
    Rel 𝒰 M φ i j P ((G 𝒰 M i).presheaf.map (homOfLE h).op x)
      ((G 𝒰 M j).presheaf.map (homOfLE h).op y) := by
  unfold Rel at *
  rw [← OpenCoverHomGluing.hom_map_app, ← OpenCoverHomGluing.hom_map_app, hr]

lemma rel_restrict {i j : 𝒰.I₀} {O : X.Opens} {x : Γ(G 𝒰 M i, O)} {y : Γ(G 𝒰 M j, O)}
    (hr : Rel 𝒰 M φ i j O x y) (A : (pullback (𝒰.f i) (𝒰.f j)).Opens)
    (hA : A ≤ pullback.fst (𝒰.f i) (𝒰.f j) ⁻¹ᵁ (𝒰.f i) ⁻¹ᵁ O)
    (r : op ((𝒰.f i) ⁻¹ᵁ O) ⟶ op (pullback.fst (𝒰.f i) (𝒰.f j) ''ᵁ A))
    (r' : op ((𝒰.f j) ⁻¹ᵁ O) ⟶ op (pullback.snd (𝒰.f i) (𝒰.f j) ''ᵁ A)) :
    (φr 𝒰 M φ i j).hom.app A ((M i).presheaf.map r x) = (M j).presheaf.map r' y := by
  have h := congrArg (((M j).restrict (pullback.snd (𝒰.f i) (𝒰.f j))).presheaf.map
    (homOfLE hA).op) hr
  rw [aMap_app, bMap_app 𝒰 M i j O y (homOfLE (image_snd_le 𝒰 i j O)).op,
    OpenCoverHomGluing.hom_map_app, Scheme.Modules.restrict_map,
    Scheme.Modules.restrict_map] at h
  exact (congrArg _ (res_res (M i) _ _ r x).symm).trans (h.trans (res_res (M j) _ _ r' y))

lemma rel_of {i j : 𝒰.I₀} {O : X.Opens} {x : Γ(G 𝒰 M i, O)} {y : Γ(G 𝒰 M j, O)}
    (r : op ((𝒰.f i) ⁻¹ᵁ O) ⟶ op (pullback.fst (𝒰.f i) (𝒰.f j) ''ᵁ
      (pullback.fst (𝒰.f i) (𝒰.f j) ⁻¹ᵁ (𝒰.f i) ⁻¹ᵁ O)))
    (r' : op ((𝒰.f j) ⁻¹ᵁ O) ⟶ op (pullback.snd (𝒰.f i) (𝒰.f j) ''ᵁ
      (pullback.fst (𝒰.f i) (𝒰.f j) ⁻¹ᵁ (𝒰.f i) ⁻¹ᵁ O)))
    (h : (φr 𝒰 M φ i j).hom.app _ ((M i).presheaf.map r x) = (M j).presheaf.map r' y) :
    Rel 𝒰 M φ i j O x y := by
  unfold Rel
  rw [aMap_app, bMap_app 𝒰 M i j O y r', presheaf_map_subsingleton (M i).presheaf _ r]
  exact h

lemma H_map_injective (i j : 𝒰.I₀) {O P : X.Opens} (hPO : P ≤ O)
    (h : pullback.fst (𝒰.f i) (𝒰.f j) ⁻¹ᵁ (𝒰.f i) ⁻¹ᵁ P =
      pullback.fst (𝒰.f i) (𝒰.f j) ⁻¹ᵁ (𝒰.f i) ⁻¹ᵁ O) :
    Function.Injective ((H 𝒰 M i j).presheaf.map (homOfLE hPO).op) := by
  rw [H, Scheme.Modules.pushforward_obj_presheaf_map, Scheme.Modules.pushforward_obj_presheaf_map,
    Scheme.Modules.restrict_map]
  exact (res_bijective _ _ (congrArg _ h.symm)).1

lemma preimage_inf_eq (i j : 𝒰.I₀) (O : X.Opens) :
    pullback.fst (𝒰.f i) (𝒰.f j) ⁻¹ᵁ (𝒰.f i) ⁻¹ᵁ (O ⊓ (𝒰.f i).opensRange ⊓ (𝒰.f j).opensRange) =
      pullback.fst (𝒰.f i) (𝒰.f j) ⁻¹ᵁ (𝒰.f i) ⁻¹ᵁ O := by
  refine le_antisymm (Scheme.Hom.preimage_mono _ (Scheme.Hom.preimage_mono _
    (inf_le_left.trans inf_le_left))) fun y hy => ⟨⟨hy, ⟨_, rfl⟩⟩, ⟨pullback.snd (𝒰.f i) (𝒰.f j) y, ?_⟩⟩
  rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]

lemma rel_of_inf {i j : 𝒰.I₀} {O : X.Opens} {x : Γ(G 𝒰 M i, O)} {y : Γ(G 𝒰 M j, O)}
    (h : Rel 𝒰 M φ i j (O ⊓ (𝒰.f i).opensRange ⊓ (𝒰.f j).opensRange)
      ((G 𝒰 M i).presheaf.map (homOfLE (inf_le_left.trans inf_le_left)).op x)
      ((G 𝒰 M j).presheaf.map (homOfLE (inf_le_left.trans inf_le_left)).op y)) :
    Rel 𝒰 M φ i j O x y := by
  unfold Rel at *
  rw [← OpenCoverHomGluing.hom_map_app, ← OpenCoverHomGluing.hom_map_app] at h
  exact H_map_injective i j _ (preimage_inf_eq i j O) h

end Relation

section Cocycle

open Langlands.SchemeModule.RigidifiedModule (compHom)

/-- A morphism of pullbacks along two open immersions, read on restrictions. -/
def rHom {B C C' : AlgebraicGeometry.Scheme.{u}} (b : B ⟶ C) (b' : B ⟶ C')
    [IsOpenImmersion b] [IsOpenImmersion b'] {M : C.Modules} {N : C'.Modules}
    (ψ : (Scheme.Modules.pullback b).obj M ⟶ (Scheme.Modules.pullback b').obj N) :
    M.restrict b ⟶ N.restrict b' :=
  (restrictFunctorIsoPullback b).hom.app M ≫ ψ ≫ (restrictFunctorIsoPullback b').inv.app N

lemma φr_hom (i j : 𝒰.I₀) :
    (φr 𝒰 M φ i j).hom = rHom (pullback.fst (𝒰.f i) (𝒰.f j)) (pullback.snd (𝒰.f i) (𝒰.f j))
      (φ i j).hom := rfl

/-- Conjugating a pulled-back morphism by composition comparisons agrees with iterated
restriction. -/
lemma conj_eq' {A B C C' : AlgebraicGeometry.Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) (b' : B ⟶ C')
    (c : A ⟶ C) (c' : A ⟶ C') (h : a ≫ b = c) (h' : a ≫ b' = c')
    [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion b'] [IsOpenImmersion c]
    [IsOpenImmersion c'] {M : C.Modules} {N : C'.Modules}
    (ψ : (Scheme.Modules.pullback b).obj M ⟶ (Scheme.Modules.pullback b').obj N) :
    (restrictFunctorIsoPullback c).hom.app M ≫ inv (compHom a b c h M) ≫
        (Scheme.Modules.pullback a).map ψ ≫ compHom a b' c' h' N ≫
          (restrictFunctorIsoPullback c').inv.app N =
      (restrictCompIso a b c h).hom.app M ≫ (restrictFunctor a).map (rHom b b' ψ) ≫
        (restrictCompIso a b' c' h').inv.app N := by
  rw [← cancel_mono ((restrictFunctorIsoPullback c').hom.app N)]
  simp only [Category.assoc, Iso.inv_hom_id_app, Category.comp_id]
  rw [← restrictCompIso_hom_app_comp a b c h M, ← restrictCompIso_hom_app_comp a b' c' h' N]
  simp only [rHom, Category.assoc, IsIso.hom_inv_id_assoc, Iso.inv_hom_id_app_assoc,
    Functor.map_comp]
  rw [← Functor.map_comp_assoc (restrictFunctor a) ((restrictFunctorIsoPullback b').inv.app N),
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp,
    (restrictFunctorIsoPullback a).hom.naturality_assoc ψ]

/-- The cocycle condition of pulled-back morphisms around a triple overlap, read on iterated
restrictions. -/
lemma restrict_cocycle {W Zab Zbc Zac Ua Ub Uc : AlgebraicGeometry.Scheme.{u}}
    (t₁ : W ⟶ Zab) (q : W ⟶ Zbc) (t₂ : W ⟶ Zac) (fab : Zab ⟶ Ua) (gab : Zab ⟶ Ub)
    (fbc : Zbc ⟶ Ub) (gbc : Zbc ⟶ Uc) (fac : Zac ⟶ Ua) (gac : Zac ⟶ Uc)
    [IsOpenImmersion t₁] [IsOpenImmersion q] [IsOpenImmersion t₂] [IsOpenImmersion fab]
    [IsOpenImmersion gab] [IsOpenImmersion fbc] [IsOpenImmersion gbc] [IsOpenImmersion fac]
    [IsOpenImmersion gac]
    (h₀ : t₁ ≫ fab = t₂ ≫ fac) (h₁ : t₁ ≫ gab = q ≫ fbc) (h₂ : q ≫ gbc = t₂ ≫ gac)
    {Ma : Ua.Modules} {Mb : Ub.Modules} {Mc : Uc.Modules}
    (φab : (Scheme.Modules.pullback fab).obj Ma ⟶ (Scheme.Modules.pullback gab).obj Mb)
    (φbc : (Scheme.Modules.pullback fbc).obj Mb ⟶ (Scheme.Modules.pullback gbc).obj Mc)
    (φac : (Scheme.Modules.pullback fac).obj Ma ⟶ (Scheme.Modules.pullback gac).obj Mc)
    (H : (Scheme.Modules.pullback t₁).map φab ≫ (squarePullbackIso fbc t₁ q gab h₁ Mb).hom ≫
        (Scheme.Modules.pullback q).map φbc ≫ (squarePullbackIso gac q t₂ gbc h₂ Mc).hom =
      (squarePullbackIso fac t₁ t₂ fab h₀ Ma).hom ≫ (Scheme.Modules.pullback t₂).map φac) :
    (restrictCompIso t₁ fab (t₁ ≫ fab) rfl).hom.app Ma ≫
        (restrictFunctor t₁).map (rHom fab gab φab) ≫
        (restrictCompIso t₁ gab (t₁ ≫ gab) rfl).inv.app Mb ≫
        (restrictCompIso q fbc (t₁ ≫ gab) h₁.symm).hom.app Mb ≫
        (restrictFunctor q).map (rHom fbc gbc φbc) ≫
        (restrictCompIso q gbc (q ≫ gbc) rfl).inv.app Mc =
      (restrictCompIso t₂ fac (t₁ ≫ fab) h₀.symm).hom.app Ma ≫
        (restrictFunctor t₂).map (rHom fac gac φac) ≫
        (restrictCompIso t₂ gac (q ≫ gbc) h₂.symm).inv.app Mc := by
  have s₀ : (squarePullbackIso fac t₁ t₂ fab h₀ Ma).hom =
      compHom t₁ fab _ rfl Ma ≫ inv (compHom t₂ fac _ h₀.symm Ma) :=
    (IsIso.eq_comp_inv _).2 (OpenCoverHomGluing.squarePullbackIso_hom_compHom _ _ _ _ _ _)
  have s₁ : (squarePullbackIso fbc t₁ q gab h₁ Mb).hom =
      compHom t₁ gab _ rfl Mb ≫ inv (compHom q fbc _ h₁.symm Mb) :=
    (IsIso.eq_comp_inv _).2 (OpenCoverHomGluing.squarePullbackIso_hom_compHom _ _ _ _ _ _)
  have s₂ : (squarePullbackIso gac q t₂ gbc h₂ Mc).hom =
      compHom q gbc _ rfl Mc ≫ inv (compHom t₂ gac _ h₂.symm Mc) :=
    (IsIso.eq_comp_inv _).2 (OpenCoverHomGluing.squarePullbackIso_hom_compHom _ _ _ _ _ _)
  rw [s₀, s₁, s₂] at H
  simp only [Category.assoc] at H
  have e₁ := conj_eq' t₁ fab gab (t₁ ≫ fab) (t₁ ≫ gab) rfl rfl φab
  have e₂ := conj_eq' q fbc gbc (t₁ ≫ gab) (q ≫ gbc) h₁.symm rfl φbc
  have e₃ := conj_eq' t₂ fac gac (t₁ ≫ fab) (q ≫ gbc) h₀.symm h₂.symm φac
  rw [← e₃, ← e₂, ← reassoc_of% e₁]
  simp only [Iso.inv_hom_id_app_assoc]
  congr 1
  rw [IsIso.inv_comp_eq, ← reassoc_of% H]
  simp

lemma image_congr {A B : AlgebraicGeometry.Scheme.{u}} {f g : A ⟶ B} [IsOpenImmersion f]
    [IsOpenImmersion g] (h : f = g) (U : A.Opens) : f ''ᵁ U = g ''ᵁ U := by
  subst h
  rfl

/-- On sections, the comparison of restriction along a composite is a restriction map. -/
lemma rCI_hom_apply {A B C : AlgebraicGeometry.Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) (c : A ⟶ C)
    (h : a ≫ b = c) [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion c] (M : C.Modules)
    (U : A.Opens) (x : Γ(M, c ''ᵁ U)) (p : op (c ''ᵁ U) ⟶ op (b ''ᵁ a ''ᵁ U)) :
    ((restrictCompIso a b c h).hom.app M).app U x = M.presheaf.map p x := by
  simp only [restrictCompIso, Iso.trans_hom, NatTrans.comp_app, Scheme.Modules.Hom.comp_app,
    Scheme.Modules.restrictFunctorCongr_hom_app_app,
    Scheme.Modules.restrictFunctorComp_hom_app_app, ConcreteCategory.comp_apply]
  exact res_res M _ _ p x

/-- On sections, the inverse comparison of restriction along a composite is a restriction map. -/
lemma rCI_inv_apply {A B C : AlgebraicGeometry.Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C) (c : A ⟶ C)
    (h : a ≫ b = c) [IsOpenImmersion a] [IsOpenImmersion b] [IsOpenImmersion c] (M : C.Modules)
    (U : A.Opens) (x : Γ(M, b ''ᵁ a ''ᵁ U)) (p : op (b ''ᵁ a ''ᵁ U) ⟶ op (c ''ᵁ U)) :
    ((restrictCompIso a b c h).inv.app M).app U x = M.presheaf.map p x := by
  simp only [restrictCompIso, Iso.trans_inv, NatTrans.comp_app, Scheme.Modules.Hom.comp_app,
    Scheme.Modules.restrictFunctorCongr_inv_app_app,
    Scheme.Modules.restrictFunctorComp_inv_app_app, ConcreteCategory.comp_apply]
  exact res_res M _ _ p x

set_option maxRecDepth 8000 in
/-- The cocycle condition around a triple overlap, read on sections over an open of the triple
overlap. -/
lemma section_cocycle {W Zab Zbc Zac Ua Ub Uc : AlgebraicGeometry.Scheme.{u}}
    (t₁ : W ⟶ Zab) (q : W ⟶ Zbc) (t₂ : W ⟶ Zac) (fab : Zab ⟶ Ua) (gab : Zab ⟶ Ub)
    (fbc : Zbc ⟶ Ub) (gbc : Zbc ⟶ Uc) (fac : Zac ⟶ Ua) (gac : Zac ⟶ Uc)
    [IsOpenImmersion t₁] [IsOpenImmersion q] [IsOpenImmersion t₂] [IsOpenImmersion fab]
    [IsOpenImmersion gab] [IsOpenImmersion fbc] [IsOpenImmersion gbc] [IsOpenImmersion fac]
    [IsOpenImmersion gac]
    (h₀ : t₁ ≫ fab = t₂ ≫ fac) (h₁ : t₁ ≫ gab = q ≫ fbc) (h₂ : q ≫ gbc = t₂ ≫ gac)
    {Ma : Ua.Modules} {Mb : Ub.Modules} {Mc : Uc.Modules}
    (φab : (Scheme.Modules.pullback fab).obj Ma ⟶ (Scheme.Modules.pullback gab).obj Mb)
    (φbc : (Scheme.Modules.pullback fbc).obj Mb ⟶ (Scheme.Modules.pullback gbc).obj Mc)
    (φac : (Scheme.Modules.pullback fac).obj Ma ⟶ (Scheme.Modules.pullback gac).obj Mc)
    (H : (Scheme.Modules.pullback t₁).map φab ≫ (squarePullbackIso fbc t₁ q gab h₁ Mb).hom ≫
        (Scheme.Modules.pullback q).map φbc ≫ (squarePullbackIso gac q t₂ gbc h₂ Mc).hom =
      (squarePullbackIso fac t₁ t₂ fab h₀ Ma).hom ≫ (Scheme.Modules.pullback t₂).map φac)
    (U : W.Opens) (x : Γ(Ma, fab ''ᵁ t₁ ''ᵁ U))
    (r₀ : op (fab ''ᵁ t₁ ''ᵁ U) ⟶ op (fac ''ᵁ t₂ ''ᵁ U))
    (r₁ : op (gab ''ᵁ t₁ ''ᵁ U) ⟶ op (fbc ''ᵁ q ''ᵁ U))
    (r₂ : op (gbc ''ᵁ q ''ᵁ U) ⟶ op (gac ''ᵁ t₂ ''ᵁ U)) :
    (rHom fac gac φac).app (t₂ ''ᵁ U) (Ma.presheaf.map r₀ x) =
      Mc.presheaf.map r₂ ((rHom fbc gbc φbc).app (q ''ᵁ U)
        (Mb.presheaf.map r₁ ((rHom fab gab φab).app (t₁ ''ᵁ U) x))) := by
  have key := restrict_cocycle t₁ q t₂ fab gab fbc gbc fac gac h₀ h₁ h₂ φab φbc φac H
  have hU : fab ''ᵁ t₁ ''ᵁ U = (t₁ ≫ fab) ''ᵁ U := (Scheme.Hom.comp_image _ _ _).symm
  have hc : gac ''ᵁ t₂ ''ᵁ U = (q ≫ gbc) ''ᵁ U :=
    (Scheme.Hom.comp_image t₂ gac U).symm.trans (image_congr h₂.symm U)
  have hb : fbc ''ᵁ q ''ᵁ U = (t₁ ≫ gab) ''ᵁ U :=
    (Scheme.Hom.comp_image q fbc U).symm.trans (image_congr h₁.symm U)
  have ha : fac ''ᵁ t₂ ''ᵁ U = (t₁ ≫ fab) ''ᵁ U :=
    (Scheme.Hom.comp_image t₂ fac U).symm.trans (image_congr h₀.symm U)
  have E := ConcreteCategory.congr_hom (congrArg (fun f => Scheme.Modules.Hom.app f U) key)
    (Ma.presheaf.map (eqToHom hU.symm).op x)
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply] at E
  have e1 := rCI_hom_apply t₁ fab (t₁ ≫ fab) rfl Ma U (Ma.presheaf.map (eqToHom hU.symm).op x)
    (eqToHom hU).op
  rw [e1] at E
  rw [res_res Ma _ _ (𝟙 _), res_self] at E
  erw [rCI_inv_apply t₁ gab (t₁ ≫ gab) rfl Mb U _
    (eqToHom (Scheme.Hom.comp_image t₁ gab U)).op] at E
  erw [rCI_hom_apply q fbc (t₁ ≫ gab) h₁.symm Mb U _ (eqToHom hb).op] at E
  rw [res_res Mb _ _ r₁] at E
  erw [rCI_inv_apply q gbc (q ≫ gbc) rfl Mc U _ (eqToHom (Scheme.Hom.comp_image q gbc U)).op] at E
  erw [rCI_hom_apply t₂ fac (t₁ ≫ fab) h₀.symm Ma U _ (eqToHom ha).op] at E
  rw [res_res Ma _ _ r₀] at E
  erw [rCI_inv_apply t₂ gac (q ≫ gbc) h₂.symm Mc U _ (eqToHom hc.symm).op] at E
  apply (res_bijective Mc (eqToHom hc.symm).op hc).1
  rw [res_res Mc r₂ (eqToHom hc.symm).op (eqToHom (Scheme.Hom.comp_image q gbc U)).op]
  exact E.symm

/-- Two overlap relations around a triple overlap compose, read on sections. -/
lemma section_trans {W Zab Zbc Zac Ua Ub Uc : AlgebraicGeometry.Scheme.{u}}
    (t₁ : W ⟶ Zab) (q : W ⟶ Zbc) (t₂ : W ⟶ Zac) (fab : Zab ⟶ Ua) (gab : Zab ⟶ Ub)
    (fbc : Zbc ⟶ Ub) (gbc : Zbc ⟶ Uc) (fac : Zac ⟶ Ua) (gac : Zac ⟶ Uc)
    [IsOpenImmersion t₁] [IsOpenImmersion q] [IsOpenImmersion t₂] [IsOpenImmersion fab]
    [IsOpenImmersion gab] [IsOpenImmersion fbc] [IsOpenImmersion gbc] [IsOpenImmersion fac]
    [IsOpenImmersion gac]
    (h₀ : t₁ ≫ fab = t₂ ≫ fac) (h₁ : t₁ ≫ gab = q ≫ fbc) (h₂ : q ≫ gbc = t₂ ≫ gac)
    {Ma : Ua.Modules} {Mb : Ub.Modules} {Mc : Uc.Modules}
    (φab : (Scheme.Modules.pullback fab).obj Ma ⟶ (Scheme.Modules.pullback gab).obj Mb)
    (φbc : (Scheme.Modules.pullback fbc).obj Mb ⟶ (Scheme.Modules.pullback gbc).obj Mc)
    (φac : (Scheme.Modules.pullback fac).obj Ma ⟶ (Scheme.Modules.pullback gac).obj Mc)
    (H : (Scheme.Modules.pullback t₁).map φab ≫ (squarePullbackIso fbc t₁ q gab h₁ Mb).hom ≫
        (Scheme.Modules.pullback q).map φbc ≫ (squarePullbackIso gac q t₂ gbc h₂ Mc).hom =
      (squarePullbackIso fac t₁ t₂ fab h₀ Ma).hom ≫ (Scheme.Modules.pullback t₂).map φac)
    (U : W.Opens) {Oa : Ua.Opens} {Ob : Ub.Opens} {Oc : Uc.Opens}
    (x : Γ(Ma, Oa)) (y : Γ(Mb, Ob)) (z : Γ(Mc, Oc))
    (ha : fab ''ᵁ t₁ ''ᵁ U ≤ Oa) (hb₁ : gab ''ᵁ t₁ ''ᵁ U ≤ Ob) (hb₂ : fbc ''ᵁ q ''ᵁ U ≤ Ob)
    (hc : gbc ''ᵁ q ''ᵁ U ≤ Oc)
    (hxy : ∀ (r : op Oa ⟶ op (fab ''ᵁ t₁ ''ᵁ U)) (r' : op Ob ⟶ op (gab ''ᵁ t₁ ''ᵁ U)),
      (rHom fab gab φab).app (t₁ ''ᵁ U) (Ma.presheaf.map r x) = Mb.presheaf.map r' y)
    (hyz : ∀ (r : op Ob ⟶ op (fbc ''ᵁ q ''ᵁ U)) (r' : op Oc ⟶ op (gbc ''ᵁ q ''ᵁ U)),
      (rHom fbc gbc φbc).app (q ''ᵁ U) (Mb.presheaf.map r y) = Mc.presheaf.map r' z)
    (r : op Oa ⟶ op (fac ''ᵁ t₂ ''ᵁ U)) (r' : op Oc ⟶ op (gac ''ᵁ t₂ ''ᵁ U)) :
    (rHom fac gac φac).app (t₂ ''ᵁ U) (Ma.presheaf.map r x) = Mc.presheaf.map r' z := by
  have hA : fab ''ᵁ t₁ ''ᵁ U = fac ''ᵁ t₂ ''ᵁ U := by
    rw [← Scheme.Hom.comp_image, ← Scheme.Hom.comp_image]
    exact image_congr h₀ U
  have hB : gab ''ᵁ t₁ ''ᵁ U = fbc ''ᵁ q ''ᵁ U := by
    rw [← Scheme.Hom.comp_image, ← Scheme.Hom.comp_image]
    exact image_congr h₁ U
  have hC : gbc ''ᵁ q ''ᵁ U = gac ''ᵁ t₂ ''ᵁ U := by
    rw [← Scheme.Hom.comp_image, ← Scheme.Hom.comp_image]
    exact image_congr h₂ U
  have e := section_cocycle t₁ q t₂ fab gab fbc gbc fac gac h₀ h₁ h₂ φab φbc φac H U
    (Ma.presheaf.map (homOfLE ha).op x) (homOfLE hA.ge).op (homOfLE hB.ge).op (homOfLE hC.ge).op
  rw [hxy (homOfLE ha).op (homOfLE hb₁).op, res_res Mb _ _ (homOfLE hb₂).op,
    hyz (homOfLE hb₂).op (homOfLE hc).op, res_res Mc _ _ r', res_res Ma _ _ r] at e
  exact e

end Cocycle

section Wrappers

variable {C : Type*} [Category C]

/-- An equation between a composite of four morphisms and a composite of two. It is a regular
definition so that the kernel compares two instances argument by argument instead of unfolding
the composites (the copies of the statement's equations here differ from the statement's
elaborated terms in auxiliary proofs). -/
def CompEq4 {A B₁ B₂ B₃ B₄ D : C} (f₁ : A ⟶ B₁) (f₂ : B₁ ⟶ B₂) (f₃ : B₂ ⟶ B₃) (f₄ : B₃ ⟶ D)
    (g₁ : A ⟶ B₄) (g₂ : B₄ ⟶ D) : Prop :=
  f₁ ≫ f₂ ≫ f₃ ≫ f₄ = g₁ ≫ g₂

lemma CompEq4.of_eq {A B₁ B₂ B₃ B₄ D : C} {f₁ : A ⟶ B₁} {f₂ : B₁ ⟶ B₂} {f₃ : B₂ ⟶ B₃}
    {f₄ : B₃ ⟶ D} {g₁ : A ⟶ B₄} {g₂ : B₄ ⟶ D} (h : f₁ ≫ f₂ ≫ f₃ ≫ f₄ = g₁ ≫ g₂) :
    CompEq4 f₁ f₂ f₃ f₄ g₁ g₂ :=
  h

lemma CompEq4.eq {A B₁ B₂ B₃ B₄ D : C} {f₁ : A ⟶ B₁} {f₂ : B₁ ⟶ B₂} {f₃ : B₂ ⟶ B₃}
    {f₄ : B₃ ⟶ D} {g₁ : A ⟶ B₄} {g₂ : B₄ ⟶ D} (h : CompEq4 f₁ f₂ f₃ f₄ g₁ g₂) :
    f₁ ≫ f₂ ≫ f₃ ≫ f₄ = g₁ ≫ g₂ :=
  h

/-- An equation between two composites of two morphisms, packaged like `CompEq4`. -/
def CompEq2 {A B₁ B₂ D : C} (f₁ : A ⟶ B₁) (f₂ : B₁ ⟶ D) (g₁ : A ⟶ B₂) (g₂ : B₂ ⟶ D) : Prop :=
  f₁ ≫ f₂ = g₁ ≫ g₂

lemma CompEq2.of_eq {A B₁ B₂ D : C} {f₁ : A ⟶ B₁} {f₂ : B₁ ⟶ D} {g₁ : A ⟶ B₂} {g₂ : B₂ ⟶ D}
    (h : f₁ ≫ f₂ = g₁ ≫ g₂) : CompEq2 f₁ f₂ g₁ g₂ :=
  h

lemma CompEq2.eq {A B₁ B₂ D : C} {f₁ : A ⟶ B₁} {f₂ : B₁ ⟶ D} {g₁ : A ⟶ B₂} {g₂ : B₂ ⟶ D}
    (h : CompEq2 f₁ f₂ g₁ g₂) : f₁ ≫ f₂ = g₁ ≫ g₂ :=
  h

end Wrappers

/-- The cocycle condition of the statement, on the Mathlib triple overlaps. -/
def CocycleCondition : Prop :=
  ∀ i j k,
    CompEq4
      ((AlgebraicGeometry.Scheme.Modules.pullback
        (pullback.fst (pullback.fst (𝒰.f i) (𝒰.f j))
          (pullback.fst (𝒰.f i) (𝒰.f k)))).map (φ i j).hom)
      ((squarePullbackIso (pullback.fst (𝒰.f j) (𝒰.f k))
        (pullback.fst (pullback.fst (𝒰.f i) (𝒰.f j)) (pullback.fst (𝒰.f i) (𝒰.f k)))
        (pullback.lift
          (pullback.fst (pullback.fst (𝒰.f i) (𝒰.f j)) (pullback.fst (𝒰.f i) (𝒰.f k)) ≫
            pullback.snd (𝒰.f i) (𝒰.f j))
          (pullback.snd (pullback.fst (𝒰.f i) (𝒰.f j)) (pullback.fst (𝒰.f i) (𝒰.f k)) ≫
            pullback.snd (𝒰.f i) (𝒰.f k))
          (by simp only [Category.assoc, ← pullback.condition, pullback.condition_assoc]))
        (pullback.snd (𝒰.f i) (𝒰.f j)) (pullback.lift_fst _ _ _).symm (M j)).hom)
      ((AlgebraicGeometry.Scheme.Modules.pullback
        (pullback.lift
          (pullback.fst (pullback.fst (𝒰.f i) (𝒰.f j)) (pullback.fst (𝒰.f i) (𝒰.f k)) ≫
            pullback.snd (𝒰.f i) (𝒰.f j))
          (pullback.snd (pullback.fst (𝒰.f i) (𝒰.f j)) (pullback.fst (𝒰.f i) (𝒰.f k)) ≫
            pullback.snd (𝒰.f i) (𝒰.f k))
          (by simp only [Category.assoc, ← pullback.condition, pullback.condition_assoc]))).map
        (φ j k).hom)
      ((squarePullbackIso (pullback.snd (𝒰.f i) (𝒰.f k))
        (pullback.lift
          (pullback.fst (pullback.fst (𝒰.f i) (𝒰.f j)) (pullback.fst (𝒰.f i) (𝒰.f k)) ≫
            pullback.snd (𝒰.f i) (𝒰.f j))
          (pullback.snd (pullback.fst (𝒰.f i) (𝒰.f j)) (pullback.fst (𝒰.f i) (𝒰.f k)) ≫
            pullback.snd (𝒰.f i) (𝒰.f k))
          (by simp only [Category.assoc, ← pullback.condition, pullback.condition_assoc]))
        (pullback.snd (pullback.fst (𝒰.f i) (𝒰.f j)) (pullback.fst (𝒰.f i) (𝒰.f k)))
        (pullback.snd (𝒰.f j) (𝒰.f k)) (pullback.lift_snd _ _ _) (M k)).hom)
      ((squarePullbackIso (pullback.fst (𝒰.f i) (𝒰.f k))
        (pullback.fst (pullback.fst (𝒰.f i) (𝒰.f j)) (pullback.fst (𝒰.f i) (𝒰.f k)))
        (pullback.snd (pullback.fst (𝒰.f i) (𝒰.f j)) (pullback.fst (𝒰.f i) (𝒰.f k)))
        (pullback.fst (𝒰.f i) (𝒰.f j)) pullback.condition (M i)).hom)
      ((AlgebraicGeometry.Scheme.Modules.pullback
        (pullback.snd (pullback.fst (𝒰.f i) (𝒰.f j))
          (pullback.fst (𝒰.f i) (𝒰.f k)))).map (φ i k).hom)

section Transitivity

variable {𝒰 M φ}

lemma image_le_of_le_preimage {A B : AlgebraicGeometry.Scheme.{u}} (f : A ⟶ B)
    [IsOpenImmersion f] {U : A.Opens} {V : B.Opens} (h : U ≤ f ⁻¹ᵁ V) : f ''ᵁ U ≤ V :=
  (Scheme.Hom.image_mono f h).trans (Scheme.Hom.image_preimage_le f V)

lemma preimage_congr {A B : AlgebraicGeometry.Scheme.{u}} {f g : A ⟶ B} (h : f = g)
    (V : B.Opens) : f ⁻¹ᵁ V = g ⁻¹ᵁ V := by
  subst h
  rfl

lemma rel_of' {i j : 𝒰.I₀} {O : X.Opens} {x : Γ(G 𝒰 M i, O)} {y : Γ(G 𝒰 M j, O)}
    (B : (pullback (𝒰.f i) (𝒰.f j)).Opens)
    (hB : B = pullback.fst (𝒰.f i) (𝒰.f j) ⁻¹ᵁ (𝒰.f i) ⁻¹ᵁ O)
    (h : ∀ (r : op ((𝒰.f i) ⁻¹ᵁ O) ⟶ op (pullback.fst (𝒰.f i) (𝒰.f j) ''ᵁ B))
      (r' : op ((𝒰.f j) ⁻¹ᵁ O) ⟶ op (pullback.snd (𝒰.f i) (𝒰.f j) ''ᵁ B)),
      (φr 𝒰 M φ i j).hom.app B ((M i).presheaf.map r x) = (M j).presheaf.map r' y) :
    Rel 𝒰 M φ i j O x y := by
  subst hB
  exact rel_of (homOfLE (Scheme.Hom.image_preimage_le _ _)).op
    (homOfLE (image_snd_le 𝒰 i j O)).op (h _ _)

lemma rel_trans_aux {a b c : 𝒰.I₀} {P : X.Opens} {x : Γ(G 𝒰 M a, P)} {y : Γ(G 𝒰 M b, P)}
    {z : Γ(G 𝒰 M c, P)} {W : AlgebraicGeometry.Scheme.{u}}
    (t₁ : W ⟶ pullback (𝒰.f a) (𝒰.f b)) (q : W ⟶ pullback (𝒰.f b) (𝒰.f c))
    (t₂ : W ⟶ pullback (𝒰.f a) (𝒰.f c)) [IsOpenImmersion t₁] [IsOpenImmersion t₂]
    (h₀ : t₁ ≫ pullback.fst (𝒰.f a) (𝒰.f b) = t₂ ≫ pullback.fst (𝒰.f a) (𝒰.f c))
    (h₁ : t₁ ≫ pullback.snd (𝒰.f a) (𝒰.f b) = q ≫ pullback.fst (𝒰.f b) (𝒰.f c))
    (h₂ : q ≫ pullback.snd (𝒰.f b) (𝒰.f c) = t₂ ≫ pullback.snd (𝒰.f a) (𝒰.f c))
    (H : (Scheme.Modules.pullback t₁).map (φ a b).hom ≫
        (squarePullbackIso (pullback.fst (𝒰.f b) (𝒰.f c)) t₁ q
          (pullback.snd (𝒰.f a) (𝒰.f b)) h₁ (M b)).hom ≫
        (Scheme.Modules.pullback q).map (φ b c).hom ≫
        (squarePullbackIso (pullback.snd (𝒰.f a) (𝒰.f c)) q t₂
          (pullback.snd (𝒰.f b) (𝒰.f c)) h₂ (M c)).hom =
      (squarePullbackIso (pullback.fst (𝒰.f a) (𝒰.f c)) t₁ t₂
          (pullback.fst (𝒰.f a) (𝒰.f b)) h₀ (M a)).hom ≫
        (Scheme.Modules.pullback t₂).map (φ a c).hom)
    (hr : pullback.fst (𝒰.f a) (𝒰.f c) ⁻¹ᵁ (𝒰.f a) ⁻¹ᵁ P ≤ t₂.opensRange)
    (hxy : Rel 𝒰 M φ a b P x y) (hyz : Rel 𝒰 M φ b c P y z) : Rel 𝒰 M φ a c P x z := by
  have : IsOpenImmersion (q ≫ pullback.fst (𝒰.f b) (𝒰.f c)) := by
    rw [← h₁]
    infer_instance
  have : IsOpenImmersion q := IsOpenImmersion.of_comp q (pullback.fst (𝒰.f b) (𝒰.f c))
  have e₀ : t₂ ≫ pullback.fst (𝒰.f a) (𝒰.f c) ≫ 𝒰.f a =
      t₁ ≫ pullback.fst (𝒰.f a) (𝒰.f b) ≫ 𝒰.f a := by
    rw [reassoc_of% h₀]
  have e₁ : t₂ ≫ pullback.fst (𝒰.f a) (𝒰.f c) ≫ 𝒰.f a =
      q ≫ pullback.fst (𝒰.f b) (𝒰.f c) ≫ 𝒰.f b := by
    rw [e₀, pullback.condition (f := 𝒰.f a) (g := 𝒰.f b), reassoc_of% h₁]
  have hU₁ : t₂ ⁻¹ᵁ pullback.fst (𝒰.f a) (𝒰.f c) ⁻¹ᵁ (𝒰.f a) ⁻¹ᵁ P ≤
      t₁ ⁻¹ᵁ pullback.fst (𝒰.f a) (𝒰.f b) ⁻¹ᵁ (𝒰.f a) ⁻¹ᵁ P :=
    (preimage_congr e₀ P).le
  have hU₂ : t₂ ⁻¹ᵁ pullback.fst (𝒰.f a) (𝒰.f c) ⁻¹ᵁ (𝒰.f a) ⁻¹ᵁ P ≤
      q ⁻¹ᵁ pullback.fst (𝒰.f b) (𝒰.f c) ⁻¹ᵁ (𝒰.f b) ⁻¹ᵁ P :=
    (preimage_congr e₁ P).le
  have hU₃ : t₂ ''ᵁ (t₂ ⁻¹ᵁ pullback.fst (𝒰.f a) (𝒰.f c) ⁻¹ᵁ (𝒰.f a) ⁻¹ᵁ P) =
      pullback.fst (𝒰.f a) (𝒰.f c) ⁻¹ᵁ (𝒰.f a) ⁻¹ᵁ P := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
    exact inf_eq_right.2 hr
  have hA₁ := image_le_of_le_preimage t₁ hU₁
  have hA₂ := image_le_of_le_preimage q hU₂
  refine rel_of' _ hU₃ fun r r' => ?_
  exact section_trans t₁ q t₂ _ _ _ _ _ _ h₀ h₁ h₂ (φ a b).hom (φ b c).hom (φ a c).hom H _ x y z
    ((Scheme.Hom.image_mono _ hA₁).trans (Scheme.Hom.image_preimage_le _ _))
    ((Scheme.Hom.image_mono _ hA₁).trans (image_snd_le 𝒰 a b P))
    ((Scheme.Hom.image_mono _ hA₂).trans (Scheme.Hom.image_preimage_le _ _))
    ((Scheme.Hom.image_mono _ hA₂).trans (image_snd_le 𝒰 b c P))
    (rel_restrict hxy _ hA₁) (rel_restrict hyz _ hA₂) r r'

/-- The overlap relation is transitive through a piece containing the open. -/
lemma rel_trans (hφ : CocycleCondition 𝒰 M φ) {a b c : 𝒰.I₀} {P : X.Opens}
    (hb : P ≤ (𝒰.f b).opensRange) {x : Γ(G 𝒰 M a, P)} {y : Γ(G 𝒰 M b, P)}
    {z : Γ(G 𝒰 M c, P)} (hxy : Rel 𝒰 M φ a b P x y) (hyz : Rel 𝒰 M φ b c P y z) :
    Rel 𝒰 M φ a c P x z := by
  refine rel_trans_aux _ _ _ pullback.condition (pullback.lift_fst _ _ _).symm
    (pullback.lift_snd _ _ _) (hφ a b c).eq ?_ hxy hyz
  rw [Scheme.Hom.opensRange_pullbackSnd, Scheme.Hom.opensRange_pullbackFst]
  exact Scheme.Hom.preimage_mono _ (Scheme.Hom.preimage_mono _ hb)

end Transitivity

section Symmetry

variable {𝒰 M φ}

/-- Over an open inside a piece, every section of that piece is related to itself. -/
lemma rel_self (hφ : CocycleCondition 𝒰 M φ) {k : 𝒰.I₀} {P : X.Opens}
    (hP : P ≤ (𝒰.f k).opensRange) (x : Γ(G 𝒰 M k, P)) : Rel 𝒰 M φ k k P x x := by
  obtain ⟨y, hy⟩ := (bMap_bijective 𝒰 M k k hP).2 ((aMap 𝒰 M φ k k).app P x)
  obtain ⟨z, hz⟩ := (bMap_bijective 𝒰 M k k hP).2 ((aMap 𝒰 M φ k k).app P y)
  have hxz : (aMap 𝒰 M φ k k).app P x = (bMap 𝒰 M k k).app P z :=
    rel_trans hφ hP (Eq.symm hy) (Eq.symm hz)
  have hzy : z = y := (bMap_bijective 𝒰 M k k hP).1 (hxz.symm.trans hy.symm)
  have hyy : (aMap 𝒰 M φ k k).app P y = (bMap 𝒰 M k k).app P y :=
    hz.symm.trans (congrArg _ hzy)
  have hxy : x = y := (aMap_bijective 𝒰 M φ k k hP).1 (hy.symm.trans hyy.symm)
  show (aMap 𝒰 M φ k k).app P x = (bMap 𝒰 M k k).app P x
  rw [hxy]
  exact hyy

/-- Over an open inside a piece, the relation of that piece with itself is equality. -/
lemma rel_self_iff (hφ : CocycleCondition 𝒰 M φ) {k : 𝒰.I₀} {P : X.Opens}
    (hP : P ≤ (𝒰.f k).opensRange) {x y : Γ(G 𝒰 M k, P)} : Rel 𝒰 M φ k k P x y ↔ x = y := by
  refine ⟨fun h => (bMap_bijective 𝒰 M k k hP).1 ?_, fun h => h ▸ rel_self hφ hP x⟩
  exact (Eq.symm (rel_self hφ hP x)).trans h

/-- The overlap relation is symmetric over an open inside both pieces. -/
lemma rel_symm (hφ : CocycleCondition 𝒰 M φ) {i k : 𝒰.I₀} {P : X.Opens}
    (hi : P ≤ (𝒰.f i).opensRange) (hk : P ≤ (𝒰.f k).opensRange) {z : Γ(G 𝒰 M k, P)}
    {s : Γ(G 𝒰 M i, P)} (h : Rel 𝒰 M φ k i P z s) : Rel 𝒰 M φ i k P s z := by
  obtain ⟨z', hz'⟩ := (bMap_bijective 𝒰 M i k hi).2 ((aMap 𝒰 M φ i k).app P s)
  have e : z = z' := (rel_self_iff hφ hk).1 (rel_trans hφ hi h (Eq.symm hz'))
  show (aMap 𝒰 M φ i k).app P s = (bMap 𝒰 M i k).app P z
  rw [e]
  exact hz'.symm

end Symmetry

section Projection

variable {𝒰 M φ}

/-- Over an open inside a piece, a section of the glued module is determined by its projection
to that piece. -/
lemma proj_app_injective {k : 𝒰.I₀} {O : X.Opens} (hO : O ≤ (𝒰.f k).opensRange) :
    Function.Injective ((proj 𝒰 M φ k).app O) := by
  intro x y hxy
  refine proj_ext 𝒰 M φ O x y fun i => (aMap_bijective 𝒰 M φ i k hO).1 ?_
  rw [proj_condition_apply, proj_condition_apply, hxy]

/-- Over an open inside a piece, every section of that piece comes from the glued module. -/
lemma proj_app_surjective (hφ : CocycleCondition 𝒰 M φ) {k : 𝒰.I₀} {O : X.Opens}
    (hO : O ≤ (𝒰.f k).opensRange) : Function.Surjective ((proj 𝒰 M φ k).app O) := by
  intro z
  choose s hs using fun i => (aMap_bijective 𝒰 M φ i k hO).2 ((bMap 𝒰 M i k).app O z)
  have hrel : ∀ i j, (aMap 𝒰 M φ i j).app O (s i) = (bMap 𝒰 M i j).app O (s j) := by
    intro i j
    have hPO : O ⊓ (𝒰.f i).opensRange ⊓ (𝒰.f j).opensRange ≤ O := inf_le_left.trans inf_le_left
    have hP : O ⊓ (𝒰.f i).opensRange ⊓ (𝒰.f j).opensRange ≤ (𝒰.f k).opensRange := hPO.trans hO
    have hi : Rel 𝒰 M φ i k _ _ _ := rel_map hPO (hs i)
    have hj : Rel 𝒰 M φ j k _ _ _ := rel_map hPO (hs j)
    exact rel_of_inf (rel_trans hφ hP hi (rel_symm hφ hP inf_le_right hj))
  obtain ⟨x, hx⟩ := proj_exists 𝒰 M φ O s hrel
  exact ⟨x, (hx k).trans ((rel_self_iff hφ hO).1 (hs k))⟩

lemma proj_app_bijective (hφ : CocycleCondition 𝒰 M φ) {k : 𝒰.I₀} {O : X.Opens}
    (hO : O ≤ (𝒰.f k).opensRange) : Function.Bijective ((proj 𝒰 M φ k).app O) :=
  ⟨proj_app_injective hO, proj_app_surjective hφ hO⟩

variable (𝒰 M φ) in
/-- The restriction of the glued module to a piece, mapped to that piece. -/
def restrictProj (k : 𝒰.I₀) : (restrictFunctor (𝒰.f k)).obj (glued 𝒰 M φ) ⟶ M k :=
  (restrictFunctor (𝒰.f k)).map (proj 𝒰 M φ k) ≫ (restrictAdjunction (𝒰.f k)).counit.app (M k)

lemma restrictProj_app_apply (k : 𝒰.I₀) (W : (𝒰.X k).Opens)
    (y : Γ(glued 𝒰 M φ, (𝒰.f k) ''ᵁ W)) (r : op ((𝒰.f k) ⁻¹ᵁ (𝒰.f k) ''ᵁ W) ⟶ op W) :
    (restrictProj 𝒰 M φ k).app W y =
      (M k).presheaf.map r ((proj 𝒰 M φ k).app ((𝒰.f k) ''ᵁ W) y) := by
  rw [presheaf_map_subsingleton (M k).presheaf r
    (eqToHom ((𝒰.f k).preimage_image_eq W).symm).op]
  rfl

lemma restrictProj_app_bijective (hφ : CocycleCondition 𝒰 M φ) (k : 𝒰.I₀)
    (W : (𝒰.X k).Opens) : Function.Bijective ((restrictProj 𝒰 M φ k).app W) := by
  have e : ⇑((restrictProj 𝒰 M φ k).app W) =
      (M k).presheaf.map (eqToHom ((𝒰.f k).preimage_image_eq W).symm).op ∘
        (proj 𝒰 M φ k).app ((𝒰.f k) ''ᵁ W) :=
    funext fun y => restrictProj_app_apply k W y _
  rw [e]
  exact (res_bijective _ _ ((𝒰.f k).preimage_image_eq W)).comp
    (proj_app_bijective hφ ((𝒰.f k).image_le_opensRange W))

lemma restrictProj_isIso (hφ : CocycleCondition 𝒰 M φ) (k : 𝒰.I₀) :
    IsIso (restrictProj 𝒰 M φ k) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  exact fun W => (ConcreteCategory.isIso_iff_bijective _).2 (restrictProj_app_bijective hφ k W)

end Projection

section Compatibility

open Langlands.SchemeModule.RigidifiedModule (compHom)

/-- A compatibility of pullbacks around a commutative square of open immersions follows from the
same compatibility read on iterated restrictions. -/
lemma pullback_compat_of_restrict {Z A B Y : AlgebraicGeometry.Scheme.{u}} (f : Z ⟶ A)
    (a : A ⟶ Y) (g : Z ⟶ B) (b : B ⟶ Y) [IsOpenImmersion f] [IsOpenImmersion a]
    [IsOpenImmersion g] [IsOpenImmersion b] (h : f ≫ a = g ≫ b) {N : Y.Modules}
    {Ma : A.Modules} {Mb : B.Modules} (ψa : (Scheme.Modules.pullback a).obj N ⟶ Ma)
    (ψb : (Scheme.Modules.pullback b).obj N ⟶ Mb)
    (e : (Scheme.Modules.pullback f).obj Ma ⟶ (Scheme.Modules.pullback g).obj Mb)
    (H : (restrictCompIso f a (f ≫ a) rfl).hom.app N ≫
        (restrictFunctor f).map ((restrictFunctorIsoPullback a).hom.app N ≫ ψa) ≫ rHom f g e =
      (restrictCompIso g b (f ≫ a) h.symm).hom.app N ≫
        (restrictFunctor g).map ((restrictFunctorIsoPullback b).hom.app N ≫ ψb)) :
    (Scheme.Modules.pullback f).map ψa ≫ e =
      (squarePullbackIso b f g a h N).hom ≫ (Scheme.Modules.pullback g).map ψb := by
  have s : (squarePullbackIso b f g a h N).hom =
      compHom f a _ rfl N ≫ inv (compHom g b _ h.symm N) :=
    (IsIso.eq_comp_inv _).2 (OpenCoverHomGluing.squarePullbackIso_hom_compHom _ _ _ _ _ _)
  have ka : (restrictCompIso f a (f ≫ a) rfl).hom.app N ≫
      (restrictFunctor f).map ((restrictFunctorIsoPullback a).hom.app N) ≫
        (restrictFunctorIsoPullback f).hom.app ((Scheme.Modules.pullback a).obj N) =
      (restrictFunctorIsoPullback (f ≫ a)).hom.app N ≫ inv (compHom f a _ rfl N) :=
    (IsIso.eq_comp_inv _).2
      (by simpa only [Category.assoc] using restrictCompIso_hom_app_comp f a _ rfl N)
  have kb : (restrictCompIso g b (f ≫ a) h.symm).hom.app N ≫
      (restrictFunctor g).map ((restrictFunctorIsoPullback b).hom.app N) ≫
        (restrictFunctorIsoPullback g).hom.app ((Scheme.Modules.pullback b).obj N) =
      (restrictFunctorIsoPullback (f ≫ a)).hom.app N ≫ inv (compHom g b _ h.symm N) :=
    (IsIso.eq_comp_inv _).2
      (by simpa only [Category.assoc] using restrictCompIso_hom_app_comp g b _ h.symm N)
  have H' := H =≫ (restrictFunctorIsoPullback g).hom.app Mb
  simp only [rHom, Functor.map_comp, Category.assoc, Iso.inv_hom_id_app,
    Category.comp_id] at H'
  rw [(restrictFunctorIsoPullback f).hom.naturality_assoc ψa,
    (restrictFunctorIsoPullback g).hom.naturality ψb, reassoc_of% ka, reassoc_of% kb,
    cancel_epi] at H'
  rw [s, Category.assoc, ← IsIso.inv_comp_eq]
  exact H'

lemma hom_ext_apply {T : AlgebraicGeometry.Scheme.{u}} {F F' : T.Modules} {f g : F ⟶ F'}
    (h : ∀ U x, f.app U x = g.app U x) : f = g :=
  Scheme.Modules.hom_ext _ _ fun U => ConcreteCategory.hom_ext _ _ (h U)

/-- A compatibility of iterated restrictions around a commutative square of open immersions can
be checked on sections. -/
lemma restrict_square_ext {Z A B Y : AlgebraicGeometry.Scheme.{u}} (f : Z ⟶ A) (a : A ⟶ Y)
    (g : Z ⟶ B) (b : B ⟶ Y) [IsOpenImmersion f] [IsOpenImmersion a] [IsOpenImmersion g]
    [IsOpenImmersion b] (h : f ≫ a = g ≫ b) {N : Y.Modules} {Ma : A.Modules} {Mb : B.Modules}
    (χa : (restrictFunctor a).obj N ⟶ Ma) (χb : (restrictFunctor b).obj N ⟶ Mb)
    (e : (restrictFunctor f).obj Ma ⟶ (restrictFunctor g).obj Mb)
    (H : ∀ (U : Z.Opens) (x : Γ(N, (f ≫ a) ''ᵁ U)),
      e.app U (χa.app (f ''ᵁ U)
          (N.presheaf.map (homOfLE (Scheme.Hom.comp_image f a U).ge).op x)) =
        χb.app (g ''ᵁ U) (N.presheaf.map
          (homOfLE ((Scheme.Hom.comp_image g b U).ge.trans (image_congr h U).ge)).op x)) :
    (restrictCompIso f a (f ≫ a) rfl).hom.app N ≫ (restrictFunctor f).map χa ≫ e =
      (restrictCompIso g b (f ≫ a) h.symm).hom.app N ≫ (restrictFunctor g).map χb := by
  refine hom_ext_apply fun U x => ?_
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
  erw [rCI_hom_apply f a (f ≫ a) rfl N U x (homOfLE (Scheme.Hom.comp_image f a U).ge).op,
    rCI_hom_apply g b (f ≫ a) h.symm N U x
      (homOfLE ((Scheme.Hom.comp_image g b U).ge.trans (image_congr h U).ge)).op]
  exact H U x

variable {𝒰 M φ}

lemma restrictProj_map_apply (k : 𝒰.I₀) (W : (𝒰.X k).Opens) {O : X.Opens}
    (hle : (𝒰.f k) ''ᵁ W ≤ O) (x : Γ(glued 𝒰 M φ, O)) (r : op ((𝒰.f k) ⁻¹ᵁ O) ⟶ op W) :
    (restrictProj 𝒰 M φ k).app W ((glued 𝒰 M φ).presheaf.map (homOfLE hle).op x) =
      (M k).presheaf.map r ((proj 𝒰 M φ k).app O x) := by
  rw [restrictProj_app_apply k W _ (eqToHom ((𝒰.f k).preimage_image_eq W).symm).op,
    ← OpenCoverHomGluing.hom_map_app]
  exact res_res (M k) _ _ r _

/-- The projections of the glued module are compatible with the overlap isomorphisms, read on
iterated restrictions. -/
lemma restrict_compat (i j : 𝒰.I₀) :
    (restrictCompIso (pullback.fst (𝒰.f i) (𝒰.f j)) (𝒰.f i)
        (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i) rfl).hom.app (glued 𝒰 M φ) ≫
      (restrictFunctor (pullback.fst (𝒰.f i) (𝒰.f j))).map (restrictProj 𝒰 M φ i) ≫
        (φr 𝒰 M φ i j).hom =
    (restrictCompIso (pullback.snd (𝒰.f i) (𝒰.f j)) (𝒰.f j)
        (pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i) pullback.condition.symm).hom.app (glued 𝒰 M φ) ≫
      (restrictFunctor (pullback.snd (𝒰.f i) (𝒰.f j))).map (restrictProj 𝒰 M φ j) := by
  refine restrict_square_ext _ _ _ _ pullback.condition _ _ _ fun A x => ?_
  have hA : A ≤ pullback.fst (𝒰.f i) (𝒰.f j) ⁻¹ᵁ (𝒰.f i) ⁻¹ᵁ
      ((pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i) ''ᵁ A) :=
    ((pullback.fst (𝒰.f i) (𝒰.f j) ≫ 𝒰.f i).preimage_image_eq A).ge
  rw [restrictProj_map_apply i _ _ x (homOfLE (image_le_of_le_preimage _ hA)).op,
    restrictProj_map_apply j _ _ x
      (homOfLE ((Scheme.Hom.image_mono _ hA).trans (image_snd_le 𝒰 i j _))).op]
  exact rel_restrict (proj_condition_apply 𝒰 M φ i j _ x) A hA _ _

variable (𝒰 M φ) in
/-- The identification of the pullback of the glued module to a piece with that piece. -/
def pieceIso (hφ : CocycleCondition 𝒰 M φ) (k : 𝒰.I₀) :
    (Scheme.Modules.pullback (𝒰.f k)).obj (glued 𝒰 M φ) ≅ M k :=
  haveI := restrictProj_isIso hφ k
  ((restrictFunctorIsoPullback (𝒰.f k)).app (glued 𝒰 M φ)).symm ≪≫
    asIso (restrictProj 𝒰 M φ k)

lemma restrictFunctorIsoPullback_hom_pieceIso_hom (hφ : CocycleCondition 𝒰 M φ) (k : 𝒰.I₀) :
    (restrictFunctorIsoPullback (𝒰.f k)).hom.app (glued 𝒰 M φ) ≫ (pieceIso 𝒰 M φ hφ k).hom =
      restrictProj 𝒰 M φ k :=
  Iso.hom_inv_id_app_assoc _ _ _

/-- The identifications of the pullbacks of the glued module with the pieces are compatible with
the overlap isomorphisms. -/
lemma pieceIso_compat (hφ : CocycleCondition 𝒰 M φ) (i j : 𝒰.I₀) :
    CompEq2
      ((Scheme.Modules.pullback (pullback.fst (𝒰.f i) (𝒰.f j))).map (pieceIso 𝒰 M φ hφ i).hom)
      (φ i j).hom
      (squarePullbackIso (𝒰.f j) (pullback.fst (𝒰.f i) (𝒰.f j)) (pullback.snd (𝒰.f i) (𝒰.f j))
          (𝒰.f i) pullback.condition (glued 𝒰 M φ)).hom
      ((Scheme.Modules.pullback (pullback.snd (𝒰.f i) (𝒰.f j))).map
        (pieceIso 𝒰 M φ hφ j).hom) := by
  refine CompEq2.of_eq (pullback_compat_of_restrict _ _ _ _ pullback.condition _ _ _ ?_)
  rw [restrictFunctorIsoPullback_hom_pieceIso_hom, restrictFunctorIsoPullback_hom_pieceIso_hom,
    ← φr_hom]
  exact restrict_compat i j

end Compatibility

end Langlands.Scheme.Modules.OpenCoverModuleGluing

namespace Langlands.Scheme.Modules

/-- Module sheaves on the members of an open cover with overlap isomorphisms satisfying the
cocycle condition glue to a module sheaf on the whole scheme. -/
theorem openCoverModuleGluing : OpenCoverModuleGluingStatement.{u} := fun _ 𝒰 M φ hφ =>
  have hφ' : OpenCoverModuleGluing.CocycleCondition 𝒰 M φ := fun i j k =>
    (OpenCoverModuleGluing.CompEq4.of_eq (hφ i j k) :)
  ⟨OpenCoverModuleGluing.glued 𝒰 M φ, OpenCoverModuleGluing.pieceIso 𝒰 M φ hφ',
    fun i j => OpenCoverModuleGluing.CompEq2.eq (OpenCoverModuleGluing.pieceIso_compat hφ' i j)⟩

end Langlands.Scheme.Modules
