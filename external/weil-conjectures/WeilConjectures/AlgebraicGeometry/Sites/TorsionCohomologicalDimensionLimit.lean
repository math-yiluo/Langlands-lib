/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing
public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyContinuity
public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyFilteredColimit
public import WeilConjectures.AlgebraicGeometry.Sites.EtaleZariskiComparison
public import WeilConjectures.AlgebraicGeometry.Sites.SectionContinuity
public import WeilConjectures.AlgebraicGeometry.Sites.TorsionCohomologicalDimension
public import WeilConjectures.SixFunctors.BaseChange.Sections

/-!
# Torsion cohomological dimension of an inverse limit

A uniform bound `cd_tor(Xᵢ) ≤ c` on a cofiltered system of quasi-compact quasi-separated schemes
with affine transition maps passes to the limit `X = lim Xᵢ`
(`AlgebraicGeometry.Scheme.HasTorsionCohomologicalDimensionLE.of_isLimit`).

## Main definitions and statements

- `AlgebraicGeometry.Etale.pushPullTransition`: for `pᵢ = pⱼ ≫ f`, the transition map
  `pᵢ^* pᵢ_* F ⟶ pⱼ^* pⱼ_* F`, compatible with the counits and with composition.
- `AlgebraicGeometry.Etale.pushPullDiagram`, `AlgebraicGeometry.Etale.pushPullCocone`: for the
  projections `pᵢ : X ⟶ Dᵢ` of a limit, the diagram `i ↦ pᵢ^* pᵢ_* F` and its cocone of counits.
- `AlgebraicGeometry.Etale.isColimitPushPullCocone`: every abelian étale sheaf `F` on
  `X = lim Dᵢ` is the colimit of the `pᵢ^* pᵢ_* F`.
- `AlgebraicGeometry.Scheme.HasTorsionCohomologicalDimensionLE.of_isLimit`: a uniform bound
  `cd_tor(Xᵢ) ≤ c` passes to the limit.

## Implementation notes

That `F = colimᵢ pᵢ^* pᵢ_* F` is checked on sections: every section of `F` is, locally on an
affine étale `X`-scheme `V` lying over an affine open of `X`, a section over
`V = Y ×_{Dᵢ} X` for an étale `Dᵢ`-scheme `Y`, that is a section of `pᵢ_* F` over `Y`; and a
section `φ^* g` of `pᵢ^* pᵢ_* F` vanishing in `F` vanishes in `pⱼ^* pⱼ_* F` as soon as the
morphism `φ` descends to the stage `Dⱼ` (`AlgebraicGeometry.Etale.exists_hasStageModel`).
The cohomology of `pᵢ^* pᵢ_* F` is computed by the continuity of étale cohomology
(`AlgebraicGeometry.Etale.isZero_rightDerived_sectionsFunctor_upperStar_of_isLimit_addCommGrpCat`).
For the bound on the limit, a torsion sheaf `F` killed by `n` is the filtered colimit of the
`pᵢ^* pᵢ_* F`, whose cohomology is the colimit of the cohomology of the `pⱼᵢ^* pᵢ_* F` on the
`Xⱼ` (`AlgebraicGeometry.Scheme.subsingleton_H_pushPullDiagram_obj`); cohomology commutes with
filtered colimits, and a general torsion sheaf is the union of its `n`-torsion subsheaves.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

section Transition

variable {X T T' : Scheme.{u}} (pj : X ⟶ T') (f : T' ⟶ T) (pi : X ⟶ T) (h : pi = pj ≫ f)
  (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})

/-- (Implementation) The adjoint `pᵢ_* F ⟶ pᵢ_* pⱼ^* pⱼ_* F` of the transition map
`AlgebraicGeometry.Etale.pushPullTransition`. -/
noncomputable def pushPullTransitionAdj :
    (pi)_*[AddCommGrpCat.{u + 1}].obj F ⟶ (pi)_*[AddCommGrpCat.{u + 1}].obj
      ((pj)^*[AddCommGrpCat.{u + 1}].obj ((pj)_*[AddCommGrpCat.{u + 1}].obj F)) :=
  (lowerStarComp AddCommGrpCat.{u + 1} pj f pi h).inv.app F ≫
    (f)_*[AddCommGrpCat.{u + 1}].map
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} pj).unit.app
        ((pj)_*[AddCommGrpCat.{u + 1}].obj F)) ≫
    (lowerStarComp AddCommGrpCat.{u + 1} pj f pi h).hom.app _

/-- For `pᵢ = pⱼ ≫ f`, the transition map `pᵢ^* pᵢ_* F ⟶ pⱼ^* pⱼ_* F` compatible with the
counits (`AlgebraicGeometry.Etale.pushPullTransition_comp_counit`). -/
noncomputable def pushPullTransition :
    (pi)^*[AddCommGrpCat.{u + 1}].obj ((pi)_*[AddCommGrpCat.{u + 1}].obj F) ⟶
      (pj)^*[AddCommGrpCat.{u + 1}].obj ((pj)_*[AddCommGrpCat.{u + 1}].obj F) :=
  ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} pi).homEquiv _ _).symm
    (pushPullTransitionAdj pj f pi h F)

lemma unit_app_comp_lowerStar_map_pushPullTransition :
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} pi).unit.app _ ≫
      (pi)_*[AddCommGrpCat.{u + 1}].map (pushPullTransition pj f pi h F) =
        pushPullTransitionAdj pj f pi h F :=
  ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} pi).homEquiv_unit _ _ _).symm.trans
    (Equiv.apply_symm_apply _ _)

lemma pushPullTransitionAdj_comp_lowerStar_map_counit :
    pushPullTransitionAdj pj f pi h F ≫ (pi)_*[AddCommGrpCat.{u + 1}].map
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} pj).counit.app F) = 𝟙 _ := by
  rw [pushPullTransitionAdj, Category.assoc, Category.assoc,
    ← (lowerStarComp AddCommGrpCat.{u + 1} pj f pi h).hom.naturality, Functor.comp_map,
    ← Functor.map_comp_assoc]
  simp only [Functor.id_obj, Adjunction.right_triangle_components, CategoryTheory.Functor.map_id,
    Category.id_comp, Iso.inv_hom_id_app]

@[reassoc (attr := simp)]
lemma pushPullTransition_comp_counit :
    pushPullTransition pj f pi h F ≫
      (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} pj).counit.app F =
        (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} pi).counit.app F := by
  rw [pushPullTransition, ← Adjunction.homEquiv_naturality_right_symm,
    pushPullTransitionAdj_comp_lowerStar_map_counit, Adjunction.homEquiv_counit,
    CategoryTheory.Functor.map_id, Category.id_comp]
  rfl



/-- The counit of `pᵢ^* ⊣ pᵢ_*` sends the pullback `φ^* g` of a section `g` of `pᵢ_* F` to the
restriction of `g` along `V ⟶ U ×_T X`. -/
lemma counit_app_pullSection {V : X.Etale} {U : T.Etale} (φ : V.left ⟶ U.left)
    (hφ : φ ≫ U.hom = V.hom ≫ pi) (g : ((pi)_*[AddCommGrpCat.{u + 1}].obj F).obj.obj (op U)) :
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} pi).counit.app F).hom.app (op V)
        (pullSection pi _ φ hφ g) = F.obj.map (homToPullback pi φ hφ).op g := by
  refine (NatTrans.naturality_apply
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} pi).counit.app F).hom
    (homToPullback pi φ hφ).op _).trans ?_
  congr 1
  exact congrArg (fun φ ↦ φ.hom.app (op U) g)
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} pi).right_triangle_components F)

/-- The transition map sends the pullback `φ^* g` of a section `g` of `pᵢ_* F` to the pullback
of the corresponding section of `pⱼ_* F` over `U ×_T T'`. -/
lemma pushPullTransition_app_pullSection {V : X.Etale} {U : T.Etale} (φ : V.left ⟶ U.left)
    (hφ : φ ≫ U.hom = V.hom ≫ pi) (g : ((pi)_*[AddCommGrpCat.{u + 1}].obj F).obj.obj (op U)) :
    (pushPullTransition pj f pi h F).hom.app (op V) (pullSection pi _ φ hφ g) =
      pullSection pj _ (U := (MorphismProperty.Over.pullback @Etale ⊤ f).obj U)
        (pullback.lift φ (V.hom ≫ pj) (by rw [hφ, h, Category.assoc])) (by simp)
        (((lowerStarComp AddCommGrpCat.{u + 1} pj f pi h).inv.app F).hom.app (op U) g) := by
  refine (NatTrans.naturality_apply (pushPullTransition pj f pi h F).hom
    (homToPullback pi φ hφ).op _).trans ?_
  have h₁ : (pushPullTransition pj f pi h F).hom.app
      (op ((MorphismProperty.Over.pullback @Etale ⊤ pi).obj U))
      (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} pi).unit.app _).hom.app (op U) g) =
        (pushPullTransitionAdj pj f pi h F).hom.app (op U) g :=
    congrArg (fun φ ↦ φ.hom.app (op U) g)
      (unit_app_comp_lowerStar_map_pushPullTransition pj f pi h F)
  rw [h₁]
  change ((pj)^*[AddCommGrpCat.{u + 1}].obj ((pj)_*[AddCommGrpCat.{u + 1}].obj F)).obj.map _
    (((lowerStarComp AddCommGrpCat.{u + 1} pj f pi h).hom.app _).hom.app (op U)
      (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} pj).unit.app _).hom.app
        (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U))
        (((lowerStarComp AddCommGrpCat.{u + 1} pj f pi h).inv.app F).hom.app (op U) g))) = _
  rw [lowerStarComp_hom_app_hom_app]
  erw [← ConcreteCategory.comp_apply, ← Functor.map_comp,
    ← op_comp, map_unit_app_eq_pullSection]
  apply pullSection_congr
  apply pullback.hom_ext <;> simp [homToPullback, pullback.condition]


/-- Morphisms out of `t^* G` agreeing on all pullbacks `φ^* g` of sections of `G` agree. -/
lemma upperStar_hom_ext {R : Scheme.{u}} (t : X ⟶ R)
    {G : Sheaf R.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {a b : (t)^*[AddCommGrpCat.{u + 1}].obj G ⟶ H}
    (hab : ∀ (V : X.Etale) (U : R.Etale) (φ : V.left ⟶ U.left) (hφ : φ ≫ U.hom = V.hom ≫ t)
      (g : G.obj.obj (op U)),
      a.hom.app (op V) (pullSection t G φ hφ g) = b.hom.app (op V) (pullSection t G φ hφ g)) :
    a = b := by
  refine (sheafToPresheaf _ _).map_injective (NatTrans.ext (funext fun V ↦ ?_))
  ext s
  change a.hom.app V s = b.hom.app V s
  rw [← sub_eq_zero]
  choose V' a' U φ hφ g hx hs using fun x ↦ exists_pullSection_eq t G s x
  refine eq_zero_of_forall_map_eq_zero H a' (fun x ↦ ⟨x, hx x⟩) _ fun x ↦ ?_
  rw [map_sub, ← NatTrans.naturality_apply, ← NatTrans.naturality_apply]
  change a.hom.app _ _ - b.hom.app _ _ = 0
  rw [hs, hab, sub_self]


/-- The transition maps are compatible with composition. -/
lemma pushPullTransition_comp {T'' : Scheme.{u}} (pk : X ⟶ T'') (f' : T'' ⟶ T')
    (hj : pj = pk ≫ f') :
    pushPullTransition pj f pi h F ≫ pushPullTransition pk f' pj hj F =
      pushPullTransition pk (f' ≫ f) pi (by rw [h, hj, Category.assoc]) F := by
  refine upperStar_hom_ext pi fun V U φ hφ g ↦ ?_
  rw [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, ConcreteCategory.comp_apply,
    pushPullTransition_app_pullSection, pushPullTransition_app_pullSection,
    pushPullTransition_app_pullSection]
  let b := (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) f' f).hom.app U
  have hψ : pullback.lift φ (V.hom ≫ pk) (by rw [hφ, h, hj, Category.assoc, Category.assoc]) ≫
      ((MorphismProperty.Over.pullback @Etale ⊤ (f' ≫ f)).obj U).hom = V.hom ≫ pk := by simp
  refine (pullSection_congr pk _ _ (φ' := pullback.lift φ (V.hom ≫ pk) (by
      rw [hφ, h, hj, Category.assoc, Category.assoc]) ≫ b.left) (by
      apply pullback.hom_ext
      · apply pullback.hom_ext <;> simp [b, hj]
      · simp [b]) _).trans
    ((pullSection_comp pk _ b _ hψ _).trans ?_)
  congr 1
  simp only [lowerStarComp_inv_app_hom_app, lowerStar_obj_val_map]
  have key : (MorphismProperty.Over.pullback @Etale ⊤ pk).map b ≫
      (MorphismProperty.Over.pullbackComp pk f' pj hj).inv.app
        ((MorphismProperty.Over.pullback @Etale ⊤ f).obj U) ≫
      (MorphismProperty.Over.pullbackComp pj f pi h).inv.app U =
      (MorphismProperty.Over.pullbackComp pk (f' ≫ f) pi
        (by rw [h, hj, Category.assoc])).inv.app U := by
    apply MorphismProperty.Over.Hom.ext
    refine pullback.hom_ext ?_ ?_ <;> simp [b]
  rw [← key, op_comp, op_comp, Functor.map_comp, Functor.map_comp]
  rfl

end Transition


section Colimit

variable {X : Scheme.{u}}

/-- A section of an abelian étale sheaf which vanishes locally on the members of a covering
sieve, each of which is again covered by a sieve on which it vanishes, is zero. -/
lemma eq_zero_of_forall_mem_exists {G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    {W : X.Etale} (s : G.obj.obj (op W)) {R : Sieve W} (hR : R ∈ X.smallEtaleTopology W)
    (h : ∀ ⦃V : X.Etale⦄ (f : V ⟶ W), R f → ∃ R' ∈ X.smallEtaleTopology V,
      ∀ ⦃V' : X.Etale⦄ (g : V' ⟶ V), R' g → G.obj.map (g ≫ f).op s = 0) : s = 0 := by
  let S : Sieve W :=
    { arrows := fun _ f ↦ G.obj.map f.op s = 0
      downward_closed := fun {_ _} f hf g ↦ by
        rw [op_comp, G.obj.map_comp, ConcreteCategory.comp_apply, hf, map_zero] }
  have hS : S ∈ X.smallEtaleTopology W := by
    refine X.smallEtaleTopology.transitive hR S fun V f hf ↦ ?_
    obtain ⟨R', hR', hR's⟩ := h f hf
    exact X.smallEtaleTopology.superset_covering (fun V' g hg ↦ hR's g hg) hR'
  let GT := (sheafCompose X.smallEtaleTopology (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj G
  refine ((isSheaf_iff_isSheaf_of_type _ _).1 GT.property _ hS).isSeparatedFor.ext
    fun V f hf ↦ ?_
  change G.obj.map f.op s = G.obj.map f.op 0
  rw [map_zero]
  exact hf

/-- **A cocone of abelian étale sheaves which is locally surjective and locally injective is a
colimit.** Let `c` be a cocone over a filtered diagram `Φ` of abelian étale sheaves. If every
section of `c.pt` locally comes from some `Φ k`, and every section of some `Φ k` which vanishes
in `c.pt` locally vanishes in some later `Φ k'`, then `c` is a colimit cocone. -/
noncomputable def isColimitOfLocally {K : Type u} [SmallCategory K] [IsFiltered K]
    {Φ : K ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (c : Cocone Φ)
    (hsurj : ∀ (W : X.Etale) (s : c.pt.obj.obj (op W)), ∃ R ∈ X.smallEtaleTopology W,
      ∀ ⦃V : X.Etale⦄ (f : V ⟶ W), R f →
        ∃ (k : K) (t : (Φ.obj k).obj.obj (op V)), (c.ι.app k).hom.app (op V) t =
          c.pt.obj.map f.op s)
    (hinj : ∀ (k : K) (W : X.Etale) (t : (Φ.obj k).obj.obj (op W)),
      (c.ι.app k).hom.app (op W) t = 0 → ∃ R ∈ X.smallEtaleTopology W,
        ∀ ⦃V : X.Etale⦄ (f : V ⟶ W), R f →
          ∃ (k' : K) (a : k ⟶ k'), (Φ.map a).hom.app (op V) ((Φ.obj k).obj.map f.op t) = 0) :
    IsColimit c := by
  have : HasColimitsOfSize.{u + 1, u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    IsGrothendieckAbelian.hasColimits _
  have : HasColimitsOfSize.{u, u} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    hasColimitsOfSizeShrink.{u, u, u + 1, u + 1} _
  let d := colimit.desc Φ c
  have hd (k : K) (V : X.Etale) (t : (Φ.obj k).obj.obj (op V)) :
      d.hom.app (op V) ((colimit.ι Φ k).hom.app (op V) t) = (c.ι.app k).hom.app (op V) t := by
    rw [← ConcreteCategory.comp_apply, ← NatTrans.comp_app,
      ← ObjectProperty.FullSubcategory.comp_hom, colimit.ι_desc]
    rfl
  have : Sheaf.IsLocallySurjective d := ⟨fun {W} s ↦ by
    obtain ⟨R, hR, hRs⟩ := hsurj W s
    refine X.smallEtaleTopology.superset_covering (fun V f hf ↦ ?_) hR
    obtain ⟨k, t, ht⟩ := hRs f hf
    exact ⟨(colimit.ι Φ k).hom.app (op V) t, (hd k V t).trans ht⟩⟩
  have : Mono d := by
    refine Sheaf.mono_of_injective _ fun W ↦ (injective_iff_map_eq_zero _).2 fun s hs ↦ ?_
    obtain ⟨R, hR, hRs⟩ := GrothendieckTopology.exists_mem_forall_exists_app_eq_of_isColimit
      (Scheme.isConservativeFamilyOfPoints_ulift_pointSmallEtale X) (colimit.isColimit Φ) s
    refine eq_zero_of_forall_mem_exists s hR fun V f hf ↦ ?_
    obtain ⟨k, t, ht⟩ := hRs f hf
    replace ht : (colimit.ι Φ k).hom.app (op V) t = (colimit Φ).obj.map f.op s := ht
    have h0 : (c.ι.app k).hom.app (op V) t = 0 := by
      rw [← hd, ht, NatTrans.naturality_apply, hs, map_zero]
    obtain ⟨R', hR', hR't⟩ := hinj k V t h0
    refine ⟨R', hR', fun V' g hg ↦ ?_⟩
    obtain ⟨k', a, ha⟩ := hR't g hg
    rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, ← ht,
      ← NatTrans.naturality_apply, ← colimit.w Φ a, ObjectProperty.FullSubcategory.comp_hom,
      NatTrans.comp_app, ConcreteCategory.comp_apply, ha, map_zero]
  have : IsIso ((colimit.isColimit Φ).desc c) := isIso_of_mono_of_epi d
  exact IsColimit.ofPointIso (colimit.isColimit Φ)

end Colimit


/-- The transition map along an identity is the identity. -/
lemma pushPullTransition_self {X T : Scheme.{u}} (pi : X ⟶ T) (f : T ⟶ T) (hf : f = 𝟙 T)
    (h : pi = pi ≫ f) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    pushPullTransition pi f pi h F = 𝟙 _ := by
  subst hf
  refine upperStar_hom_ext pi fun V U φ hφ g ↦ ?_
  rw [pushPullTransition_app_pullSection, ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app,
    CategoryTheory.id_apply]
  let b := (MorphismProperty.Over.pullbackId (P := @Etale) ⊤ T).hom.app U
  have hψ : pullback.lift φ (V.hom ≫ pi) (by rw [hφ, Category.comp_id]) ≫
      ((MorphismProperty.Over.pullback @Etale ⊤ (𝟙 T)).obj U).hom = V.hom ≫ pi := by simp
  refine Eq.trans ?_ (pullSection_congr pi _ (φ := pullback.lift φ (V.hom ≫ pi)
      (by rw [hφ, Category.comp_id]) ≫ b.left) (φ' := φ) (by simp [b, hφ])
      (by rw [MorphismProperty.Over.pullbackId_hom_app_left, pullback.lift_fst]) _)
  refine Eq.trans ?_ (pullSection_comp pi _ b _ hψ _).symm
  congr 1
  simp only [lowerStarComp_inv_app_hom_app, lowerStar_obj_val_map]
  have key : (MorphismProperty.Over.pullbackComp pi (𝟙 T) pi h).inv.app U =
      (MorphismProperty.Over.pullback @Etale ⊤ pi).map b := by
    apply MorphismProperty.Over.Hom.ext
    refine pullback.hom_ext ?_ ?_ <;> simp [b]
  rw [key]
  rfl

/-- `pushPullTransition` only depends on the morphism `f`, not on the proof of `pᵢ = pⱼ ≫ f`. -/
lemma pushPullTransition_congr {X T T' : Scheme.{u}} (pj : X ⟶ T') {f f' : T' ⟶ T} (pi : X ⟶ T)
    (h : pi = pj ≫ f) (hf : f = f') (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    pushPullTransition pj f pi h F = pushPullTransition pj f' pi (hf ▸ h) F := by
  subst hf; rfl

section Limit

variable {I : Type u} [SmallCategory I] (D : I ⥤ Scheme.{u}) (c : Cone D)
  (F : Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})

/-- The diagram `i ↦ pᵢ^* pᵢ_* F` of abelian étale sheaves on the limit `X = lim Dᵢ`, for the
projections `pᵢ : X ⟶ Dᵢ`. -/
@[simps]
noncomputable def pushPullDiagram : Iᵒᵖ ⥤ Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1} where
  obj i := (c.π.app i.unop)^*[AddCommGrpCat.{u + 1}].obj
    ((c.π.app i.unop)_*[AddCommGrpCat.{u + 1}].obj F)
  map {i j} g := pushPullTransition (c.π.app j.unop) (D.map g.unop) (c.π.app i.unop)
    (c.w g.unop).symm F
  map_id i := pushPullTransition_self _ _ (by simp) _ F
  map_comp {i j k} g g' := by
    rw [pushPullTransition_comp]
    exact pushPullTransition_congr _ _ _ (by simp) F

/-- The cocone of counits `pᵢ^* pᵢ_* F ⟶ F` over `AlgebraicGeometry.Etale.pushPullDiagram`. -/
@[simps]
noncomputable def pushPullCocone : Cocone (pushPullDiagram D c F) where
  pt := F
  ι :=
    { app i := (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (c.π.app i.unop)).counit.app F
      naturality i j g := by
        simp only [Functor.const_obj_obj, pushPullDiagram_map,
          pushPullTransition_comp_counit, Functor.const_obj_map, Category.comp_id] }

end Limit


section Model

variable {X R : Scheme.{u}} (P : X ⟶ R)

/-- For a cartesian square `V = Y ×_R X` with `Y` étale over `R`, the canonical morphism
`V ⟶ Y ×_R X` of étale `X`-schemes has an inverse. -/
lemma exists_inverse_homToPullback {V : X.Etale} {Y : Scheme.{u}} {p : Y ⟶ R} (hp : Etale p)
    {e : V.left ⟶ Y} (H : IsPullback e V.hom p P) :
    ∃ κ : (MorphismProperty.Over.pullback @Etale ⊤ P).obj (MorphismProperty.Over.mk ⊤ p hp) ⟶ V,
      homToPullback P (U := MorphismProperty.Over.mk ⊤ p hp) e H.w ≫ κ = 𝟙 V ∧
        κ ≫ homToPullback P (U := MorphismProperty.Over.mk ⊤ p hp) e H.w = 𝟙 _ := by
  have he : (homToPullback P (U := MorphismProperty.Over.mk ⊤ p hp) e H.w).left =
      H.isoPullback.hom := by
    apply pullback.hom_ext
    · simp only [homToPullback_left_fst]
      exact H.isoPullback_hom_fst.symm
    · simp only [homToPullback_left_snd]
      exact H.isoPullback_hom_snd.symm
  refine ⟨MorphismProperty.Over.homMk H.isoPullback.inv H.isoPullback_inv_snd trivial, ?_, ?_⟩
  · apply MorphismProperty.Over.Hom.ext
    simp [he]
  · apply MorphismProperty.Over.Hom.ext
    simp [he]

end Model


section LimitLocal

variable {I : Type u} [SmallCategory I] [IsCofiltered I] (D : I ⥤ Scheme.{u}) {c : Cone D}
  (hc : IsLimit c) (F : Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
  [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)] [∀ i, QuasiSeparatedSpace (D.obj i)]

/-- Every étale `X`-scheme is covered by affine étale `X`-schemes lying over affine opens of
`X`. -/
lemma exists_affine_ofOpens {X : Scheme.{u}} (W : X.Etale) (x : W.left) :
    ∃ (V₀ : W.left.Opens) (N : X.Opens), IsAffineOpen V₀ ∧ IsAffineOpen N ∧ x ∈ V₀ ∧
      Set.range (Scheme.Etale.ofOpens W V₀).hom ⊆ (N : Set X) := by
  obtain ⟨_, ⟨N, hN, rfl⟩, hxN, -⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (W.hom x)) isOpen_univ
  obtain ⟨_, ⟨V₀, hV₀, rfl⟩, hxV₀, hV₀N⟩ := W.left.isBasis_affineOpens.exists_subset_of_mem_open
    (show x ∈ W.hom ⁻¹ᵁ N from hxN) (W.hom ⁻¹ᵁ N).isOpen
  refine ⟨V₀, N, hV₀, hN, hxV₀, ?_⟩
  rintro _ ⟨z, rfl⟩
  exact hV₀N z.2

include hc in
/-- Every section of `F` is locally the image of a section of some `pᵢ^* pᵢ_* F`. -/
lemma pushPullCocone_exists_app_eq (W : c.pt.Etale) (s : F.obj.obj (op W)) :
    ∃ R ∈ c.pt.smallEtaleTopology W, ∀ ⦃V : c.pt.Etale⦄ (f : V ⟶ W), R f →
      ∃ (i : Iᵒᵖ) (t : ((pushPullDiagram D c F).obj i).obj.obj (op V)),
        ((pushPullCocone D c F).ι.app i).hom.app (op V) t = F.obj.map f.op s := by
  have key (x : W.left) : ∃ (V : c.pt.Etale) (a : V ⟶ W) (i : Iᵒᵖ)
      (t : ((pushPullDiagram D c F).obj i).obj.obj (op V)), x ∈ Set.range a.left ∧
        ((pushPullCocone D c F).ι.app i).hom.app (op V) t = F.obj.map a.op s := by
    obtain ⟨V₀, N, hV₀, hN, hxV₀, hVN⟩ := exists_affine_ofOpens W x
    let V := Scheme.Etale.ofOpens W V₀
    have : IsAffine ((𝟭 Scheme).obj V.left) := hV₀
    have : Etale V.hom := V.prop
    obtain ⟨i, Y, -, p, hp, e, H⟩ :=
      Scheme.exists_isPullback_of_etale_of_isAffineOpen D c hc V.hom hN hVN
    obtain ⟨κ, hκ, -⟩ := exists_inverse_homToPullback (c.π.app i) hp H
    refine ⟨V, Scheme.Etale.ofOpensι W V₀, op i,
      pullSection (c.π.app i) _ (U := MorphismProperty.Over.mk ⊤ p hp) e H.w
        (F.obj.map κ.op (F.obj.map (Scheme.Etale.ofOpensι W V₀).op s)), ⟨⟨x, hxV₀⟩, rfl⟩, ?_⟩
    change ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (c.π.app i)).counit.app F).hom.app
      _ _ = _
    rw [counit_app_pullSection, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
      hκ, op_id, CategoryTheory.Functor.map_id, CategoryTheory.id_apply]
  choose V a i t hx ht using key
  refine ⟨Sieve.ofArrows V a, (Scheme.ofArrows_mem_smallEtaleTopology_iff a).2
    (Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.2 ⟨x, hx x⟩), ?_⟩
  rintro V' f ⟨_, g, _, ⟨x⟩, rfl⟩
  refine ⟨i x, ((pushPullDiagram D c F).obj (i x)).obj.map g.op (t x), ?_⟩
  rw [NatTrans.naturality_apply, ht x, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
  rfl


include hc in
/-- A section of some `pᵢ^* pᵢ_* F` which vanishes in `F` locally vanishes in some later
`pⱼ^* pⱼ_* F`. -/
lemma pushPullCocone_exists_map_eq_zero [∀ i, CompactSpace (D.obj i)] (k : Iᵒᵖ) (W : c.pt.Etale)
    (t : ((pushPullDiagram D c F).obj k).obj.obj (op W))
    (ht : ((pushPullCocone D c F).ι.app k).hom.app (op W) t = 0) :
    ∃ R ∈ c.pt.smallEtaleTopology W, ∀ ⦃V : c.pt.Etale⦄ (f : V ⟶ W), R f →
      ∃ (k' : Iᵒᵖ) (a : k ⟶ k'),
        ((pushPullDiagram D c F).map a).hom.app (op V)
          (((pushPullDiagram D c F).obj k).obj.map f.op t) = 0 := by
  have key (x : W.left) : ∃ (V : c.pt.Etale) (a : V ⟶ W) (k' : Iᵒᵖ) (g : k ⟶ k'),
      x ∈ Set.range a.left ∧ ((pushPullDiagram D c F).map g).hom.app (op V)
        (((pushPullDiagram D c F).obj k).obj.map a.op t) = 0 := by
    obtain ⟨V', a', U, φ, hφ, g₀, ⟨y, hy⟩, hs⟩ := exists_pullSection_eq (c.π.app k.unop)
      ((c.π.app k.unop)_*[AddCommGrpCat.{u + 1}].obj F) t x
    obtain ⟨V₀, N, hV₀, hN, hyV₀, hVN⟩ := exists_affine_ofOpens V' y
    let V := Scheme.Etale.ofOpens V' V₀
    let a := Scheme.Etale.ofOpensι V' V₀ ≫ a'
    have hφ₀ : (V₀.ι ≫ φ) ≫ U.hom = V.hom ≫ c.π.app k.unop := by
      rw [Category.assoc, hφ]; rfl
    have hs₀ : ((pushPullDiagram D c F).obj k).obj.map a.op t =
        pullSection (c.π.app k.unop) ((c.π.app k.unop)_*[AddCommGrpCat.{u + 1}].obj F) (V := V)
          (U := U) (V₀.ι ≫ φ) hφ₀ g₀ := by
      rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
      erw [hs]
      exact map_pullSection (c.π.app k.unop) _ φ hφ g₀ (Scheme.Etale.ofOpensι V' V₀)
    have hzero : F.obj.map (homToPullback (c.π.app k.unop) (V := V) (U := U) _ hφ₀).op g₀ = 0 := by
      rw [← counit_app_pullSection, ← hs₀]
      refine (NatTrans.naturality_apply ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
        (c.π.app k.unop)).counit.app F).hom a.op t).trans ?_
      erw [ht]
      exact map_zero _
    -- descend `V` and `V₀.ι ≫ φ` to a stage over `k`
    let i := k.unop
    let D' : Over i ⥤ Scheme.{u} := Over.forget i ⋙ D
    let π' : D' ⟶ (Functor.const (Over i)).obj (D.obj i) :=
      { app j := D.map j.hom
        naturality j j' g := by
          simp only [D', Functor.comp_obj, Over.forget_obj, Functor.comp_map, Over.forget_map,
            Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id, ← D.map_comp,
            Over.w g] }
    have hc' : IsLimit (c.whisker (Over.forget i)) :=
      (Functor.Initial.isLimitWhiskerEquiv (Over.forget i) c).symm hc
    have (j : Over i) : CompactSpace (D'.obj j) := inferInstanceAs (CompactSpace (D.obj j.left))
    have (j : Over i) : QuasiSeparatedSpace (D'.obj j) :=
      inferInstanceAs (QuasiSeparatedSpace (D.obj j.left))
    have {j j' : Over i} (g : j ⟶ j') : IsAffineHom (D'.map g) :=
      inferInstanceAs (IsAffineHom (D.map g.left))
    have : IsAffine V.left := hV₀
    have : LocallyOfFinitePresentation U.hom := inferInstance
    obtain ⟨j, Y, p, e, ψ, -, hp, -, H, hψ, -, heψ, -⟩ := exists_hasStageModel (D := D') (π := π')
      hc' (c.π.app i) (fun j ↦ (c.w j.hom).symm) V hN hVN U.hom U.hom
      _ hφ₀ _ hφ₀
    have H' : IsPullback e V.hom p (c.π.app j.left) := H
    obtain ⟨κ, -, hκ⟩ := exists_inverse_homToPullback (c.π.app j.left) hp H'
    refine ⟨V, a, op j.left, j.hom.op, ⟨⟨y, hyV₀⟩, by rw [← hy]; rfl⟩, ?_⟩
    change (pushPullTransition (c.π.app j.left) (D.map j.hom) (c.π.app i) (c.w j.hom).symm
      F).hom.app (op V) (((pushPullDiagram D c F).obj k).obj.map a.op t) = 0
    rw [hs₀, pushPullTransition_app_pullSection]
    let Ymk : (D.obj j.left).Etale := MorphismProperty.Over.mk ⊤ p hp
    let b : Ymk ⟶ (MorphismProperty.Over.pullback @Etale ⊤ (D.map j.hom)).obj U :=
      MorphismProperty.Over.homMk (pullback.lift ψ p hψ) (pullback.lift_snd _ _ _) trivial
    have hb : (e ≫ b.left) ≫ ((MorphismProperty.Over.pullback @Etale ⊤ (D.map j.hom)).obj U).hom =
        V.hom ≫ c.π.app j.left := by
      simpa [b] using H'.w
    refine (pullSection_congr _ _ (φ := e ≫ b.left) hb (by
      apply pullback.hom_ext <;> simp [b, heψ, H'.w]) _).symm.trans ?_
    refine (pullSection_comp _ _ b e H'.w _).trans ?_
    have key : (MorphismProperty.Over.pullback @Etale ⊤ (c.π.app j.left)).map b ≫
        (MorphismProperty.Over.pullbackComp (c.π.app j.left) (D.map j.hom) (c.π.app i)
          (c.w j.hom).symm).inv.app U = κ ≫ homToPullback (c.π.app i) _ hφ₀ := by
      rw [← Category.id_comp ((MorphismProperty.Over.pullback @Etale ⊤ (c.π.app j.left)).map b ≫
        _), ← hκ, Category.assoc]
      congr 1
      apply hom_ext_pullback
      simp only [b, homToPullback, ← heψ]
      simp only [Functor.const_obj_obj, Functor.id_obj, overPullback_obj_left,
        MorphismProperty.Comma.comp_hom, MorphismProperty.Over.homMk_hom, Comma.comp_left,
        Over.homMk_left, overPullback_obj_hom, MorphismProperty.Over.pullback_map_left,
        MorphismProperty.Over.pullbackComp_inv_app_left, Category.assoc, limit.lift_π,
        PullbackCone.mk_π_app, Category.comp_id, pullbackLeftPullbackSndIso_hom_fst,
        limit.lift_π_assoc, cospan_left, Cone.whisker_pt]
      exact pullback.lift_fst_assoc _ _ _ _
    have h0 : ((c.π.app j.left)_*[AddCommGrpCat.{u + 1}].obj F).obj.map b.op
        (((lowerStarComp AddCommGrpCat.{u + 1} (c.π.app j.left) (D.map j.hom) (c.π.app i)
          (c.w j.hom).symm).inv.app F).hom.app (op U) g₀) = 0 := by
      rw [lowerStarComp_inv_app_hom_app, lowerStar_obj_val_map]
      erw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, key, op_comp,
        Functor.map_comp, ConcreteCategory.comp_apply, hzero, map_zero]
    rw [h0]
    exact pullSection_zero (c.π.app j.left) ((c.π.app j.left)_*[AddCommGrpCat.{u + 1}].obj F)
      (V := V) (U := Ymk) e H'.w
  choose V a k' g hx hg using key
  refine ⟨Sieve.ofArrows V a, (Scheme.ofArrows_mem_smallEtaleTopology_iff a).2
    (Set.eq_univ_of_forall fun x ↦ Set.mem_iUnion.2 ⟨x, hx x⟩), ?_⟩
  rintro V' f ⟨_, r, _, ⟨x⟩, rfl⟩
  refine ⟨k' x, g x, ?_⟩
  rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, NatTrans.naturality_apply, hg x,
    map_zero]


include hc in
/-- **Sheaves on a limit are colimits of pulled back sheaves.** For a cofiltered limit
`X = lim Dᵢ` of quasi-compact quasi-separated schemes with affine transition maps, every abelian
étale sheaf `F` on `X` is the colimit of the `pᵢ^* pᵢ_* F` along the counits. -/
noncomputable def isColimitPushPullCocone [∀ i, CompactSpace (D.obj i)] :
    IsColimit (pushPullCocone D c F) :=
  isColimitOfLocally _ (pushPullCocone_exists_app_eq D hc F)
    (fun k W t ht ↦ pushPullCocone_exists_map_eq_zero D hc F k W t ht)

end LimitLocal

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Scheme

open _root_.AlgebraicGeometry.Etale

section

variable {I : Type u} [SmallCategory I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
  [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
  [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)] {c : Cone D} (hc : IsLimit c) {n : ℕ}

include hc in
/-- For a sheaf `F` on `X = lim Dᵢ` killed by `N > 0`, the cohomology of `pᵢ^* pᵢ_* F` vanishes
above `n` if `cd_tor(Dⱼ) ≤ n` for all `j`: by continuity of étale cohomology it is the colimit of
the cohomology of the pullbacks of the torsion sheaf `pᵢ_* F` to the `Dⱼ`, `j ⟶ i`. -/
lemma subsingleton_H_pushPullDiagram_obj (h : ∀ i, (D.obj i).HasTorsionCohomologicalDimensionLE n)
    (F : Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1}) {N : ℕ} (hN : 0 < N)
    (hF : N • 𝟙 F = 0) (i : I) (q : ℕ) (hq : n < q) :
    Subsingleton (Sheaf.H ((pushPullDiagram D c F).obj (op i)) q) := by
  let G := (c.π.app i)_*[AddCommGrpCat.{u + 1}].obj F
  have hG : G.IsTorsion := isTorsion_of_nsmul_id_eq_zero hN (by
    rw [← CategoryTheory.Functor.map_id, ← Functor.map_nsmul, hF, Functor.map_zero])
  let Dov : Over i ⥤ Over (D.obj i) :=
    { obj j := Over.mk (D.map j.hom)
      map {j j'} g := Over.homMk (D.map g.left) (by simp [← D.map_comp, Over.w g]) }
  let cov : Cone Dov :=
    { pt := Over.mk (c.π.app i)
      π := { app j := Over.homMk (c.π.app j.left) (c.w j.hom)
             naturality j j' g := by ext; simp [Dov] } }
  have hcov : IsLimit ((Over.forget (D.obj i)).mapCone cov) :=
    (Functor.Initial.isLimitWhiskerEquiv (Over.forget i) c).symm hc
  have : ∀ j, CompactSpace (Dov.obj j).left := fun j ↦ inferInstanceAs (CompactSpace (D.obj j.left))
  have : ∀ j, QuasiSeparatedSpace (Dov.obj j).left := fun j ↦
    inferInstanceAs (QuasiSeparatedSpace (D.obj j.left))
  have : ∀ {j j'} (g : j ⟶ j'), IsAffineHom (Dov.map g).left := fun g ↦
    inferInstanceAs (IsAffineHom (D.map g.left))
  have key := isZero_rightDerived_sectionsFunctor_upperStar_of_isLimit_addCommGrpCat G
    Dov cov hcov q fun j ↦ (Sheaf.subsingleton_H_iff_isZero_rightDerived
      (Dov.obj j).left.smallEtaleTopology (isTerminalEtaleMkId (D.obj j.left)) q _).1
      (h j.left _ (isTorsion_upperStar (D.map j.hom) hG) q hq)
  exact (Sheaf.subsingleton_H_iff_isZero_rightDerived c.pt.smallEtaleTopology
    (isTerminalEtaleMkId c.pt) q _).2 key

end



/-- **Passing a uniform torsion bound to an affine limit.** Let `X = lim Xᵢ` be the limit of a
cofiltered system `D` of quasi-compact quasi-separated schemes with affine transition maps. If
`cd_tor(Xᵢ) ≤ n` for every `i`, then `cd_tor(X) ≤ n`. -/
theorem HasTorsionCohomologicalDimensionLE.of_isLimit {I : Type u} [SmallCategory I]
    [IsCofiltered I] (D : I ⥤ Scheme.{u}) [∀ i, CompactSpace (D.obj i)]
    [∀ i, QuasiSeparatedSpace (D.obj i)] [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)]
    (c : Cone D) (hc : IsLimit c) {n : ℕ}
    (h : ∀ i, (D.obj i).HasTorsionCohomologicalDimensionLE n) :
    c.pt.HasTorsionCohomologicalDimensionLE n := fun F hF q hq ↦ by
  have : CompactSpace c.pt := Scheme.compactSpace_of_isLimit D c hc
  obtain ⟨i⟩ := IsCofiltered.nonempty (C := I)
  have := isAffineHom_π_app D c hc i
  have : QuasiSeparatedSpace c.pt := quasiSeparatedSpace_of_quasiSeparated (c.π.app i)
  refine Etale.subsingleton_H_of_isTorsion hF q fun G N hN hG ↦
    subsingleton_of_forall_eq 0 fun x ↦ ?_
  obtain ⟨j, y, rfl⟩ :=
    (H_map_isColimit_of_isFiltered_of_large c.pt (isColimitPushPullCocone D hc G) q).1 x
  have := subsingleton_H_pushPullDiagram_obj D hc h G hN hG j.unop q hq
  rw [Subsingleton.elim y 0, map_zero]

end AlgebraicGeometry.Scheme
