/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Sites.LocallyInjective
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import WeilConjectures.Mathlib.CategoryTheory.Limits.MorphismProperty
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Pullback
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantEtale.Universal
public import WeilConjectures.AlgebraicGeometry.Sites.CohomologyColimit
public import WeilConjectures.AlgebraicGeometry.Sites.UnitComparison
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence

/-!
# Sections of the inverse image of an étale sheaf

Let `t : T ⟶ R` be a morphism of schemes and `G` an abelian étale sheaf on `R`. For an étale
`R`-scheme `U`, an étale `T`-scheme `V`, a morphism `φ : V ⟶ U` over `R` and a section `g` of
`G` over `U`, the pullback `φ^* g` is a section of `t^* G` over `V`
(`AlgebraicGeometry.Etale.pullSection`). Every section of `t^* G` is étale locally of this
form (`AlgebraicGeometry.Etale.exists_pullSection_eq`), and if `φ^* g` vanishes, then étale
locally `φ` factors through an étale `U' ⟶ U` on which `g` vanishes
(`AlgebraicGeometry.Etale.exists_of_pullSection_eq_zero`): the inverse image is the
sheafification of the left Kan extension along the opposite of base change, a filtered colimit
since base change is representably flat.

For `f : T' ⟶ T`, the restriction of sections of `t^* G` to sections of `(f ≫ t)^* G` along a
morphism `m : V' ⟶ V` over `f` is `AlgebraicGeometry.Etale.restrictAlong`; it sends `φ^* g` to
`(m ≫ φ)^* g` (`AlgebraicGeometry.Etale.restrictAlong_pullSection`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

namespace Etale

variable {R T : Scheme.{u}} (t : T ⟶ R)

@[reassoc (attr := simp)]
lemma etale_comp_left {X : Scheme.{u}} {V₁ V₂ V₃ : X.Etale} (a : V₁ ⟶ V₂) (b : V₂ ⟶ V₃) :
    (a ≫ b).left = a.left ≫ b.left :=
  rfl

@[simp]
lemma overPullback_obj_left (U : R.Etale) :
    ((MorphismProperty.Over.pullback @Etale ⊤ t).obj U).left = pullback U.hom t :=
  rfl

@[simp]
lemma overPullback_obj_hom (U : R.Etale) :
    ((MorphismProperty.Over.pullback @Etale ⊤ t).obj U).hom = pullback.snd U.hom t :=
  rfl

@[simp]
lemma overPullback_map_left {U U' : R.Etale} (b : U' ⟶ U) :
    ((MorphismProperty.Over.pullback @Etale ⊤ t).map b).left =
      pullback.lift (pullback.fst U'.hom t ≫ b.left) (pullback.snd U'.hom t)
        (by rw [Category.assoc, MorphismProperty.Over.w b, pullback.condition]) :=
  rfl

/-- The morphism `V ⟶ U ×_R T` of étale `T`-schemes induced by a morphism `φ : V ⟶ U` over
`R`. -/
noncomputable def homToPullback {V : T.Etale} {U : R.Etale} (φ : V.left ⟶ U.left)
    (hφ : φ ≫ U.hom = V.hom ≫ t) :
    V ⟶ (MorphismProperty.Over.pullback @Etale ⊤ t).obj U :=
  MorphismProperty.Over.homMk (pullback.lift φ V.hom hφ) (pullback.lift_snd _ _ _)

@[reassoc (attr := simp)]
lemma homToPullback_left_fst {V : T.Etale} {U : R.Etale} (φ : V.left ⟶ U.left)
    (hφ : φ ≫ U.hom = V.hom ≫ t) :
    (homToPullback t φ hφ).left ≫ pullback.fst U.hom t = φ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma homToPullback_left_snd {V : T.Etale} {U : R.Etale} (φ : V.left ⟶ U.left)
    (hφ : φ ≫ U.hom = V.hom ≫ t) :
    (homToPullback t φ hφ).left ≫ pullback.snd U.hom t = V.hom :=
  pullback.lift_snd _ _ _

lemma eq_homToPullback {V : T.Etale} {U : R.Etale}
    (a : V ⟶ (MorphismProperty.Over.pullback @Etale ⊤ t).obj U) :
    a = homToPullback t (a.left ≫ pullback.fst U.hom t)
      (by rw [Category.assoc, pullback.condition, ← Category.assoc]
          exact congrArg (· ≫ t) (MorphismProperty.Over.w a)) := by
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext
  · simp
  · simpa [homToPullback] using MorphismProperty.Over.w a

variable (G : Sheaf R.smallEtaleTopology AddCommGrpCat.{u + 1})

/-- The pullback `φ^* g` of a section `g` of `G` over an étale `R`-scheme `U` along a morphism
`φ : V ⟶ U` over `R` from an étale `T`-scheme `V`: a section of `t^* G` over `V`. -/
noncomputable def pullSection {V : T.Etale} {U : R.Etale} (φ : V.left ⟶ U.left)
    (hφ : φ ≫ U.hom = V.hom ≫ t) (g : G.obj.obj (op U)) :
    ((t)^*[AddCommGrpCat.{u + 1}].obj G).obj.obj (op V) :=
  ((t)^*[AddCommGrpCat.{u + 1}].obj G).obj.map (homToPullback t φ hφ).op
    (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} t).unit.app G).hom.app (op U) g)

lemma map_unit_app_eq_pullSection {V : T.Etale} {U : R.Etale}
    (a : V ⟶ (MorphismProperty.Over.pullback @Etale ⊤ t).obj U) (g : G.obj.obj (op U)) :
    ((t)^*[AddCommGrpCat.{u + 1}].obj G).obj.map a.op
      (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} t).unit.app G).hom.app (op U) g) =
      pullSection t G (a.left ≫ pullback.fst U.hom t)
        (by rw [Category.assoc, pullback.condition, ← Category.assoc]
            exact congrArg (· ≫ t) (MorphismProperty.Over.w a)) g := by
  rw [pullSection, ← eq_homToPullback]

lemma pullSection_congr {V : T.Etale} {U : R.Etale} {φ φ' : V.left ⟶ U.left}
    (hφ : φ ≫ U.hom = V.hom ≫ t) (h : φ = φ') (g : G.obj.obj (op U)) :
    pullSection t G φ hφ g = pullSection t G φ' (h ▸ hφ) g := by
  subst h; rfl

/-- Restriction of `φ^* g` along `a : V' ⟶ V` is `(a ≫ φ)^* g`. -/
lemma map_pullSection {V V' : T.Etale} {U : R.Etale} (φ : V.left ⟶ U.left)
    (hφ : φ ≫ U.hom = V.hom ≫ t) (g : G.obj.obj (op U)) (a : V' ⟶ V) :
    ((t)^*[AddCommGrpCat.{u + 1}].obj G).obj.map a.op (pullSection t G φ hφ g) =
      pullSection t G (a.left ≫ φ)
        (by rw [Category.assoc, hφ, ← Category.assoc, MorphismProperty.Over.w a]) g := by
  rw [pullSection, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
    map_unit_app_eq_pullSection]
  exact pullSection_congr _ _ _ (by
    rw [MorphismProperty.Comma.comp_left, Category.assoc, homToPullback_left_fst]) _

/-- `(φ ≫ b)^* g = φ^* (b^* g)` for a morphism `b : U' ⟶ U` of étale `R`-schemes. -/
lemma pullSection_comp {V : T.Etale} {U U' : R.Etale} (b : U' ⟶ U) (φ : V.left ⟶ U'.left)
    (hφ : φ ≫ U'.hom = V.hom ≫ t) (g : G.obj.obj (op U)) :
    pullSection t G (φ ≫ b.left)
        (by rw [Category.assoc, MorphismProperty.Over.w b, hφ]) g =
      pullSection t G φ hφ (G.obj.map b.op g) := by
  have e : ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} t).unit.app G).hom.app (op U')
      (G.obj.map b.op g) = ((t)^*[AddCommGrpCat.{u + 1}].obj G).obj.map
        ((MorphismProperty.Over.pullback @Etale ⊤ t).map b).op
        (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} t).unit.app G).hom.app (op U) g) :=
    NatTrans.naturality_apply
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} t).unit.app G).hom b.op g
  refine Eq.trans ?_ (congrArg (((t)^*[AddCommGrpCat.{u + 1}].obj G).obj.map
    (homToPullback t φ hφ).op) e).symm
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
    map_unit_app_eq_pullSection]
  exact pullSection_congr _ _ _ (by simp [homToPullback]) _

@[simp]
lemma pullSection_zero {V : T.Etale} {U : R.Etale} (φ : V.left ⟶ U.left)
    (hφ : φ ≫ U.hom = V.hom ≫ t) :
    pullSection t G φ hφ 0 = 0 := by
  rw [pullSection, map_zero, map_zero]

lemma pullSection_add {V : T.Etale} {U : R.Etale} (φ : V.left ⟶ U.left)
    (hφ : φ ≫ U.hom = V.hom ≫ t) (g g' : G.obj.obj (op U)) :
    pullSection t G φ hφ (g + g') = pullSection t G φ hφ g + pullSection t G φ hφ g' := by
  simp only [pullSection]
  rw [map_add, map_add]

lemma pullSection_sub {V : T.Etale} {U : R.Etale} (φ : V.left ⟶ U.left)
    (hφ : φ ≫ U.hom = V.hom ≫ t) (g g' : G.obj.obj (op U)) :
    pullSection t G φ hφ (g - g') = pullSection t G φ hφ g - pullSection t G φ hφ g' := by
  simp only [pullSection]
  rw [map_sub, map_sub]

section Local

/-- Base change along `t` is representably flat. -/
lemma representablyFlat_pullback :
    RepresentablyFlat (MorphismProperty.Over.pullback @Etale ⊤ t : R.Etale ⥤ T.Etale) :=
  Scheme.Hom.representablyFlat_etale t

/-- The colimits computing the left Kan extension along the opposite of base change are
filtered, base change being representably flat, so they are preserved by the forgetful
functor of abelian groups. -/
instance preservesColimitsOfShape_costructuredArrow_pullback (Y : T.Etaleᵒᵖ) :
    PreservesColimitsOfShape
      (CostructuredArrow (MorphismProperty.Over.pullback @Etale ⊤ t : R.Etale ⥤ T.Etale).op Y)
      (forget AddCommGrpCat.{u + 1}) := by
  have := representablyFlat_pullback t
  have : IsFiltered (CostructuredArrow
      (MorphismProperty.Over.pullback @Etale ⊤ t : R.Etale ⥤ T.Etale).op Y) :=
    IsFiltered.of_equivalence (structuredArrowOpEquivalence _ Y.unop)
  have : PreservesFilteredColimitsOfSize.{u, u + 1} (forget AddCommGrpCat.{u + 1}) :=
    preservesFilteredColimitsOfSize_shrink.{u + 1, u + 1, u, u + 1} _
  infer_instance

/-- **Local generation.** Every section of `t^* G` is étale locally of the form `φ^* g`. -/
lemma exists_pullSection_eq {V : T.Etale}
    (s : ((t)^*[AddCommGrpCat.{u + 1}].obj G).obj.obj (op V)) (x : V.left) :
    ∃ (V' : T.Etale) (a : V' ⟶ V) (U : R.Etale) (φ : V'.left ⟶ U.left)
      (hφ : φ ≫ U.hom = V'.hom ≫ t) (g : G.obj.obj (op U)),
      x ∈ Set.range a.left ∧
        ((t)^*[AddCommGrpCat.{u + 1}].obj G).obj.map a.op s = pullSection t G φ hφ g := by
  let F : R.Etale ⥤ T.Etale := MorphismProperty.Over.pullback @Etale ⊤ t
  have : ∀ Y, PreservesColimitsOfShape (CostructuredArrow F.op Y) (forget AddCommGrpCat.{u + 1}) :=
    fun Y ↦ preservesColimitsOfShape_costructuredArrow_pullback t Y
  let L : T.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1} := F.op.leftKanExtension G.obj
  have hS := Presheaf.imageSieve_mem T.smallEtaleTopology (toSheafify T.smallEtaleTopology L) s
  obtain ⟨V', a, ⟨ℓ, hℓ⟩, hx⟩ := (Scheme.mem_smallEtaleTopology_iff _).1 hS x
  obtain ⟨j, y, rfl⟩ := Concrete.isColimit_exists_rep _
    (F.op.isPointwiseLeftKanExtensionLeftKanExtensionUnit G.obj (op V')) ℓ
  refine ⟨V', a, j.left.unop, _, _, y, hx,
    (hℓ.symm.trans ?_).trans (map_unit_app_eq_pullSection t G j.hom.unop y)⟩
  have h₁ : ((Functor.LeftExtension.mk _ (F.op.leftKanExtensionUnit G.obj)).coconeAt
      (op V')).ι.app j y = L.map j.hom ((F.op.leftKanExtensionUnit G.obj).app j.left y) := by
    rw [Functor.LeftExtension.coconeAt_ι_app, ConcreteCategory.comp_apply]
    rfl
  rw [h₁]
  exact NatTrans.naturality_apply (toSheafify T.smallEtaleTopology L) j.hom _

/-- **Local vanishing.** If `φ^* g` vanishes, then étale locally `φ` factors through an étale
`U' ⟶ U` on which `g` vanishes. -/
lemma exists_of_pullSection_eq_zero {V : T.Etale} {U : R.Etale} (φ : V.left ⟶ U.left)
    (hφ : φ ≫ U.hom = V.hom ≫ t) (g : G.obj.obj (op U)) (h : pullSection t G φ hφ g = 0)
    (x : V.left) :
    ∃ (V' : T.Etale) (a : V' ⟶ V) (U' : R.Etale) (b : U' ⟶ U) (φ' : V'.left ⟶ U'.left)
      (_ : φ' ≫ U'.hom = V'.hom ≫ t), x ∈ Set.range a.left ∧ φ' ≫ b.left = a.left ≫ φ ∧
        G.obj.map b.op g = 0 := by
  let F : R.Etale ⥤ T.Etale := MorphismProperty.Over.pullback @Etale ⊤ t
  have : ∀ Y, PreservesColimitsOfShape (CostructuredArrow F.op Y) (forget AddCommGrpCat.{u + 1}) :=
    fun Y ↦ preservesColimitsOfShape_costructuredArrow_pullback t Y
  have := representablyFlat_pullback t
  let L : T.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1} := F.op.leftKanExtension G.obj
  have h' : (toSheafify T.smallEtaleTopology L).app (op V)
      (L.map (homToPullback t φ hφ).op ((F.op.leftKanExtensionUnit G.obj).app (op U) g)) =
      (toSheafify T.smallEtaleTopology L).app (op V) 0 := by
    rw [map_zero]
    refine (NatTrans.naturality_apply (toSheafify T.smallEtaleTopology L) _ _).trans ?_
    exact h
  have hS := Presheaf.equalizerSieve_mem T.smallEtaleTopology _ _ _ h'
  obtain ⟨V', a, ha, hx⟩ := (Scheme.mem_smallEtaleTopology_iff _).1 hS x
  obtain ⟨U', b, ψ, hψ, hg⟩ := Functor.exists_map_eq_of_leftKanExtensionUnit_eq F G.obj
    (a ≫ homToPullback t φ hφ) g 0 (by
      rw [map_zero, map_zero, op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
      simpa only [Presheaf.equalizerSieve_apply, map_zero] using ha)
  refine ⟨V', a, U', b, ψ.left ≫ pullback.fst _ _, ?_, hx, ?_, by simpa using hg⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (· ≫ t) (MorphismProperty.Over.w ψ)
  · have := congrArg (fun c ↦ c.left ≫ pullback.fst U.hom t) hψ
    change (ψ.left ≫ ((MorphismProperty.Over.pullback @Etale ⊤ t).map b).left) ≫ _ =
      (a.left ≫ (homToPullback t φ hφ).left) ≫ _ at this
    simpa using this

end Local


section Transition

variable {T' : Scheme.{u}} (f : T' ⟶ T) (t' : T' ⟶ R) (ht' : t' = f ≫ t)

/-- The transition map `t^* G ⟶ f_* (f ≫ t)^* G`: the unit of `f^* ⊣ f_*` followed by the
composition isomorphism of the pullbacks. -/
noncomputable def transition :
    (t)^*[AddCommGrpCat.{u + 1}].obj G ⟶
      (f)_*[AddCommGrpCat.{u + 1}].obj ((t')^*[AddCommGrpCat.{u + 1}].obj G) :=
  (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app
      ((t)^*[AddCommGrpCat.{u + 1}].obj G) ≫
    (f)_*[AddCommGrpCat.{u + 1}].map
      ((upperStarComp AddCommGrpCat.{u + 1} f t t' ht').inv.app G)

/-- The restriction of sections of `t^* G` over `V` to sections of `(f ≫ t)^* G` over `V'`
along a morphism `m : V' ⟶ V` over `f`. -/
noncomputable def restrictAlong {V : T.Etale} {V' : T'.Etale} (m : V'.left ⟶ V.left)
    (hm : m ≫ V.hom = V'.hom ≫ f) :
    ((t)^*[AddCommGrpCat.{u + 1}].obj G).obj.obj (op V) ⟶
      ((t')^*[AddCommGrpCat.{u + 1}].obj G).obj.obj (op V') :=
  (transition t G f t' ht').hom.app (op V) ≫
    ((t')^*[AddCommGrpCat.{u + 1}].obj G).obj.map (homToPullback f m hm).op

/-- Two morphisms into a base change `U ×_R T` agree as soon as their first projections to `U`
agree. -/
lemma hom_ext_pullback {V : T.Etale} {U : R.Etale}
    {a b : V ⟶ (MorphismProperty.Over.pullback @Etale ⊤ t).obj U}
    (h : a.left ≫ pullback.fst U.hom t = b.left ≫ pullback.fst U.hom t) : a = b := by
  apply MorphismProperty.Over.Hom.ext
  apply pullback.hom_ext h
  have ha := MorphismProperty.Over.w a
  have hb := MorphismProperty.Over.w b
  simp only [MorphismProperty.Over.pullback_obj_hom] at ha hb
  rw [ha, hb]

/-- The comparison map `unitComparison` on sections over `W` is the restriction along the
projection `W ×_R T' ⟶ W ×_R T`. -/
lemma unitComparison_hom_app_eq (W : R.Etale) :
    (unitComparison f t t' ht' G).hom.app (op W) =
      restrictAlong t G f t' ht'
        (V := (MorphismProperty.Over.pullback @Etale ⊤ t).obj W)
        (V' := (MorphismProperty.Over.pullback @Etale ⊤ t').obj W)
        (pullback.map W.hom t' W.hom t (𝟙 _) f (𝟙 _) (by simp) (by simp [ht']))
        (pullback.lift_snd _ _ _) := by
  have hp : (MorphismProperty.Over.pullbackComp f t t' ht').hom.app W =
      homToPullback f (pullback.map W.hom t' W.hom t (𝟙 _) f (𝟙 _) (by simp) (by simp [ht']))
        (pullback.lift_snd _ _ _) := by
    apply hom_ext_pullback
    rw [homToPullback_left_fst]
    subst ht'
    apply pullback.hom_ext
    · simp
    · simp [pullback.condition]
  change _ ≫ ((lowerStarComp AddCommGrpCat.{u + 1} f t t' ht').hom.app _).hom.app (op W) ≫ _ = _
  rw [lowerStarComp_hom_app_hom_app, hp]
  exact congrArg (_ ≫ ·)
    (((upperStarComp AddCommGrpCat.{u + 1} f t t' ht').inv.app G).hom.naturality _)

/-- The transition map sends the unit section `g|_{U ×_R T}` to the unit section
`g|_{U ×_R T'}`. -/
lemma transition_hom_app_unit (U : R.Etale) (g : G.obj.obj (op U)) :
    (transition t G f t' ht').hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ t).obj U))
        (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} t).unit.app G).hom.app (op U) g) =
      pullSection t' G (pullback.fst (pullback.snd U.hom t) f ≫ pullback.fst U.hom t)
        (by rw [ht', Category.assoc, pullback.condition, pullback.condition_assoc]; rfl) g := by
  set F' := (t')^*[AddCommGrpCat.{u + 1}].obj G
  set X := (transition t G f t' ht').hom.app
    (op ((MorphismProperty.Over.pullback @Etale ⊤ t).obj U))
      (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} t).unit.app G).hom.app (op U) g)
  have h := congrArg (fun φ ↦ φ.hom.app (op U) g) (unit_app_comp_unitComparison f t t' ht' G)
  have h₂ : F'.obj.map (homToPullback f (U := (MorphismProperty.Over.pullback @Etale ⊤ t).obj U)
      (V := (MorphismProperty.Over.pullback @Etale ⊤ t').obj U)
      (pullback.map U.hom t' U.hom t (𝟙 _) f (𝟙 _) (by simp) (by simp [ht']))
        (pullback.lift_snd _ _ _)).op X =
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} t').unit.app G).hom.app (op U) g := by
    refine Eq.trans ?_ h
    change _ = (unitComparison f t t' ht' G).hom.app (op U) _
    rw [unitComparison_hom_app_eq]
    rfl
  have he : homToPullback t' (pullback.fst (pullback.snd U.hom t) f ≫ pullback.fst U.hom t)
      (by rw [ht', Category.assoc, pullback.condition, pullback.condition_assoc]; rfl) ≫
      homToPullback f (U := (MorphismProperty.Over.pullback @Etale ⊤ t).obj U)
        (V := (MorphismProperty.Over.pullback @Etale ⊤ t').obj U)
        (pullback.map U.hom t' U.hom t (𝟙 _) f (𝟙 _) (by simp) (by simp [ht']))
        (pullback.lift_snd _ _ _) = 𝟙 _ := by
    apply hom_ext_pullback
    rw [MorphismProperty.Comma.comp_left, Category.assoc, homToPullback_left_fst]
    apply pullback.hom_ext
    · simp
    · simp [pullback.condition]
  calc X = F'.obj.map (𝟙 _).op X := by rw [op_id, CategoryTheory.Functor.map_id]; rfl
    _ = _ := by rw [← he, op_comp, Functor.map_comp, ConcreteCategory.comp_apply, h₂]; rfl

/-- `restrictAlong` only depends on the morphism `m`, not on the proof of compatibility. -/
lemma restrictAlong_congr {V : T.Etale} {V' : T'.Etale} {m₁ m₂ : V'.left ⟶ V.left}
    (hm₁ : m₁ ≫ V.hom = V'.hom ≫ f) (h : m₁ = m₂) :
    restrictAlong t G f t' ht' m₁ hm₁ = restrictAlong t G f t' ht' m₂ (h ▸ hm₁) := by
  subst h
  rfl

/-- Restriction of `φ^* g` along `m` is `(m ≫ φ)^* g`. -/
lemma restrictAlong_pullSection {V : T.Etale} {V' : T'.Etale} (m : V'.left ⟶ V.left)
    (hm : m ≫ V.hom = V'.hom ≫ f) {U : R.Etale} (φ : V.left ⟶ U.left)
    (hφ : φ ≫ U.hom = V.hom ≫ t) (g : G.obj.obj (op U)) :
    restrictAlong t G f t' ht' m hm (pullSection t G φ hφ g) =
      pullSection t' G (m ≫ φ) (by rw [Category.assoc, hφ, reassoc_of% hm, ht']) g := by
  set F' := (t')^*[AddCommGrpCat.{u + 1}].obj G
  have e₁ : (transition t G f t' ht').hom.app (op V) (pullSection t G φ hφ g) =
      F'.obj.map ((MorphismProperty.Over.pullback @Etale ⊤ f).map (homToPullback t φ hφ)).op
        ((transition t G f t' ht').hom.app
          (op ((MorphismProperty.Over.pullback @Etale ⊤ t).obj U))
          (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} t).unit.app G).hom.app
            (op U) g)) :=
    NatTrans.naturality_apply (transition t G f t' ht').hom _ _
  rw [transition_hom_app_unit] at e₁
  refine (congrArg (F'.obj.map (homToPullback f m hm).op) e₁).trans ?_
  refine (congrArg (F'.obj.map (homToPullback f m hm).op)
    (map_pullSection t' G _ _ g _)).trans ?_
  refine (map_pullSection t' G _ _ g _).trans ?_
  apply pullSection_congr
  simp [homToPullback]

/-- Restriction along `m` of the restriction of `s` along `a : V₁ ⟶ V` is the restriction of
`s` along `m ≫ a`. -/
lemma restrictAlong_map {V V₁ : T.Etale} {V' : T'.Etale} (a : V₁ ⟶ V) (m : V'.left ⟶ V₁.left)
    (hm : m ≫ V₁.hom = V'.hom ≫ f)
    (s : ((t)^*[AddCommGrpCat.{u + 1}].obj G).obj.obj (op V)) :
    restrictAlong t G f t' ht' m hm (((t)^*[AddCommGrpCat.{u + 1}].obj G).obj.map a.op s) =
      restrictAlong t G f t' ht' (m ≫ a.left)
        (by rw [Category.assoc, MorphismProperty.Over.w a, hm]) s := by
  set F' := (t')^*[AddCommGrpCat.{u + 1}].obj G
  have e₁ : (transition t G f t' ht').hom.app (op V₁)
      (((t)^*[AddCommGrpCat.{u + 1}].obj G).obj.map a.op s) =
      F'.obj.map ((MorphismProperty.Over.pullback @Etale ⊤ f).map a).op
        ((transition t G f t' ht').hom.app (op V) s) :=
    NatTrans.naturality_apply (transition t G f t' ht').hom _ _
  refine (congrArg (F'.obj.map (homToPullback f m hm).op) e₁).trans ?_
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, restrictAlong,
    ConcreteCategory.comp_apply]
  congr 3
  refine congrArg Quiver.Hom.op ?_
  apply hom_ext_pullback
  simp [homToPullback]

/-- Restricting the restriction of `s` along `m` further along `b : V'' ⟶ V'` is the
restriction of `s` along `b ≫ m`. -/
lemma map_restrictAlong {V : T.Etale} {V' V'' : T'.Etale} (b : V'' ⟶ V')
    (m : V'.left ⟶ V.left) (hm : m ≫ V.hom = V'.hom ≫ f)
    (s : ((t)^*[AddCommGrpCat.{u + 1}].obj G).obj.obj (op V)) :
    ((t')^*[AddCommGrpCat.{u + 1}].obj G).obj.map b.op (restrictAlong t G f t' ht' m hm s) =
      restrictAlong t G f t' ht' (b.left ≫ m)
        (by rw [Category.assoc, hm, ← Category.assoc, MorphismProperty.Over.w b]) s := by
  set F' := (t')^*[AddCommGrpCat.{u + 1}].obj G
  rw [restrictAlong, ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    ← Functor.map_comp, ← op_comp, restrictAlong, ConcreteCategory.comp_apply]
  congr 3
  refine congrArg Quiver.Hom.op ?_
  apply hom_ext_pullback
  rw [MorphismProperty.Comma.comp_left, Category.assoc, homToPullback_left_fst,
    homToPullback_left_fst]

end Transition

section Gluing

variable {X : Scheme.{u}} (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})

/-- The fibre product `V₁ ×_V V₂` of two étale `X`-schemes over a third, as an étale
`X`-scheme. -/
noncomputable def overlap {V V₁ V₂ : X.Etale} (a₁ : V₁ ⟶ V) (a₂ : V₂ ⟶ V) : X.Etale :=
  MorphismProperty.Over.mk ⊤ (pullback.fst a₁.left a₂.left ≫ V₁.hom) inferInstance

/-- The first projection from `V₁ ×_V V₂`. -/
noncomputable def overlapFst {V V₁ V₂ : X.Etale} (a₁ : V₁ ⟶ V) (a₂ : V₂ ⟶ V) :
    overlap a₁ a₂ ⟶ V₁ :=
  MorphismProperty.Over.homMk (pullback.fst a₁.left a₂.left) rfl

/-- The second projection from `V₁ ×_V V₂`. -/
noncomputable def overlapSnd {V V₁ V₂ : X.Etale} (a₁ : V₁ ⟶ V) (a₂ : V₂ ⟶ V) :
    overlap a₁ a₂ ⟶ V₂ :=
  MorphismProperty.Over.homMk (pullback.snd a₁.left a₂.left) (by
    change _ = pullback.fst a₁.left a₂.left ≫ V₁.hom
    rw [← MorphismProperty.Over.w a₂, ← pullback.condition_assoc, MorphismProperty.Over.w a₁])

@[simp]
lemma overlap_left {V V₁ V₂ : X.Etale} (a₁ : V₁ ⟶ V) (a₂ : V₂ ⟶ V) :
    (overlap a₁ a₂).left = pullback a₁.left a₂.left :=
  rfl

@[simp]
lemma overlapFst_left {V V₁ V₂ : X.Etale} (a₁ : V₁ ⟶ V) (a₂ : V₂ ⟶ V) :
    (overlapFst a₁ a₂).left = pullback.fst a₁.left a₂.left :=
  rfl

@[simp]
lemma overlapSnd_left {V V₁ V₂ : X.Etale} (a₁ : V₁ ⟶ V) (a₂ : V₂ ⟶ V) :
    (overlapSnd a₁ a₂).left = pullback.snd a₁.left a₂.left :=
  rfl

/-- A section of a sheaf vanishing on a jointly surjective family vanishes. -/
lemma eq_zero_of_forall_map_eq_zero {V : X.Etale} {ι : Type*} {V' : ι → X.Etale}
    (a : ∀ i, V' i ⟶ V) (ha : ∀ x : V.left, ∃ i, x ∈ Set.range (a i).left)
    (s : F.obj.obj (op V)) (hs : ∀ i, F.obj.map (a i).op s = 0) : s = 0 :=
  (Scheme.isSheafFor_ofArrows F a (Set.iUnion_eq_univ_iff.2 ha)).isSeparatedFor.ext fun _ _ ⟨i⟩ ↦ by
    change F.obj.map (a i).op s = F.obj.map (a i).op 0
    rw [hs i, map_zero]

/-- Sections of a sheaf over a jointly surjective family which agree on the overlaps glue. -/
lemma exists_map_eq_of_compatible {V : X.Etale} {ι : Type*} {V' : ι → X.Etale}
    (a : ∀ i, V' i ⟶ V) (ha : ∀ x : V.left, ∃ i, x ∈ Set.range (a i).left)
    (σ : ∀ i, F.obj.obj (op (V' i)))
    (hσ : ∀ i j, F.obj.map (overlapFst (a i) (a j)).op (σ i) =
      F.obj.map (overlapSnd (a i) (a j)).op (σ j)) :
    ∃ s : F.obj.obj (op V), ∀ i, F.obj.map (a i).op s = σ i := by
  obtain ⟨s, hs, -⟩ := (Presieve.isSheafFor_arrows_iff _ _).1
    (Scheme.isSheafFor_ofArrows F a (Set.iUnion_eq_univ_iff.2 ha)) σ
    (fun i j Z gi gj h ↦ by
      have hl : gi.left ≫ (a i).left = gj.left ≫ (a j).left := by
        simpa using congrArg (fun c ↦ c.left) h
      let l : Z ⟶ overlap (a i) (a j) :=
        MorphismProperty.Over.homMk (pullback.lift gi.left gj.left hl) (by
          change _ ≫ pullback.fst _ _ ≫ _ = _
          rw [pullback.lift_fst_assoc, MorphismProperty.Over.w gi])
      have h₁ : gi = l ≫ overlapFst (a i) (a j) := by
        apply MorphismProperty.Over.Hom.ext; simp [l]
      have h₂ : gj = l ≫ overlapSnd (a i) (a j) := by
        apply MorphismProperty.Over.Hom.ext; simp [l]
      change F.obj.map gi.op (σ i) = F.obj.map gj.op (σ j)
      rw [h₁, h₂, op_comp, op_comp, Functor.map_comp, Functor.map_comp,
        ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hσ i j])
  exact ⟨s, hs⟩

/-- Two sections of a sheaf which agree étale locally agree. -/
lemma eq_of_forall_exists_map_eq {V : X.Etale} (s₁ s₂ : F.obj.obj (op V))
    (h : ∀ x : V.left, ∃ (W : X.Etale) (b : W ⟶ V), x ∈ Set.range b.left ∧
      F.obj.map b.op s₁ = F.obj.map b.op s₂) : s₁ = s₂ := by
  choose W b hx hb using h
  rw [← sub_eq_zero]
  exact eq_zero_of_forall_map_eq_zero F b (fun x ↦ ⟨x, hx x⟩) _
    (fun x ↦ by rw [map_sub, hb, sub_self])

end Gluing

section Composition

variable {T' T'' : Scheme.{u}} (f : T' ⟶ T) (t' : T' ⟶ R) (ht' : t' = f ≫ t)
  (f' : T'' ⟶ T') (t'' : T'' ⟶ R) (ht'' : t'' = f' ≫ t')

/-- The étale `T''`-scheme `V'' ×_V V₁` for `m : V'' ⟶ V` over `T'' ⟶ T` and an étale
`a : V₁ ⟶ V`. -/
noncomputable def pullbackObj {S S' : Scheme.{u}} {V : S.Etale} {V'' : S'.Etale} {V₁ : S.Etale}
    (m : V''.left ⟶ V.left) (a : V₁ ⟶ V) : S'.Etale :=
  MorphismProperty.Over.mk ⊤ (pullback.fst m a.left ≫ V''.hom) inferInstance

/-- The projection `V'' ×_V V₁ ⟶ V''`. -/
noncomputable def pullbackObjFst {S S' : Scheme.{u}} {V : S.Etale} {V'' : S'.Etale}
    {V₁ : S.Etale} (m : V''.left ⟶ V.left) (a : V₁ ⟶ V) : pullbackObj m a ⟶ V'' :=
  MorphismProperty.Over.homMk (pullback.fst m a.left) rfl

@[simp]
lemma pullbackObj_left {S S' : Scheme.{u}} {V : S.Etale} {V'' : S'.Etale} {V₁ : S.Etale}
    (m : V''.left ⟶ V.left) (a : V₁ ⟶ V) : (pullbackObj m a).left = pullback m a.left :=
  rfl

@[simp]
lemma pullbackObj_hom {S S' : Scheme.{u}} {V : S.Etale} {V'' : S'.Etale} {V₁ : S.Etale}
    (m : V''.left ⟶ V.left) (a : V₁ ⟶ V) :
    (pullbackObj m a).hom = pullback.fst m a.left ≫ V''.hom :=
  rfl

@[simp]
lemma pullbackObjFst_left {S S' : Scheme.{u}} {V : S.Etale} {V'' : S'.Etale} {V₁ : S.Etale}
    (m : V''.left ⟶ V.left) (a : V₁ ⟶ V) :
    (pullbackObjFst m a).left = pullback.fst m a.left :=
  rfl

/-- **Restrictions compose.** -/
lemma restrictAlong_restrictAlong {V : T.Etale} {V' : T'.Etale} {V'' : T''.Etale}
    (m : V'.left ⟶ V.left) (hm : m ≫ V.hom = V'.hom ≫ f) (m' : V''.left ⟶ V'.left)
    (hm' : m' ≫ V'.hom = V''.hom ≫ f')
    (s : ((t)^*[AddCommGrpCat.{u + 1}].obj G).obj.obj (op V)) :
    restrictAlong t' G f' t'' ht'' m' hm' (restrictAlong t G f t' ht' m hm s) =
      restrictAlong t G (f' ≫ f) t'' (by rw [ht'', ht', Category.assoc]) (m' ≫ m)
        (by rw [Category.assoc, hm, reassoc_of% hm']) s := by
  apply eq_of_forall_exists_map_eq
  intro x
  obtain ⟨V₁, a, U, φ, hφ, g, ⟨w, hw⟩, hs⟩ := exists_pullSection_eq t G s (m (m' x))
  obtain ⟨z, hz₁, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := m' ≫ m) (g := a.left) x w
    (by rw [hw]; rfl)
  refine ⟨pullbackObj (m' ≫ m) a, pullbackObjFst (m' ≫ m) a, ⟨z, hz₁⟩, ?_⟩
  -- the intermediate étale `T'`-scheme `V' ×_V V₁`
  let δ : (pullbackObj (m' ≫ m) a).left ⟶ (pullbackObj m a).left :=
    pullback.lift (pullback.fst _ _ ≫ m') (pullback.snd _ _)
      (by rw [Category.assoc, pullback.condition])
  have hδ : δ ≫ (pullbackObj m a).hom = (pullbackObj (m' ≫ m) a).hom ≫ f' := by
    simp [δ, hm']
  have wa : a.left ≫ V.hom = V₁.hom := MorphismProperty.Over.w a
  have hsnd : pullback.snd m a.left ≫ V₁.hom = (pullbackObj m a).hom ≫ f := by
    rw [pullbackObj_hom, Category.assoc, ← hm, ← wa, ← pullback.condition_assoc]
  have hsnd' : pullback.snd (m' ≫ m) a.left ≫ V₁.hom =
      (pullbackObj (m' ≫ m) a).hom ≫ f' ≫ f := by
    rw [pullbackObj_hom, ← wa, ← pullback.condition_assoc, Category.assoc, hm,
      reassoc_of% hm', Category.assoc]
  -- both sides are `(snd ≫ φ)^* g`
  have e₀ : restrictAlong t G f t' ht' (pullback.snd m a.left) hsnd
      (((t)^*[AddCommGrpCat.{u + 1}].obj G).obj.map a.op s) =
        pullSection t' G (V := pullbackObj m a) (pullback.snd m a.left ≫ φ)
          (by rw [Category.assoc, hφ, reassoc_of% hsnd, ht']) g := by
    rw [hs, restrictAlong_pullSection]
  rw [map_restrictAlong, map_restrictAlong]
  have e₁ : (pullbackObjFst (m' ≫ m) a).left ≫ m' = δ ≫ (pullbackObjFst m a).left := by
    simp [δ]
  rw [restrictAlong_congr (h := e₁),
    ← restrictAlong_map _ _ _ _ _ (V' := pullbackObj (m' ≫ m) a) (pullbackObjFst m a) δ hδ,
    map_restrictAlong,
    restrictAlong_congr (h := show (pullbackObjFst m a).left ≫ m =
      pullback.snd m a.left ≫ a.left from pullback.condition),
    ← restrictAlong_map _ _ _ _ _ (V' := pullbackObj m a) a
      (pullback.snd m a.left) hsnd, e₀, restrictAlong_pullSection,
    restrictAlong_congr (h := show (pullbackObjFst (m' ≫ m) a).left ≫ m' ≫ m =
      pullback.snd (m' ≫ m) a.left ≫ a.left by simp [pullback.condition]),
    ← restrictAlong_map _ _ _ _ _ (V' := pullbackObj (m' ≫ m) a) a
      (pullback.snd (m' ≫ m) a.left) hsnd', hs,
    restrictAlong_pullSection]
  apply pullSection_congr
  simp [δ]

end Composition

end Etale

end AlgebraicGeometry
