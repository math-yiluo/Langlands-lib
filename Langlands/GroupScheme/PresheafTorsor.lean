import Langlands.GroupScheme.CocycleTorsor
import Mathlib.CategoryTheory.Sites.IsSheafFor

/-! # Descending a simply transitive presheaf action to an affine torsor -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.PresheafTorsor

variable {S : Scheme.{u}} {G : GroupScheme S} {F : (Over S)ᵒᵖ ⥤ Type (u + 1)}

private theorem property_pullback_fst (P : MorphismProperty Scheme.{u})
    [P.IsStableUnderBaseChange] {V W Z : Over S} (f : V ⟶ Z) (q : W ⟶ Z)
    (hq : P q.left) : P (pullback.fst f q).left :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    ((IsPullback.of_hasPullback f q).map (Over.forget S)).flip hq

/-- A natural action on sections, with uniqueness and existence of a group
element taking any supplied section to any other supplied section. -/
structure Action (G : GroupScheme S) (F : (Over S)ᵒᵖ ⥤ Type (u + 1)) where
  act : ∀ {Z : Over S}, (Z ⟶ G.X) → F.obj (op Z) → F.obj (op Z)
  one_act : ∀ {Z : Over S} (x : F.obj (op Z)), act 1 x = x
  mul_act : ∀ {Z : Over S} (g h : Z ⟶ G.X) (x : F.obj (op Z)),
    act (g * h) x = act g (act h x)
  naturality : ∀ {Z Z' : Over S} (t : Z' ⟶ Z) (g : Z ⟶ G.X)
      (x : F.obj (op Z)), F.map t.op (act g x) = act (t ≫ g) (F.map t.op x)
  simplyTransitive : ∀ {Z : Over S} (x y : F.obj (op Z)),
    ∃! g : Z ⟶ G.X, act g x = y

namespace Action

variable (A : Action G F)

/-- The unique group point taking one given presheaf section to another. -/
def diff {Z : Over S} (x y : F.obj (op Z)) : Z ⟶ G.X :=
  (A.simplyTransitive x y).exists.choose

theorem diff_act {Z : Over S} (x y : F.obj (op Z)) :
    A.act (A.diff x y) x = y :=
  (A.simplyTransitive x y).exists.choose_spec

theorem eq_diff {Z : Over S} {x y : F.obj (op Z)} {g : Z ⟶ G.X}
    (h : A.act g x = y) : g = A.diff x y :=
  (A.simplyTransitive x y).unique h (A.diff_act x y)

theorem diff_naturality {Z Z' : Over S} (t : Z' ⟶ Z) (x y : F.obj (op Z)) :
    A.diff (F.map t.op x) (F.map t.op y) = t ≫ A.diff x y := by
  symm
  apply A.eq_diff
  rw [← A.naturality, A.diff_act]

/-- A section over a cover gives its difference cocycle. -/
def cocycle {U : Over S} (x : F.obj (op U)) : Cocycle G U where
  toFun a b := A.diff (F.map b.op x) (F.map a.op x)
  naturality t a b := by
    simp only [op_comp, F.map_comp]
    exact A.diff_naturality t _ _
  cocycle a b c := by
    symm
    apply A.eq_diff
    rw [A.mul_act, A.diff_act, A.diff_act]

theorem cocycle_act {U Z : Over S} (x : F.obj (op U)) (a b : Z ⟶ U) :
    A.act ((A.cocycle x).toFun a b) (F.map b.op x) = F.map a.op x :=
  A.diff_act _ _

section Affine

variable [IsAffine S] [IsAffineHom G.X.hom] {U : Over S}
    [IsAffine U.left] [Etale U.hom] [Surjective U.hom] (x : F.obj (op U))

abbrev model : Over S := CocycleTorsor.torsor (A.cocycle x)

/-- The actual action on the affine model. -/
@[instance_reducible]
def modelAction : ModObj G.X (A.model x) := CocycleTorsor.modObj (A.cocycle x)

local instance : ModObj G.X (A.model x) := A.modelAction x

private instance : Etale (CocycleTorsor.proj (A.cocycle x)).left :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Etale)
    (CocycleTorsor.quotient (A.cocycle x)).isPullback inferInstance

/-- The section over the trivial torsor over the cover. -/
def coverSection : F.obj (op (G.X ⊗ U)) :=
  A.act (fst G.X U) (F.map (snd G.X U).op x)

omit [IsAffine S] [IsAffineHom G.X.hom] [IsAffine U.left] [Etale U.hom]
    [Surjective U.hom] in
theorem coverSection_map {Z : Over S} (a : Z ⟶ G.X ⊗ U) :
    F.map a.op (A.coverSection x) =
      A.act (a ≫ fst G.X U) (F.map (a ≫ snd G.X U).op x) := by
  rw [coverSection, A.naturality]
  simp only [op_comp, F.map_comp, ConcreteCategory.comp_apply]

theorem coverSection_matches {Z : Over S} (a b : Z ⟶ G.X ⊗ U)
    (h : a ≫ CocycleTorsor.proj (A.cocycle x) =
      b ≫ CocycleTorsor.proj (A.cocycle x)) :
    F.map a.op (A.coverSection x) = F.map b.op (A.coverSection x) := by
  have he := (CocycleTorsor.mk_eq_mk_iff (A.cocycle x)
    (a ≫ fst G.X U) (b ≫ fst G.X U) (a ≫ snd G.X U) (b ≫ snd G.X U)).mp
      (by simpa only [CocycleTorsor.mk, lift_comp_fst_snd] using h)
  rw [A.coverSection_map, A.coverSection_map, he, A.mul_act, A.cocycle_act]

variable
  (hF : ∀ {V W : Over S} (p : V ⟶ W) [Etale p.left] [Surjective p.left],
    Presieve.IsSheafFor F (.singleton p))

/-- The universal section descended from the affine cocycle presentation. -/
def universalSection : F.obj (op (A.model x)) :=
  (Presieve.isSheafFor_singleton.mp (hF (CocycleTorsor.proj (A.cocycle x)))
    (A.coverSection x) (fun a b h => A.coverSection_matches x a b h)).exists.choose

theorem universalSection_map_proj :
    F.map (CocycleTorsor.proj (A.cocycle x)).op (A.universalSection x hF) =
      A.coverSection x :=
  (Presieve.isSheafFor_singleton.mp (hF (CocycleTorsor.proj (A.cocycle x)))
    (A.coverSection x) (fun a b h => A.coverSection_matches x a b h)).exists.choose_spec

/-- Evaluation of the descended universal section. -/
def eval {Z : Over S} (f : Z ⟶ A.model x) : F.obj (op Z) :=
  F.map f.op (A.universalSection x hF)

theorem eval_naturality {Z Z' : Over S} (t : Z' ⟶ Z) (f : Z ⟶ A.model x) :
    A.eval x hF (t ≫ f) = F.map t.op (A.eval x hF f) := by
  simp only [eval, op_comp, F.map_comp, ConcreteCategory.comp_apply]

theorem eval_mk {Z : Over S} (g : Z ⟶ G.X) (a : Z ⟶ U) :
    A.eval x hF (CocycleTorsor.mk (A.cocycle x) g a) = A.act g (F.map a.op x) := by
  rw [CocycleTorsor.mk, A.eval_naturality]
  change F.map (lift g a).op
    (F.map (CocycleTorsor.proj (A.cocycle x)).op (A.universalSection x hF)) = _
  rw [A.universalSection_map_proj, A.coverSection_map, lift_fst, lift_snd]

/-- Evaluation commutes with the actual action of the cocycle torsor. -/
theorem eval_act {Z : Over S} (g : Z ⟶ G.X) (f : Z ⟶ A.model x) :
    A.eval x hF (g • f) = A.act g (A.eval x hF f) := by
  let q := CocycleTorsor.proj (A.cocycle x)
  let p : pullback f q ⟶ Z := pullback.fst f q
  let a : pullback f q ⟶ G.X ⊗ U := pullback.snd f q
  let : Etale p.left := property_pullback_fst @Etale f q inferInstance
  let : Surjective p.left := property_pullback_fst @Surjective f q inferInstance
  apply Presieve.isSeparatedFor_singleton.mp (hF p).isSeparatedFor
  rw [← A.eval_naturality, A.naturality, ← A.eval_naturality, ModObj.comp_smul]
  have hf : p ≫ f = a ≫ q := pullback.condition
  have hmk : a ≫ q = CocycleTorsor.mk (A.cocycle x)
      (a ≫ fst G.X U) (a ≫ snd G.X U) := by
    rw [CocycleTorsor.mk, lift_comp_fst_snd]
  rw [hf, hmk, CocycleTorsor.smul_mk, A.eval_mk, A.eval_mk, A.mul_act]

/-- Evaluation is injective on every test scheme. -/
theorem eval_injective (Z : Over S) : Function.Injective (A.eval x hF (Z := Z)) := by
  intro f g hfg
  have hX := CocycleTorsor.isIso_leftSMul (A.cocycle x)
  let d := torsorDiff hX f g
  have hd : d • f = g := torsorDiff_smul hX f g
  have he : A.act d (A.eval x hF f) = A.eval x hF f := by
    rw [← A.eval_act, hd, hfg]
  have hd1 : d = 1 := (A.eq_diff he).trans (A.eq_diff (A.one_act _)).symm
  simpa only [hd1, one_smul] using hd

/-- Evaluation is surjective on every test scheme, by descent of a local
lift along the pullback of the original cover. -/
theorem eval_surjective (Z : Over S) : Function.Surjective (A.eval x hF (Z := Z)) := by
  intro z
  let W : Over S := Z ⊗ U
  let p : W ⟶ Z := fst Z U
  let a : W ⟶ U := snd Z U
  have hpb : IsPullback p.left a.left Z.hom U.hom :=
    IsPullback.of_hasPullback Z.hom U.hom
  let : Etale p.left :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Etale) hpb.flip inferInstance
  let : Surjective p.left :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Surjective) hpb.flip
      inferInstance
  let : QuasiCompact p.left :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @QuasiCompact) hpb.flip
      inferInstance
  let : EffectiveEpi p.left := inferInstance
  let d := A.diff (F.map a.op x) (F.map p.op z)
  let m : W ⟶ A.model x := CocycleTorsor.mk (A.cocycle x) d a
  have hm : A.eval x hF m = F.map p.op z := by
    rw [A.eval_mk]
    exact A.diff_act _ _
  obtain ⟨f, hf⟩ := CocycleTorsor.exists_desc p m (fun {V} b c hbc => by
    apply A.eval_injective x hF V
    rw [A.eval_naturality, A.eval_naturality, hm]
    simpa only [op_comp, F.map_comp, ConcreteCategory.comp_apply] using
      congrArg (fun k => F.map k.op z) hbc)
  refine ⟨f, ?_⟩
  apply Presieve.isSeparatedFor_singleton.mp (hF p).isSeparatedFor
  rw [← A.eval_naturality, hf, hm]

/-- The affine cocycle torsor represents the original presheaf on all tests. -/
def pointsEquiv (Z : Over S) : (Z ⟶ A.model x) ≃ F.obj (op Z) :=
  Equiv.ofBijective (A.eval x hF) ⟨A.eval_injective x hF Z, A.eval_surjective x hF Z⟩

/-- The affine torsor represents the presheaf, with its natural section
correspondence on arbitrary tests. -/
def representation : F.RepresentableBy (A.model x) where
  homEquiv := A.pointsEquiv x hF _
  homEquiv_comp := A.eval_naturality x hF

/-- The affine model has affine structure morphism. -/
theorem model_affineHom : IsAffineHom (A.model x).hom := by
  infer_instance

/-- The structure morphism of the affine model is surjective. -/
theorem model_surjective : Surjective (A.model x).hom :=
  CocycleTorsor.surjective_hom (A.cocycle x)

/-- Smoothness of the group gives smoothness of the model. -/
theorem model_smooth [Smooth G.X.hom] : Smooth (A.model x).hom :=
  CocycleTorsor.smooth_hom (A.cocycle x)

/-- The actual affine-model action is a torsor action. -/
theorem model_leftSMul_isIso : IsIso (ModObj.leftSMul G.X (A.model x)) :=
  CocycleTorsor.isIso_leftSMul (A.cocycle x)

end Affine
end Action
end Langlands.GroupScheme.PresheafTorsor
