/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Gluing
public import Mathlib.AlgebraicGeometry.Morphisms.Basic
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Gluing schemes over the members of an open cover

Let `{Y_i ⟶ Y}` be an open cover of a scheme `Y` and `p_i : P_i ⟶ Y_i` a scheme over each `Y_i`.
A *gluing datum* for the `P_i` consists of morphisms `γ_ij : P_i ×_Y Y_j ⟶ P_j` over `Y_j`,
i.e. of the morphisms `φ_ij = (γ_ij, p_i ∘ pr₁) : P_i ×_Y Y_j ⟶ P_j ×_Y Y_i` over
`Y_i ×_Y Y_j`, such that `φ_ii = id` and `φ_jk ∘ φ_ij = φ_ik` over `Y_i ×_Y Y_j ×_Y Y_k`.
Then the `P_i` glue to a `Y`-scheme `X` with cartesian squares
```
  P_i --ι_i--> X
   |           |
  p_i          n
   v           v
  Y_i -------> Y
```
compatible with the `φ_ij`, and `X` is unique up to unique isomorphism
(`AlgebraicGeometry.Scheme.Cover.exists_isPullback_of_cocycle`).

The glued scheme is the gluing (`AlgebraicGeometry.Scheme.GlueData`) of the `P_i` along the open
subschemes `P_i ×_Y Y_j ⊆ P_i`, with transition maps the `φ_ij`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Cover

variable {Y : Scheme.{u}} (𝒰 : Scheme.OpenCover.{u} Y) {P : 𝒰.I₀ → Scheme.{u}}
  (p : ∀ i, P i ⟶ 𝒰.X i)

/-- `P_i ×_Y Y_j`. -/
noncomputable abbrev glueV (i j : 𝒰.I₀) : Scheme.{u} := pullback (p i ≫ 𝒰.f i) (𝒰.f j)

section Construction

variable (γ : ∀ i j, glueV 𝒰 p i j ⟶ P j) (hγ : ∀ i j, γ i j ≫ p j = pullback.snd _ _)

/-- The transition map `φ_ij = (γ_ij, p_i ∘ pr₁) : P_i ×_Y Y_j ⟶ P_j ×_Y Y_i`. -/
noncomputable def glueT (i j : 𝒰.I₀) : glueV 𝒰 p i j ⟶ glueV 𝒰 p j i :=
  pullback.lift (γ i j) (pullback.fst _ _ ≫ p i) (by
    rw [reassoc_of% hγ, Category.assoc, pullback.condition])

@[reassoc (attr := simp)]
lemma glueT_fst (i j : 𝒰.I₀) : glueT 𝒰 p γ hγ i j ≫ pullback.fst _ _ = γ i j :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma glueT_snd (i j : 𝒰.I₀) :
    glueT 𝒰 p γ hγ i j ≫ pullback.snd _ _ = pullback.fst _ _ ≫ p i :=
  pullback.lift_snd _ _ _

@[reassoc]
lemma glueV_fst_comp (i : 𝒰.I₀) :
    pullback.fst (p i ≫ 𝒰.f i) (𝒰.f i) ≫ p i = pullback.snd (p i ≫ 𝒰.f i) (𝒰.f i) := by
  rw [← cancel_mono (𝒰.f i), Category.assoc, pullback.condition]

lemma glueV_fst_lift (i : 𝒰.I₀) :
    pullback.fst (p i ≫ 𝒰.f i) (𝒰.f i) ≫ pullback.lift (𝟙 (P i)) (p i) (Category.id_comp _) =
      𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, Category.comp_id, Category.id_comp]
  · rw [Category.assoc, pullback.lift_snd, Category.id_comp, glueV_fst_comp]

instance (i : 𝒰.I₀) : IsIso (pullback.fst (p i ≫ 𝒰.f i) (𝒰.f i)) :=
  ⟨⟨pullback.lift (𝟙 _) (p i) (Category.id_comp _), glueV_fst_lift 𝒰 p i, pullback.lift_fst _ _ _⟩⟩

variable (hid : ∀ i, pullback.lift (𝟙 (P i)) (p i) (Category.id_comp _) ≫ γ i i = 𝟙 (P i))
  (hcocycle : ∀ (i j k : 𝒰.I₀) {T : Scheme.{u}} (u : T ⟶ glueV 𝒰 p i j) (v : T ⟶ glueV 𝒰 p j k)
    (w : T ⟶ glueV 𝒰 p i k), u ≫ pullback.fst _ _ = w ≫ pullback.fst _ _ →
      u ≫ γ i j = v ≫ pullback.fst _ _ → v ≫ pullback.snd _ _ = w ≫ pullback.snd _ _ →
        v ≫ γ j k = w ≫ γ i k)

include hid in
lemma glue_γ_self (i : 𝒰.I₀) : γ i i = pullback.fst _ _ := by
  rw [← Category.id_comp (γ i i), ← glueV_fst_lift 𝒰 p i, Category.assoc, hid, Category.comp_id]

include hid in
lemma glueT_self (i : 𝒰.I₀) : glueT 𝒰 p γ hγ i i = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [glueT_fst, glue_γ_self 𝒰 p γ hid, Category.id_comp]
  · rw [glueT_snd, glueV_fst_comp, Category.id_comp]

include hid hcocycle in
lemma glueT_γ (i j : 𝒰.I₀) : glueT 𝒰 p γ hγ i j ≫ γ j i = pullback.fst _ _ := by
  have := hcocycle i j i (𝟙 _) (glueT 𝒰 p γ hγ i j)
    (pullback.lift (pullback.fst _ _) (pullback.fst _ _ ≫ p i) (by simp [pullback.condition]))
    (by rw [Category.id_comp, pullback.lift_fst]) (by rw [Category.id_comp, glueT_fst])
    (by rw [glueT_snd, pullback.lift_snd])
  rw [this, glue_γ_self 𝒰 p γ hid, pullback.lift_fst]

include hid hcocycle in
lemma glueT_inv (i j : 𝒰.I₀) : glueT 𝒰 p γ hγ i j ≫ glueT 𝒰 p γ hγ j i = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, glueT_fst, glueT_γ 𝒰 p γ hγ hid hcocycle, Category.id_comp]
  · rw [Category.assoc, glueT_snd, glueT_fst_assoc, hγ, Category.id_comp]

/-- The map `t'_ijk : (P_i ×_Y Y_j) ×_{P_i} (P_i ×_Y Y_k) ⟶ (P_j ×_Y Y_k) ×_{P_j} (P_j ×_Y Y_i)`
of the gluing datum. -/
noncomputable def glueT' (i j k : 𝒰.I₀) :
    pullback (pullback.fst (p i ≫ 𝒰.f i) (𝒰.f j)) (pullback.fst (p i ≫ 𝒰.f i) (𝒰.f k)) ⟶
      pullback (pullback.fst (p j ≫ 𝒰.f j) (𝒰.f k)) (pullback.fst (p j ≫ 𝒰.f j) (𝒰.f i)) :=
  pullback.lift
    (pullback.lift (pullback.fst _ _ ≫ γ i j) (pullback.snd _ _ ≫ pullback.snd _ _) (by
      rw [Category.assoc, reassoc_of% hγ, ← pullback.condition, pullback.condition_assoc,
        pullback.condition, Category.assoc]))
    (pullback.fst _ _ ≫ glueT 𝒰 p γ hγ i j) (by rw [pullback.lift_fst, Category.assoc, glueT_fst])

@[reassoc (attr := simp)]
lemma glueT'_fst_fst (i j k : 𝒰.I₀) :
    glueT' 𝒰 p γ hγ i j k ≫ pullback.fst _ _ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ γ i j := by
  rw [glueT', pullback.lift_fst_assoc, pullback.lift_fst]

@[reassoc (attr := simp)]
lemma glueT'_fst_snd (i j k : 𝒰.I₀) :
    glueT' 𝒰 p γ hγ i j k ≫ pullback.fst _ _ ≫ pullback.snd _ _ =
      pullback.snd _ _ ≫ pullback.snd _ _ := by
  rw [glueT', pullback.lift_fst_assoc, pullback.lift_snd]

@[reassoc (attr := simp)]
lemma glueT'_snd (i j k : 𝒰.I₀) :
    glueT' 𝒰 p γ hγ i j k ≫ pullback.snd _ _ = pullback.fst _ _ ≫ glueT 𝒰 p γ hγ i j := by
  rw [glueT', pullback.lift_snd]

include hid hcocycle in
lemma glueT'_cocycle (i j k : 𝒰.I₀) :
    glueT' 𝒰 p γ hγ i j k ≫ glueT' 𝒰 p γ hγ j k i ≫ glueT' 𝒰 p γ hγ k i j = 𝟙 _ := by
  -- the cocycle condition for `(z₁, z₂)`
  have hA : glueT' 𝒰 p γ hγ i j k ≫ pullback.fst _ _ ≫ γ j k =
      pullback.snd _ _ ≫ γ i k := by
    have := hcocycle i j k (pullback.fst _ _) (glueT' 𝒰 p γ hγ i j k ≫ pullback.fst _ _)
      (pullback.snd _ _) pullback.condition (by rw [Category.assoc, glueT'_fst_fst])
      (by rw [Category.assoc, glueT'_fst_snd])
    rwa [Category.assoc] at this
  have hB : glueT' 𝒰 p γ hγ i j k ≫ glueT' 𝒰 p γ hγ j k i ≫ pullback.fst _ _ =
      pullback.snd _ _ ≫ glueT 𝒰 p γ hγ i k := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, glueT'_fst_fst, hA, Category.assoc, glueT_fst]
    · rw [Category.assoc, Category.assoc, glueT'_fst_snd, glueT'_snd_assoc, glueT_snd,
        Category.assoc, glueT_snd, pullback.condition_assoc]
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · simp only [Category.assoc, Category.id_comp]
      rw [glueT'_fst_fst, reassoc_of% hB, glueT_γ 𝒰 p γ hγ hid hcocycle, pullback.condition]
    · simp only [Category.assoc, Category.id_comp]
      rw [glueT'_fst_snd, glueT'_snd_assoc, glueT_snd, glueT'_fst_fst_assoc, hγ]
  · simp only [Category.assoc, Category.id_comp]
    rw [glueT'_snd, reassoc_of% hB, glueT_inv 𝒰 p γ hγ hid hcocycle, Category.comp_id]
/-- The gluing datum of schemes attached to a cocycle. -/
noncomputable def glueDataOfCocycle : Scheme.GlueData.{u} where
  J := 𝒰.I₀
  U := P
  V ij := glueV 𝒰 p ij.1 ij.2
  f i j := pullback.fst _ _
  f_mono _ _ := inferInstance
  f_id _ := inferInstance
  t := glueT 𝒰 p γ hγ
  t_id := glueT_self 𝒰 p γ hγ hid
  t' := glueT' 𝒰 p γ hγ
  t_fac i j k := glueT'_snd 𝒰 p γ hγ i j k
  cocycle := glueT'_cocycle 𝒰 p γ hγ hid hcocycle
  f_open _ _ := inferInstance

section Glued

variable (hid : ∀ i, pullback.lift (𝟙 (P i)) (p i) (Category.id_comp _) ≫ γ i i = 𝟙 (P i))
  (hcocycle : ∀ (i j k : 𝒰.I₀) {T : Scheme.{u}} (u : T ⟶ glueV 𝒰 p i j) (v : T ⟶ glueV 𝒰 p j k)
    (w : T ⟶ glueV 𝒰 p i k), u ≫ pullback.fst _ _ = w ≫ pullback.fst _ _ →
      u ≫ γ i j = v ≫ pullback.fst _ _ → v ≫ pullback.snd _ _ = w ≫ pullback.snd _ _ →
        v ≫ γ j k = w ≫ γ i k)

lemma glueT_comp_base (i j : 𝒰.I₀) : glueT 𝒰 p γ hγ i j ≫ pullback.fst _ _ ≫ p j ≫ 𝒰.f j =
    pullback.fst (p i ≫ 𝒰.f i) (𝒰.f j) ≫ p i ≫ 𝒰.f i := by
  rw [glueT_fst_assoc, reassoc_of% hγ, pullback.condition]

/-- The glued scheme. -/
noncomputable def glued : Scheme.{u} := (glueDataOfCocycle 𝒰 p γ hγ hid hcocycle).glued

/-- The open immersion `ι_i : P_i ⟶ X` into the glued scheme. -/
noncomputable def glueι (i : 𝒰.I₀) : P i ⟶ glued 𝒰 p γ hγ hid hcocycle :=
  (glueDataOfCocycle 𝒰 p γ hγ hid hcocycle).ι i

instance (i : 𝒰.I₀) : IsOpenImmersion (glueι 𝒰 p γ hγ hid hcocycle i) :=
  Scheme.GlueData.ι_isOpenImmersion (glueDataOfCocycle 𝒰 p γ hγ hid hcocycle) i

lemma glueι_jointly_surjective (x : glued 𝒰 p γ hγ hid hcocycle) :
    ∃ (i : 𝒰.I₀) (z : P i), glueι 𝒰 p γ hγ hid hcocycle i z = x :=
  (glueDataOfCocycle 𝒰 p γ hγ hid hcocycle).ι_jointly_surjective x

/-- The compatibility of the `ι_i` with the gluing datum: `ι_i (x) = ι_j (γ_ij (x, y))`. -/
@[reassoc]
lemma fst_glueι (i j : 𝒰.I₀) :
    pullback.fst (p i ≫ 𝒰.f i) (𝒰.f j) ≫ glueι 𝒰 p γ hγ hid hcocycle i =
      γ i j ≫ glueι 𝒰 p γ hγ hid hcocycle j :=
  ((glueDataOfCocycle 𝒰 p γ hγ hid hcocycle).glue_condition i j).symm.trans
    (glueT_fst_assoc 𝒰 p γ hγ i j _)

lemma glued_hom_ext {Z : Scheme.{u}} {g g' : glued 𝒰 p γ hγ hid hcocycle ⟶ Z}
    (h : ∀ i, glueι 𝒰 p γ hγ hid hcocycle i ≫ g = glueι 𝒰 p γ hγ hid hcocycle i ≫ g') :
    g = g' :=
  Multicoequalizer.hom_ext _ _ _ h

/-- The morphism out of the glued scheme defined by morphisms `P_i ⟶ Z` compatible with the
gluing datum. -/
noncomputable def glueDesc {Z : Scheme.{u}} (g : ∀ i, P i ⟶ Z)
    (hg : ∀ i j, pullback.fst (p i ≫ 𝒰.f i) (𝒰.f j) ≫ g i = γ i j ≫ g j) :
    glued 𝒰 p γ hγ hid hcocycle ⟶ Z :=
  Multicoequalizer.desc _ _ g (by
    rintro ⟨i, j⟩
    exact (hg i j).trans (glueT_fst_assoc 𝒰 p γ hγ i j _).symm)

@[reassoc (attr := simp)]
lemma glueι_glueDesc {Z : Scheme.{u}} (g : ∀ i, P i ⟶ Z)
    (hg : ∀ i j, pullback.fst (p i ≫ 𝒰.f i) (𝒰.f j) ≫ g i = γ i j ≫ g j) (i : 𝒰.I₀) :
    glueι 𝒰 p γ hγ hid hcocycle i ≫ glueDesc 𝒰 p γ hγ hid hcocycle g hg = g i :=
  Multicoequalizer.π_desc _ _ _ _ _

/-- The structure morphism `X ⟶ Y` of the glued scheme. -/
noncomputable def glueToBase : glued 𝒰 p γ hγ hid hcocycle ⟶ Y :=
  glueDesc 𝒰 p γ hγ hid hcocycle (fun i ↦ p i ≫ 𝒰.f i) fun i j ↦
    (glueT_comp_base 𝒰 p γ hγ i j).symm.trans (glueT_fst_assoc 𝒰 p γ hγ i j _)

@[reassoc (attr := simp)]
lemma glueι_glueToBase (i : 𝒰.I₀) :
    glueι 𝒰 p γ hγ hid hcocycle i ≫ glueToBase 𝒰 p γ hγ hid hcocycle = p i ≫ 𝒰.f i :=
  glueι_glueDesc _ _ _ _ _ _ _ _ _

lemma preimage_glueToBase_opensRange (i : 𝒰.I₀) :
    glueToBase 𝒰 p γ hγ hid hcocycle ⁻¹ᵁ (𝒰.f i).opensRange =
      (glueι 𝒰 p γ hγ hid hcocycle i).opensRange := by
  ext x
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨j, z, rfl⟩ := glueι_jointly_surjective 𝒰 p γ hγ hid hcocycle x
    rw [← Scheme.Hom.comp_apply, glueι_glueToBase] at hy
    obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := p j ≫ 𝒰.f j) (g := 𝒰.f i)
      z y hy.symm
    refine ⟨γ j i w, ?_⟩
    rw [← hw, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, fst_glueι]
  · rintro ⟨z, rfl⟩
    refine ⟨p i z, ?_⟩
    rw [← Scheme.Hom.comp_apply (glueι 𝒰 p γ hγ hid hcocycle i), glueι_glueToBase,
      Scheme.Hom.comp_apply]

lemma isPullback_glueι (i : 𝒰.I₀) :
    IsPullback (glueι 𝒰 p γ hγ hid hcocycle i) (p i) (glueToBase 𝒰 p γ hγ hid hcocycle)
      (𝒰.f i) :=
  (IsOpenImmersion.isPullback _ _ _ _ (glueι_glueToBase 𝒰 p γ hγ hid hcocycle i)
    (preimage_glueToBase_opensRange 𝒰 p γ hγ hid hcocycle i)).flip

/-- Any `Y`-scheme `X'` with cartesian squares `P_i ⟶ X'` over `Y_i ⟶ Y` compatible with the
gluing datum is isomorphic to the glued scheme. -/
lemma isIso_glueDesc {X' : Scheme.{u}} (n' : X' ⟶ Y) (ι' : ∀ i, P i ⟶ X')
    (hX' : ∀ i, IsPullback (ι' i) (p i) n' (𝒰.f i))
    (hc' : ∀ i j, pullback.fst (p i ≫ 𝒰.f i) (𝒰.f j) ≫ ι' i = γ i j ≫ ι' j) :
    IsIso (glueDesc 𝒰 p γ hγ hid hcocycle ι' hc') := by
  have hgn : glueDesc 𝒰 p γ hγ hid hcocycle ι' hc' ≫ n' = glueToBase 𝒰 p γ hγ hid hcocycle :=
    glued_hom_ext _ _ _ _ _ _ fun i ↦ by
      rw [glueι_glueDesc_assoc, glueι_glueToBase, (hX' i).w]
  have hι' (i : 𝒰.I₀) : IsOpenImmersion (ι' i) :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (hX' i).flip inferInstance
  let 𝒱 : X'.OpenCover := Cover.mkOfCovers 𝒰.I₀ P ι' (fun x ↦ by
      obtain ⟨i, y, hy⟩ := 𝒰.exists_eq (n' x)
      obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := n') (g := 𝒰.f i) x y
        hy.symm
      refine ⟨i, (hX' i).isoPullback.inv w, ?_⟩
      rw [← Scheme.Hom.comp_apply, IsPullback.isoPullback_inv_fst, hw]) hι'
  rw [← MorphismProperty.isomorphisms.iff]
  refine IsZariskiLocalAtTarget.of_openCover 𝒱 fun (i : 𝒰.I₀) ↦ ?_
  have h : IsPullback (glueι 𝒰 p γ hγ hid hcocycle i) (𝟙 _) (glueDesc 𝒰 p γ hγ hid hcocycle ι' hc')
      (ι' i) := by
    refine IsPullback.of_bot ?_ (by rw [glueι_glueDesc, Category.id_comp]) (hX' i)
    rw [Category.id_comp, hgn]
    exact isPullback_glueι 𝒰 p γ hγ hid hcocycle i
  have e := h.isoPullback_hom_snd
  rw [← Iso.eq_inv_comp, Category.comp_id] at e
  rw [MorphismProperty.isomorphisms.iff]
  have : IsIso (pullback.snd (glueDesc 𝒰 p γ hγ hid hcocycle ι' hc') (ι' i)) := by
    rw [e]
    infer_instance
  exact this

end Glued

end Construction

/-- **Gluing schemes along an open cover** (blueprint: `lem-galois-glue`). Let `{Y_i ⟶ Y}` be an
open cover, `p_i : P_i ⟶ Y_i` schemes over its members, and `γ_ij : P_i ×_Y Y_j ⟶ P_j` morphisms
over `Y_j` (`γ_ij ≫ p_j = pr₂`), i.e. morphisms
`φ_ij = (γ_ij, p_i ∘ pr₁) : P_i ×_Y Y_j ⟶ P_j ×_Y Y_i`
over `Y_i ×_Y Y_j`, satisfying `φ_ii = id` and the cocycle condition `φ_jk ∘ φ_ij = φ_ik` over
the triple intersections: for `u = (x, a)` in `P_i ×_Y Y_j`, `w = (x, b)` in `P_i ×_Y Y_k` and
`v = (γ_ij (x, a), b)` in `P_j ×_Y Y_k`, we have `γ_jk v = γ_ik w`.

Then there is a `Y`-scheme `n : X ⟶ Y` with morphisms `ι_i : P_i ⟶ X` such that the squares
```
  P_i --ι_i--> X
   |           |
  p_i          n
   v           v
  Y_i -------> Y
```
are cartesian (`X ×_Y Y_i ≅ P_i`), compatibly with the `φ_ij`: `ι_i x = ι_j (γ_ij (x, a))`.
It is unique up to unique isomorphism: any other such `(X', n', ι')` is isomorphic to `X` by a
unique isomorphism compatible with the `ι_i`. -/
theorem exists_isPullback_of_cocycle
    (γ : ∀ i j, glueV 𝒰 p i j ⟶ P j) (hγ : ∀ i j, γ i j ≫ p j = pullback.snd _ _)
    (hid : ∀ i, pullback.lift (𝟙 (P i)) (p i) (Category.id_comp _) ≫ γ i i = 𝟙 (P i))
    (hcocycle : ∀ (i j k : 𝒰.I₀) {T : Scheme.{u}} (u : T ⟶ glueV 𝒰 p i j)
      (v : T ⟶ glueV 𝒰 p j k) (w : T ⟶ glueV 𝒰 p i k),
      u ≫ pullback.fst _ _ = w ≫ pullback.fst _ _ → u ≫ γ i j = v ≫ pullback.fst _ _ →
        v ≫ pullback.snd _ _ = w ≫ pullback.snd _ _ → v ≫ γ j k = w ≫ γ i k) :
    ∃ (X : Scheme.{u}) (n : X ⟶ Y) (ι : ∀ i, P i ⟶ X),
      (∀ i, IsPullback (ι i) (p i) n (𝒰.f i)) ∧
      (∀ i j, pullback.fst (p i ≫ 𝒰.f i) (𝒰.f j) ≫ ι i = γ i j ≫ ι j) ∧
      ∀ (X' : Scheme.{u}) (n' : X' ⟶ Y) (ι' : ∀ i, P i ⟶ X'),
        (∀ i, IsPullback (ι' i) (p i) n' (𝒰.f i)) →
        (∀ i j, pullback.fst (p i ≫ 𝒰.f i) (𝒰.f j) ≫ ι' i = γ i j ≫ ι' j) →
        ∃! e : X ≅ X', ∀ i, ι i ≫ e.hom = ι' i := by
  refine ⟨glued 𝒰 p γ hγ hid hcocycle, glueToBase 𝒰 p γ hγ hid hcocycle,
    glueι 𝒰 p γ hγ hid hcocycle, isPullback_glueι 𝒰 p γ hγ hid hcocycle,
    fst_glueι 𝒰 p γ hγ hid hcocycle, fun X' n' ι' hX' hc' ↦ ?_⟩
  have := isIso_glueDesc 𝒰 p γ hγ hid hcocycle n' ι' hX' hc'
  refine ⟨asIso (glueDesc 𝒰 p γ hγ hid hcocycle ι' hc'),
    glueι_glueDesc 𝒰 p γ hγ hid hcocycle ι' hc', fun e he ↦ ?_⟩
  ext1
  exact glued_hom_ext _ _ _ _ _ _ fun i ↦ by rw [he, asIso_hom, glueι_glueDesc]

end AlgebraicGeometry.Scheme.Cover
