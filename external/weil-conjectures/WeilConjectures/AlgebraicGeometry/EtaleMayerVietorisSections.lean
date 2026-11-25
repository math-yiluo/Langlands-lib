/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.Algebra.Category.Grp.Limits

/-!
# Sections for a two-open étale cover

Source: Stacks Project, Tag 0A50, proof, first and middle spots.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale
noncomputable section

private abbrev incl (X : Scheme.{u}) (U : X.Opens) :
    Scheme.Etale.mk U.ι ⟶ Scheme.Etale.mk (𝟙 X) :=
  MorphismProperty.Over.homMk U.ι (Category.comp_id U.ι)

private abbrev leftIncl (X : Scheme.{u}) (U V : X.Opens) :
    Scheme.Etale.mk (U ⊓ V).ι ⟶ Scheme.Etale.mk U.ι :=
  MorphismProperty.Over.homMk (X.homOfLE inf_le_left) (X.homOfLE_ι inf_le_left)

private abbrev rightIncl (X : Scheme.{u}) (U V : X.Opens) :
    Scheme.Etale.mk (U ⊓ V).ι ⟶ Scheme.Etale.mk V.ι :=
  MorphismProperty.Over.homMk (X.homOfLE inf_le_right) (X.homOfLE_ι inf_le_right)

private theorem twoOpen_cover (X : Scheme.{u}) (U V : X.Opens) (hcover : U ⊔ V = ⊤) :
    Sieve.ofArrows (fun b : Bool => Bool.casesOn b (Scheme.Etale.mk V.ι) (Scheme.Etale.mk U.ι))
      (fun b => Bool.casesOn b (incl X V) (incl X U)) ∈
      X.smallEtaleTopology (Scheme.Etale.mk (𝟙 X)) := by
  rw [Scheme.ofArrows_mem_smallEtaleTopology_iff]
  ext x
  simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
  have hx : x ∈ (U : Set X) ∪ V := by
    rw [← TopologicalSpace.Opens.coe_sup, hcover]
    trivial
  rcases hx with hx | hx
  · exact ⟨true, ⟨x, hx⟩, rfl⟩
  · exact ⟨false, ⟨x, hx⟩, rfl⟩

private theorem sections_pullback (X : Scheme.{u}) (U V : X.Opens)
    (hcover : U ⊔ V = ⊤) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    IsPullback (F.obj.map (incl X U).op) (F.obj.map (incl X V).op)
      (F.obj.map (leftIncl X U V).op) (F.obj.map (rightIncl X U V).op) := by
  have hcov := twoOpen_cover X U V hcover
  have hcomm : leftIncl X U V ≫ incl X U = rightIncl X U V ≫ incl X V := by
    apply MorphismProperty.Over.Hom.ext
    change X.homOfLE inf_le_left ≫ U.ι = X.homOfLE inf_le_right ≫ V.ι
    simp [Scheme.homOfLE_ι]
  refine IsPullback.of_isLimit (c := PullbackCone.mk _ _ (by
    rw [← F.obj.map_comp, ← F.obj.map_comp, ← op_comp, ← op_comp, hcomm])) ?_
  refine PullbackCone.IsLimit.mk _ (fun s => ?_) (fun s => ?_) (fun s => ?_)
    (fun s m hm₁ hm₂ => ?_)
  · exact F.property.amalgamateOfArrows _ hcov
      (fun b => Bool.casesOn b s.snd s.fst) (by
        intro W i j a b hab
        cases i <;> cases j
        · have : a = b := by
            apply MorphismProperty.Over.Hom.ext
            apply (cancel_mono V.ι).1
            exact congrArg (fun f => f.left) hab
          subst b
          rfl
        · have hab' : b.left ≫ U.ι = a.left ≫ V.ι := by
            exact congrArg (fun f => f.left) hab.symm
          let l := (isPullback_opens_inf U V).lift b.left a.left hab'
          let t : W ⟶ Scheme.Etale.mk (U ⊓ V).ι :=
            MorphismProperty.Over.homMk l (by
              change l ≫ (U ⊓ V).ι = W.hom
              rw [← X.homOfLE_ι (inf_le_left : U ⊓ V ≤ U), ← Category.assoc]
              dsimp [l]
              rw [IsPullback.lift_fst]
              exact b.w)
          have ht₁ : t ≫ leftIncl X U V = b := by
            apply MorphismProperty.Over.Hom.ext
            exact (isPullback_opens_inf U V).lift_fst _ _ _
          have ht₂ : t ≫ rightIncl X U V = a := by
            apply MorphismProperty.Over.Hom.ext
            exact (isPullback_opens_inf U V).lift_snd _ _ _
          rw [← ht₁, ← ht₂, op_comp, op_comp, F.obj.map_comp, F.obj.map_comp]
          simpa [Category.assoc] using congrArg (fun f => f ≫ F.obj.map t.op) s.condition.symm
        · have hab' : a.left ≫ U.ι = b.left ≫ V.ι := by
            exact congrArg (fun f => f.left) hab
          let l := (isPullback_opens_inf U V).lift a.left b.left hab'
          let t : W ⟶ Scheme.Etale.mk (U ⊓ V).ι :=
            MorphismProperty.Over.homMk l (by
              change l ≫ (U ⊓ V).ι = W.hom
              rw [← X.homOfLE_ι (inf_le_left : U ⊓ V ≤ U), ← Category.assoc]
              dsimp [l]
              rw [IsPullback.lift_fst]
              exact a.w)
          have ht₁ : t ≫ leftIncl X U V = a := by
            apply MorphismProperty.Over.Hom.ext
            exact (isPullback_opens_inf U V).lift_fst _ _ _
          have ht₂ : t ≫ rightIncl X U V = b := by
            apply MorphismProperty.Over.Hom.ext
            exact (isPullback_opens_inf U V).lift_snd _ _ _
          rw [← ht₁, ← ht₂, op_comp, op_comp, F.obj.map_comp, F.obj.map_comp]
          simpa [Category.assoc] using congrArg (fun f => f ≫ F.obj.map t.op) s.condition
        · have : a = b := by
            apply MorphismProperty.Over.Hom.ext
            apply (cancel_mono U.ι).1
            exact congrArg (fun f => f.left) hab
          subst b
          rfl)
  · exact F.property.amalgamateOfArrows_map _ hcov _ _ true
  · exact F.property.amalgamateOfArrows_map _ hcov _ _ false
  · apply F.property.hom_ext_ofArrows _ hcov
    intro b
    cases b
    · exact hm₂.trans (F.property.amalgamateOfArrows_map _ hcov
        (fun b => Bool.casesOn b s.snd s.fst) _ false).symm
    · exact hm₁.trans (F.property.amalgamateOfArrows_map _ hcov
        (fun b => Bool.casesOn b s.snd s.fst) _ true).symm

/-- Source: Stacks Project, Tag 0A50, proof, first and middle spots.
(blueprint: lem-weil-pbc-etale-mayer-vietoris-sections)

Proof: The open immersions are a covering by joint surjectivity. Their intersection
is their scheme-theoretic pullback. The sheaf gluing and uniqueness axioms therefore
make the square of sections a pullback. Forgetting to sets preserves this pullback;
its universal property gives injection into the product and identifies its image
with pairs whose restrictions coincide, the kernel of their difference. -/
theorem etale_mayerVietoris_sections (X : Scheme.{u}) (U V : X.Opens)
    (hcover : U ⊔ V = ⊤) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    Function.Injective (fun x : F.obj.obj (op (Scheme.Etale.mk (𝟙 X))) =>
      (F.obj.map (MorphismProperty.Over.homMk
        (A := Scheme.Etale.mk U.ι) (B := Scheme.Etale.mk (𝟙 X))
        U.ι (Category.comp_id U.ι)).op x,
       F.obj.map (MorphismProperty.Over.homMk
        (A := Scheme.Etale.mk V.ι) (B := Scheme.Etale.mk (𝟙 X))
        V.ι (Category.comp_id V.ι)).op x)) ∧
    Function.Exact (fun x : F.obj.obj (op (Scheme.Etale.mk (𝟙 X))) =>
      (F.obj.map (MorphismProperty.Over.homMk
        (A := Scheme.Etale.mk U.ι) (B := Scheme.Etale.mk (𝟙 X))
        U.ι (Category.comp_id U.ι)).op x,
       F.obj.map (MorphismProperty.Over.homMk
        (A := Scheme.Etale.mk V.ι) (B := Scheme.Etale.mk (𝟙 X))
        V.ι (Category.comp_id V.ι)).op x))
      (fun x => F.obj.map (MorphismProperty.Over.homMk
        (A := Scheme.Etale.mk (U ⊓ V).ι) (B := Scheme.Etale.mk U.ι)
        (X.homOfLE inf_le_left) (X.homOfLE_ι inf_le_left)).op x.1 -
        F.obj.map (MorphismProperty.Over.homMk
        (A := Scheme.Etale.mk (U ⊓ V).ι) (B := Scheme.Etale.mk V.ι)
        (X.homOfLE inf_le_right) (X.homOfLE_ι inf_le_right)).op x.2) := by
  let h := IsPullback.map (forget AddCommGrpCat) (sections_pullback X U V hcover F)
  let e := PullbackCone.IsLimit.equivPullbackObj h.isLimit
  constructor
  · intro x y hxy
    apply PullbackCone.IsLimit.type_ext h.isLimit
    · exact congrArg Prod.fst hxy
    · exact congrArg Prod.snd hxy
  · intro p
    constructor
    · intro hp
      let q : Types.PullbackObj
          ((forget AddCommGrpCat).map (F.obj.map (leftIncl X U V).op))
          ((forget AddCommGrpCat).map (F.obj.map (rightIncl X U V).op)) :=
        ⟨p, sub_eq_zero.mp hp⟩
      refine ⟨e.symm q, ?_⟩
      apply Prod.ext
      · exact PullbackCone.IsLimit.equivPullbackObj_symm_apply_fst h.isLimit q
      · exact PullbackCone.IsLimit.equivPullbackObj_symm_apply_snd h.isLimit q
    · rintro ⟨x, rfl⟩
      apply sub_eq_zero.mpr
      exact ConcreteCategory.congr_hom h.w x

end
end AlgebraicGeometry.Etale
