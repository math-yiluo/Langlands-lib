/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Filtered.Basic

/-!
# Filtered colimit cocones of ring objects

Source: blueprint `chap-The-pro-etale-site`, proof of `lemma-comparison-completed-coefficients`,
paragraph "Third isomorphism"; Stacks Project, Tags 002F, 002V and 0FFK
(blueprint: lem-sfb-filtered-ring-object-cocone-colimit).

## Main statements

* `CategoryTheory.Mon.filtered_cocone_isColimit`: an underlying colimit cocone is colimiting
  in ring objects, and its canonical mediating maps preserve the unit and multiplication.
* `CategoryTheory.CommMon.filtered_cocone_isColimit`: the commutative version, in a braided
  monoidal category.
-/

@[expose] public section

universe v u w

open CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace CategoryTheory

open MonObj

/-- An underlying filtered colimit cocone of ring objects is colimiting in ring objects.
Source: blueprint `lemma-comparison-completed-coefficients`, proof, "Third isomorphism"; Stacks
Project, Tags 002F, 002V and 0FFK (blueprint: lem-sfb-filtered-ring-object-cocone-colimit).

Proof: (1) For a competing ring-object cocone `s`, the underlying colimit gives the unique
map `b` with `c_i ≫ b = s_i` (def-weil-pbc-category-colimit). (2) Choose an index using
nonemptiness. Unit preservation by its two legs implies unit preservation by `b`
(sk-def-sfb-ring-object). (3) Multiplication preservation by these legs shows that
`μ_A ≫ b` and `(b ⊗ b) ≫ μ_B` agree after `c_k ⊗ c_k` for each `k`.
(4) Filteredness provides a common successor for `i,j`; cocone naturality and tensor
bifunctoriality (def-sfb-monoidal-category) give agreement after `c_i ⊗ c_j`.
(5) For fixed `i`, preservation by `D(i) ⊗ -` and colimit uniqueness give agreement after
`c_i ⊗ id_A`. (6) Preservation by `- ⊗ A` and colimit uniqueness give the multiplication
equation for `b`. Together with (2), this is `IsMonHom b`.
(7) Bundle `b` as a ring-object morphism. Its factorization and uniqueness follow from the
underlying colimit, since ring-object morphisms are determined by their underlying maps. -/
theorem Mon.filtered_cocone_isColimit
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    {I : Type w} [SmallCategory I] [IsFiltered I]
    [∀ Y : C, PreservesColimitsOfShape I (tensorLeft Y)]
    [∀ Y : C, PreservesColimitsOfShape I (tensorRight Y)]
    {D : I ⥤ Mon C} (c : Cocone D)
    (hc : IsColimit ((Mon.forget C).mapCocone c)) :
    Nonempty (IsColimit c) ∧
      ∀ s : Cocone D,
        IsMonHom (M := c.pt.X) (N := s.pt.X) (hc.desc ((Mon.forget C).mapCocone s)) := by
  classical
  have hmon (s : Cocone D) :
      IsMonHom (M := c.pt.X) (N := s.pt.X)
        (hc.desc ((Mon.forget C).mapCocone s)) := by
    let d : c.pt.X ⟶ s.pt.X := hc.desc ((Mon.forget C).mapCocone s)
    have hd (i : I) : (c.ι.app i).hom ≫ d = (s.ι.app i).hom :=
      hc.fac ((Mon.forget C).mapCocone s) i
    constructor
    · obtain ⟨i⟩ := IsFiltered.nonempty (C := I)
      rw [← IsMonHom.one_hom (c.ι.app i).hom, Category.assoc, hd i]
      exact IsMonHom.one_hom (s.ι.app i).hom
    · have hdiag (i : I) :
          ((c.ι.app i).hom ⊗ₘ (c.ι.app i).hom) ≫ μ[c.pt.X] ≫ d =
            ((c.ι.app i).hom ⊗ₘ (c.ι.app i).hom) ≫ (d ⊗ₘ d) ≫ μ[s.pt.X] := by
        rw [← IsMonHom.mul_hom_assoc, hd i,
          tensorHom_comp_tensorHom_assoc, hd i]
        exact IsMonHom.mul_hom (s.ι.app i).hom
      have hmixed (i j : I) :
          ((c.ι.app i).hom ⊗ₘ (c.ι.app j).hom) ≫ μ[c.pt.X] ≫ d =
            ((c.ι.app i).hom ⊗ₘ (c.ι.app j).hom) ≫ (d ⊗ₘ d) ≫ μ[s.pt.X] := by
        let k := IsFiltered.max i j
        let u : i ⟶ k := IsFiltered.leftToMax i j
        let v : j ⟶ k := IsFiltered.rightToMax i j
        have hu : (D.map u).hom ≫ (c.ι.app k).hom = (c.ι.app i).hom :=
          congrArg Mon.Hom.hom (c.w u)
        have hv : (D.map v).hom ≫ (c.ι.app k).hom = (c.ι.app j).hom :=
          congrArg Mon.Hom.hom (c.w v)
        have hleg : ((c.ι.app i).hom ⊗ₘ (c.ι.app j).hom) =
            ((D.map u).hom ⊗ₘ (D.map v).hom) ≫
              ((c.ι.app k).hom ⊗ₘ (c.ι.app k).hom) := by
          rw [tensorHom_comp_tensorHom, hu, hv]
        rw [hleg]
        simpa only [Category.assoc] using
          congrArg (((D.map u).hom ⊗ₘ (D.map v).hom) ≫ ·) (hdiag k)
      apply (isColimitOfPreserves (tensorRight c.pt.X) hc).hom_ext
      intro i
      apply (isColimitOfPreserves (tensorLeft (D.obj i).X) hc).hom_ext
      intro j
      change ((D.obj i).X ◁ (c.ι.app j).hom) ≫
          ((c.ι.app i).hom ▷ c.pt.X) ≫ μ[c.pt.X] ≫ d =
        ((D.obj i).X ◁ (c.ι.app j).hom) ≫
          ((c.ι.app i).hom ▷ c.pt.X) ≫ (d ⊗ₘ d) ≫ μ[s.pt.X]
      simpa only [tensorHom_def' (c.ι.app i).hom (c.ι.app j).hom, Category.assoc,
        Functor.const_obj_obj]
        using hmixed i j
  let desc (s : Cocone D) : c.pt ⟶ s.pt :=
    { hom := hc.desc ((Mon.forget C).mapCocone s)
      isMonHom_hom := hmon s }
  refine ⟨⟨{ desc := desc, fac := ?_, uniq := ?_ }⟩, hmon⟩
  · intro s i
    apply Mon.Hom.ext
    exact hc.fac ((Mon.forget C).mapCocone s) i
  · intro s m hm
    apply Mon.Hom.ext
    apply hc.hom_ext
    intro i
    exact (congrArg Mon.Hom.hom (hm i)).trans
      (hc.fac ((Mon.forget C).mapCocone s) i).symm

end CategoryTheory
