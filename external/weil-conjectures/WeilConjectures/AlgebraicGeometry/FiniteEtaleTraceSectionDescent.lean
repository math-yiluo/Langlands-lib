/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTraceLocalSums
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTraceSplitCover
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTraceSplitSumCompatibility

/-!
# Local sum characterization of finite étale traces

Source: Stacks Project, Section 03SH, paragraph after Definition 03SE;
SGA 4, Exposé IX, 5.1.
(blueprint: lem-weil-pbc-finite-etale-trace-section-descent)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Descent of one section of the pullback sheaf to its characterized local sum.
Source: Stacks Project, Section 03SH, after Definition 03SE; SGA 4, Exposé IX, 5.1.
(blueprint: lem-weil-pbc-finite-etale-trace-section-descent)

Proof. Cover `W` by étale objects whose pullbacks of `Y` split (Stacks 04HN and
covering base change). Sum the restrictions of the given section along each splitting's
sections. These sums commute with restriction by the pullback universal property.
They do not depend on the splitting: intersect two splittings' clopen pieces, project
these intersections to the base, and cover the base by the opens on which the resulting
bijection between the finite sets of sheets is fixed. On each open the two sections
in corresponding sheets invert the same isomorphism and hence agree, so reindexing
the finite sum gives equality. Separatedness gives equality on the base; if there is
no such bijection the base is empty and its sections are zero.

On overlaps of the splitting cover the two restrictions of the local sums are thus
equal. The sheaf condition glues them to `u`. For any `T → W` with a splitting,
pull the chosen cover back to `T`; on its members restriction compatibility and
independence of splitting identify the restrictions of `u` with the displayed sum.
Separatedness gives the formula on `T`. Two sections with these formulas agree on
the original splitting cover, so are equal. This proves existence and uniqueness,
including an empty splitting and the empty base by the empty-cover sheaf condition. -/
theorem finiteEtaleTrace_section_descent {X Y : Scheme.{u}} (f : Y ⟶ X)
    (hfin : IsFinite f) (hf : Etale f) :
    let B := MorphismProperty.Over.pullback @Etale ⊤ f ⋙ MorphismProperty.Over.map ⊤ hf
    ∀ (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (W : X.Etale)
      (s : F.obj.obj (op (B.obj W))),
      ∃! u : F.obj.obj (op W),
        ∀ (T : X.Etale) (h : T ⟶ W) (J : Type u) [Fintype J]
          (V : J → Scheme.{u}) (i : ∀ j, V j ⟶ pullback T.hom f)
          (t : ∀ j, T.left ⟶ V j)
          (_ : IsColimit (Cofan.mk (pullback T.hom f) i))
          (hinv₁ : ∀ j, t j ≫ i j ≫ pullback.fst T.hom f = 𝟙 T.left)
          (_ : ∀ j, i j ≫ pullback.fst T.hom f ≫ t j = 𝟙 (V j))
          (_ : ∀ j, IsOpenImmersion (i j)) (_ : ∀ j, IsClosedImmersion (i j)),
          F.obj.map h.op u = ∑ j, F.obj.map (MorphismProperty.Over.homMk
            (A := T) (B := B.obj T) (t j ≫ i j)
            (by
              change (t j ≫ i j) ≫ pullback.snd T.hom f ≫ f = T.hom
              rw [← pullback.condition]
              simpa [← Category.assoc] using
                congrArg (fun k ↦ k ≫ T.hom) (hinv₁ j))).op
                  (F.obj.map (B.map h).op s) := by
  classical
  dsimp only
  intro F W s
  let B := MorphismProperty.Over.pullback @Etale ⊤ f ⋙ MorphismProperty.Over.map ⊤ hf
  let R := finiteEtaleTraceSplitPresieve f W
  let P := F.obj ⋙ forget AddCommGrpCat.{u + 1}
  have hvalue (T : X.Etale) (h : T ⟶ W) (hh : R h) :
      ∃! a : F.obj.obj (op T),
        ∀ D : FiniteEtaleTraceSplitting f T,
          a = D.sum hf F (F.obj.map (B.map h).op s) := by
    obtain ⟨D⟩ := hh
    refine ⟨D.sum hf F (F.obj.map (B.map h).op s), ?_, ?_⟩
    · intro E
      have he := finiteEtaleTrace_split_sum_compatibility f hf F W T T T h h
        (𝟙 T) (𝟙 T) rfl D E s
      simpa [B] using he
    · intro a ha
      exact ha D
  let x : Presieve.FamilyOfElements P R := fun {T} h hh ↦
    Classical.choose (hvalue T h hh).exists
  have hsum (T : X.Etale) (h : T ⟶ W) (hh : R h)
      (D : FiniteEtaleTraceSplitting f T) :
      x h hh = D.sum hf F (F.obj.map (B.map h).op s) :=
    Classical.choose_spec (hvalue T h hh).exists D
  have hx : x.Compatible := by
    intro T₁ T₂ Z g₁ g₂ h₁ h₂ hh₁ hh₂ he
    obtain ⟨D₁⟩ := hh₁
    obtain ⟨D₂⟩ := hh₂
    change F.obj.map g₁.op (x h₁ ⟨D₁⟩) = F.obj.map g₂.op (x h₂ ⟨D₂⟩)
    rw [hsum T₁ h₁ ⟨D₁⟩ D₁, hsum T₂ h₂ ⟨D₂⟩ D₂]
    exact finiteEtaleTrace_split_sum_compatibility f hf F W T₁ T₂ Z h₁ h₂ g₁ g₂ he
      D₁ D₂ s
  have hP : Presieve.IsSheaf X.smallEtaleTopology P :=
    (isSheaf_iff_isSheaf_of_type X.smallEtaleTopology P).mp
      ((Presheaf.isSheaf_iff_isSheaf_forget X.smallEtaleTopology F.obj
        (forget AddCommGrpCat.{u + 1})).mp F.property)
  obtain ⟨u, hu, huniq⟩ :=
    hP.isSheafFor R (finiteEtaleTrace_split_cover f hfin hf W) x hx
  refine ⟨u, ?_, ?_⟩
  · intro T h J inst V i t hc hi₁ hi₂ ho hcl
    let D : FiniteEtaleTraceSplitting f T :=
      ⟨J, inst, V, i, t, hc, hi₁, hi₂, ho, hcl⟩
    exact (hu h ⟨D⟩).trans (hsum T h ⟨D⟩ D)
  · intro v hv
    apply huniq v
    intro T h hh
    obtain ⟨D⟩ := hh
    let := D.finiteIndex
    exact (hv T h D.J D.V D.i D.t D.colimit D.inv₁ D.inv₂
      D.openImmersion D.closedImmersion).trans (hsum T h ⟨D⟩ D).symm

end AlgebraicGeometry.Etale
