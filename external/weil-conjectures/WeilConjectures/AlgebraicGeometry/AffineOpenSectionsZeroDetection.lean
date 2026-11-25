/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Category.Grp.Basic
import WeilConjectures.AlgebraicGeometry.EtaleSectionZeroNeighbourhood
import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-! # Detection of zero sections at an affine stage -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace

/-- A section whose canonical restriction to the affine limit is zero vanishes at a later stage.
Source: Stacks Project, Tag 03Q6, degree zero of lemma-colimit, proof steps (1)--(3);
Sites, Tag 0A35, lemma-pullback-to-limit; Etale Cohomology, Tag 0EYL.
Proof: Rewrite the canonical component formula in the vanishing hypothesis.
The zero-neighbourhood lemma gives an open U in D(j) containing the limit image
and on which s restricts to zero. Each stage is compact because it is affine,
and each transition is affine because its source and target are affine.
Mathlib exists_map_eq_top supplies k and f : k ⟶ j whose image lies in U.
Use IsOpenImmersion.lift to factor D(f) through U as a morphism of etale objects
over X. Presheaf functoriality expresses restriction along D(f) as restriction
to U followed by restriction along this factor. The first restriction is zero;
the second is a group homomorphism and preserves zero.
The empty limit is covered by the same compact-limit theorem, which then supplies
a stage mapping into U. Singleton diagrams and the zero sheaf need no separate case.
No site-colimit or directed-reindexing theorem is used by this proof.
(blueprint: affine-open-sections-zero-detection) -/
theorem affineOpenSections_zero_detection
    {X : Scheme.{u + 1}} {J : Type (u + 1)} [SmallCategory J] [IsCofiltered J]
    (D : J ⥤ X.Etale)
    [∀ j, IsAffine (D.obj j).left] [∀ j, IsOpenImmersion (D.obj j).hom]
    (c : Cone (D ⋙ Scheme.Etale.forget X ⋙ Over.forget X))
    (p : c.pt ⟶ X) (hp : ∀ j, c.π.app j ≫ (D.obj j).hom = p)
    (hc : IsLimit c)
    (H : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤
      Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hH : H ⊣ p.Etale.sheafPushforwardContinuous
      AddCommGrpCat.{u + 1} X.smallEtaleTopology c.pt.smallEtaleTopology)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (ν₀ : D.op ⋙ F.obj ⟶ (Functor.const Jᵒᵖ).obj
      ((H.obj F).obj.obj (op (Scheme.Etale.mk (𝟙 c.pt)))))
    (hν₀ : ∀ j, ν₀.app (op j) = (hH.unit.app F).hom.app (op (D.obj j)) ≫
      (H.obj F).obj.map (MorphismProperty.Over.homMk
        (B := p.Etale.obj (D.obj j))
        (pullback.lift (c.π.app j) (𝟙 c.pt) (by
          change c.π.app j ≫ (D.obj j).hom = 𝟙 c.pt ≫ p
          rw [Category.id_comp]
          exact hp j))
        (by exact pullback.lift_snd _ _ _)).op) :
    ∀ (j : J) (s : F.obj.obj (op (D.obj j))), ν₀.app (op j) s = 0 →
      ∃ (k : J) (f : k ⟶ j), F.obj.map (D.map f).op s = 0 := by
  intro j s hs
  rw [hν₀ j] at hs
  obtain ⟨U, hU, hz⟩ := etaleSection_zero_neighbourhood
    (D.obj j) (c.π.app j) p (hp j) H hH F s hs
  let E := D ⋙ Scheme.Etale.forget X ⋙ Over.forget X
  have : ∀ i, CompactSpace (E.obj i) := fun i ↦
    inferInstanceAs (CompactSpace (D.obj i).left)
  have : ∀ {i k : J} (f : i ⟶ k), IsAffineHom (E.map f) := fun f ↦
    inferInstanceAs (IsAffineHom (D.map f).left)
  have htop : c.π.app j ⁻¹ᵁ U = ⊤ := by
    apply top_le_iff.mp
    intro x _
    exact hU ⟨x, rfl⟩
  obtain ⟨k, f, hf⟩ := exists_map_eq_top E c hc U htop
  let b : (D.obj k).left ⟶ U :=
    IsOpenImmersion.lift U.ι (D.map f).left (by
      rintro _ ⟨x, rfl⟩
      rw [Scheme.Opens.range_ι]
      have hx := hf.ge (Set.mem_univ x)
      change (D.map f).left x ∈ U at hx
      exact hx)
  let g : D.obj k ⟶ Scheme.Etale.mk (U.ι ≫ (D.obj j).hom) :=
    MorphismProperty.Over.homMk b (by
      change b ≫ (U.ι ≫ (D.obj j).hom) = (D.obj k).hom
      rw [← Category.assoc]
      dsimp only [b]
      rw [IsOpenImmersion.lift_fac]
      exact (D.map f).w)
  let i : Scheme.Etale.mk (U.ι ≫ (D.obj j).hom) ⟶ D.obj j :=
    MorphismProperty.Over.homMk U.ι rfl
  have hgi : g ≫ i = D.map f := by
    apply MorphismProperty.Over.Hom.ext
    exact IsOpenImmersion.lift_fac _ _ _
  refine ⟨k, f, ?_⟩
  rw [← hgi, op_comp, F.obj.map_comp]
  change F.obj.map g.op (F.obj.map i.op s) = 0
  rw [hz, map_zero]
