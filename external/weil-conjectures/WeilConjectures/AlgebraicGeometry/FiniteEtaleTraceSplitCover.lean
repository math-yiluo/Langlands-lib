/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTraceSplitting
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.AlgebraicGeometry.FiniteEtaleEtaleLocalSplit

/-!
# The presieve of finite étale splittings covers

Source: Stacks Project, Lemma 04HN, and Section 03SH after Definition 03SE.
(blueprint: lem-weil-pbc-finite-etale-trace-split-cover)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- Split domains form a covering presieve. Apply the étale local splitting theorem to
`W ×[X] Y → W`, and identify its further pullback with `T ×[X] Y` using pullback pasting.
The inverses of the piece projections supply the splitting data. The resulting arrows cover
all points of `W`; the sieve criterion then gives the covering. The empty base is covered
vacuously. Source: Stacks Project, Lemma 04HN, and Section 03SH after Definition 03SE.
(blueprint: lem-weil-pbc-finite-etale-trace-split-cover) -/
theorem finiteEtaleTrace_split_cover {X Y : Scheme.{u}} (f : Y ⟶ X)
    (hfin : IsFinite f) (hf : Etale f) (W : X.Etale) :
    Sieve.generate (finiteEtaleTraceSplitPresieve f W) ∈ X.smallEtaleTopology W := by
  classical
  let := hfin
  let := hf
  have hlocal : ∀ w : W.left, ∃ (T : X.Etale) (h : T ⟶ W),
      Nonempty (FiniteEtaleTraceSplitting f T) ∧ w ∈ Set.range h.left := by
    intro w
    obtain ⟨U, g, z, hg, hz, J, V, i, hJ, hc, hi, he⟩ :=
      finite_etale_etale_local_split (pullback.fst W.hom f) w
    let := hg
    let := hJ
    let T : X.Etale := MorphismProperty.Over.mk ⊤ (g ≫ W.hom) inferInstance
    let h : T ⟶ W := MorphismProperty.Over.homMk g rfl
    let e := pullbackSymmetry (pullback.fst W.hom f) g ≪≫
      pullbackRightPullbackFstIso W.hom f g
    let a : ∀ j, V j ⟶ pullback T.hom f := fun j ↦ i j ≫ e.hom
    have ha (j : J) : a j ≫ pullback.fst (g ≫ W.hom) f =
        i j ≫ pullback.snd (pullback.fst W.hom f) g := by
      change (i j ≫ e.hom) ≫ pullback.fst (g ≫ W.hom) f = _
      simp [e, Category.assoc]
    choose d hd using he
    let D : FiniteEtaleTraceSplitting f T :=
      { J := J
        finiteIndex := Fintype.ofFinite J
        V := V
        i := a
        t := fun j ↦ (d j).inv
        colimit := IsColimit.ofIsoColimit hc.some (Cofan.ext e (fun j ↦ rfl))
        inv₁ := fun j ↦ by
          change ((d j).inv ≫ a j) ≫ pullback.fst (g ≫ W.hom) f = 𝟙 U
          rw [Category.assoc, ha, ← hd]
          exact (d j).inv_hom_id
        inv₂ := fun j ↦ by
          change a j ≫ pullback.fst (g ≫ W.hom) f ≫ (d j).inv = 𝟙 (V j)
          rw [← Category.assoc, ha, ← hd]
          exact (d j).hom_inv_id
        openImmersion := fun j ↦ by
          let := (hi j).1
          dsimp [a]
          infer_instance
        closedImmersion := fun j ↦ by
          let := (hi j).2
          dsimp [a]
          infer_instance }
    refine ⟨T, h, ⟨D⟩, z, ?_⟩
    exact hz
  choose T h hD hw using hlocal
  apply X.smallEtaleTopology.superset_covering _
    ((Scheme.ofArrows_mem_smallEtaleTopology_iff h).mpr ?_)
  · rw [Sieve.ofArrows, Sieve.generate_le_iff]
    intro Z k hk
    obtain ⟨w⟩ := hk
    exact Sieve.le_generate _ _ _ (hD w)
  · exact Set.eq_univ_of_forall fun w ↦ Set.mem_iUnion.mpr ⟨w, hw w⟩

end AlgebraicGeometry.Etale
