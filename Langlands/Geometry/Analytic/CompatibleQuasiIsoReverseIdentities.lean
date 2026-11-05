import Langlands.Geometry.Analytic.CoherentQuasiIsoReverseSubatlas
import Langlands.Geometry.Analytic.CompatibleStrongSubatlasRefinement

/-! # Full compatible reverse identities after actual chart refinement -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open CategoryTheory Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace AffinoidAtlasPresentation.CompatibleStrongHom

variable {A B C : AffinoidAtlasPresentation.{u, v, w} K}

private theorem pullback_eq_of_eq {f g : CompatibleStrongHom A B} (heq : f = g)
    (i : A.atlas.Index) (j : B.atlas.Index)
    (hf : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j))
    (hg : g.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j)) :
    f.pullback i j hf = g.pullback i j hg := by
  subst g
  rfl

/-- Full affinoid-test uniqueness cancels postcomposition by an actual
quasi-isomorphism, without directedness or domain-closure hypotheses. -/
theorem cancel_comp {s : CompatibleStrongHom B C} (hs : s.toStrongHom.IsQuasiIso)
    {f g : CompatibleStrongHom A B} (heq : f.comp s = g.comp s) : f = g := by
  have hbase : f.baseMap = g.baseMap := by
    ext x
    apply hs.1.injective
    exact congrArg (fun F : CompatibleStrongHom A C => F.baseMap x) heq
  refine ext_of_pullback hbase ?_
  intro i
  obtain ⟨j, hf⟩ := f.target_exists i
  have hg : g.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j) := by
    rw [← hbase]
    exact hf
  obtain ⟨k, hsmap⟩ := s.target_exists j
  have hfs := f.toStrongHom.comp_admissible s.toStrongHom i j k hf hsmap
  have hgs := g.toStrongHom.comp_admissible s.toStrongHom i j k hg hsmap
  refine ⟨j, hf, ?_⟩
  apply (hs.2 j k hsmap).hom_ext (A.atlas.algebra i)
  have hlocal := pullback_eq_of_eq heq i k hfs hgs
  rw [comp_pullback f s i j k hf hsmap hfs,
    comp_pullback g s i j k hg hsmap hgs] at hlocal
  exact hlocal

theorem comp_quasiIso_eq_iff (s : CompatibleStrongHom B C)
    (hs : s.toStrongHom.IsQuasiIso) (f g : CompatibleStrongHom A B) :
    f.comp s = g.comp s ↔ f = g :=
  ⟨cancel_comp hs, fun h => congrArg (fun F => F.comp s) h⟩

/-- Postcomposition embeds complete compatible-map hom sets, including all
admissible bounded algebra pullbacks. -/
def postcompQuasiIsoEmbedding (s : CompatibleStrongHom B C)
    (hs : s.toStrongHom.IsQuasiIso) :
    CompatibleStrongHom A B ↪ CompatibleStrongHom A C where
  toFun f := f.comp s
  inj' _ _ h := cancel_comp hs h

@[simp]
theorem postcompQuasiIsoEmbedding_apply (s : CompatibleStrongHom B C)
    (hs : s.toStrongHom.IsQuasiIso) (f : CompatibleStrongHom A B) :
    postcompQuasiIsoEmbedding s hs f = f.comp s := rfl

/-- The reverse map on the constructed target selection, followed by the
original map, is exactly the full compatible subatlas inclusion. -/
theorem reverse_comp (f : CompatibleStrongHom A B) (hf : f.toStrongHom.IsQuasiIso)
    (hb : B.atlas.HasAllLocalDomains) :
    (hf.reverseCompatibleStrongMap f.coherent hb).comp f =
      B.compatibleSubatlasInclusion hf.reverseChartSelection
        (hf.reverseChartSelection_locallyRefining hb) := by
  have hbase :
      ((hf.reverseCompatibleStrongMap f.coherent hb).comp f).baseMap =
        (B.compatibleSubatlasInclusion hf.reverseChartSelection
          (hf.reverseChartSelection_locallyRefining hb)).baseMap := by
    ext x
    exact hf.baseMap_inverseBaseMap x
  refine ext_of_pullback hbase ?_
  intro j
  obtain ⟨i, hi⟩ := j.property
  obtain ⟨q, hfq⟩ := f.target_exists i
  have hinv := (hf.inverse_admissible_iff j.val i).mpr hi
  have hjq := hi.trans hfq
  have h := (hf.reverseStrongMap f.coherent hb).comp_admissible f.toStrongHom
    j i q hinv hfq
  refine ⟨q, h, ?_⟩
  rw [comp_pullback (hf.reverseCompatibleStrongMap f.coherent hb) f
    j i q hinv hfq h]
  change (hf.reverseChartPullback j.val i hi).comp (f.pullback i q hfq) =
    B.atlas.restriction j.val q hjq
  exact hf.reverseChartPullback_comp_pullback f.coherent j.val i hi q hfq hjq

/-- Lift the original forward map to the reverse target selection by the
actual source-refinement construction. Its composite with the reverse map
is the complete original-source inclusion. -/
theorem lift_comp_reverse (f : CompatibleStrongHom A B)
    (hf : f.toStrongHom.IsQuasiIso) (ha : A.atlas.HasAllLocalDomains)
    (hb : B.atlas.HasAllLocalDomains) :
    (f.targetSubatlasLift ha hf.reverseChartSelection
      (hf.reverseChartSelection_locallyRefining hb)).comp
        (hf.reverseCompatibleStrongMap f.coherent hb) =
      A.compatibleSubatlasInclusion
        (f.toStrongHom.sourceSelectionForTarget hf.reverseChartSelection)
        (f.toStrongHom.sourceSelectionForTarget_locallyRefining ha
          hf.reverseChartSelection (hf.reverseChartSelection_locallyRefining hb)) := by
  apply cancel_comp hf
  let L := f.targetSubatlasLift ha hf.reverseChartSelection
    (hf.reverseChartSelection_locallyRefining hb)
  let r := hf.reverseCompatibleStrongMap f.coherent hb
  exact (comp_assoc L r f).trans
    ((congrArg (fun g : CompatibleStrongHom (hf.reverseSubpresentation hb) B => L.comp g)
      (f.reverse_comp hf hb)).trans
        (f.targetSubatlasLift_square ha hf.reverseChartSelection
          (hf.reverseChartSelection_locallyRefining hb)))

end AffinoidAtlasPresentation.CompatibleStrongHom

namespace CompatibleAtlasPresentation

variable {A B C : CompatibleAtlasPresentation.{u, v, w} K}

/-- Quasi-isomorphisms are monomorphisms in the actual compatible-map
category by uniqueness on all presented-affinoid coefficient tests. -/
theorem mono_of_isQuasiIso (s : B ⟶ C) (hs : s.toStrongHom.IsQuasiIso) : Mono s where
  right_cancellation _ _ h :=
    AffinoidAtlasPresentation.CompatibleStrongHom.cancel_comp hs h

end CompatibleAtlasPresentation
end Langlands.Analytic
