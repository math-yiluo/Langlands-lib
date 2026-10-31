import Langlands.Geometry.Analytic.StrongAtlasQuasiIsomorphisms
import Langlands.Geometry.Analytic.DirectedAtlasComposition

/-! # Algebraic cancellation along actual strong quasi-isomorphisms -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open Set Topology CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace PresentedAffinoidAlgebra

/-- The full bounded factorization property cancels a representing structural
map on algebra homomorphisms to any presented affinoid test algebra. -/
theorem Represents.hom_ext {A B : PresentedAffinoidAlgebra K}
    {i : BoundedAlgHom K A B} {U : Set (BanachSpectrum A)}
    (hi : Represents K i U) (R : PresentedAffinoidAlgebra K)
    (ψ χ : BoundedAlgHom K B R) (heq : ψ.comp i = χ.comp i) : ψ = χ := by
  have hφ : HasImageIn K (ψ.comp i) U := by
    intro x
    change BanachSpectrum.comap i.toBoundedRingHom
      (BanachSpectrum.comap ψ.toBoundedRingHom x) ∈ U
    exact hi.hasImageIn _
  exact (hi.2.2 R _ hφ).unique rfl heq.symm

end PresentedAffinoidAlgebra

namespace AffinoidAtlasPresentation.StrongHom

variable {A B C : AffinoidAtlasPresentation.{u, v, w} K}

private theorem pullback_eq_of_eq {f g : StrongHom A B} (heq : f = g)
    (i : A.atlas.Index) (j : B.atlas.Index)
    (hf : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j))
    (hg : g.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j)) :
    f.pullback i j hf = g.pullback i j hg := by
  subst g
  rfl

/-- A strong quasi-isomorphism cancels after full directed composition.
The proof compares actual bounded pullbacks using domain uniqueness. -/
theorem IsQuasiIso.cancel_compOfDirected {s : StrongHom B C}
    (hs : s.IsQuasiIso) (hb : B.atlas.HasDirectedCharts)
    (hc : C.atlas.HasDirectedCharts) {f g : StrongHom A B}
    (heq : f.compOfDirected s hb hc = g.compOfDirected s hb hc) : f = g := by
  have hbase : f.baseMap = g.baseMap := by
    ext x
    apply hs.1.homeomorph.injective
    exact congrArg (fun F : StrongHom A C => F.baseMap x) heq
  refine ext_of_directed (f := f) (g := g) hb hbase ?_
  intro i
  obtain ⟨j, hf⟩ := f.target_exists i
  have hg : g.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j) := by
    rw [← hbase]
    exact hf
  obtain ⟨k, hsmap⟩ := s.target_exists j
  have hfs := f.comp_admissible s i j k hf hsmap
  have hgs := g.comp_admissible s i j k hg hsmap
  refine ⟨j, hf, ?_⟩
  apply (hs.2 j k hsmap).hom_ext (A.atlas.algebra i)
  have hlocal := pullback_eq_of_eq heq i k hfs hgs
  rw [compOfDirected_pullback f s hb hc i j k hf hsmap hfs,
    compOfDirected_pullback g s hb hc i j k hg hsmap hgs] at hlocal
  exact hlocal

theorem IsQuasiIso.compOfDirected_eq_iff {s : StrongHom B C}
    (hs : s.IsQuasiIso) (hb : B.atlas.HasDirectedCharts)
    (hc : C.atlas.HasDirectedCharts) (f g : StrongHom A B) :
    f.compOfDirected s hb hc = g.compOfDirected s hb hc ↔ f = g :=
  ⟨hs.cancel_compOfDirected hb hc, fun h => congrArg (fun F => F.compOfDirected s hb hc) h⟩

end AffinoidAtlasPresentation.StrongHom

namespace DirectedAtlasPresentation

variable {A B C : DirectedAtlasPresentation.{u, v, w} K}

/-- The actual directed-category arrow is monic because every local bounded
pullback of a quasi-isomorphism has the full uniqueness property. -/
theorem mono_of_isQuasiIso (s : B ⟶ C) (hs : s.IsQuasiIso) : Mono s where
  right_cancellation _ _ h := hs.cancel_compOfDirected B.directed C.directed h

/-- Postcomposition along an actual strong quasi-isomorphism embeds full
directed strong-map hom sets. -/
def postcompQuasiIsoEmbedding (s : B ⟶ C) (hs : s.IsQuasiIso) :
    (A ⟶ B) ↪ (A ⟶ C) where
  toFun f := f ≫ s
  inj' _ _ h := hs.cancel_compOfDirected B.directed C.directed h

@[simp]
theorem postcompQuasiIsoEmbedding_apply (s : B ⟶ C) (hs : s.IsQuasiIso)
    (f : A ⟶ B) :
    postcompQuasiIsoEmbedding s hs f = f ≫ s := rfl

end DirectedAtlasPresentation

end Langlands.Analytic
