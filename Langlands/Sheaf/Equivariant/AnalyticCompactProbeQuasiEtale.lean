import Langlands.Geometry.Analytic.QuasiEtaleCompactProbeTopology
import Langlands.Sheaf.Equivariant.AnalyticGSheaves

/-! # Twisted compact-probe quasi-étale sheaves -/

noncomputable section

universe u v z

namespace Langlands.Sheaf.Equivariant.Analytic

open CategoryTheory
open Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.TwistedOver

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X Y : LocalizedCategory.{u, v, v} (K := K)}

/-- Translating the target along an analytic isomorphism preserves the compact-probe
covering test under sieve restriction. -/
theorem QuasiEtaleSite.isCocontinuous_translate_compactProbe (e : X ≅ Y) :
    (translate e).functor.IsCocontinuous
      (compactProbeQuasiEtaleTopology X) (compactProbeQuasiEtaleTopology Y) where
  cover_lift {U S} hS := by
    let E := translate e
    intro C g hC
    obtain ⟨n, V, f, hV, hfS, hf⟩ := hS (E.functor.map g) hC
    let W i := E.inverse.obj (V i)
    let p (i : Fin n) : W i ⟶ C := MorphismProperty.Over.homMk (f i).left (by
      let a : (V i).left ⟶ C.left := (f i).left
      change a ≫ C.hom = (V i).hom ≫ e.inv
      have w : a ≫ (C.hom ≫ e.hom) = (V i).hom := MorphismProperty.Over.w (f i)
      simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using
        congrArg (fun b => b ≫ e.inv) w)
    refine ⟨n, W, p, hV, ?_, hf⟩
    intro i
    change S (E.functor.map (p i ≫ g))
    have h : E.functor.map (p i) = E.counit.app (V i) ≫ f i := by
      apply MorphismProperty.Over.Hom.ext
      change (f i).left = 𝟙 _ ≫ (f i).left
      rw [Category.id_comp]
    rw [Functor.map_comp, h, Category.assoc]
    exact S.downward_closed (hfS i) (E.counit.app (V i))

variable {G : Type z} [Group G] (ρ : G →* Aut X)

/-- The compact-probe topology is invariant under every translation of the action. -/
instance compactProbeQuasiEtale_isTranslationInvariant :
    IsTranslationInvariant (P := quasiEtale (K := K)) (ρ := ρ) (compactProbeQuasiEtaleTopology X) where
  isCocontinuous g := QuasiEtaleSite.isCocontinuous_translate_compactProbe (ρ g).asIso

/-- The twisted site carries the topology obtained from compact-probe covers after
restricting a sieve to arrows with trivial twist. -/
abbrev twistedCompactProbeQuasiEtaleTopology :
    GrothendieckTopology (TwistedOver (quasiEtale (K := K)) ρ) :=
  twistedTopology ρ (compactProbeQuasiEtaleTopology X)

variable [TopologicalSpace G]

/-- Quasi-étale `G`-sheaves over the compact-probe topology. On compact test
objects the local action on sections is discrete for every admissible lift. -/
abbrev CompactProbeQuasiEtaleGSheaf (A : Type*) [Category A] {FA : A → A → Type*}
    {CA : A → Type*} [∀ M N, FunLike (FA M N) (CA M) (CA N)] [ConcreteCategory A FA] :=
  (compactLiftSystem ρ).DiscreteSheaf A (twistedCompactProbeQuasiEtaleTopology ρ)

end Langlands.Sheaf.Equivariant.Analytic
