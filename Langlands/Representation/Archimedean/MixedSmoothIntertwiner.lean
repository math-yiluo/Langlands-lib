import Langlands.Representation.Archimedean.MixedSmoothExtension

/-! # Transport of mixed smooth vectors and continuous functionals -/

noncomputable section
set_option autoImplicit false
open scoped Manifold ContDiff

namespace Langlands.Archimedean.MixedSmooth

open Langlands.HarishChandraSchwartz SmoothInvariantSubspace

universe uA uG uL uE uE'

variable {A : Type uA} [NormedAddCommGroup A] [NormedSpace ℝ A]
  {G : Type uG} [Group G] [TopologicalSpace G] [ChartedSpace A G]
  {L : Type uL} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  {E' : Type uE'} [NormedAddCommGroup E'] [InnerProductSpace ℂ E']
  (σ : L →* (E →L[ℂ] E)) (π : G →* (E →L[ℂ] E))
  (c : ∀ g d x, π g (σ d x) = σ d (π g x))
  (σ' : L →* (E' →L[ℂ] E')) (π' : G →* (E' →L[ℂ] E'))
  (c' : ∀ g d x, π' g (σ' d x) = σ' d (π' g x))
  (M : E →L[ℂ] E') (hf : ∀ d x, M (σ d x) = σ' d (M x))
  (ha : ∀ g x, M (π g x) = π' g (M x))

local notation "I" => 𝓘(ℝ, A)
local notation "W" => Vectors (A := A) σ π c
local notation "W'" => Vectors (A := A) σ' π' c'

/-- A bounded map intertwining both actions restricts to an intertwiner
of the genuine mixed smooth representations. -/
def map : (finiteRepresentation (A := A) σ π c).IntertwiningMap
    (finiteRepresentation (A := A) σ' π' c') :=
  Langlands.smoothMap
    ((SmoothIntertwiner.map I π π' M ha).intertwiningMap_of_isIntertwiningMap
      (finiteOnSmooth σ π c) (finiteOnSmooth σ' π' c')
      (fun d x => Subtype.ext (hf d x.val)))

@[simp]
theorem map_val (w : W) : (map σ π c σ' π' c' M hf ha w).val =
    SmoothIntertwiner.map I π π' M ha w.val :=
  rfl

/-- The induced mixed smooth map preserves each finite fixed level. -/
theorem map_fixed (J : Subgroup L) (w : W) (hw : w.val.val ∈ fixedSubspace σ J) :
    (map σ π c σ' π' c' M hf ha w).val.val ∈ fixedSubspace σ' J := by
  intro d
  change σ' d.val (M w.val.val) = M w.val.val
  exact (hf d.val w.val.val).symm.trans (congrArg M (hw d))

variable [LieGroup 𝓘(ℝ, A) ∞ G]

/-- The same mixed map intertwines the actual archimedean translations. -/
theorem map_archimedeanRepresentation (g : G) (w : W) :
    map σ π c σ' π' c' M hf ha (archimedeanRepresentation σ π c g w) =
      archimedeanRepresentation σ' π' c' g (map σ π c σ' π' c' M hf ha w) := by
  apply Subtype.ext
  apply Subtype.ext
  exact ha g w.val.val

/-- Pullback along a bounded intertwiner preserves derivative continuity
at every compact open level. -/
theorem isContinuousAtEachLevel_comp
    (P : W' →ₗ[ℂ] ℂ) (hP : IsContinuousAtEachLevel σ' π' c' P) :
    IsContinuousAtEachLevel σ π c (P.comp (map σ π c σ' π' c' M hf ha).toLinearMap) := by
  intro J
  obtain ⟨f, hfc, hfJ⟩ := hP J
  refine ⟨f.comp (SmoothIntertwiner.map I π π' M ha),
    SmoothIntertwiner.isContinuousOnSmoothVectors_comp I π π' M ha f hfc, ?_⟩
  intro w hw
  exact hfJ (map σ π c σ' π' c' M hf ha w) (map_fixed σ π c σ' π' c' M hf ha J.toSubgroup w hw)

end Langlands.Archimedean.MixedSmooth
