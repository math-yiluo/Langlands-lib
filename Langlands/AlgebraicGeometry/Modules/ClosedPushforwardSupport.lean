import Langlands.AlgebraicGeometry.Modules.CoherentGraph
import Langlands.AlgebraicGeometry.Modules.PushforwardInjectiveAcyclicProof
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Support under closed pushforward -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology

namespace Langlands.AlgebraicGeometry.Modules

variable {X Y : Scheme.{u}}

/-- The underlying abelian stalk of a pushforward along an inducing map
is the original stalk at each image point. -/
def pushforwardStalkIso (f : X ⟶ Y) (hf : IsInducing f) (M : X.Modules) (x : X) :
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (f x)).obj
      ((Scheme.Modules.pushforward f).obj M).presheaf ≅
    (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).obj M.presheaf := by
  have h : IsIso (M.presheaf.stalkPushforward AddCommGrpCat.{u} f.base x) :=
    TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing
      AddCommGrpCat.{u} hf M.presheaf x
  exact @asIso _ _ _ _ (M.presheaf.stalkPushforward AddCommGrpCat.{u} f.base x) h

/-- Nonzero stalks agree at image points of an inducing scheme morphism. -/
theorem mem_stalkSupport_pushforward_iff (f : X ⟶ Y) (hf : IsInducing f)
    (M : X.Modules) (x : X) :
    f x ∈ stalkSupport ((Scheme.Modules.pushforward f).obj M) ↔ x ∈ stalkSupport M :=
  not_congr (pushforwardStalkIso f hf M x).isZero_iff

/-- Pushforward vanishes on the complement of a closed image. -/
theorem vanishesOn_pushforward_compl_range (f : X ⟶ Y) (hf : IsClosedEmbedding f)
    (M : X.Modules) :
    QuasicoherentLocal.VanishesOn ((Scheme.Modules.pushforward f).obj M)
      ⟨(Set.range f)ᶜ, hf.isClosed_range.isOpen_compl⟩ := by
  intro W hW s
  have hpre : f ⁻¹ᵁ W = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    exact (hW hx) ⟨x, rfl⟩
  exact @Subsingleton.elim _
    (ClosedImmersionHigherDirectImageVanishing.subsingleton_sections_of_eq_bot M hpre) s 0

/-- For a closed embedding, pushforward support is the image of actual stalk support. -/
theorem stalkSupport_pushforward (f : X ⟶ Y) (hf : IsClosedEmbedding f) (M : X.Modules) :
    stalkSupport ((Scheme.Modules.pushforward f).obj M) = f '' stalkSupport M := by
  ext y
  constructor
  · intro hy
    have hyr : y ∈ Set.range f := by
      have := (vanishesOn_pushforward_compl_range f hf M).stalkSupport_subset_compl hy
      simpa using this
    obtain ⟨x, rfl⟩ := hyr
    exact ⟨x, (mem_stalkSupport_pushforward_iff f hf.isInducing M x).mp hy, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact (mem_stalkSupport_pushforward_iff f hf.isInducing M x).mpr hx

end Langlands.AlgebraicGeometry.Modules
