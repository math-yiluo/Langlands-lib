import Langlands.AlgebraicGeometry.Modules.ClosedStalkSupport
import Langlands.AlgebraicGeometry.Modules.ClosedPushforwardSupport
import Langlands.AlgebraicGeometry.Modules.SectionLocusComparison
import Mathlib.Topology.Irreducible

/-! # Dimension of actual closed stalk support -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Topology Order
open Langlands.SchemeModule

namespace Langlands.AlgebraicGeometry.Modules

variable {X Y : Scheme.{u}}

/-- Topological Krull dimension of the closure of the nonzero-stalk locus. -/
def supportDimension (M : X.Modules) : WithBot ℕ∞ :=
  topologicalKrullDim (closedStalkSupport M : Set X)

/-- The closed support bound is precisely the natural strict dimension bound. -/
theorem hasSupportDimensionLT_iff_supportDimension (M : X.Modules) (e : ℕ) :
    HasSupportDimensionLT M e ↔ supportDimension M < (e : WithBot ℕ∞) :=
  hasSupportDimensionLT_iff_topologicalKrullDim_closedStalkSupport M e

/-- Isomorphic modules have the same support dimension. -/
theorem supportDimension_eq_of_iso {M N : X.Modules} (i : M ≅ N) :
    supportDimension M = supportDimension N := by
  unfold supportDimension
  rw [closedStalkSupport_eq_of_iso i]

/-- The closed support of a closed pushforward is the image of the original closed support. -/
theorem coe_closedStalkSupport_pushforward (f : X ⟶ Y) (hf : IsClosedEmbedding f)
    (M : X.Modules) :
    (closedStalkSupport ((Scheme.Modules.pushforward f).obj M) : Set Y) =
      f '' (closedStalkSupport M : Set X) := by
  simp only [coe_closedStalkSupport, stalkSupport_pushforward f hf M, hf.closure_image_eq]

/-- A closed pushforward preserves the topological dimension of closed stalk support. -/
theorem topologicalKrullDim_closedStalkSupport_pushforward
    (f : X ⟶ Y) (hf : IsClosedEmbedding f) (M : X.Modules) :
    topologicalKrullDim (closedStalkSupport ((Scheme.Modules.pushforward f).obj M) : Set Y) =
      topologicalKrullDim (closedStalkSupport M : Set X) := by
  rw [coe_closedStalkSupport_pushforward f hf M]
  let e := hf.isEmbedding.homeomorphImage (closedStalkSupport M : Set X)
  exact (IsHomeomorph.topologicalKrullDim_eq e e.isHomeomorph).symm

/-- Closed pushforward preserves and reflects every actual support-dimension bound. -/
theorem hasSupportDimensionLT_pushforward_iff
    (f : X ⟶ Y) (hf : IsClosedEmbedding f) (M : X.Modules) (e : ℕ) :
    HasSupportDimensionLT ((Scheme.Modules.pushforward f).obj M) e ↔
      HasSupportDimensionLT M e := by
  simp only [hasSupportDimensionLT_iff_topologicalKrullDim_closedStalkSupport,
    topologicalKrullDim_closedStalkSupport_pushforward f hf M]


/-- The support-height bound holds for a short exact middle term precisely
when it holds for both outer terms. -/
theorem hasSupportDimensionLT_shortExact_iff
    (S : ShortComplex X.Modules) (hS : S.ShortExact) (e : ℕ) :
    HasSupportDimensionLT S.X₂ e ↔
      HasSupportDimensionLT S.X₁ e ∧ HasSupportDimensionLT S.X₃ e := by
  simp only [hasSupportDimensionLT_iff_closedStalkSupport]
  rw [closedStalkSupport_shortExact S hS]
  constructor
  · intro h
    exact ⟨fun T hT => h T (hT.trans (show
        (closedStalkSupport S.X₁ : Set X) ⊆
          (closedStalkSupport S.X₁ ⊔ closedStalkSupport S.X₃ : Closeds X) from
            Set.subset_union_left)),
      fun T hT => h T (hT.trans (show
        (closedStalkSupport S.X₃ : Set X) ⊆
          (closedStalkSupport S.X₁ ⊔ closedStalkSupport S.X₃ : Closeds X) from
            Set.subset_union_right))⟩
  · rintro ⟨h₁, h₃⟩ T hT
    obtain h | h := isPreirreducible_iff_isClosed_union_isClosed.mp
      T.isIrreducible.isPreirreducible _ _
      (closedStalkSupport S.X₁).isClosed (closedStalkSupport S.X₃).isClosed hT
    · exact h₁ T h
    · exact h₃ T h

/-- The actual structure module has a nonzero abelian stalk at every point. -/
theorem stalkSupport_structureModule (X : Scheme.{u}) :
    stalkSupport (structureModule X) = Set.univ := by
  ext x
  simp only [Set.mem_univ, iff_true, mem_stalkSupport,
    AddCommGrpCat.isZero_iff_subsingleton]
  intro h
  have he : (structureModule X).presheaf.germ ⊤ x trivial (1 : Γ(X, ⊤)) =
      (structureModule X).presheaf.germ ⊤ x trivial (0 : Γ(X, ⊤)) :=
    @Subsingleton.elim _ h _ _
  obtain ⟨W, hxW, i₁, i₀, heq⟩ :=
    (structureModule X).presheaf.germ_eq (U := ⊤) (V := ⊤) x trivial trivial _ _ he
  change X.presheaf.map i₁.op (1 : Γ(X, ⊤)) =
    X.presheaf.map i₀.op (0 : Γ(X, ⊤)) at heq
  have heq' : (1 : Γ(X, W)) = 0 := by simpa only [map_one, map_zero] using heq
  have hscalar := congrArg (X.presheaf.germ W x hxW) heq'
  exact one_ne_zero (by simpa only [map_one, map_zero] using hscalar)

/-- The structure module has full closed support. -/
theorem closedStalkSupport_structureModule (X : Scheme.{u}) :
    closedStalkSupport (structureModule X) = ⊤ := by
  apply Closeds.ext
  simp [stalkSupport_structureModule]

/-- The dimension of the structure module is the scheme's topological dimension. -/
theorem supportDimension_structureModule (X : Scheme.{u}) :
    supportDimension (structureModule X) = topologicalKrullDim X := by
  unfold supportDimension
  rw [closedStalkSupport_structureModule]
  exact (IsHomeomorph.topologicalKrullDim_eq
    (Homeomorph.Set.univ X) (Homeomorph.Set.univ X).isHomeomorph)

/-- Restricting to an open does not change the support at its points. -/
theorem mem_stalkSupport_restrict_iff (M : X.Modules) (U : X.Opens) (x : U.toScheme) :
    x ∈ stalkSupport (M.restrict U.ι) ↔ U.ι x ∈ stalkSupport M :=
  not_congr ((Scheme.Modules.restrictStalkNatIso U.ι x).app M).isZero_iff

/-- A module that agrees with the structure module on a nonempty open of
an irreducible scheme has full closed support. -/
theorem closedStalkSupport_eq_top_of_restrict_iso [IrreducibleSpace X]
    (M : X.Modules) (U : X.Opens) (hU : (U : Set X).Nonempty)
    (i : M.restrict U.ι ≅ structureModule U.toScheme) :
    closedStalkSupport M = ⊤ := by
  have hUM : (U : Set X) ⊆ stalkSupport M := by
    intro x hx
    apply (mem_stalkSupport_restrict_iff M U ⟨x, hx⟩).mp
    rw [stalkSupport_eq_of_iso i, stalkSupport_structureModule]
    trivial
  apply top_unique
  intro x _
  have hcl : closure (U : Set X) = Set.univ := (U.isOpen.dense hU).closure_eq
  exact closure_mono hUM (hcl.symm ▸ Set.mem_univ x)

/-- Tensoring with a line bundle preserves closed stalk support. -/
theorem closedStalkSupport_tensor_lineBundle (M N : X.Modules)
    (hN : Picard.IsLocallyFreeRankOne N) :
    closedStalkSupport (Langlands.Scheme.Modules.tensorObj M N) = closedStalkSupport M := by
  apply Closeds.ext
  simp only [coe_closedStalkSupport, stalkSupport_tensor_lineBundle M N hN]

/-- Tensoring with a line bundle preserves the actual support dimension. -/
theorem supportDimension_tensor_lineBundle (M N : X.Modules)
    (hN : Picard.IsLocallyFreeRankOne N) :
    supportDimension (Langlands.Scheme.Modules.tensorObj M N) = supportDimension M := by
  unfold supportDimension
  rw [closedStalkSupport_tensor_lineBundle M N hN]

end Langlands.AlgebraicGeometry.Modules
