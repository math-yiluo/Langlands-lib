import Langlands.Representation.Jacquet.IwahoriContractionRemarks
import Langlands.Representation.Jacquet.CanonicalLiftIntertwinerNaturalityProof
import Langlands.Representation.Category.Basic

/-! # Renard VI.9.1: the bound `b ≤ c(G, K)` from separation by irreducibles -/

noncomputable section

open CategoryTheory

namespace Langlands.Jacquet

universe uG uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- Irreducible smooth representations separate natural endomorphisms of the `K`-fixed
vectors: a family of linear endomorphisms of the `K`-fixed vectors of all smooth complex
representations with carriers in `Type uV`, natural for intertwiners, vanishes as soon as
it vanishes on every irreducible one. -/
def FixedVectorsSeparatedByIrreducibles (K : Subgroup G) : Prop :=
  ∀ T : ∀ A : SmoothRep.{0, uG, uV} ℂ G, Module.End ℂ (fixedVectors A.representation K),
    (∀ (A B : SmoothRep.{0, uG, uV} ℂ G) (f : A ⟶ B) (v : fixedVectors A.representation K),
      fixedVectorsMap (SmoothRep.hom f) K (T A v) = T B (fixedVectorsMap (SmoothRep.hom f) K v)) →
    (∀ A : SmoothRep.{0, uG, uV} ℂ G, A.IsIrreducible → T A = 0) →
    ∀ A : SmoothRep.{0, uG, uV} ℂ G, T A = 0

variable [IsTopologicalGroup G]

section Bound

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- On a finite-dimensional space of dimension at most `c`, the `c`-th power of an
endomorphism kills every vector killed by some power. -/
theorem pow_apply_eq_zero_of_finrank_le {E : Type*} [AddCommGroup E] [Module ℂ E]
    [FiniteDimensional ℂ E] (t : Module.End ℂ E) (c : ℕ) (hc : Module.finrank ℂ E ≤ c)
    (v : E) (hv : v ∈ ⨆ r : ℕ, LinearMap.ker (t ^ r)) : (t ^ c) v = 0 := by
  have hle : (⨆ r : ℕ, LinearMap.ker (t ^ r)) ≤ LinearMap.ker (t ^ c) := by
    refine iSup_le fun r => ?_
    rw [Module.End.ker_pow_eq_ker_pow_finrank_of_le hc]
    exact Module.End.ker_pow_le_ker_pow_finrank t r
  exact hle hv

/-- Intertwiners map the kernel supremum into the kernel supremum. -/
theorem fixedVectorsMap_mem_powerKernelSup
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (hρ : IsSmooth ρ) (hσ : IsSmooth σ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (g : G) (f : ρ.IntertwiningMap σ)
    (v : fixedVectors ρ K.toSubgroup) (hv : v ∈ powerKernelSup ρ hρ K hK g) :
    fixedVectorsMap f K.toSubgroup v ∈ powerKernelSup σ hσ K hK g := by
  have hle : powerKernelSup ρ hρ K hK g ≤
      (powerKernelSup σ hσ K hK g).comap (fixedVectorsMap f K.toSubgroup) := by
    refine iSup_le fun r w hw => ?_
    rw [Submodule.mem_comap]
    refine Submodule.mem_iSup_of_mem r ?_
    rw [LinearMap.mem_ker, ← compressedAction_pow_natural ρ σ hρ hσ K hK g f r w,
      LinearMap.mem_ker.mp hw, map_zero]
  exact hle hv

/-- The projection onto the kernel supremum along the stable image commutes with
intertwiners, when both compressions split. -/
theorem fixedVectorsMap_projection
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (hρ : IsSmooth ρ) (hσ : IsSmooth σ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (g : G) (f : ρ.IntertwiningMap σ)
    (hV : CompactCompressionSplits ρ hρ K hK g) (hW : CompactCompressionSplits σ hσ K hK g)
    (v : fixedVectors ρ K.toSubgroup) :
    fixedVectorsMap f K.toSubgroup (Submodule.projection _ _ hV v) =
      Submodule.projection _ _ hW (fixedVectorsMap f K.toSubgroup v) := by
  set p := Submodule.projection _ _ hV v
  have hp : p ∈ powerKernelSup ρ hρ K hK g := Submodule.projection_apply_mem hV v
  have hq : v - p ∈ stableImage ρ hρ K hK g := Submodule.sub_projection_mem hV v
  have hfp := fixedVectorsMap_mem_powerKernelSup ρ σ hρ hσ K hK g f p hp
  have hfq := fixedVectorsMap_mem_stableImage ρ σ hρ hσ K hK g f (v - p) hq
  have hv : v = p + (v - p) := by abel
  conv_rhs => rw [hv, map_add, map_add, Submodule.projection_apply_of_mem_left hW hfp,
    Submodule.projection_apply_of_mem_right hW hfq, add_zero]

/-- Renard VI.9.1, the bound `b ≤ c(G, K)`, for an abstract compressed action: if
irreducible smooth representations separate natural endomorphisms of `K`-fixed vectors,
the compressions of `g` stabilize from a uniform exponent on and split, and `c` bounds
the dimension of the `K`-fixed vectors of every irreducible smooth representation, then
every power of exponent at least `c` has range the stable image and kernel the kernel
supremum. -/
theorem stabilization_bound_of_separation (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (g : G) (hsep : FixedVectorsSeparatedByIrreducibles.{uG, uV} K.toSubgroup)
    (hsplit : ∀ (W : Type uV) [AddCommGroup W] [Module ℂ W]
      (σ : Representation ℂ G W) (hσ : IsSmooth σ), CompactCompressionSplits σ hσ K hK g)
    (c : ℕ) (hc : ∀ A : SmoothRep.{0, uG, uV} ℂ G, A.IsIrreducible →
      Module.rank ℂ (fixedVectors A.representation K.toSubgroup) ≤ c)
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ) :
    ∀ s : ℕ, c ≤ s →
      stableImage ρ hρ K hK g = LinearMap.range (compressedAction ρ hρ K hK g ^ s) ∧
        powerKernelSup ρ hρ K hK g = LinearMap.ker (compressedAction ρ hρ K hK g ^ s) := by
  let T : ∀ A : SmoothRep.{0, uG, uV} ℂ G,
      Module.End ℂ (fixedVectors A.representation K.toSubgroup) := fun A =>
    (compressedAction A.representation A.isSmooth K hK g ^ c) ∘ₗ
      Submodule.projection _ _ (hsplit A A.representation A.isSmooth)
  have hnat : ∀ (A B : SmoothRep.{0, uG, uV} ℂ G) (f : A ⟶ B)
      (v : fixedVectors A.representation K.toSubgroup),
      fixedVectorsMap (SmoothRep.hom f) K.toSubgroup (T A v) =
        T B (fixedVectorsMap (SmoothRep.hom f) K.toSubgroup v) := by
    intro A B f v
    simp only [T, LinearMap.comp_apply]
    rw [compressedAction_pow_natural A.representation B.representation A.isSmooth B.isSmooth
      K hK g (SmoothRep.hom f) c, fixedVectorsMap_projection A.representation B.representation
      A.isSmooth B.isSmooth K hK g (SmoothRep.hom f)]
  have hirr : ∀ A : SmoothRep.{0, uG, uV} ℂ G, A.IsIrreducible → T A = 0 := by
    intro A hA
    have hr := hc A hA
    have hfin : FiniteDimensional ℂ (fixedVectors A.representation K.toSubgroup) :=
      Module.rank_lt_aleph0_iff.mp (hr.trans_lt (Cardinal.natCast_lt_aleph0))
    refine LinearMap.ext fun v => ?_
    simp only [T, LinearMap.comp_apply, LinearMap.zero_apply]
    exact pow_apply_eq_zero_of_finrank_le _ c (Module.finrank_le_of_rank_le hr) _
      (Submodule.projection_apply_mem _ v)
  have hzero := hsep T hnat hirr (SmoothRep.of ρ hρ)
  refine stabilization_of_pow_kill ρ hρ K hK g (hsplit V ρ hρ) c fun v hv => ?_
  have h := LinearMap.congr_fun hzero v
  simp only [T, LinearMap.comp_apply, LinearMap.zero_apply] at h
  calc (compressedAction ρ hρ K hK g ^ c) v =
        (compressedAction ρ hρ K hK g ^ c) (Submodule.projection _ _ (hsplit V ρ hρ) v) := by
          rw [Submodule.projection_apply_of_mem_left (hsplit V ρ hρ) hv]
    _ = 0 := h

end Bound

end Langlands.Jacquet
