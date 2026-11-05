import Mathlib.Data.Int.Interval
import Mathlib.Data.Set.Finite.Powerset
import Mathlib.Topology.Algebra.Group.Pointwise
import Mathlib.Topology.Algebra.Support

/-! # Compact support from bounded Cartan parameters in a valuation kernel -/

noncomputable section

open scoped Pointwise

namespace Langlands.Aubert.General

universe uΔ uX uG uQ uE

/-- The integral root coordinates and the ambient valuation together distinguish
Cartan parameters. Root coordinates alone may have a nontrivial central kernel. -/
def JointCartanDetection {Δ : Type uΔ} {X : Type uX} {Q : Type uQ}
    (pair : Δ → X → ℤ) (val : X → Q) : Prop :=
  Function.Injective (fun x => ((fun β => pair β x), val x))

/-- A bounded box of integral root coordinates meets a fixed valuation fiber in
finitely many parameters, provided these coordinates jointly distinguish them. -/
theorem JointCartanDetection.finite_bounded_fiber
    {Δ : Type uΔ} [Finite Δ] {X : Type uX} {Q : Type uQ}
    {pair : Δ → X → ℤ} {val : X → Q}
    (hdet : JointCartanDetection pair val) (lo hi : ℤ) (q : Q) :
    {x : X | (∀ β, lo ≤ pair β x ∧ pair β x ≤ hi) ∧ val x = q}.Finite := by
  let box : Set (Δ → ℤ) := Set.pi Set.univ (fun _ => Set.Icc lo hi)
  have hbox : box.Finite := Set.Finite.pi (fun _ => Set.finite_Icc lo hi)
  have hpre := Set.Finite.preimage hdet.injOn (hbox.prod (Set.finite_singleton q))
  exact hpre.subset fun x hx => ⟨fun β _ => hx.1 β, hx.2⟩

/-- If the nonzero values in a closed valuation kernel admit Cartan expressions
with bounded root coordinates, their support is compact. The compact subgroup is
contained in the valuation kernel, and the residual set is finite. -/
theorem hasCompactSupport_of_bounded_cartan_parameters
    {Δ : Type uΔ} [Finite Δ] {X : Type uX}
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    {Q : Type uQ} [Group Q] {E : Type uE} [Zero E]
    (q : G →* Q) (K : Subgroup G) (hK : IsCompact (K : Set G))
    (hKq : K ≤ q.ker) (hq : IsClosed (q.ker : Set G))
    (e : X → G) (pair : Δ → X → ℤ)
    (hdet : JointCartanDetection pair (fun x => q (e x)))
    (F₀ : Set G) (hF₀ : F₀.Finite) (lo hi : ℤ) (φ : q.ker → E)
    (hsupp : ∀ g : q.ker, φ g ≠ 0 →
      ∃ k₁ ∈ K, ∃ f ∈ F₀, ∃ x : X, ∃ k₂ ∈ K,
        (∀ β, lo ≤ pair β x ∧ pair β x ≤ hi) ∧
          (g : G) = k₁ * f * e x * k₂) :
    HasCompactSupport φ := by
  let R (f : G) : Set X :=
    {x | (∀ β, lo ≤ pair β x ∧ pair β x ≤ hi) ∧ q (e x) = (q f)⁻¹}
  let D : Set G := ⋃ f ∈ F₀, (fun x => f * e x) '' R f
  have hD : D.Finite := hF₀.biUnion fun f _ =>
    (hdet.finite_bounded_fiber lo hi ((q f)⁻¹)).image (fun x => f * e x)
  have hC : IsCompact (((K : Set G) * D) * (K : Set G)) := (hK.mul hD.isCompact).mul hK
  have hC' : IsCompact ((Subtype.val : q.ker → G) ⁻¹' (((K : Set G) * D) * (K : Set G))) :=
    hq.isClosedEmbedding_subtypeVal.isCompact_preimage hC
  apply HasCompactSupport.of_support_subset_isCompact hC'
  intro g hg
  obtain ⟨k₁, hk₁, f, hf, x, k₂, hk₂, hx, hgexpr⟩ := hsupp g hg
  have hk₁q : q k₁ = 1 := hKq hk₁
  have hk₂q : q k₂ = 1 := hKq hk₂
  have hgq : q (g : G) = 1 := g.property
  have hfx : q f * q (e x) = 1 := by
    simpa only [hgexpr, map_mul, hk₁q, hk₂q, one_mul, mul_one] using hgq
  have hxR : x ∈ R f := ⟨hx, eq_inv_of_mul_eq_one_right hfx⟩
  have hxD : f * e x ∈ D :=
    Set.mem_iUnion₂.mpr ⟨f, hf, ⟨x, hxR, rfl⟩⟩
  exact ⟨k₁ * (f * e x), ⟨k₁, hk₁, f * e x, hxD, rfl⟩,
    k₂, hk₂, by simpa only [mul_assoc] using hgexpr.symm⟩

end Langlands.Aubert.General
