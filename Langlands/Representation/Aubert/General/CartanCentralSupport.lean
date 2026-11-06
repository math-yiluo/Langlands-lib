import Langlands.Representation.Aubert.General.CartanSupportReduction
import Mathlib.Algebra.Group.Pointwise.Set.Finite

/-! # Compact support from bounded Cartan coordinates in a quotient -/

noncomputable section

open scoped Pointwise

namespace Langlands.Aubert.General

universe uΔ uX uG uQ uE

/-- Equality of root coordinates determines the image of a Cartan parameter.
The parameters themselves may have a nontrivial central kernel. -/
def CartanDetectionModulo {Δ : Type uΔ} {X : Type uX} {Q : Type uQ}
    (pair : Δ → X → ℤ) (e : X → Q) : Prop :=
  ∀ x y, (∀ β, pair β x = pair β y) → e x = e y

/-- A bounded integral root box has finite image when root coordinates determine
that image, even if the parameter set itself is infinite. -/
theorem CartanDetectionModulo.finite_bounded_image
    {Δ : Type uΔ} [Finite Δ] {X : Type uX} {Q : Type uQ}
    {pair : Δ → X → ℤ} {e : X → Q}
    (hdet : CartanDetectionModulo pair e) (lo hi : ℤ) :
    (e '' {x : X | ∀ β, lo ≤ pair β x ∧ pair β x ≤ hi}).Finite := by
  let box : Set (Δ → ℤ) := Set.pi Set.univ (fun _ => Set.Icc lo hi)
  have hbox : box.Finite := Set.Finite.pi (fun _ => Set.finite_Icc lo hi)
  let fiber (t : Δ → ℤ) : Set Q := {q | ∃ x, (∀ β, pair β x = t β) ∧ e x = q}
  have hfiber (t : Δ → ℤ) : (fiber t).Finite := by
    apply Set.Subsingleton.finite
    rintro q ⟨x, hx, rfl⟩ r ⟨y, hy, rfl⟩
    exact hdet x y (fun β => (hx β).trans (hy β).symm)
  apply (hbox.biUnion (fun t _ => hfiber t)).subset
  rintro q ⟨x, hx, rfl⟩
  exact Set.mem_iUnion₂.mpr ⟨(fun β => pair β x), (fun β _ => hx β),
    ⟨x, (fun _ => rfl), rfl⟩⟩

/-- A function on a Hausdorff topological group has compact support if all its
nonzero values have Cartan expressions with compact outside factors, finitely
many residual factors, and parameters whose bounded root coordinates determine
their images. The source group need not be Hausdorff. -/
theorem hasCompactSupport_of_bounded_cartan_image
    {Δ : Type uΔ} [Finite Δ] {X : Type uX}
    {G : Type uG} [Group G] [TopologicalSpace G]
    {Q : Type uQ} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [T2Space Q]
    {E : Type uE} [Zero E]
    (q : G →* Q) (hq : Continuous q) (hsurj : Function.Surjective q)
    (K : Set G) (hK : IsCompact K) (F₀ : Set G) (hF₀ : F₀.Finite)
    (e : X → G) (pair : Δ → X → ℤ)
    (hdet : CartanDetectionModulo pair (fun x => q (e x)))
    (lo hi : ℤ) (φ : Q → E)
    (hsupp : ∀ g : G, φ (q g) ≠ 0 →
      ∃ k₁ ∈ K, ∃ f ∈ F₀, ∃ x : X, ∃ k₂ ∈ K,
        (∀ β, lo ≤ pair β x ∧ pair β x ≤ hi) ∧ g = k₁ * f * e x * k₂) :
    HasCompactSupport φ := by
  let D : Set Q := (fun x => q (e x)) '' {x : X | ∀ β, lo ≤ pair β x ∧ pair β x ≤ hi}
  have hD : D.Finite := hdet.finite_bounded_image lo hi
  have hC : IsCompact (((q '' K) * ((q '' F₀) * D)) * (q '' K)) :=
    ((hK.image hq).mul (((hF₀.image q).mul hD).isCompact)).mul (hK.image hq)
  apply HasCompactSupport.of_support_subset_isCompact hC
  intro z hz
  obtain ⟨g, rfl⟩ := hsurj z
  obtain ⟨k₁, hk₁, f, hf, x, k₂, hk₂, hx, rfl⟩ := hsupp g hz
  refine ⟨q k₁ * (q f * q (e x)), ?_, q k₂, ⟨k₂, hk₂, rfl⟩, ?_⟩
  · exact ⟨q k₁, ⟨k₁, hk₁, rfl⟩, q f * q (e x),
      ⟨q f, ⟨f, hf, rfl⟩, q (e x), ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
  · simp only [map_mul, mul_assoc]

end Langlands.Aubert.General
