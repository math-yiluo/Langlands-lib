import Langlands.Group.TitsSystemBruhat

/-!
# Bruhat bijectivity across components

An internal algebraic form of the corrected KP Theorem 7.8.1(2) argument.
The Tits system lives in the kernel of the component homomorphism. Representatives
of every component normalize its Borel subgroup.
-/

noncomputable section

namespace Langlands.Group.TitsSystem

universe u v w

variable {G : Type u} [Group G] {W : Type v} [Group W] {Γ : Type w} [Group Γ]
  {B N : Subgroup G} (π : N →* W) (q : G →* Γ) (c : W →* Γ)
  (hcompat : ∀ n : N, c (π n) = q (n : G))

/-- Restriction of a compatible normalizer projection to the component kernels. -/
def kernelProjection : N.subgroupOf q.ker →* c.ker where
  toFun n := ⟨π ⟨((n : q.ker) : G), n.property⟩, by
    rw [MonoidHom.mem_ker, hcompat]
    exact (n : q.ker).property⟩
  map_one' := Subtype.ext (map_one π)
  map_mul' a b := by
    apply Subtype.ext
    change π (⟨((a : q.ker) : G), a.property⟩ *
      ⟨((b : q.ker) : G), b.property⟩) =
        π ⟨((a : q.ker) : G), a.property⟩ *
          π ⟨((b : q.ker) : G), b.property⟩
    exact map_mul π _ _

variable {π q c hcompat}
  (hB : B ≤ q.ker) {S : Set c.ker}
  (h : IsTitsSystem (B.subgroupOf q.ker) (N.subgroupOf q.ker)
    (kernelProjection (π := π) (q := q) (c := c) (hcompat := hcompat)) S)

include h

theorem mem_of_projection_eq_one (n : N) (hn : π n = 1) : (n : G) ∈ B := by
  have hnq : (n : G) ∈ q.ker := by
    rw [MonoidHom.mem_ker, ← hcompat n, hn, map_one]
  let n₀ : N.subgroupOf q.ker := ⟨⟨(n : G), hnq⟩, n.property⟩
  have hn₀ : kernelProjection (π := π) (q := q) (c := c) (hcompat := hcompat) n₀ = 1 := Subtype.ext hn
  exact (h.mem_iff n₀).2 hn₀

include hB

omit hB in
theorem doubleCoset_eq_of_projection_eq (n m : N) (hnm : π n = π m) :
    DoubleCoset.mk B B (n : G) = DoubleCoset.mk B B (m : G) := by
  have hk : ((n⁻¹ * m : N) : G) ∈ B :=
    mem_of_projection_eq_one h (n⁻¹ * m) (by simp [hnm])
  exact DoubleCoset.eq.2 ⟨1, B.one_mem, (n⁻¹ * m : N), hk, by simp⟩

variable
  (hreps : ∀ γ : Γ, ∃ r : N, q (r : G) = γ ∧ (r : G) ∈ Subgroup.normalizer (B : Set G))

include hreps

/-- Removing a common normalizing component representative reduces injectivity to
Bruhat uniqueness in the component kernel. -/
theorem projection_eq_of_doubleCoset_eq (n m : N)
    (hnm : DoubleCoset.mk B B (n : G) = DoubleCoset.mk B B (m : G)) :
    π n = π m := by
  obtain ⟨b₁, hb₁, b₂, hb₂, hm⟩ := DoubleCoset.eq.1 hnm
  have hq : q (m : G) = q (n : G) := by
    rw [hm, map_mul, map_mul, (hB hb₁ : q b₁ = 1), (hB hb₂ : q b₂ = 1)]
    simp
  obtain ⟨r, hr, hrB⟩ := hreps (q (n : G))
  have hnq : ((n * r⁻¹ : N) : G) ∈ q.ker := by
    change q ((n : G) * (r : G)⁻¹) = 1
    simp [hr]
  have hmq : ((m * r⁻¹ : N) : G) ∈ q.ker := by
    change q ((m : G) * (r : G)⁻¹) = 1
    simp [hr, hq]
  let n₀ : N.subgroupOf q.ker := ⟨⟨((n * r⁻¹ : N) : G), hnq⟩, (n * r⁻¹).property⟩
  let m₀ : N.subgroupOf q.ker := ⟨⟨((m * r⁻¹ : N) : G), hmq⟩, (m * r⁻¹).property⟩
  have hb₂' : (r : G) * b₂ * (r : G)⁻¹ ∈ B :=
    (Subgroup.mem_normalizer_iff.1 hrB b₂).1 hb₂
  let a : B.subgroupOf q.ker := ⟨⟨b₁, hB hb₁⟩, hb₁⟩
  let b : B.subgroupOf q.ker :=
    ⟨⟨(r : G) * b₂ * (r : G)⁻¹, hB hb₂'⟩, hb₂'⟩
  have hm₀ : (m₀ : q.ker) = (a : q.ker) * (n₀ : q.ker) * (b : q.ker) := by
    apply Subtype.ext
    change (m : G) * (r : G)⁻¹ =
      b₁ * ((n : G) * (r : G)⁻¹) * ((r : G) * b₂ * (r : G)⁻¹)
    simp [hm, mul_assoc]
  have hc : (m₀ : q.ker) ∈ cell (B.subgroupOf q.ker)
      (kernelProjection (π := π) (q := q) (c := c) (hcompat := hcompat)) (kernelProjection (π := π) (q := q) (c := c) (hcompat := hcompat) n₀) := by
    rw [hm₀]
    exact mul_mem_cell_right (mul_mem_cell_left (coe_mem_cell n₀) a.property) b.property
  have heq := congrArg Subtype.val (h.eq_of_mem_cell hc (coe_mem_cell m₀))
  change π (n * r⁻¹) = π (m * r⁻¹) at heq
  simp only [map_mul, map_inv] at heq
  exact mul_right_cancel heq

omit hB in
/-- Every full-group double coset has a normalizer representative, using Bruhat
existence in the kernel and a normalizing representative of its component. -/
theorem exists_doubleCoset_rep (g : G) :
    ∃ n : N, DoubleCoset.mk B B (n : G) = DoubleCoset.mk B B g := by
  obtain ⟨r, hr, hrB⟩ := hreps (q g)
  have hgq : g * (r : G)⁻¹ ∈ q.ker := by
    change q (g * (r : G)⁻¹) = 1
    simp [hr]
  obtain ⟨w, n₀, hn₀, a, ha, b, hb, heq⟩ := h.exists_mem_cell ⟨g * (r : G)⁻¹, hgq⟩
  let n : N := ⟨((n₀ : q.ker) : G), n₀.property⟩
  have hb' : (r : G)⁻¹ * (b : G) * (r : G) ∈ B :=
    by simpa only [inv_inv] using
      (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer (B : Set G)).inv_mem hrB) (b : G)).1 hb
  refine ⟨n * r, DoubleCoset.eq.2 ⟨a, ha, (r : G)⁻¹ * (b : G) * (r : G), hb', ?_⟩⟩
  have heqG := congrArg Subtype.val heq
  change g * (r : G)⁻¹ = (a : G) * (n : G) * (b : G) at heqG
  calc
    g = (g * (r : G)⁻¹) * (r : G) := by simp [mul_assoc]
    _ = (a : G) * ((n * r : N) : G) *
        ((r : G)⁻¹ * (b : G) * (r : G)) := by rw [heqG]; simp [mul_assoc]

/-- The full normalizer projection indexes the full-group Borel double cosets.
The conclusion specifies every normalizer representative. -/
theorem exists_component_doubleCoset_equiv (hπ : Function.Surjective π) :
    ∃ e : W ≃ DoubleCoset.Quotient (B : Set G) B,
      ∀ n : N, e (π n) = DoubleCoset.mk B B (n : G) := by
  let rep : W → N := Function.surjInv hπ
  have hrep : ∀ w, π (rep w) = w := Function.surjInv_eq hπ
  let f : W → DoubleCoset.Quotient (B : Set G) B :=
    fun w => DoubleCoset.mk B B (rep w : G)
  have hf : ∀ n : N, f (π n) = DoubleCoset.mk B B (n : G) := by
    intro n
    exact doubleCoset_eq_of_projection_eq h _ _ (hrep (π n))
  refine ⟨Equiv.ofBijective f ⟨?_, ?_⟩, hf⟩
  · intro a b hab
    have heq := projection_eq_of_doubleCoset_eq hB h hreps (rep a) (rep b) hab
    simpa [hrep] using heq
  · intro z
    induction z using Quotient.inductionOn with
    | h g =>
      obtain ⟨n, hn⟩ := exists_doubleCoset_rep h hreps g
      exact ⟨π n, (hf n).trans hn⟩

/-- A chosen component Bruhat equivalence; its value is specified on every
normalizer representative by `componentDoubleCosetEquiv_apply`. -/
def componentDoubleCosetEquiv (hπ : Function.Surjective π) :
    W ≃ DoubleCoset.Quotient (B : Set G) B :=
  Classical.choose (exists_component_doubleCoset_equiv hB h hreps hπ)

/-- The component Bruhat equivalence sends every normalizer image to its actual
full-group double coset. -/
theorem componentDoubleCosetEquiv_apply (hπ : Function.Surjective π) (n : N) :
    componentDoubleCosetEquiv hB h hreps hπ (π n) =
      DoubleCoset.mk B B (n : G) :=
  Classical.choose_spec (exists_component_doubleCoset_equiv hB h hreps hπ) n

end Langlands.Group.TitsSystem
