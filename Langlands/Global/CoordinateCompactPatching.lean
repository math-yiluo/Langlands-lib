import Langlands.Global.CoordinateCompactAssembly

/-! # Repairing an almost-everywhere local compact family -/

noncomputable section

universe u v w x y

open scoped Pointwise
open Filter

namespace Langlands.Global.CoordinateCompactPatching

section Patching

variable {I : Type u} {D : I → Type v}

/-- Keep the original member when it has the desired property, and otherwise
choose a member from the supplied local existence hypothesis. -/
def patchFamily (good : ∀ i, D i → Prop) (hex : ∀ i, ∃ d, good i d)
    (d₀ : ∀ i, D i) : ∀ i, D i := by
  classical
  exact fun i => if good i (d₀ i) then d₀ i else Classical.choose (hex i)

theorem good_patchFamily (good : ∀ i, D i → Prop) (hex : ∀ i, ∃ d, good i d)
    (d₀ : ∀ i, D i) (i : I) :
    good i (patchFamily good hex d₀ i) := by
  classical
  by_cases hi : good i (d₀ i)
  · simpa only [patchFamily, ite_eq_left hi] using hi
  · simpa only [patchFamily, ite_eq_right hi] using Classical.choose_spec (hex i)

theorem patchFamily_eq_of_good (good : ∀ i, D i → Prop)
    (hex : ∀ i, ∃ d, good i d) (d₀ : ∀ i, D i) (i : I)
    (hi : good i (d₀ i)) :
    patchFamily good hex d₀ i = d₀ i := by
  classical
  simp only [patchFamily, ite_eq_left hi]

/-- The repair changes the family only on the original exceptional set.
The statement also applies to filters other than the cofinite filter. -/
theorem patchFamily_eventually_eq (good : ∀ i, D i → Prop)
    (hex : ∀ i, ∃ d, good i d) (d₀ : ∀ i, D i) {l : Filter I}
    (hgood : ∀ᶠ i in l, good i (d₀ i)) :
    ∀ᶠ i in l, patchFamily good hex d₀ i = d₀ i :=
  hgood.mono fun i hi => patchFamily_eq_of_good good hex d₀ i hi

end Patching

section Assembly

variable {I : Type u} {A : Type v} [Group A] [TopologicalSpace A]
  {H : I → Type w} [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)]
  {B : Type x} [Group B] {Q : I → Type y} [∀ i, Group (Q i)]

/-- Compactness, unrestricted maximality, and source-left covering in a
single local group. No existence assertion is part of this predicate. -/
def IsLocalIwasawaCompact {H₀ : Type w} [Group H₀] [TopologicalSpace H₀]
    {Q₀ : Type y} [Group Q₀] (φ : Q₀ →* H₀) (K : Subgroup H₀) : Prop :=
  (IsCompact (K : Set H₀) ∧
    ∀ L : Subgroup H₀, IsCompact (L : Set H₀) → K ≤ L → L = K) ∧
    Set.range φ * (K : Set H₀) = Set.univ

/-- Conditional local-to-global assembly after replacing finitely many
members of an almost-everywhere good local family.

The full local existence, coordinate maps, continuous lifts, and finite-support
source lifting are explicit assumptions. -/
theorem exists_compact_maximal_cover_of_ae_local
    (π : ∀ i, A →* H i) (f : B →* A)
    (ρ : ∀ i, B →* Q i) (φ : ∀ i, Q i →* H i)
    (K₀ : ∀ i, Subgroup (H i))
    (hlocal : ∀ i, ∃ K, IsLocalIwasawaCompact (φ i) K)
    (hae : ∀ᶠ i in cofinite, IsLocalIwasawaCompact (φ i) (K₀ i))
    (hsep : ∀ a b : A, (∀ i, π i a = π i b) → a = b)
    (hπ : ∀ i, Continuous (π i))
    (hcompat : ∀ i b, π i (f b) = φ i (ρ i b))
    (hgood : ∀ a : A, ∀ᶠ i in cofinite, π i a ∈ K₀ i)
    (hlift : ∀ K : ∀ i, Subgroup (H i),
      (∀ᶠ i in cofinite, K i = K₀ i) →
        CoordinateCompactAssembly.CompactProductLift π K)
    (hfiniteLift : ∀ q : ∀ i, Q i, (∀ᶠ i in cofinite, q i = 1) →
      ∃ b : B, ∀ i, ρ i b = q i) :
    ∃ K : Subgroup A,
      (IsCompact (K : Set A) ∧
        ∀ L : Subgroup A, IsCompact (L : Set A) → K ≤ L → L = K) ∧
      Set.range f * (K : Set A) = Set.univ := by
  let good : ∀ i, Subgroup (H i) → Prop :=
    fun i K => IsLocalIwasawaCompact (φ i) K
  let K : ∀ i, Subgroup (H i) := patchFamily good hlocal K₀
  have hK (i : I) : IsLocalIwasawaCompact (φ i) (K i) :=
    good_patchFamily good hlocal K₀ i
  have hKeq : ∀ᶠ i in cofinite, K i = K₀ i :=
    patchFamily_eventually_eq good hlocal K₀ hae
  have hgood' (a : A) : ∀ᶠ i in cofinite, π i a ∈ K i := by
    filter_upwards [hKeq, hgood a] with i heq hi
    rwa [heq]
  refine ⟨CoordinateCompactAssembly.coordinateSubgroup π K, ?_, ?_⟩
  · exact CoordinateCompactAssembly.compact_maximal_coordinateSubgroup
      (hlift K hKeq) hsep hπ (fun i => (hK i).1.1) (fun i => (hK i).1.2)
  · exact CoordinateCompactAssembly.range_mul_coordinateSubgroup_eq_univ
      f ρ φ hcompat hgood' hfiniteLift (fun i => (hK i).2)

end Assembly

end Langlands.Global.CoordinateCompactPatching
