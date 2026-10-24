import Mathlib

/-!
# Low-degree cohomology of a product decomposition

Let `A` be a representation of `G` and `p i : A ⟶ B i` a family of morphisms that is jointly
injective and jointly surjective, so that `A` is the product of the `B i`. Then the induced
map `Hⁿ(G, A) → ∏ᵢ Hⁿ(G, B i)` is bijective for `n = 1, 2`. The index type is arbitrary.
-/

namespace Langlands.Cohomology.ProductDecomposition

open CategoryTheory groupCohomology

universe u w

variable {k G : Type u} [CommRing k] [Group G] {ι : Type w} {A : Rep.{u} k G}
  {B : ι → Rep.{u} k G} (p : ∀ i, A ⟶ B i)

/-- The map from the cohomology of `A` to the product of the cohomologies of the `B i`. -/
noncomputable def productMap (n : ℕ) :
    groupCohomology A n → ∀ i, groupCohomology (B i) n :=
  fun c i => groupCohomology.map (MonoidHom.id G) (p i) n c

theorem exists_H1π_eq {C : Rep.{u} k G} (c : groupCohomology C 1) :
    ∃ x : cocycles₁ C, H1π C x = c :=
  H1_induction_on c fun x => ⟨x, rfl⟩

theorem exists_H2π_eq {C : Rep.{u} k G} (c : groupCohomology C 2) :
    ∃ x : cocycles₂ C, H2π C x = c :=
  H2_induction_on c fun x => ⟨x, rfl⟩

/-- The cocycle `p ∘ x`. -/
noncomputable def compCocycles₁ {C D : Rep.{u} k G} (q : C ⟶ D) (x : cocycles₁ C) :
    cocycles₁ D :=
  ⟨fun g => q.hom (x g), (mem_cocycles₁_iff _).2 fun g h => by
    rw [(mem_cocycles₁_iff x).1 x.2 g h, map_add, Rep.hom_comm_apply]⟩

/-- The cocycle `p ∘ x`. -/
noncomputable def compCocycles₂ {C D : Rep.{u} k G} (q : C ⟶ D) (x : cocycles₂ C) :
    cocycles₂ D :=
  ⟨fun g => q.hom (x g), (mem_cocycles₂_iff _).2 fun g h j => by
    rw [← map_add, (mem_cocycles₂_iff x).1 x.2 g h j, map_add, Rep.hom_comm_apply]⟩

theorem map_H1π {C D : Rep.{u} k G} (q : C ⟶ D) (x : cocycles₁ C) :
    groupCohomology.map (MonoidHom.id G) q 1 (H1π C x) = H1π D (compCocycles₁ q x) := by
  rw [H1π_comp_map_apply]
  rfl

theorem map_H2π {C D : Rep.{u} k G} (q : C ⟶ D) (x : cocycles₂ C) :
    groupCohomology.map (MonoidHom.id G) q 2 (H2π C x) = H2π D (compCocycles₂ q x) := by
  rw [H2π_comp_map_apply]
  rfl

variable {p}
variable (hinj : ∀ a : A, (∀ i, (p i).hom a = 0) → a = 0)
  (hsurj : ∀ b : ∀ i, B i, ∃ a : A, ∀ i, (p i).hom a = b i)

include hinj in
theorem eq_of_forall_hom_eq {a a' : A} (h : ∀ i, (p i).hom a = (p i).hom a') : a = a' :=
  sub_eq_zero.1 (hinj _ fun i => by rw [map_sub, h, sub_self])

include hinj hsurj in
theorem productMap_bijective_one : Function.Bijective (productMap p 1) := by
  constructor
  · have hker : ∀ c, productMap p 1 c = 0 → c = 0 := by
      intro c hc
      obtain ⟨x, rfl⟩ := exists_H1π_eq c
      rw [H1π_eq_zero_iff]
      have hi : ∀ i, ∃ b : B i, ∀ g, (B i).ρ g b - b = (p i).hom (x g) := by
        intro i
        have h : groupCohomology.map (MonoidHom.id G) (p i) 1 (H1π A x) = 0 := congrFun hc i
        rw [map_H1π, H1π_eq_zero_iff] at h
        obtain ⟨b, hb⟩ := h
        exact ⟨b, fun g => congrFun hb g⟩
      choose b hb using hi
      obtain ⟨a, ha⟩ := hsurj b
      refine ⟨a, funext fun g => ?_⟩
      rw [d₀₁_hom_apply]
      exact eq_of_forall_hom_eq hinj fun i => by
        rw [map_sub, Rep.hom_comm_apply, ha, hb]
    intro c c' h
    rw [← sub_eq_zero]
    apply hker
    funext i
    have := congrFun h i
    simp only [productMap, Pi.zero_apply] at this ⊢
    rw [map_sub, this, sub_self]
  · intro c
    have hi : ∀ i, ∃ y : cocycles₁ (B i), H1π (B i) y = c i := fun i => exists_H1π_eq (c i)
    choose y hy using hi
    have hpt : ∀ g, ∃ a : A, ∀ i, (p i).hom a = y i g := fun g => hsurj fun i => y i g
    choose x hx using hpt
    have hxc : x ∈ cocycles₁ A := (mem_cocycles₁_iff _).2 fun g h =>
      eq_of_forall_hom_eq hinj fun i => by
        rw [hx, map_add, Rep.hom_comm_apply, hx, hx, (mem_cocycles₁_iff (y i)).1 (y i).2 g h]
    refine ⟨H1π A ⟨x, hxc⟩, funext fun i => ?_⟩
    change groupCohomology.map (MonoidHom.id G) (p i) 1 (H1π A ⟨x, hxc⟩) = c i
    rw [map_H1π, ← hy i]
    congr 1
    apply Subtype.ext
    funext g
    exact hx g i

include hinj hsurj in
theorem productMap_bijective_two : Function.Bijective (productMap p 2) := by
  constructor
  · have hker : ∀ c, productMap p 2 c = 0 → c = 0 := by
      intro c hc
      obtain ⟨x, rfl⟩ := exists_H2π_eq c
      rw [H2π_eq_zero_iff]
      have hi : ∀ i, ∃ b : G → B i, ∀ q : G × G,
          (B i).ρ q.1 (b q.2) - b (q.1 * q.2) + b q.1 = (p i).hom (x q) := by
        intro i
        have h : groupCohomology.map (MonoidHom.id G) (p i) 2 (H2π A x) = 0 := congrFun hc i
        rw [map_H2π, H2π_eq_zero_iff] at h
        obtain ⟨b, hb⟩ := h
        exact ⟨b, fun q => by rw [← d₁₂_hom_apply]; exact congrFun hb q⟩
      choose b hb using hi
      have hpt : ∀ g, ∃ a : A, ∀ i, (p i).hom a = b i g := fun g => hsurj fun i => b i g
      choose a ha using hpt
      refine ⟨a, funext fun q => ?_⟩
      rw [d₁₂_hom_apply]
      exact eq_of_forall_hom_eq hinj fun i => by
        rw [map_add, map_sub, Rep.hom_comm_apply, ha, ha, ha, hb]
    intro c c' h
    rw [← sub_eq_zero]
    apply hker
    funext i
    have := congrFun h i
    simp only [productMap, Pi.zero_apply] at this ⊢
    rw [map_sub, this, sub_self]
  · intro c
    have hi : ∀ i, ∃ y : cocycles₂ (B i), H2π (B i) y = c i := fun i => exists_H2π_eq (c i)
    choose y hy using hi
    have hpt : ∀ q : G × G, ∃ a : A, ∀ i, (p i).hom a = y i q := fun q => hsurj fun i => y i q
    choose x hx using hpt
    have hxc : x ∈ cocycles₂ A := (mem_cocycles₂_iff _).2 fun g h j =>
      eq_of_forall_hom_eq hinj fun i => by
        rw [map_add, map_add, Rep.hom_comm_apply, hx, hx, hx, hx,
          (mem_cocycles₂_iff (y i)).1 (y i).2 g h j]
    refine ⟨H2π A ⟨x, hxc⟩, funext fun i => ?_⟩
    change groupCohomology.map (MonoidHom.id G) (p i) 2 (H2π A ⟨x, hxc⟩) = c i
    rw [map_H2π, ← hy i]
    congr 1
    apply Subtype.ext
    funext q
    exact hx q i

/-- The cohomology groups of `A` in degrees one and two are equivalent to the products of
those of the `B i`. -/
noncomputable def productEquiv (n : ℕ) (hn : n = 1 ∨ n = 2) :
    groupCohomology A n ≃ ∀ i, groupCohomology (B i) n :=
  Equiv.ofBijective (productMap p n) (by
    rcases hn with rfl | rfl
    · exact productMap_bijective_one hinj hsurj
    · exact productMap_bijective_two hinj hsurj)


section Cardinality

variable {κ : Type*} {X : κ → Type*}

/-- Restriction of a dependent function to a finite set of indices. -/
def restrictPi (s : Finset κ) (f : ∀ i, X i) : ∀ i : s, X i := fun i => f i

theorem restrictPi_bijective [∀ i, Nonempty (X i)] (s : Finset κ)
    (hs : ∀ i ∉ s, Subsingleton (X i)) : Function.Bijective (restrictPi (X := X) s) := by
  classical
  constructor
  · intro f f' h
    funext i
    by_cases hi : i ∈ s
    · exact congrFun h ⟨i, hi⟩
    · exact (hs i hi).elim _ _
  · intro g
    refine ⟨fun i => if hi : i ∈ s then g ⟨i, hi⟩ else Classical.arbitrary _, funext fun i => ?_⟩
    simp [restrictPi, i.2]

/-- If all factors outside a finite set are subsingletons, the product has the cardinality of
the finite product of the remaining factors. -/
theorem natCard_pi_eq_prod [∀ i, Nonempty (X i)] (s : Finset κ)
    (hs : ∀ i ∉ s, Subsingleton (X i)) : Nat.card (∀ i, X i) = ∏ i ∈ s, Nat.card (X i) := by
  rw [Nat.card_congr (Equiv.ofBijective _ (restrictPi_bijective s hs)), Nat.card_pi,
    Finset.prod_coe_sort s (fun i => Nat.card (X i))]

/-- If all factors outside a finite set are subsingletons and the others are finite, the
product is finite. -/
theorem finite_pi [∀ i, Nonempty (X i)] (s : Finset κ) (hs : ∀ i ∉ s, Subsingleton (X i))
    (hf : ∀ i ∈ s, Finite (X i)) : Finite (∀ i, X i) := by
  have : ∀ i : s, Finite (X i) := fun i => hf i i.2
  exact Finite.of_equiv _ (Equiv.ofBijective _ (restrictPi_bijective s hs)).symm

end Cardinality

end Langlands.Cohomology.ProductDecomposition
