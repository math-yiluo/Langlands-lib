import Mathlib.RepresentationTheory.Homological.GroupCohomology.Shapiro
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-! # Coinduced modules and filtered colimits in group cohomology -/

noncomputable section

namespace Langlands.Cohomology.CoinducedFilteredAcyclic

open CategoryTheory CategoryTheory.Limits

universe u

section Coinduced

variable {k G : Type u} [CommRing k] [Group G]

/-- The representation coinduced from the trivial subgroup: all functions `G → A`, with
`h` acting by `(h • f) g = f (g * h)`. -/
abbrev coindBot (k G : Type u) [CommRing k] [Group G] (A : Type u) [AddCommGroup A]
    [Module k A] : Rep.{u} k G :=
  Rep.coind (⊥ : Subgroup G).subtype (Rep.trivial k (⊥ : Subgroup G) A)

lemma mem_coindV_bot {A : Type u} [AddCommGroup A] [Module k A] (f : G → A) :
    f ∈ Representation.coindV (⊥ : Subgroup G).subtype
      (Representation.trivial k (⊥ : Subgroup G) A) := by
  rintro ⟨g, hg⟩ h
  rw [Subgroup.mem_bot] at hg
  subst hg
  simp

variable (M : Rep.{u} k G) {A : Type u} [AddCommGroup A] [Module k A] (π : M →ₗ[k] A)

/-- The coordinate map `m ↦ (g ↦ π (g • m))` into the module coinduced from the trivial
subgroup. -/
def coordinates : M →ₗ[k] coindBot k G A where
  toFun m := ⟨fun g => π (M.ρ g m), mem_coindV_bot _⟩
  map_add' x y := by
    apply Subtype.ext
    funext g
    simp
  map_smul' r x := by
    apply Subtype.ext
    funext g
    simp

/-- If the coordinate map is bijective, it is a linear isomorphism onto the coinduced
module. -/
def coordinatesEquiv (hπ : Function.Bijective fun m : M => fun g : G => π (M.ρ g m)) :
    M ≃ₗ[k] coindBot k G A :=
  LinearEquiv.ofBijective (coordinates M π)
    ⟨fun x y h => hπ.1 (congrArg Subtype.val h), fun f => by
      obtain ⟨m, hm⟩ := hπ.2 f.1
      exact ⟨m, Subtype.ext hm⟩⟩

lemma coordinatesEquiv_comm (hπ : Function.Bijective fun m : M => fun g : G => π (M.ρ g m))
    (g : G) :
    (coordinatesEquiv M π hπ).toLinearMap ∘ₗ M.ρ g =
      (coindBot k G A).ρ (MulEquiv.refl G g) ∘ₗ (coordinatesEquiv M π hπ).toLinearMap := by
  apply LinearMap.ext
  intro m
  apply Subtype.ext
  funext h
  change π (M.ρ h (M.ρ g m)) = π (M.ρ (h * g) m)
  rw [map_mul, Module.End.mul_apply]

/-- **Coinduced modules are acyclic.** If some linear map `π : M → A` makes
`m ↦ (g ↦ π (g • m))` a bijection from `M` onto all functions `G → A`, then the positive
group cohomology of `M` vanishes. -/
theorem isZero_groupCohomology_succ_of_bijective
    (hπ : Function.Bijective fun m : M => fun g : G => π (M.ρ g m)) (n : ℕ) :
    IsZero (groupCohomology M (n + 1)) :=
  (isZero_groupCohomology_succ_of_subsingleton _ n).of_iso
    (groupCohomology.mapIso (MulEquiv.refl G) (coordinatesEquiv M π hπ)
        (coordinatesEquiv_comm M π hπ) (n + 1) ≪≫
      groupCohomology.coindIso _ (n + 1))

/-- The same criterion with the coordinates `g ↦ π (g⁻¹ • m)`. -/
theorem isZero_groupCohomology_succ_of_bijective_inv
    (hπ : Function.Bijective fun m : M => fun g : G => π (M.ρ g⁻¹ m)) (n : ℕ) :
    IsZero (groupCohomology M (n + 1)) := by
  apply isZero_groupCohomology_succ_of_bijective M π _ n
  have hinv : Function.Involutive fun f : G → A => fun g : G => f g⁻¹ := by
    intro f
    funext g
    simp
  have heq : (fun m : M => fun g : G => π (M.ρ g m)) =
      (fun f : G → A => fun g : G => f g⁻¹) ∘ fun m : M => fun g : G => π (M.ρ g⁻¹ m) := by
    funext m g
    simp
  rw [heq]
  exact hinv.bijective.comp hπ

end Coinduced

section Complexes

variable {R : Type u} [Ring R] {ι : Type*} {c : ComplexShape ι}
  {J : Type*} [Category J]

/-- Exactness at `n` passes from the complexes of a diagram of complexes of modules to the
vertex of a cocone, when the cocone is jointly surjective in degree `n` and every element of
degree `c.next n` that dies in the cocone already dies along some morphism of the diagram.
(These hypotheses hold for a colimit cocone over a filtered category.) -/
theorem exactAt_of_cocone {F : J ⥤ HomologicalComplex (ModuleCat.{u} R) c}
    (C : Cocone F) (n : ι)
    (hsurj : ∀ x : C.pt.X n, ∃ (i : J) (y : (F.obj i).X n), (C.ι.app i).f n y = x)
    (hzero : ∀ (i : J) (y : (F.obj i).X (c.next n)), (C.ι.app i).f (c.next n) y = 0 →
      ∃ (j : J) (f : i ⟶ j), (F.map f).f (c.next n) y = 0)
    (hex : ∀ j, (F.obj j).ExactAt n) : C.pt.ExactAt n := by
  rw [HomologicalComplex.exactAt_iff, ShortComplex.moduleCat_exact_iff]
  intro x hx
  obtain ⟨i, y, rfl⟩ := hsurj x
  have hdy : (C.ι.app i).f (c.next n) ((F.obj i).d n (c.next n) y) = 0 := by
    have h := ConcreteCategory.congr_hom ((C.ι.app i).comm n (c.next n)) y
    simp only [ConcreteCategory.comp_apply] at h
    rw [← h]
    exact hx
  obtain ⟨j, f, hf⟩ := hzero i _ hdy
  have hcyc : (F.obj j).d n (c.next n) ((F.map f).f n y) = 0 := by
    have h := ConcreteCategory.congr_hom ((F.map f).comm n (c.next n)) y
    simp only [ConcreteCategory.comp_apply] at h
    rw [h]
    exact hf
  obtain ⟨w, hw⟩ := (ShortComplex.moduleCat_exact_iff _).1 (hex j) _ hcyc
  change (F.obj j).X (c.prev n) at w
  refine ⟨(C.ι.app j).f _ w, ?_⟩
  have h₁ := ConcreteCategory.congr_hom ((C.ι.app j).comm (c.prev n) n) w
  simp only [ConcreteCategory.comp_apply] at h₁
  have h₂ := ConcreteCategory.congr_hom
    (congrArg (fun φ => HomologicalComplex.Hom.f φ n) (C.w f)) y
  simp only [HomologicalComplex.comp_f, ConcreteCategory.comp_apply] at h₂
  refine h₁.trans ?_
  rw [← h₂]
  exact congrArg _ hw

end Complexes

section Filtered

variable {k G : Type u} [CommRing k] [Group G]
  {J : Type u} [SmallCategory J] [IsFiltered J] {F : J ⥤ Rep.{u} k G}

omit [IsFiltered J] in
lemma preservesColimit_forget_of_filtered [IsFiltered J] (F : J ⥤ Rep.{u} k G) :
    PreservesColimit F (forget (Rep.{u} k G)) := by
  have : PreservesColimit F (forget₂ (Rep.{u} k G) (ModuleCat.{u} k) ⋙
      forget (ModuleCat.{u} k)) := inferInstance
  exact preservesColimit_of_natIso F
    (eqToIso (HasForget₂.forget_comp (C := Rep.{u} k G) (D := ModuleCat.{u} k)))

variable {c : Cocone F} (hc : IsColimit c)
include hc

/-- A finite family of elements of a filtered colimit of representations comes from one
stage. -/
lemma exists_family_rep {ι : Type*} [Finite ι] (x : ι → c.pt) :
    ∃ (i : J) (y : ι → F.obj i), ∀ t, c.ι.app i (y t) = x t := by
  classical
  have := preservesColimit_forget_of_filtered F
  have := Fintype.ofFinite ι
  choose j y hy using fun t => Concrete.isColimit_exists_rep F hc (x t)
  let O : Finset J := Finset.univ.image j
  have hO : ∀ t, j t ∈ O := fun t => Finset.mem_image_of_mem j (Finset.mem_univ t)
  refine ⟨IsFiltered.sup O ∅, fun t => F.map (IsFiltered.toSup O ∅ (hO t)) (y t), fun t => ?_⟩
  rw [← hy t, ← ConcreteCategory.comp_apply, c.w]

/-- A finite family of elements of one stage that vanishes in a filtered colimit of
representations already vanishes at a later stage. -/
lemma exists_family_eq_zero {ι : Type*} [Finite ι] {i : J} (y : ι → F.obj i)
    (hy : ∀ t, c.ι.app i (y t) = 0) :
    ∃ (j : J) (f : i ⟶ j), ∀ t, F.map f (y t) = 0 := by
  classical
  have := preservesColimit_forget_of_filtered F
  have := Fintype.ofFinite ι
  have hrep : ∀ t, ∃ (l : J) (f : i ⟶ l), F.map f (y t) = 0 := by
    intro t
    obtain ⟨l, f, g, hfg⟩ := Concrete.isColimit_exists_of_rep_eq F hc (y t) 0
      (by rw [hy t, map_zero])
    exact ⟨l, f, by rw [hfg, map_zero]⟩
  choose l f hf using hrep
  let O : Finset J := insert i (Finset.univ.image l)
  have hi : i ∈ O := Finset.mem_insert_self _ _
  have hl : ∀ t, l t ∈ O := fun t =>
    Finset.mem_insert_of_mem (Finset.mem_image_of_mem l (Finset.mem_univ t))
  let H : Finset (Σ' (X Y : J) (_ : X ∈ O) (_ : Y ∈ O), X ⟶ Y) :=
    Finset.univ.image fun t => ⟨i, l t, hi, hl t, f t⟩
  refine ⟨IsFiltered.sup O H, IsFiltered.toSup O H hi, fun t => ?_⟩
  have hcomm : f t ≫ IsFiltered.toSup O H (hl t) = IsFiltered.toSup O H hi :=
    IsFiltered.toSup_commutes O H hi (hl t)
      (Finset.mem_image_of_mem _ (Finset.mem_univ t))
  rw [← hcomm, Functor.map_comp, ConcreteCategory.comp_apply, hf t, map_zero]

/-- **Filtered colimits over a finite group.** For a finite group `G`, if the `n`-th group
cohomology of every representation in a filtered diagram vanishes, so does that of its
colimit. -/
theorem isZero_groupCohomology_of_isColimit [Finite G] (n : ℕ)
    (h : ∀ j, IsZero (groupCohomology (F.obj j) n)) :
    IsZero (groupCohomology c.pt n) := by
  have hex : ∀ A : Rep.{u} k G,
      IsZero (groupCohomology A n) ↔ (groupCohomology.inhomogeneousCochains A).ExactAt n :=
    fun A => (HomologicalComplex.exactAt_iff_isZero_homology _ _).symm
  rw [hex]
  refine exactAt_of_cocone ((groupCohomology.cochainsFunctor k G).mapCocone c) n ?_ ?_
    (fun j => (hex _).1 (h j))
  · intro x
    obtain ⟨i, y, hy⟩ := exists_family_rep hc x
    exact ⟨i, y, funext hy⟩
  · intro i y hy
    obtain ⟨j, f, hf⟩ := exists_family_eq_zero hc y (fun t => congrFun hy t)
    exact ⟨j, f, funext hf⟩

/-- For a finite group, a filtered colimit of coinduced representations has vanishing
positive group cohomology. -/
theorem isZero_groupCohomology_succ_of_isColimit_coinduced [Finite G] (n : ℕ)
    (h : ∀ j, ∃ (A : ModuleCat.{u} k) (π : F.obj j →ₗ[k] A),
      Function.Bijective fun m : F.obj j => fun g : G => π ((F.obj j).ρ g m)) :
    IsZero (groupCohomology c.pt (n + 1)) :=
  isZero_groupCohomology_of_isColimit hc (n + 1) fun j => by
    obtain ⟨A, π, hπ⟩ := h j
    exact isZero_groupCohomology_succ_of_bijective (F.obj j) π hπ n

end Filtered

end Langlands.Cohomology.CoinducedFilteredAcyclic
