import Langlands.Representation.Jacquet.Localization
import Langlands.Representation.Filtration.Definitions

/-! Actual images of subrepresentations and filtrations in character localization. -/

noncomputable section

open CategoryTheory

namespace Langlands.Jacquet.Localization

universe uR uG uV uC vC

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module R V]
  (U : Subgroup G) (θ : U →* Rˣ) (M : Subgroup G)
  (hMU : M ≤ Subgroup.normalizer U) (hθ : IsInvariant U M hMU θ)

/-- The actual image of a subrepresentation under the character quotient map. -/
def imageSubrepresentation (ρ : Representation R G V) (S : Subrepresentation ρ) :
    Subrepresentation (action ρ U θ M hMU hθ) where
  toSubmodule := S.toSubmodule.map (mk ρ U θ)
  apply_mem_toSubmodule m := by
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨ρ m v, S.apply_mem_toSubmodule m hv, rfl⟩

@[simp]
theorem mem_imageSubrepresentation (ρ : Representation R G V)
    (S : Subrepresentation ρ) (q : Coinvariants ρ U θ) :
    q ∈ imageSubrepresentation U θ M hMU hθ ρ S ↔
      ∃ v ∈ S, mk ρ U θ v = q := Iff.rfl

/-- Membership of a quotient class is membership modulo the ambient relation span. -/
theorem mk_mem_imageSubrepresentation (ρ : Representation R G V)
    (S : Subrepresentation ρ) (v : V) :
    mk ρ U θ v ∈ imageSubrepresentation U θ M hMU hθ ρ S ↔
      ∃ s ∈ S, s - v ∈ relations ρ U θ := by
  simp only [mem_imageSubrepresentation, mk_eq_iff]

theorem imageSubrepresentation_mono (ρ : Representation R G V)
    {S T : Subrepresentation ρ} (h : S ≤ T) :
    imageSubrepresentation U θ M hMU hθ ρ S ≤
      imageSubrepresentation U θ M hMU hθ ρ T := by
  rintro _ ⟨v, hv, rfl⟩
  exact ⟨v, h hv, rfl⟩

@[simp]
theorem imageSubrepresentation_bot (ρ : Representation R G V) :
    imageSubrepresentation U θ M hMU hθ ρ ⊥ = ⊥ := by
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    have hv0 : v = 0 := hv
    change mk ρ U θ v = 0
    rw [hv0, map_zero]
  · exact bot_le

@[simp]
theorem imageSubrepresentation_top (ρ : Representation R G V) :
    imageSubrepresentation U θ M hMU hθ ρ ⊤ = ⊤ := by
  apply le_antisymm le_top
  intro q _
  obtain ⟨v, rfl⟩ := mk_surjective ρ U θ q
  exact ⟨v, trivial, rfl⟩

/-- The image of a sum is the sum of the images; no exactness is used. -/
theorem imageSubrepresentation_sup (ρ : Representation R G V)
    (S T : Subrepresentation ρ) :
    imageSubrepresentation U θ M hMU hθ ρ (S ⊔ T) =
      imageSubrepresentation U θ M hMU hθ ρ S ⊔
        imageSubrepresentation U θ M hMU hθ ρ T := by
  apply Subrepresentation.toSubmodule_injective
  exact Submodule.map_sup _ _ _

variable {C : Type uC} [Category.{vC} C] {F : C ⥤ Rep.{uV} R G}

/-- Images of the actual objectwise subspaces form a natural subfunctor
of the localization of `F`. -/
def imageSubfunctor (S : RepSubfunctor F) :
    RepSubfunctor (F ⋙ functor U θ M hMU hθ) where
  obj X := imageSubrepresentation U θ M hMU hθ (F.obj X).ρ (S.obj X)
  map_mem := by
    intro X Y f q hq
    obtain ⟨v, hv, rfl⟩ := hq
    exact ⟨(F.map f).hom v, S.map_mem f hv, rfl⟩

@[simp]
theorem imageSubfunctor_obj (S : RepSubfunctor F) (X : C) :
    (imageSubfunctor U θ M hMU hθ S).obj X =
      imageSubrepresentation U θ M hMU hθ (F.obj X).ρ (S.obj X) := rfl

/-- The fixed image filtration, with the same order and endpoints as the
given filtration. It does not assert an identification of graded pieces. -/
def imageFiltration {n : ℕ} (s : RepFunctorFiltration F n) :
    RepFunctorFiltration (F ⋙ functor U θ M hMU hθ) n where
  step k := imageSubfunctor U θ M hMU hθ (s.step k)
  monotone X := by
    intro i j hij
    exact imageSubrepresentation_mono U θ M hMU hθ (F.obj X).ρ
      (s.monotone X hij)
  zero X := by
    change imageSubrepresentation U θ M hMU hθ (F.obj X).ρ ((s.step 0).obj X) = ⊥
    rw [s.zero X, imageSubrepresentation_bot]
  top X := by
    change imageSubrepresentation U θ M hMU hθ (F.obj X).ρ
      ((s.step (Fin.last _)).obj X) = ⊤
    rw [s.top X, imageSubrepresentation_top]

/-- Explicit membership in the fixed kth image step. -/
theorem mem_imageFiltration_step {n : ℕ} (s : RepFunctorFiltration F n)
    (k : Fin (n + 1)) (X : C) (q : Coinvariants (F.obj X).ρ U θ) :
    q ∈ ((imageFiltration U θ M hMU hθ s).step k).obj X ↔
      ∃ v ∈ (s.step k).obj X, mk (F.obj X).ρ U θ v = q := Iff.rfl

end Langlands.Jacquet.Localization
