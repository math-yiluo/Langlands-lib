import Langlands.Representation.Jacquet.LocalizationFiltration
import Mathlib.RepresentationTheory.Rep.Res

/-! Images of subgroup-stable support spaces in an ambient character quotient. -/

noncomputable section

open CategoryTheory

namespace Langlands.Jacquet.Localization

universe uR uG uV uC vC

variable {R : Type uR} [CommRing R] {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module R V]
  (U : Subgroup G) (θ : U →* Rˣ) (M : Subgroup G)
  (hMU : M ≤ Subgroup.normalizer U) (hθ : IsInvariant U M hMU θ)
  (Q : Subgroup G) (hMQ : M ≤ Q)

/-- Map a `Q`-stable subspace into the actual quotient of the ambient
`G`-representation. Its image is `M`-stable because `M ≤ Q`. -/
def restrictedImageSubrepresentation (ρ : Representation R G V)
    (S : Subrepresentation (ρ.comp Q.subtype)) :
    Subrepresentation (action ρ U θ M hMU hθ) where
  toSubmodule := S.toSubmodule.map (mk ρ U θ)
  apply_mem_toSubmodule m := by
    rintro _ ⟨v, hv, rfl⟩
    exact ⟨ρ m v, S.apply_mem_toSubmodule ⟨m, hMQ m.property⟩ hv, rfl⟩

@[simp]
theorem mem_restrictedImageSubrepresentation (ρ : Representation R G V)
    (S : Subrepresentation (ρ.comp Q.subtype)) (q : Coinvariants ρ U θ) :
    q ∈ restrictedImageSubrepresentation U θ M hMU hθ Q hMQ ρ S ↔
      ∃ v ∈ S, mk ρ U θ v = q := Iff.rfl

/-- The representative differs from a vector of `S` by ambient `U,θ` relations. -/
theorem mk_mem_restrictedImageSubrepresentation (ρ : Representation R G V)
    (S : Subrepresentation (ρ.comp Q.subtype)) (v : V) :
    mk ρ U θ v ∈ restrictedImageSubrepresentation U θ M hMU hθ Q hMQ ρ S ↔
      ∃ s ∈ S, s - v ∈ relations ρ U θ := by
  simp only [mem_restrictedImageSubrepresentation, mk_eq_iff]

theorem restrictedImageSubrepresentation_mono (ρ : Representation R G V)
    {S T : Subrepresentation (ρ.comp Q.subtype)} (h : S ≤ T) :
    restrictedImageSubrepresentation U θ M hMU hθ Q hMQ ρ S ≤
      restrictedImageSubrepresentation U θ M hMU hθ Q hMQ ρ T := by
  rintro _ ⟨v, hv, rfl⟩
  exact ⟨v, h hv, rfl⟩

@[simp]
theorem restrictedImageSubrepresentation_bot (ρ : Representation R G V) :
    restrictedImageSubrepresentation U θ M hMU hθ Q hMQ ρ ⊥ = ⊥ := by
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    have hv0 : v = 0 := hv
    change mk ρ U θ v = 0
    rw [hv0, map_zero]
  · exact bot_le

@[simp]
theorem restrictedImageSubrepresentation_top (ρ : Representation R G V) :
    restrictedImageSubrepresentation U θ M hMU hθ Q hMQ ρ ⊤ = ⊤ := by
  apply le_antisymm le_top
  intro q _
  obtain ⟨v, rfl⟩ := mk_surjective ρ U θ q
  exact ⟨v, trivial, rfl⟩

/-- Images preserve sums; no exactness or intersection assertion is needed. -/
theorem restrictedImageSubrepresentation_sup (ρ : Representation R G V)
    (S T : Subrepresentation (ρ.comp Q.subtype)) :
    restrictedImageSubrepresentation U θ M hMU hθ Q hMQ ρ (S ⊔ T) =
      restrictedImageSubrepresentation U θ M hMU hθ Q hMQ ρ S ⊔
        restrictedImageSubrepresentation U θ M hMU hθ Q hMQ ρ T := by
  apply Subrepresentation.toSubmodule_injective
  exact Submodule.map_sup _ _ _

variable {C : Type uC} [Category.{vC} C] {F : C ⥤ Rep.{uV} R G}

/-- The image of a natural `Q`-stable subspace in the ambient localization.
The quotient uses the original `G`-representation, not the support subspace. -/
def restrictedImageSubfunctor (S : RepSubfunctor (F ⋙ Rep.resFunctor Q.subtype)) :
    RepSubfunctor (F ⋙ functor U θ M hMU hθ) where
  obj X := restrictedImageSubrepresentation U θ M hMU hθ Q hMQ (F.obj X).ρ (S.obj X)
  map_mem := by
    intro X Y f q hq
    obtain ⟨v, hv, rfl⟩ := hq
    exact ⟨(F.map f).hom v, S.map_mem f hv, rfl⟩

@[simp]
theorem restrictedImageSubfunctor_obj
    (S : RepSubfunctor (F ⋙ Rep.resFunctor Q.subtype)) (X : C) :
    (restrictedImageSubfunctor U θ M hMU hθ Q hMQ S).obj X =
      restrictedImageSubrepresentation U θ M hMU hθ Q hMQ (F.obj X).ρ (S.obj X) := rfl

/-- The fixed image filtration of the ambient localization, preserving the
specified indices and endpoints. Graded-piece identifications are separate. -/
def restrictedImageFiltration {n : ℕ}
    (s : RepFunctorFiltration (F ⋙ Rep.resFunctor Q.subtype) n) :
    RepFunctorFiltration (F ⋙ functor U θ M hMU hθ) n where
  step k := restrictedImageSubfunctor U θ M hMU hθ Q hMQ (s.step k)
  monotone X := by
    intro i j hij
    exact restrictedImageSubrepresentation_mono U θ M hMU hθ Q hMQ (F.obj X).ρ
      (s.monotone X hij)
  zero X := by
    change restrictedImageSubrepresentation U θ M hMU hθ Q hMQ (F.obj X).ρ
      ((s.step 0).obj X) = ⊥
    rw [s.zero X, restrictedImageSubrepresentation_bot]
  top X := by
    change restrictedImageSubrepresentation U θ M hMU hθ Q hMQ (F.obj X).ρ
      ((s.step (Fin.last _)).obj X) = ⊤
    rw [s.top X, restrictedImageSubrepresentation_top]

/-- Membership in the fixed kth image step means having a representative in
that same kth restricted subspace. -/
theorem mem_restrictedImageFiltration_step {n : ℕ}
    (s : RepFunctorFiltration (F ⋙ Rep.resFunctor Q.subtype) n)
    (k : Fin (n + 1)) (X : C) (q : Coinvariants (F.obj X).ρ U θ) :
    q ∈ ((restrictedImageFiltration U θ M hMU hθ Q hMQ s).step k).obj X ↔
      ∃ v ∈ (s.step k).obj X, mk (F.obj X).ρ U θ v = q := Iff.rfl

end Langlands.Jacquet.Localization
