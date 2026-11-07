import Langlands.HarmonicAnalysis.CompactCharacterCompleteness
import Mathlib.Topology.Algebra.Group.Quotient

/-! # Characters of a compact quotient -/

noncomputable section

universe u

namespace Langlands.HarmonicAnalysis.CompactQuotientCharacters

variable {A : Type u} [CommGroup A] [TopologicalSpace A]

/-- Descend a continuous character trivial on a subgroup to the quotient. -/
def descend (D : Subgroup A) (χ : PontryaginDual A)
    (hχ : ∀ a ∈ D, χ a = 1) : PontryaginDual (A ⧸ D) where
  toMonoidHom := QuotientGroup.lift D χ.toMonoidHom (fun a ha => hχ a ha)
  continuous_toFun := (QuotientGroup.isQuotientMap_mk D).continuous_iff.mpr χ.continuous

@[simp]
theorem descend_mk (D : Subgroup A) (χ : PontryaginDual A)
    (hχ : ∀ a ∈ D, χ a = 1) (a : A) :
    descend D χ hχ (QuotientGroup.mk a) = χ a := rfl

/-- Descent on any subgroup of characters that are trivial on `D`. -/
def descendHom (D : Subgroup A) (H : Subgroup (PontryaginDual A))
    (hH : ∀ χ ∈ H, ∀ a ∈ D, χ a = 1) :
    H →* PontryaginDual (A ⧸ D) where
  toFun χ := descend D (χ : PontryaginDual A) (hH χ χ.property)
  map_one' := by
    apply PontryaginDual.ext
    intro q
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
    rfl
  map_mul' χ η := by
    apply PontryaginDual.ext
    intro q
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective q
    rfl

@[simp]
theorem descendHom_mk (D : Subgroup A) (H : Subgroup (PontryaginDual A))
    (hH : ∀ χ ∈ H, ∀ a ∈ D, χ a = 1) (χ : H) (a : A) :
    descendHom D H hH χ (QuotientGroup.mk a) = (χ : PontryaginDual A) a := rfl

variable [IsTopologicalGroup A]

/-- Characters detecting every nonidentity quotient coset exhaust its dual. -/
theorem descendHom_range_eq_top (D : Subgroup A) [CompactSpace (A ⧸ D)]
    [T2Space (A ⧸ D)] (H : Subgroup (PontryaginDual A))
    (hH : ∀ χ ∈ H, ∀ a ∈ D, χ a = 1)
    (hsep : ∀ a ∉ D, ∃ χ ∈ H, χ a ≠ 1) :
    (descendHom D H hH).range = ⊤ := by
  apply CompactCharacterCompleteness.eq_top_of_separates
  intro x y hxy
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
  have hab : a / b ∉ D := by
    intro h
    apply hxy
    apply div_eq_one.mp
    simpa only [← QuotientGroup.mk_div] using (QuotientGroup.eq_one_iff (a / b)).mpr h
  obtain ⟨χ, hχ, habχ⟩ := hsep (a / b) hab
  refine ⟨⟨descendHom D H hH ⟨χ, hχ⟩, ⟨⟨χ, hχ⟩, rfl⟩⟩, ?_⟩
  change χ a ≠ χ b
  intro he
  apply habχ
  rw [map_div, he, div_self']

/-- A separating family on a compact quotient contains every character trivial
on the subgroup defining that quotient. -/
theorem mem_of_separates_quotient (D : Subgroup A) [CompactSpace (A ⧸ D)]
    [T2Space (A ⧸ D)] (H : Subgroup (PontryaginDual A))
    (hH : ∀ χ ∈ H, ∀ a ∈ D, χ a = 1)
    (hsep : ∀ a ∉ D, ∃ χ ∈ H, χ a ≠ 1)
    (χ : PontryaginDual A) (hχ : ∀ a ∈ D, χ a = 1) : χ ∈ H := by
  have hm : descend D χ hχ ∈ (descendHom D H hH).range := by
    rw [descendHom_range_eq_top D H hH hsep]
    exact Subgroup.mem_top _
  obtain ⟨η, hη⟩ := hm
  have heq : (η : PontryaginDual A) = χ := by
    apply PontryaginDual.ext
    intro a
    exact congrArg (fun f : PontryaginDual (A ⧸ D) => f (QuotientGroup.mk a)) hη
  rw [← heq]
  exact η.property

end Langlands.HarmonicAnalysis.CompactQuotientCharacters
