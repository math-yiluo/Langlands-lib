import Langlands.Representation.Finite.DegreeZeroBrauerStatement
import Langlands.Representation.Finite.InducedCharacterProof
import Langlands.AnthropicFLT.Definitions.Def_ClassFunction_Induced

set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open scoped Classical

namespace Langlands.FiniteRep.DegreeZeroBrauer

universe uG uQ
variable {G : Type uG} [Group G] [Fintype G]

/-- Extension by zero from a subgroup. -/
def extend (S : Subgroup G) (f : S → ℂ) : G → ℂ :=
  fun g => if hg : g ∈ S then f ⟨g, hg⟩ else 0

/-- Normalized induction of functions, additive over the integers. -/
def ind (S : Subgroup G) : (S → ℂ) →ₗ[ℤ] (G → ℂ) :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun f => ClassFunction.induced S (extend S f)
      map_zero' := by
        funext g
        simp [extend, ClassFunction.induced_apply]
      map_add' := by
        intro f h
        have he : extend S (f + h) = extend S f + extend S h := by
          funext g
          simp only [extend, Pi.add_apply]
          split_ifs <;> simp
        rw [he, ClassFunction.induced_add] }

theorem ind_apply (S : Subgroup G) (f : S → ℂ) (g : G) :
    ind S f g = (Nat.card S : ℂ)⁻¹ *
      ∑ x : G, if hx : x⁻¹ * g * x ∈ S then f ⟨x⁻¹ * g * x, hx⟩ else 0 := by
  change ClassFunction.induced S (extend S f) g = _
  rw [ClassFunction.induced_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  split_ifs with hx <;> simp [extend, hx]

theorem ind_character (S : Subgroup G) (V : FDRep ℂ S) :
    ind S V.character = (induceRep S V).character := by
  funext g
  rw [ind_apply, InducedCharacter.inducedCharacterFormula]

theorem virtualCharacter_induce (S : Subgroup G) (x : VirtualRep ℂ S) :
    virtualCharacter (k := ℂ) (virtualInduce S x) = ind S (virtualCharacter (k := ℂ) x) := by
  obtain ⟨a, b, rfl⟩ := virtualRep_exists_difference x
  induction a using Quotient.inductionOn with | h V =>
  induction b using Quotient.inductionOn with | h W =>
  change virtualCharacter (k := ℂ) (virtualInduce S
    (ofClass (classOf V) - ofClass (classOf W))) =
    ind S (virtualCharacter (k := ℂ) (ofClass (classOf V) - ofClass (classOf W)))
  simp only [map_sub, virtualInduce, virtualMap_ofClass, virtualCharacter_ofClass,
    character_classOf]
  change (induceRep S V).character - (induceRep S W).character = _
  exact congrArg₂ (· - ·) (ind_character S V).symm (ind_character S W).symm

/-- The character image of the genuine degree-zero Brauer span. -/
def characterSpan (G : Type uG) [Group G] [Fintype G] : Submodule ℤ (G → ℂ) :=
  (degreeZeroBrauerSpan G).map virtualCharacter

/-- An actual induced difference gives a member of the character image. -/
theorem generator_mem (S : Subgroup G) (χ χ' : S →* ℂˣ) :
    ind S ((fun s => (χ s : ℂ)) - (fun s => (χ' s : ℂ))) ∈ characterSpan G := by
  refine ⟨virtualInduce S (ofClass (classOf (oneDimensional χ)) -
    ofClass (classOf (oneDimensional χ'))), Submodule.subset_span ⟨S, χ, χ', rfl⟩, ?_⟩
  rw [virtualCharacter_induce]
  congr 1
  simp only [map_sub, virtualCharacter_ofClass, character_classOf]
  ext s
  simp

theorem ind_ind (S : Subgroup G) (T : Subgroup S) (f : T → ℂ) :
    ind S (ind T f) = ind (T.map S.subtype)
      (fun t => f ((T.equivMapOfInjective S.subtype S.subtype_injective).symm t)) := by
  change ClassFunction.induced S
    (fun g => if hg : g ∈ S then ClassFunction.induced T (extend T f) ⟨g, hg⟩ else 0) = _
  rw [ClassFunction.induced_induced]
  apply ClassFunction.induced_congr
  intro g hg
  obtain ⟨s, hs, rfl⟩ := hg
  change (if hg : (s : G) ∈ S then extend T f ⟨(s : G), hg⟩ else 0) =
    extend (T.map S.subtype) _ (s : G)
  rw [dite_eq_left s.2]
  change extend T f s = _
  rw [extend, dite_eq_left (show s ∈ T from hs)]
  unfold extend
  have hm : (s : G) ∈ T.map S.subtype := ⟨s, hs, rfl⟩
  rw [dite_eq_left hm]
  congr 1
  apply (T.equivMapOfInjective S.subtype S.subtype_injective).injective
  rw [MulEquiv.apply_symm_apply]
  rfl

theorem ind_mem (S : Subgroup G) {f : S → ℂ} (hf : f ∈ characterSpan S) :
    ind S f ∈ characterSpan G := by
  obtain ⟨x, hx, rfl⟩ := hf
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨T, χ, χ', rfl⟩ := hy
    rw [virtualCharacter_induce]
    simp only [map_sub, virtualCharacter_ofClass, character_classOf]
    rw [show (oneDimensional χ).character = (fun t => (χ t : ℂ)) from
      funext (character_oneDimensional χ),
      show (oneDimensional χ').character = (fun t => (χ' t : ℂ)) from
      funext (character_oneDimensional χ')]
    rw [← map_sub, ← map_sub]
    rw [ind_ind]
    exact generator_mem (T.map S.subtype)
      (χ.comp (T.equivMapOfInjective S.subtype S.subtype_injective).symm.toMonoidHom)
      (χ'.comp (T.equivMapOfInjective S.subtype S.subtype_injective).symm.toMonoidHom)
  | zero => simp only [map_zero]; exact Submodule.zero_mem _
  | add x y hx hy ihx ihy =>
    simpa only [map_add] using Submodule.add_mem (characterSpan G) ihx ihy
  | smul a x hx ih =>
    simpa only [map_smul] using Submodule.smul_mem (characterSpan G) a ih

section Surjections
variable {Q : Type uQ} [Group Q] [Fintype Q]

/-- Every fiber of a surjective group homomorphism has kernel cardinality. -/
theorem sum_comp_surjective (π : G →* Q) (hπ : Function.Surjective π) (f : Q → ℂ) :
    ∑ g : G, f (π g) = (Nat.card π.ker : ℂ) * ∑ q : Q, f q := by
  rw [← Fintype.sum_fiberwise π]
  have hfib : ∀ q : Q, ∑ g : {g : G // π g = q}, f (π g) =
      (Nat.card π.ker : ℂ) * f q := by
    intro q
    have hconst : ∀ g : {g : G // π g = q}, f (π g) = f q :=
      fun g => congrArg f g.property
    simp only [hconst, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    congr 1
    rw [← Nat.card_eq_fintype_card]
    exact_mod_cast Nat.card_congr (MonoidHom.fiberEquivKerOfSurjective hπ q)
  rw [Finset.sum_congr rfl (fun q _ => hfib q), Finset.mul_sum]

/-- Cardinality of the inverse image of a subgroup under a surjection. -/
theorem card_comap_surjective (π : G →* Q) (hπ : Function.Surjective π) (S : Subgroup Q) :
    Nat.card (S.comap π) = Nat.card π.ker * Nat.card S := by
  have hcard : Nat.card G = Nat.card π.ker * Nat.card Q := by
    have h := sum_comp_surjective π hπ (fun _ => 1)
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      ← Nat.card_eq_fintype_card, ← Nat.cast_mul, Nat.cast_inj] using h
  have h1 := (S.comap π).card_mul_index
  have h2 := S.card_mul_index
  rw [Subgroup.index_comap_of_surjective _ hπ, hcard, ← h2, ← mul_assoc] at h1
  exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero S.index_ne_zero_of_finite) h1

/-- Induction commutes with inflation along a surjective group homomorphism. -/
theorem ind_comap (π : G →* Q) (hπ : Function.Surjective π)
    (S : Subgroup Q) (f : S → ℂ) :
    ind (S.comap π) (fun s => f (π.subgroupComap S s)) = (ind S f) ∘ π := by
  funext g
  rw [ind_apply]
  let F : Q → ℂ := fun q =>
    if hq : q⁻¹ * π g * q ∈ S then f ⟨q⁻¹ * π g * q, hq⟩ else 0
  have hsum : (∑ x : G, if hx : x⁻¹ * g * x ∈ S.comap π then
      f (π.subgroupComap S ⟨x⁻¹ * g * x, hx⟩) else 0) = ∑ x : G, F (π x) := by
    apply Finset.sum_congr rfl
    intro x _
    have he : π (x⁻¹ * g * x) = (π x)⁻¹ * π g * π x := by simp only [map_mul, map_inv]
    by_cases hx : x⁻¹ * g * x ∈ S.comap π
    · have hx' : (π x)⁻¹ * π g * π x ∈ S := by rw [← he]; exact hx
      simp only [dite_eq_left hx, F, dite_eq_left hx']
      congr 1
      exact Subtype.ext he
    · have hx' : (π x)⁻¹ * π g * π x ∉ S := by rw [← he]; exact hx
      simp only [dite_eq_right hx, F, dite_eq_right hx']
  rw [hsum, sum_comp_surjective π hπ, card_comap_surjective π hπ, Nat.cast_mul]
  change _ = ind S f (π g)
  rw [ind_apply]
  change _ = (Nat.card S : ℂ)⁻¹ * ∑ q, F q
  have hn : (Nat.card π.ker : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  field_simp

/-- Pullback of functions along a homomorphism, integer linearly. -/
def pullback (π : G →* Q) : (Q → ℂ) →ₗ[ℤ] (G → ℂ) where
  toFun f := f ∘ π
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Inflation preserves the character image of the degree-zero Brauer span. -/
theorem pullback_mem (π : G →* Q) (hπ : Function.Surjective π)
    {f : Q → ℂ} (hf : f ∈ characterSpan Q) : pullback π f ∈ characterSpan G := by
  obtain ⟨x, hx, rfl⟩ := hf
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨S, χ, χ', rfl⟩ := hy
    rw [virtualCharacter_induce]
    simp only [map_sub, virtualCharacter_ofClass, character_classOf]
    rw [show (oneDimensional χ).character = (fun t => (χ t : ℂ)) from
      funext (character_oneDimensional χ),
      show (oneDimensional χ').character = (fun t => (χ' t : ℂ)) from
      funext (character_oneDimensional χ')]
    rw [← map_sub, ← map_sub]
    change (ind S ((fun t => (χ t : ℂ)) - (fun t => (χ' t : ℂ)))) ∘ π ∈ characterSpan G
    rw [← ind_comap π hπ]
    exact generator_mem (S.comap π) (χ.comp (π.subgroupComap S)) (χ'.comp (π.subgroupComap S))
  | zero => simp only [map_zero]; exact Submodule.zero_mem _
  | add x y hx hy ihx ihy =>
    simpa only [map_add] using Submodule.add_mem (characterSpan G) ihx ihy
  | smul a x hx ih =>
    simpa only [map_smul] using Submodule.smul_mem (characterSpan G) a ih

end Surjections
end Langlands.FiniteRep.DegreeZeroBrauer
