import Langlands.GroupScheme.Rational.StarFieldQuadraticRestriction
import Langlands.GroupScheme.Rational.TypeD4StarScalarExtension
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.GroupTheory.Perm.Sign

/-! # The even part of the trialitarian diagram action -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.TitsIndexData

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 850000

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G)

/-- The sign of the star permutation in a numbering of the four vertices. -/
def starSign (e : d.Vertex ≃ Fin 4) : (SeparableClosure k ≃ₐ[k] SeparableClosure k) →* ℤˣ where
  toFun σ := Equiv.Perm.sign (e.permCongr (d.starPermutation σ))
  map_one' := by
    have h : d.starPermutation 1 = 1 := Equiv.ext d.star_one
    rw [h]
    change Equiv.Perm.sign (e.permCongr (Equiv.refl _)) = 1
    rw [Equiv.permCongr_refl]
    exact map_one _
  map_mul' σ τ := by
    rw [← map_mul]
    apply congrArg Equiv.Perm.sign
    apply Equiv.ext
    intro x
    change e (d.star (σ * τ) (e.symm x)) = e (d.star σ (e.symm (e (d.star τ (e.symm x)))))
    rw [e.symm_apply_apply, d.star_mul]

private theorem eq_one_of_sign_of_two_fixed (p : Equiv.Perm (Fin 4)) (a : Fin 4)
    (ha : a ≠ 1) (h₁ : p 1 = 1) (h₂ : p a = a) (hs : Equiv.Perm.sign p = 1) : p = 1 := by
  have h : ∀ (p : Equiv.Perm (Fin 4)) (a : Fin 4), a ≠ 1 → p 1 = 1 → p a = a →
      p = 1 ∨ ∃ i j : Fin 4, i ≠ j ∧ p = Equiv.swap i j := by decide
  rcases h p a ha h₁ h₂ with h | ⟨i, j, hij, rfl⟩
  · exact h
  · rw [Equiv.Perm.sign_swap hij] at hs
    exact (by decide : (-1 : ℤˣ) ≠ 1) hs |>.elim

/-- If every star permutation is even and the leaves move transitively,
then the field trivializing the action is cubic. -/
theorem finrank_starField_of_D4_even (e : d.Vertex ≃ Fin 4)
    (hD : ∀ a b, d.cartan a b = CartanMatrix.D 4 (e a) (e b))
    (hno : ¬ ∃ a : d.Vertex, e a ≠ 1 ∧
      ∀ σ : SeparableClosure k ≃ₐ[k] SeparableClosure k, d.star σ a = a)
    (heven : ∀ σ, d.starSign e σ = 1) : Module.finrank k d.starField = 3 := by
  let a := e.symm 0
  have ha : e a ≠ 1 := by simp [a]
  have hstab : d.starVertexStabilizer a = d.starKernel := by
    refine le_antisymm ?_ (d.starKernel_le_starVertexStabilizer a)
    intro σ hσ
    let p := e.permCongr (d.starPermutation σ)
    have h₁ : p 1 = 1 := by
      change e (d.star σ (e.symm 1)) = 1
      rw [d.star_fixes_center_of_D (by decide) e hD σ (e.symm 1) (by simp)]
      exact e.apply_symm_apply 1
    have h₂ : p (e a) = e a := by
      change e (d.star σ (e.symm (e a))) = e a
      rw [e.symm_apply_apply, (d.mem_starVertexStabilizer a σ).mp hσ]
    have hp := eq_one_of_sign_of_two_fixed p _ ha h₁ h₂ (heven σ)
    intro v
    apply e.injective
    have hv : e (d.star σ (e.symm (e v))) = e v :=
      congrArg (fun f : Equiv.Perm (Fin 4) => f (e v)) hp
    rwa [e.symm_apply_apply] at hv
  rw [d.finrank_starField, ← hstab]
  exact d.starVertexStabilizer_index_of_D4_no_fixed_leaf e hD hno a ha

/-- If the star action has an odd permutation, the fixing field of its
sign kernel is a quadratic Galois extension. Its absolute Galois action on
the original numbering has even sign everywhere. -/
theorem exists_evenStarQuadratic (e : d.Vertex ≃ Fin 4)
    (hodd : ¬ ∀ σ, d.starSign e σ = 1) :
    ∃ Q : IntermediateField k (SeparableClosure k),
      FiniteDimensional k Q ∧ IsGalois k Q ∧ Module.finrank k Q = 2 ∧
      ∀ σ ∈ Q.fixingSubgroup, d.starSign e σ = 1 := by
  let s := d.starSign e
  let Q := IntermediateField.fixedField s.ker
  have hle : d.starKernel ≤ s.ker := by
    intro σ hσ
    have h : d.starPermutation σ = d.starPermutation 1 :=
      Equiv.ext fun a => (hσ a).trans (d.star_one a).symm
    have hs : s σ = s 1 :=
      congrArg (fun p : Equiv.Perm d.Vertex => Equiv.Perm.sign (e.permCongr p)) h
    exact hs.trans (map_one s)
  have ho : IsOpen (s.ker : Set (SeparableClosure k ≃ₐ[k] SeparableClosure k)) :=
    Subgroup.isOpen_mono hle d.starKernel_isOpen
  have hfix : Q.fixingSubgroup = s.ker :=
    InfiniteGalois.fixingSubgroup_fixedField ⟨s.ker, Subgroup.isClosed_of_isOpen _ ho⟩
  have hsur : Function.Surjective s := by
    obtain ⟨σ, hσ⟩ := not_forall.mp hodd
    intro z
    rcases Int.units_eq_one_or z with rfl | rfl
    · exact ⟨1, map_one _⟩
    · exact ⟨σ, (Int.units_eq_one_or (s σ)).resolve_left hσ⟩
  have hcard : Nat.card ℤˣ = 2 := (Nat.card_eq_two_iff' (1 : ℤˣ)).mpr
    ⟨-1, by decide, fun z hz => (Int.units_eq_one_or z).resolve_left hz⟩
  refine ⟨Q, (InfiniteGalois.isOpen_iff_finite Q).mp (hfix.symm ▸ ho), ?_, ?_, ?_⟩
  · apply (InfiniteGalois.normal_iff_isGalois Q).mp
    rw [hfix]
    infer_instance
  · rw [IntermediateField.finrank_eq_fixingSubgroup_index, hfix, Subgroup.index_ker,
      MonoidHom.range_eq_top.mpr hsur, Subgroup.card_top, hcard]
  · intro σ hσ
    exact MonoidHom.mem_ker.mp (hfix ▸ hσ)

section ScalarExtension

variable (Q : IntermediateField k (SeparableClosure k))

local instance : Algebra Q (SeparableClosure Q) :=
  (separableClosure Q (AlgebraicClosure Q)).algebra

local instance : IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k Q)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom _)
  infer_instance

local instance : LocallyOfFiniteType ((GroupScheme.baseChange (algebraBaseMap k Q)).obj G).X.hom := by
  change LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd G.X.hom _)
  infer_instance

/-- Numbered star permutations are preserved under transport to an
intermediate field and restriction of the absolute Galois element. -/
theorem starSign_prescribedStabilizerIndex
    (e : d.Vertex ≃ Fin 4)
    (τ : SeparableClosure Q ≃ₐ[Q] SeparableClosure Q) :
    let C := d.prescribedStabilizerIndexComparison Q
    C.index.starSign (C.vertices.symm.trans e) τ =
      d.starSign e ((AlgEquiv.autCongr (prescribedStabilizerClosureEquiv Q) τ).restrictScalars k) := by
  let C := d.prescribedStabilizerIndexComparison Q
  let σ := (AlgEquiv.autCongr (prescribedStabilizerClosureEquiv Q) τ).restrictScalars k
  change Equiv.Perm.sign ((C.vertices.symm.trans e).permCongr (C.index.starPermutation τ)) =
    Equiv.Perm.sign (e.permCongr (d.starPermutation σ))
  apply congrArg Equiv.Perm.sign
  apply Equiv.ext
  intro x
  have h := C.star_eq τ (e.symm x)
  change C.vertices (d.star σ (e.symm x)) = C.index.star τ (C.vertices (e.symm x)) at h
  change e (C.vertices.symm (C.index.star τ (C.vertices (e.symm x)))) = e (d.star σ (e.symm x))
  rw [← h, C.vertices.symm_apply_apply]

end ScalarExtension

end Langlands.GroupScheme.TitsIndexData
