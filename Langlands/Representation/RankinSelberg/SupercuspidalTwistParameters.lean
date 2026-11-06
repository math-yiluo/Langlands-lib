import Langlands.Representation.RankinSelberg.CentralBilinearVanishingProof
import Langlands.Representation.Smooth.IsotypicProjector
import Langlands.Representation.Smooth.Contragredient.Definitions
import Langlands.Representation.Twist.Definitions

/-! # Finite contragredient unramified-twist parameters -/

noncomputable section

namespace Langlands.RankinSelberg

universe uF uV uW uG

section Pairing

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- A twist equivalence to the smooth dual supplies a nonzero bilinear form
with the inverse character as its transformation factor. -/
theorem exists_twisted_bilinear_of_contragredient_equiv
    (π : Representation ℂ G V) (σ : Representation ℂ G W)
    (χ : G →* ℂˣ) (hπ : π.IsIrreducible)
    (e : (Langlands.twist χ π).Equiv (smoothContragredient σ)) :
    ∃ β : V →ₗ[ℂ] W →ₗ[ℂ] ℂ, β ≠ 0 ∧
      ∀ g v w, β (π g v) (σ g w) = (χ g : ℂ)⁻¹ * β v w := by
  let β : V →ₗ[ℂ] W →ₗ[ℂ] ℂ :=
    (smoothDualPairing σ).comp e.toLinearMap
  refine ⟨β, ?_, ?_⟩
  · intro hβ
    have hz (v : V) : v = 0 := by
      apply e.injective
      rw [map_zero]
      apply Subtype.ext
      ext w
      exact congrArg (fun b : V →ₗ[ℂ] W →ₗ[ℂ] ℂ => b v w) hβ
    let := hπ
    apply (bot_ne_top : (⊥ : Subrepresentation π) ≠ ⊤)
    apply Subrepresentation.toSubmodule_injective
    ext v
    rw [hz v]
    exact ⟨fun _ => Submodule.zero_mem _, fun _ => Submodule.zero_mem _⟩
  · intro g v w
    have hi : (χ g : ℂ) * β (π g v) (σ g w) = β v w := by
      change (((χ g : ℂ) • e (π g v)).val) (σ g w) = (e v).val w
      rw [← map_smul]
      change (e ((Langlands.twist χ π) g v)).val (σ g w) = (e v).val w
      calc
        (e ((Langlands.twist χ π) g v)).val (σ g w) =
            ((smoothContragredient σ) g (e v)).val (σ g w) :=
          congrArg (fun l : SmoothDual σ => l.val (σ g w))
            (Representation.IntertwiningMap.isIntertwining _ _ e.toIntertwiningMap g v)
        _ = (e v).val w := by
          change (e v).val (σ g⁻¹ (σ g w)) = (e v).val w
          rw [σ.inv_self_apply]
    calc
      β (π g v) (σ g w) =
          (χ g : ℂ)⁻¹ * ((χ g : ℂ) * β (π g v) (σ g w)) :=
        (inv_mul_cancel_left₀ (Units.ne_zero (χ g)) _).symm
      _ = (χ g : ℂ)⁻¹ * β v w := congrArg (fun z : ℂ => (χ g : ℂ)⁻¹ * z) hi

end Pairing

open GeneralLinear

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) {r : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
  (σ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) W)

/-- The parameters appearing in JPSS (8.1)(ii), with the smooth
contragredient on the second representation. -/
def IsContragredientTwistParameter (a : ℂ) : Prop :=
  ∃ u : ℂ,
    a = (F.canonicalTopologicalData.residueCardinality : ℂ) ^ (-u) ∧
    ∃ χ : F.Carrierˣ →* ℂˣ,
      (∀ x : F.Carrierˣ,
        (χ x : ℂ) =
          ((F.canonicalTopologicalData.normalizedAbs (x : F.Carrier) : ℝ) : ℂ) ^ (-u)) ∧
      letI := F.canonicalTopologicalData.topology
      haveI := F.canonicalTopologicalData.generalLinearTopologicalGroup (r + 1)
      Nonempty ((Langlands.twist (χ.comp determinant) π).Equiv (smoothContragredient σ))

/-- No parameter in the contragredient-twist set is zero. -/
theorem IsContragredientTwistParameter.ne_zero {a : ℂ}
    (ha : IsContragredientTwistParameter F π σ a) : a ≠ 0 := by
  obtain ⟨u, rfl, _⟩ := ha
  apply Complex.cpow_ne_zero_iff.mpr
  exact Or.inl (Nat.cast_ne_zero.mpr
    (lt_trans Nat.zero_lt_one F.canonicalTopologicalData.residueCardinality_gt_one).ne')

/-- For irreducible admissible representations, the possible unramified
parameters giving contragredience form a finite set. -/
theorem exists_finset_contragredientTwistParameters
    (hπ : π.IsIrreducible) (hσ : σ.IsIrreducible)
    (hπa : letI := F.canonicalTopologicalData.topology; IsAdmissible π)
    (hσa : letI := F.canonicalTopologicalData.topology; IsAdmissible σ) :
    ∃ A : Finset ℂ, ∀ a, a ∈ A ↔ IsContragredientTwistParameter F π σ a := by
  classical
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.generalLinearTopologicalGroup (r + 1)
  obtain ⟨E, hE⟩ := centralBilinearVanishing F T r V W π σ
    hπa (moduleFinite_asModule_of_isIrreducible π hπ)
    hσa (moduleFinite_asModule_of_isIrreducible σ hσ)
  have hbound {a : ℂ} (ha : IsContragredientTwistParameter F π σ a) :
      a ∈ E.image (fun z : ℂ => z⁻¹) := by
    obtain ⟨u, rfl, χ, hχ, ⟨e⟩⟩ := ha
    obtain ⟨β, hβ, hinv⟩ := exists_twisted_bilinear_of_contragredient_equiv
      π σ (χ.comp determinant) hπ e
    have hs : spectralPoint T.residueCardinality (-u) ∈ E := by
      by_contra hs
      apply hβ
      apply hE (-u) hs β
      intro g v w
      rw [hinv]
      congr 1
      rw [MonoidHom.comp_apply, hχ]
      change ((((T.normalizedAbs (Matrix.det g.val)) : ℝ) : ℂ) ^ (-u))⁻¹ =
        determinantWeight (normalizedAbsoluteValue T) g (-(-u))
      simp only [determinantWeight, normalizedAbsoluteValue_apply, neg_neg,
        Complex.cpow_neg, inv_inv]
    exact Finset.mem_image.mpr ⟨_, hs, by
      simp only [spectralPoint, neg_neg, Complex.cpow_neg]
      rfl⟩
  refine ⟨(E.image (fun z : ℂ => z⁻¹)).filter
    (IsContragredientTwistParameter F π σ), ?_⟩
  intro a
  exact ⟨fun ha => (Finset.mem_filter.mp ha).2,
    fun ha => Finset.mem_filter.mpr ⟨hbound ha, ha⟩⟩

end Langlands.RankinSelberg
