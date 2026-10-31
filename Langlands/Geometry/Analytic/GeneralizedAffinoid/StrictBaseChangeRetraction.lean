import Langlands.Geometry.Analytic.GeneralizedAffinoid.StrictBaseChange

/-! # Bounded quotient descent for strict base change -/

noncomputable section

universe u v

namespace Langlands.Analytic

namespace PresentedAffinoidAlgebra

open GeneralizedTateAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {L : Type v} [NormedField L] [IsUltrametricDist L]
  (P : PresentedAffinoidAlgebra K) (ι : K →+* L) (hι : ∀ a, ‖ι a‖ = ‖a‖)
  {c : Fin P.arity → L} (hc : ∀ i, ‖c i‖ = P.polyradius i)
  (π : L →+ K) (hπ : ∀ a x, π (ι a * x) = a * π x)
  {D : ℝ} (hD : 0 ≤ D) (hπD : ∀ x, ‖π x‖ ≤ D * ‖x‖)

/-- The additive map from the strict base change back to `P` induced by the
coefficientwise descent of representatives. -/
def strictBaseChangeRetraction : strictBaseChange P ι hι hc →+ P :=
  QuotientAddGroup.lift (strictBaseChange P ι hι hc).ideal.toAddSubgroup
    ((presentationMap K P).toAlgHom.toRingHom.toAddMonoidHom.comp
      (descend P.polyradius hc π hπD))
    (fun x hx => by
      rw [AddMonoidHom.mem_ker]
      change presentationMap K P (descend P.polyradius hc π hπD x) = 0
      rw [presentationMap_eq_zero_iff]
      exact descend_mem_of_mem_closure_map P.polyradius ι hc hι π hD hπD hπ P.ideal
        P.ideal_closed hx)

/-- The retraction is computed by descending any representative. -/
theorem strictBaseChangeRetraction_presentationMap (g : StrictTateAlgebra (Fin P.arity) L) :
    strictBaseChangeRetraction P ι hι hc π hπ hD hπD
        (PresentedStrictAffinoidAlgebra.presentationMap L (strictBaseChange P ι hι hc) g) =
      presentationMap K P (descend P.polyradius hc π hπD g) :=
  rfl

/-- The retraction is bounded for the two quotient norms. -/
theorem norm_strictBaseChangeRetraction_le (b : strictBaseChange P ι hι hc) :
    ‖strictBaseChangeRetraction P ι hι hc π hπ hD hπD b‖ ≤ D * ‖b‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hD1 : 0 < D + 1 := by linarith
  obtain ⟨g, rfl, hg⟩ : ∃ g : StrictTateAlgebra (Fin P.arity) L,
      PresentedStrictAffinoidAlgebra.presentationMap L (strictBaseChange P ι hι hc) g = b ∧
        ‖g‖ < ‖b‖ + ε / (D + 1) :=
    PresentedStrictAffinoidAlgebra.exists_representative_norm_lt L
      (strictBaseChange P ι hι hc) b (div_pos hε hD1)
  rw [strictBaseChangeRetraction_presentationMap]
  calc ‖presentationMap K P (descend P.polyradius hc π hπD g)‖
      ≤ ‖descend P.polyradius hc π hπD g‖ := norm_presentationMap_le K P _
    _ ≤ D * ‖g‖ := norm_descend_le P.polyradius hc π hD hπD g
    _ ≤ D * (‖PresentedStrictAffinoidAlgebra.presentationMap L
          (strictBaseChange P ι hι hc) g‖ + ε / (D + 1)) :=
        mul_le_mul_of_nonneg_left hg.le hD
    _ ≤ D * ‖PresentedStrictAffinoidAlgebra.presentationMap L
          (strictBaseChange P ι hι hc) g‖ + ε := by
        rw [mul_add]
        have h : D * (ε / (D + 1)) ≤ ε := by
          rw [← mul_div_assoc, div_le_iff₀ hD1]
          nlinarith
        linarith

/-- The retraction is a left inverse of the base-change homomorphism. -/
theorem strictBaseChangeRetraction_strictBaseChangeHom (hπ1 : π 1 = 1) (a : P) :
    strictBaseChangeRetraction P ι hι hc π hπ hD hπD (strictBaseChangeHom P ι hι hc a) = a := by
  obtain ⟨f, rfl⟩ := presentationMap_surjective K P a
  rw [strictBaseChangeHom_presentationMap, strictBaseChangeRetraction_presentationMap,
    descend_baseChange P.polyradius ι hc hι π hπD hπ hπ1]

/-- The retraction is linear over the image of the base-change homomorphism. -/
theorem strictBaseChangeRetraction_strictBaseChangeHom_mul (a : P)
    (b : strictBaseChange P ι hι hc) :
    strictBaseChangeRetraction P ι hι hc π hπ hD hπD (strictBaseChangeHom P ι hι hc a * b) =
      a * strictBaseChangeRetraction P ι hι hc π hπ hD hπD b := by
  obtain ⟨f, rfl⟩ := presentationMap_surjective K P a
  obtain ⟨g, rfl⟩ : ∃ g : StrictTateAlgebra (Fin P.arity) L,
      PresentedStrictAffinoidAlgebra.presentationMap L (strictBaseChange P ι hι hc) g = b :=
    PresentedStrictAffinoidAlgebra.presentationMap_surjective L (strictBaseChange P ι hι hc) b
  rw [strictBaseChangeHom_presentationMap,
    show PresentedStrictAffinoidAlgebra.presentationMap L (strictBaseChange P ι hι hc)
          (baseChange P.polyradius ι hc hι f) *
        PresentedStrictAffinoidAlgebra.presentationMap L (strictBaseChange P ι hι hc) g =
      PresentedStrictAffinoidAlgebra.presentationMap L (strictBaseChange P ι hι hc)
        (baseChange P.polyradius ι hc hι f * g) from (map_mul _ _ _).symm,
    strictBaseChangeRetraction_presentationMap, strictBaseChangeRetraction_presentationMap,
    descend_baseChange_mul P.polyradius ι hc hι π hπD hπ, map_mul]

/-- The retraction preserves the unit. -/
theorem strictBaseChangeRetraction_one (hπ1 : π 1 = 1) :
    strictBaseChangeRetraction P ι hι hc π hπ hD hπD 1 = 1 := by
  simpa using strictBaseChangeRetraction_strictBaseChangeHom P ι hι hc π hπ hD hπD hπ1 1

include hπ hD hπD in
/-- In particular the base-change homomorphism is injective. -/
theorem strictBaseChangeHom_injective (hπ1 : π 1 = 1) :
    Function.Injective (strictBaseChangeHom P ι hι hc) :=
  Function.LeftInverse.injective
    (strictBaseChangeRetraction_strictBaseChangeHom P ι hι hc π hπ hD hπD hπ1)

/-- The ideal of those `b` in the strict base change whose multiples all retract into
the ideal `I` of `P`. -/
def strictBaseChangeDescentIdeal (I : Ideal P) : Ideal (strictBaseChange P ι hι hc) where
  carrier := {b | ∀ g, strictBaseChangeRetraction P ι hι hc π hπ hD hπD (g * b) ∈ I}
  add_mem' := fun {x y} hx hy g => by
    rw [mul_add, map_add]
    exact I.add_mem (hx g) (hy g)
  zero_mem' := fun g => by
    rw [mul_zero, map_zero]
    exact I.zero_mem
  smul_mem' := fun a x hx g => by
    rw [smul_eq_mul, ← mul_assoc]
    exact hx (g * a)

theorem mem_strictBaseChangeDescentIdeal (I : Ideal P) (b : strictBaseChange P ι hι hc) :
    b ∈ strictBaseChangeDescentIdeal P ι hι hc π hπ hD hπD I ↔
      ∀ g, strictBaseChangeRetraction P ι hι hc π hπ hD hπD (g * b) ∈ I :=
  Iff.rfl

/-- The descent ideal of `I` contains the ideal generated by the image of `I`. -/
theorem map_strictBaseChangeHom_le_strictBaseChangeDescentIdeal (I : Ideal P) :
    Ideal.map (strictBaseChangeHom P ι hι hc) I ≤
      strictBaseChangeDescentIdeal P ι hι hc π hπ hD hπD I := by
  apply Ideal.map_le_iff_le_comap.mpr
  intro a ha g
  rw [mul_comm, strictBaseChangeRetraction_strictBaseChangeHom_mul]
  exact I.mul_mem_right _ ha

include hπ hD hπD in
/-- A proper ideal of `P` generates a proper ideal of the strict base change. -/
theorem map_strictBaseChangeHom_ne_top (hπ1 : π 1 = 1) {I : Ideal P} (hI : I ≠ ⊤) :
    Ideal.map (strictBaseChangeHom P ι hι hc) I ≠ ⊤ := by
  intro htop
  have h1 : (1 : strictBaseChange P ι hι hc) ∈
      strictBaseChangeDescentIdeal P ι hι hc π hπ hD hπD I :=
    map_strictBaseChangeHom_le_strictBaseChangeDescentIdeal P ι hι hc π hπ hD hπD I
      (htop ▸ Submodule.mem_top)
  have h := h1 1
  rw [mul_one, strictBaseChangeRetraction_one P ι hι hc π hπ hD hπD hπ1] at h
  exact hI ((Ideal.eq_top_iff_one I).mpr h)

include hπ hD hπD in
/-- An ideal of `P` generates the unit ideal after base change only if it is already
the unit ideal. -/
theorem map_strictBaseChangeHom_eq_top_iff (hπ1 : π 1 = 1) (I : Ideal P) :
    Ideal.map (strictBaseChangeHom P ι hι hc) I = ⊤ ↔ I = ⊤ := by
  refine ⟨fun h => ?_, fun h => h ▸ Ideal.map_top _⟩
  by_contra hI
  exact map_strictBaseChangeHom_ne_top P ι hι hc π hπ hD hπD hπ1 hI h

include hπ hD hπD in
/-- An element of `P` is a unit exactly when its base change is a unit. -/
theorem isUnit_strictBaseChangeHom_iff (hπ1 : π 1 = 1) (a : P) :
    IsUnit (strictBaseChangeHom P ι hι hc a) ↔ IsUnit a := by
  refine ⟨fun h => ?_, fun h => h.map _⟩
  obtain ⟨b, hb⟩ := h.exists_right_inv
  apply IsUnit.of_mul_eq_one (strictBaseChangeRetraction P ι hι hc π hπ hD hπD b)
  rw [← strictBaseChangeRetraction_strictBaseChangeHom_mul, hb,
    strictBaseChangeRetraction_one P ι hι hc π hπ hD hπD hπ1]

end PresentedAffinoidAlgebra

end Langlands.Analytic
