import Langlands.Geometry.Analytic.GeneralizedAffinoid.FiniteRadiusRealization
import Langlands.Geometry.Analytic.GeneralizedAffinoid.StrictBaseChangeRetraction
import Langlands.Geometry.Analytic.TateNoetherian
import Langlands.Geometry.Analytic.ClosedIdealsBanach

/-! # Noetherianity and closed ideals for general presented affinoids -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra

section Descent

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {L : Type v} [NormedField L] [IsUltrametricDist L]
  (A : PresentedAffinoidAlgebra K) (ι : K →+* L) (hι : ∀ a, ‖ι a‖ = ‖a‖)
  {c : Fin A.arity → L} (hc : ∀ j, ‖c j‖ = A.polyradius j)
  (π : L →+ K) (hπ : ∀ a x, π (ι a * x) = a * π x)
  {B : ℝ} (hB : 0 ≤ B) (hπB : ∀ x, ‖π x‖ ≤ B * ‖x‖) (hπ1 : π 1 = 1)

include hπ hB hπB hπ1 in
/-- The algebraic ideal extension contracts to the original ideal, using the
module-linear retraction rather than a flatness hypothesis. -/
theorem comap_map_strictBaseChangeHom (I : Ideal A) :
    Ideal.comap (strictBaseChangeHom A ι hι hc)
      (Ideal.map (strictBaseChangeHom A ι hι hc) I) = I := by
  apply le_antisymm
  · intro a ha
    have h := map_strictBaseChangeHom_le_strictBaseChangeDescentIdeal
      A ι hι hc π hπ hB hπB I ha 1
    simpa only [one_mul, strictBaseChangeRetraction_strictBaseChangeHom
      A ι hι hc π hπ hB hπB hπ1] using h
  · exact Ideal.le_comap_map

/-- Extension to a strict scalar extension embeds the full ideal lattice. -/
def strictBaseChangeIdealOrderEmbedding :
    Ideal A ↪o Ideal (strictBaseChange A ι hι hc) where
  toFun := Ideal.map (strictBaseChangeHom A ι hι hc)
  inj' := Function.LeftInverse.injective
    (comap_map_strictBaseChangeHom A ι hι hc π hπ hB hπB hπ1)
  map_rel_iff' := by
    intro I J
    constructor
    · intro h
      simpa only [comap_map_strictBaseChangeHom A ι hι hc π hπ hB hπB hπ1] using
        (Ideal.comap_mono h :
          Ideal.comap (strictBaseChangeHom A ι hι hc)
              (Ideal.map (strictBaseChangeHom A ι hι hc) I) ≤
            Ideal.comap (strictBaseChangeHom A ι hι hc)
              (Ideal.map (strictBaseChangeHom A ι hι hc) J))
    · exact Ideal.map_mono

end Descent

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- General positive-polyradius presented affinoids are Noetherian, including
over trivially valued coefficient fields and for the zero quotient. -/
instance (A : PresentedAffinoidAlgebra K) : IsNoetherianRing A := by
  obtain ⟨R⟩ := FiniteRadiusRealization.nonempty (K := K) A.polyradius
    A.polyradius.positive
  let e := strictBaseChangeIdealOrderEmbedding A R.ι R.norm_ι R.norm_c
    R.π R.π_ι_mul R.bound_pos.le R.norm_π_le R.π_one
  exact isNoetherian_mk (e.dual.wellFounded
    (IsNoetherian.wf (R := strictBaseChange A R.ι R.norm_ι R.norm_c)
      (M := strictBaseChange A R.ι R.norm_ι R.norm_c) inferInstance))

/-- Every ideal of a general presented affinoid is closed in its actual quotient
norm. A further radius ensures that the strict extension field is nontrivially
normed even when the original coefficient field has the trivial norm. -/
theorem isClosed_ideal (A : PresentedAffinoidAlgebra K) (I : Ideal A) :
    IsClosed (I : Set A) := by
  let t : Fin A.arity ⊕ Unit → ℝ := Sum.elim A.polyradius (fun _ => 2)
  obtain ⟨R⟩ := FiniteRadiusRealization.nonempty (K := K) t (by
    intro j
    cases j with
    | inl j => exact A.polyradius.positive j
    | inr j => norm_num [t])
  let : NontriviallyNormedField R.L :=
    { (inferInstance : NormedField R.L) with
      non_trivial := ⟨R.c (.inr ()), by rw [R.norm_c]; norm_num [t]⟩ }
  let c : Fin A.arity → R.L := fun j => R.c (.inl j)
  have hc : ∀ j, ‖c j‖ = A.polyradius j := fun j => R.norm_c (.inl j)
  let f := strictBaseChangeHom A R.ι R.norm_ι hc
  have hclosed : IsClosed (Ideal.map f I : Set (strictBaseChange A R.ι R.norm_ι hc)) :=
    isClosed_ideal_of_noetherian_banach (K := R.L) _
  have hf : Continuous f := AddMonoidHomClass.continuous_of_bound f 1
    (fun a => by simpa only [one_mul] using
      norm_strictBaseChangeHom_le A R.ι R.norm_ι hc a)
  have hI := comap_map_strictBaseChangeHom A R.ι R.norm_ι hc
    R.π R.π_ι_mul R.bound_pos.le R.norm_π_le R.π_one I
  exact hI ▸ hclosed.preimage hf

end Langlands.Analytic.PresentedAffinoidAlgebra
