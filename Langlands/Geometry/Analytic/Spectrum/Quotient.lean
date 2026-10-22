import Langlands.Geometry.Analytic.Spectrum.Properties
import Langlands.Geometry.Analytic.Spectrum.Quotient.Statement

/-! # Spectra of actual closed-ideal quotients -/

noncomputable section

universe u v

namespace Langlands.Analytic

namespace BanachSpectrum

variable {A : Type u} [NormedCommRing A]

theorem isClosed_zeroLocus (I : Ideal A) : IsClosed (zeroLocus I) := by
  change IsClosed {x : BanachSpectrum A | ∀ a, a ∈ I → x a = 0}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter fun a : A => isClosed_iInter fun _ =>
    isClosed_eq (evaluation a).continuous continuous_const

private theorem eq_of_sub_mem_kernel (x : BanachSpectrum A) {a b : A}
    (h : a - b ∈ x.kernel) : x a = x b := by
  change x.toMulRingSeminorm (a - b) = 0 at h
  apply le_antisymm
  · have hle := map_add_le_add x.toMulRingSeminorm (a - b) b
    simpa only [sub_add_cancel, h, zero_add] using hle
  · have h' : x.toMulRingSeminorm (b - a) = 0 := by
      rw [← neg_sub a b, map_neg_eq_map, h]
    have hle := map_add_le_add x.toMulRingSeminorm (b - a) a
    simpa only [sub_add_cancel, h', zero_add] using hle

variable (I : Ideal A) [IsClosed (I : Set A)]

private def quotientValue (x : BanachSpectrum A) (hx : I ≤ x.kernel) :
    A ⧸ I → ℝ :=
  Quotient.lift (fun a => x a) (fun _ _ h =>
    eq_of_sub_mem_kernel x (hx ((Ideal.Quotient.eq).mp (Quotient.sound h))))

omit [IsClosed (I : Set A)] in
private theorem quotientValue_mk (x : BanachSpectrum A) (hx : I ≤ x.kernel) (a : A) :
    quotientValue I x hx (Ideal.Quotient.mk I a) = x a := rfl

/-- A seminorm annihilating the ideal descends to the actual quotient.
The norm bound follows from representatives arbitrarily close to the quotient norm. -/
def descend (x : BanachSpectrum A) (hx : I ≤ x.kernel) : BanachSpectrum (A ⧸ I) where
  toFun := quotientValue I x hx
  map_zero' := map_zero x.toMulRingSeminorm
  map_one' := map_one x.toMulRingSeminorm
  map_mul' := by
    intro a b
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact map_mul x.toMulRingSeminorm a b
  add_le' := by
    intro a b
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact map_add_le_add x.toMulRingSeminorm a b
  neg' := by
    intro a
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact map_neg_eq_map x.toMulRingSeminorm a
  le_norm a := by
    change quotientValue I x hx a ≤ ‖a‖
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨b, hb, hnorm⟩ := Ideal.Quotient.norm_mk_lt a hε
    calc
      quotientValue I x hx a = x b := by rw [← hb, quotientValue_mk]
      _ ≤ ‖a‖ + ε := (x.le_norm b).trans hnorm.le

theorem comap_quotient_injective :
    Function.Injective (comap (quotientHom I)) := by
  intro x y h
  apply ext
  intro a
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact congrArg (fun z : BanachSpectrum A => z a) h

theorem comap_quotient_closedEmbedding :
    Topology.IsClosedEmbedding (comap (quotientHom I)) :=
  (comapContinuous (quotientHom I)).continuous.isClosedEmbedding
    (comap_quotient_injective I)

theorem range_comap_quotient :
    Set.range (comap (quotientHom I)) = zeroLocus I := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩ a ha
    change y.toMulRingSeminorm (Ideal.Quotient.mk I a) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]
  · intro hx
    refine ⟨descend I x hx, ?_⟩
    apply ext
    intro a
    rfl

end BanachSpectrum

/-- The closed-ideal quotient spectrum is precisely its ideal zero locus,
with unique descent of each annihilating seminorm. -/
theorem quotientSpectrumProperties : QuotientSpectrumStatement := by
  intro A _
  refine ⟨fun I => BanachSpectrum.isClosed_zeroLocus I, fun I _ => ?_⟩
  refine ⟨BanachSpectrum.comap_quotient_closedEmbedding I,
    BanachSpectrum.range_comap_quotient I, ?_⟩
  intro x hx
  refine ⟨BanachSpectrum.descend I x hx, fun _ => rfl, ?_⟩
  intro y hy
  apply BanachSpectrum.ext
  intro a
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact hy a

end Langlands.Analytic
