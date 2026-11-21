import Langlands.Global.AdelicEisensteinConjugateCompactStatement

/-! # Eisenstein operators for conjugate Iwasawa compacts -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj Pointwise

set_option autoImplicit false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme

section Iwasawa

variable {F : Type u} [Field F] [NumberField F]
  {G P : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  {p : P ⟶ G} {K : Subgroup (AdelicGroupPoints F G)}
  (hK : IsIwasawaCompact p K) (t : AdelicGroupPoints F G)

include hK in
/-- Every conjugate of a compact with Iwasawa coverage also has coverage. -/
theorem IsIwasawaCompact.conjInv :
    IsIwasawaCompact p (K.map (MulAut.conj t⁻¹).toMonoidHom) := by
  refine ⟨?_, Set.eq_univ_of_forall fun g => ?_⟩
  · rw [Subgroup.coe_map]
    have hconj : ((MulAut.conj t⁻¹).toMonoidHom : AdelicGroupPoints F G → AdelicGroupPoints F G) =
        fun g => t⁻¹ * g * t := by
      funext g
      change t⁻¹ * g * (t⁻¹)⁻¹ = _
      rw [inv_inv]
    rw [hconj]
    exact hK.isCompact.image ((continuous_const.mul continuous_id).mul continuous_const)
  · obtain ⟨a, k, hk, ha⟩ := hK.exists_eq (g * t⁻¹)
    obtain ⟨b, v, hv, hb⟩ := hK.exists_eq t⁻¹
    refine ⟨_, ⟨a * b⁻¹, rfl⟩, t⁻¹ * (v⁻¹ * k) * t,
      ⟨v⁻¹ * k, K.mul_mem (K.inv_mem hv) hk, ?_⟩, ?_⟩
    · change t⁻¹ * (v⁻¹ * k) * (t⁻¹)⁻¹ = _
      rw [inv_inv]
    · simp only [map_mul, map_inv]
      calc
        _ = map F P G p a * ((map F P G p b)⁻¹ * t⁻¹ * v⁻¹) * k * t := by group
        _ = map F P G p a * k * t := by rw [← hb]; group
        _ = g := by rw [ha]; group

variable [IsAffine P.X.left] [IsClosedImmersion p.hom.hom.left]
  (hK' : IsIwasawaCompact p (K.map (MulAut.conj t⁻¹).toMonoidHom))

/-- Right translation by the conjugating element adds a single height
increment when the compact is conjugated. -/
theorem IsIwasawaCompact.height_mul_conjInv (g : AdelicGroupPoints F G) :
    hK'.height (g * t) = hK.height g + hK'.height t := by
  obtain ⟨a, k, hk, rfl⟩ := hK.exists_eq g
  have hk' : t⁻¹ * k * t ∈ K.map (MulAut.conj t⁻¹).toMonoidHom :=
    ⟨k, hk, by change t⁻¹ * k * (t⁻¹)⁻¹ = _; rw [inv_inv]⟩
  rw [show map F P G p a * k * t = (map F P G p a * t) * (t⁻¹ * k * t) by group,
    hK'.height_mul_right _ hk', hK'.height_map_mul, hK.height_eq hk rfl]

/-- The height power turns this increment into a scalar factor. -/
theorem IsIwasawaCompact.heightPower_mul_conjInv
    (lam : ComplexCharacterParameter F P) (g : AdelicGroupPoints F G) :
    hK'.heightPower lam (g * t) = hK.heightPower lam g * hK'.heightPower lam t := by
  simp only [IsIwasawaCompact.heightPower, hK.height_mul_conjInv t hK', map_add, Complex.exp_add]

private theorem parameterTwist_mul_conjInv
    (φ : AdelicGroupPoints F G → ℂ) (lam : ComplexCharacterParameter F P) (g : AdelicGroupPoints F G) :
    hK'.parameterTwist φ lam (g * t) =
      hK'.heightPower lam t * hK.parameterTwist (fun x => φ (x * t)) lam g := by
  simp only [IsIwasawaCompact.parameterTwist, hK.heightPower_mul_conjInv t hK']
  ring

/-- The actual rational coset sums transform termwise under the compact conjugation. -/
theorem IsIwasawaCompact.eisensteinSeries_mul_conjInv
    (φ : AdelicGroupPoints F G → ℂ) (lam : ComplexCharacterParameter F P) (g : AdelicGroupPoints F G) :
    hK'.eisensteinSeries φ lam (g * t) =
      hK'.heightPower lam t * hK.eisensteinSeries (fun x => φ (x * t)) lam g := by
  unfold IsIwasawaCompact.eisensteinSeries
  rw [← tsum_mul_left]
  apply tsum_congr
  intro x
  unfold IsIwasawaCompact.eisensteinTerm
  rw [← mul_assoc, parameterTwist_mul_conjInv hK t hK']

variable [LocallyOfFiniteType G.X.hom]
  {U V : GroupScheme (Spec (CommRingCat.of F))} [IsAffine V.X.left]
  (iU : U ⟶ P) (j : V ⟶ G) [IsClosedImmersion j.hom.hom.left]
  (w : rationalPoints G)

private theorem intertwiningIntegral_mul_conjInv
    (φ : AdelicGroupPoints F G → ℂ) (lam : ComplexCharacterParameter F P) (g : AdelicGroupPoints F G) :
    hK'.intertwiningIntegral iU j w φ lam (g * t) =
      hK'.heightPower lam t * hK.intertwiningIntegral iU j w (fun x => φ (x * t)) lam g := by
  unfold IsIwasawaCompact.intertwiningIntegral
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  unfold IsIwasawaCompact.intertwiningIntegrand
  rw [← mul_assoc, parameterTwist_mul_conjInv hK t hK']

end Iwasawa

end Langlands.Global.AdelicGroupPoints

namespace Langlands.Global

open Langlands.GroupScheme AdelicGroupPoints

/-- Right translation and the height factors give the simultaneous transport
of the two Eisenstein series and the intertwining operator. -/
theorem eisensteinConjugateCompactTransport : EisensteinConjugateCompactTransportStatement.{u} := by
  intro F _ _ G P M U Q M' V _ _ _ _ _ p _ iU l q _ iV _ c proj w K hP hQ t
  let hP' := hP.conjInv t
  let hQ' := hQ.conjInv t
  refine ⟨hP', hQ', fun φ lam g =>
    ⟨hP.eisensteinSeries_mul_conjInv t hP' φ lam g,
      hQ.eisensteinSeries_mul_conjInv t hQ' φ _ g, ?_⟩⟩
  simp only [IsIwasawaCompact.intertwiningOperator, hQ.heightPower_mul_conjInv t hQ',
    intertwiningIntegral_mul_conjInv hP t hP']
  ring

end Langlands.Global
