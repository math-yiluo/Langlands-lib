import Langlands.BaseChange.ConcordantIntegralComparison
import Langlands.BaseChange.WeylTorusNormChart
import Langlands.Topology.LocallyProfiniteProof

/-! # Exact norm lifts on open cosets -/

noncomputable section

namespace Langlands.BaseChange.WeylTorus

open Langlands.JacquetLanglands Langlands.QuotientIntegration
open Filter Set _root_.Topology
open scoped RightActions

universe u v

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {E : Type v} [CommRing E] [Algebra F E] [TopologicalSpace E]
  [IsTopologicalRing E] [IsModuleTopology F E] {σ : E ≃ₐ[F] E} {l n : ℕ}

local notation "MF" => Matrix (Fin n) (Fin n) F
local notation "ME" => Matrix (Fin n) (Fin n) E

/-- A choice of exact lifts that locally has a strictly differentiable
representative in the unshifted matrix Lie coordinates of the rational torus.
The lift representative is normalized on the right by the inverse of its
value at the center. -/
theorem exists_normLifts_with_localDifferentials (T : WeylTorus F n) (hσ : IsCyclicAlgebra σ l)
    {γ : GeneralLinear n F} (hγ : IsRegularSemisimple γ) (hT : glCentralizer γ = T.val) :
    letI : NontriviallyNormedField F := LocalGalois.localNormedField F
    letI : CompleteSpace F := LocalGalois.localNormedField_complete F
    letI : Module.Finite F E := hσ.1
    letI : Module.Finite F ME := inferInstanceAs (Module.Finite F (Fin n → Fin n → E))
    letI : IsModuleTopology F ME := inferInstanceAs (IsModuleTopology F (Fin n → Fin n → E))
    letI : NormedAddCommGroup MF := inferInstanceAs (NormedAddCommGroup (Fin n → Fin n → F))
    letI : NormedSpace F MF := inferInstanceAs (NormedSpace F (Fin n → Fin n → F))
    letI : NormedRing ME := finiteAlgebraNormedRing F ME
    letI : NormedAlgebra F ME := finiteAlgebraNormedAlgebra F ME
    ∃ (lift : T.regularNormPoints σ l → T.points E),
      (∀ t, cyclicNorm σ l (lift t).val = baseChange F E n t.val.val) ∧
      ∀ t : T.regularNormPoints σ l,
        ∃ (f : weylTorusLie γ → ME) (s : weylTorusLie γ →L[F] ME),
          f 0 = 1 ∧ HasStrictFDerivAt f s 0 ∧
          ∀ᶠ x in 𝓝 (0 : weylTorusLie γ), ∃ y : T.regularNormPoints σ l,
            y.val.val.val = (1 + x.val) * t.val.val.val ∧
            f x * (lift t).val.val = (lift y).val.val := by
  classical
  let : NontriviallyNormedField F := LocalGalois.localNormedField F
  let : CompleteSpace F := LocalGalois.localNormedField_complete F
  let : Module.Finite F E := hσ.1
  let : Nontrivial E := Module.finrank_pos_iff.mp (hσ.2.1 ▸ hσ.pos)
  let : Module.Finite F ME := inferInstanceAs (Module.Finite F (Fin n → Fin n → E))
  let : IsModuleTopology F ME := inferInstanceAs (IsModuleTopology F (Fin n → Fin n → E))
  let : NormedAddCommGroup MF := inferInstanceAs (NormedAddCommGroup (Fin n → Fin n → F))
  let : NormedSpace F MF := inferInstanceAs (NormedSpace F (Fin n → Fin n → F))
  let : NormedRing ME := finiteAlgebraNormedRing F ME
  let : NormedAlgebra F ME := finiteAlgebraNormedAlgebra F ME
  let : T2Space (GeneralLinear n F) := LocalFieldTopology.generalLinear_t2Space F n
  let : LocallyCompactSpace (GeneralLinear n F) := LocalFieldTopology.generalLinear_locallyCompactSpace F n
  let : TotallyDisconnectedSpace (GeneralLinear n F) :=
    LocalFieldTopology.generalLinear_totallyDisconnectedSpace F n
  let : LocallyCompactSpace T.val := T.isClosed_val.isClosedEmbedding_subtypeVal.locallyCompactSpace
  let : Module.Finite F MF := inferInstanceAs (Module.Finite F (Fin n → Fin n → F))
  let S := weylTorusLie γ
  let coord := T.affineCoordinate hT
  have hcoord := T.isOpenEmbedding_affineCoordinate hT
  obtain ⟨L, e, h0, he0, hlift, hdiff⟩ := T.exists_affineNormChart hσ hγ hT
  have heT : 0 ∈ e.target := he0 ▸ e.map_source h0
  have hU : coord ⁻¹' e.target ∈ 𝓝 (1 : T.val) :=
    (hcoord.continuous.tendsto' 1 0 (T.affineCoordinate_one hT)).eventually
      (e.open_target.mem_nhds heT)
  obtain ⟨K, _, hK⟩ :=
    ((Langlands.Topology.LocallyProfiniteProof.vanDantzig T.val).1
      Langlands.Topology.isLocallyProfinite_of_mathlib).2 _ hU
  let N := T.normToRational hσ
  have hsec (k : K) : ∃ d : T.points E,
      d.val.val = 1 + L (e.symm (coord k.val)) ∧ N d = k.val := by
    have hk := hK k.property
    obtain ⟨d, hval, hn⟩ := hlift _ (e.map_target hk)
    exact ⟨d, hval, hcoord.injective (hn.symm.trans (e.right_inv hk))⟩
  choose a ha using hsec
  let R := T.regularNormPoints σ l
  let q := leftQuotientMap K.toSubgroup
  let q' : R → LeftQuotient K.toSubgroup := fun t => q t.val
  let Q := range q'
  let idx (t : R) : Q := ⟨q' t, mem_range_self t⟩
  let rep (z : Q) : R := z.property.choose
  have hre (z : Q) : q (rep z).val = z.val := z.property.choose_spec
  let k (t : R) : K := ⟨t.val * (rep (idx t)).val⁻¹,
    QuotientGroup.rightRel_apply.mp (Quotient.exact (hre (idx t)))⟩
  have hrepNorm (z : Q) : ∃ d : T.points E, N d = (rep z).val := by
    have hp := (rep z).property.2
    rw [← T.range_normToRational hσ] at hp
    exact hp
  choose b hb using hrepNorm
  let lift (t : R) : T.points E := a (k t) * b (idx t)
  have hn (t : R) : N (lift t) = t.val := by
    rw [show N (lift t) = N (a (k t)) * N (b (idx t)) from map_mul _ _ _,
      (ha (k t)).2, hb]
    change t.val * (rep (idx t)).val⁻¹ * (rep (idx t)).val = t.val
    group
  refine ⟨lift, fun t => (T.baseChange_normToRational hσ (lift t)).symm.trans
    (congrArg (fun z : T.val => baseChange F E n z.val) (hn t)), ?_⟩
  intro t
  let r := (k t).val.val.val
  have hr : Commute r γ.val := by
    have ht : (k t).val.val ∈ glCentralizer γ := hT.symm ▸ (k t).val.property
    rw [glCentralizer_eq_centralizer] at ht
    exact (show Commute (k t).val.val γ from Subgroup.mem_centralizer_singleton_iff.mp ht).map
      (Units.coeHom _)
  let j : S →ₗ[F] S := ((LinearMap.mulRight F r).comp S.subtype).codRestrict S fun x =>
    (mem_ker_adjointDefect_iff γ _).mpr
      (((mem_ker_adjointDefect_iff γ _).mp x.property).mul_left hr)
  let J : S →L[F] S := j.toContinuousLinearMap
  let x₀ := coord (k t).val
  let f : S → ME := fun x =>
    (1 + L (e.symm (x₀ + J x))) * (b (idx t)).val.val * ((lift t).val⁻¹ : GeneralLinear n E).val
  obtain ⟨D, hD⟩ := hdiff x₀ (hK (k t).property)
  have hD' : HasStrictFDerivAt (fun x : S => e.symm (x₀ + J x)) (D.comp J) 0 := by
    have hJ := J.hasStrictFDerivAt (x := (0 : S)) |>.const_add (c := x₀)
    have h0' : x₀ + J 0 = x₀ := by simp
    have hDs : HasStrictFDerivAt e.symm D (x₀ + J 0) := h0'.symm ▸ hD
    exact hDs.comp 0 hJ
  have hf' := ((L.hasStrictFDerivAt.comp (0 : S) hD').const_add (c := (1 : ME))).mul_const'
    (b (idx t)).val.val |>.mul_const' ((lift t).val⁻¹ : GeneralLinear n E).val
  have hf0 :
      (1 + L (e.symm (coord (k t).val))) * (b (idx t)).val.val = (lift t).val.val := by
    rw [← (ha (k t)).1]
    rfl
  refine ⟨f, _, ?_, hf', ?_⟩
  · change (1 + L (e.symm (x₀ + J 0))) * (b (idx t)).val.val *
      ((lift t).val⁻¹ : GeneralLinear n E).val = 1
    rw [map_zero, add_zero, hf0]
    exact (lift t).val.val_inv
  let U : Set T.val := (K : Set T.val) ∩ (fun h : T.val => h * t.val) ⁻¹' R
  have hU : IsOpen U := K.isOpen.inter ((T.isOpen_regularNormPoints hσ).preimage
    (continuous_id.mul_const t.val))
  have h1 : (1 : T.val) ∈ U := ⟨K.one_mem, by simpa only [mem_preimage, one_mul] using t.property⟩
  have hB : coord '' U ∈ 𝓝 (0 : S) :=
    (hcoord.isOpenMap _ hU).mem_nhds ⟨1, h1, T.affineCoordinate_one hT⟩
  filter_upwards [hB] with x hx
  obtain ⟨h, hh, hcoordx⟩ := hx
  let y : R := ⟨h * t.val, hh.2⟩
  have hidx : idx y = idx t := by
    apply Subtype.ext
    change q (h * t.val) = q t.val
    apply Quotient.sound
    apply QuotientGroup.rightRel_apply.mpr
    rw [show t.val * (h * t.val)⁻¹ = h⁻¹ by group]
    exact K.inv_mem hh.1
  have hval : h.val.val = 1 + x.val := by
    have hh := congrArg Subtype.val hcoordx
    change h.val.val - 1 = x.val at hh
    rw [← hh]
    abel
  have hy : y.val.val.val = (1 + x.val) * t.val.val.val := by
    change h.val.val * t.val.val.val = _
    rw [hval]
  have hkval : (k y).val = h * (k t).val := by
    change y.val * (rep (idx y)).val⁻¹ = h * (t.val * (rep (idx t)).val⁻¹)
    rw [hidx]
    exact mul_assoc _ _ _
  have hkcoord : coord (k y).val = x₀ + J x := by
    rw [hkval]
    apply Subtype.ext
    change h.val.val * r - 1 = (r - 1) + x.val * r
    rw [hval, add_mul, one_mul]
    abel
  refine ⟨y, hy, ?_⟩
  change ((1 + L (e.symm (x₀ + J x))) * (b (idx t)).val.val *
    ((lift t).val⁻¹ : GeneralLinear n E).val) * (lift t).val.val =
      (a (k y)).val.val * (b (idx y)).val.val
  have hi : ((lift t).val⁻¹ : GeneralLinear n E).val * (lift t).val.val = 1 :=
    (lift t).val.inv_val
  rw [← hkcoord, ← (ha (k y)).1, hidx, mul_assoc _ ((lift t).val⁻¹ : GeneralLinear n E).val,
    hi, mul_one]

end Langlands.BaseChange.WeylTorus
