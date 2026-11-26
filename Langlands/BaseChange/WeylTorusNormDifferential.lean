import Langlands.BaseChange.WeylTorusNormSections

/-! # Derivatives of exact lifts in rational torus coordinates -/

noncomputable section

namespace Langlands.BaseChange

open Langlands.JacquetLanglands
open Filter Set _root_.Topology
open scoped RightActions

universe u v

variable {F : Type u} [Field F] {E : Type v} [CommRing E] [Algebra F E]
  {σ : E ≃ₐ[F] E} {l n : ℕ}

local notation "MF" => Matrix (Fin n) (Fin n) F
local notation "ME" => Matrix (Fin n) (Fin n) E

private theorem cyclicNorm_val_eq_listRange (d : GeneralLinear n E) :
    (cyclicNorm σ l d).val = ((List.range l).map fun k => matrixEntrywiseAut (σ ^ k) d.val).prod := by
  change (Units.coeHom ME) (((List.range l).map fun k => entrywiseAut (σ ^ k) n d).prod) = _
  rw [map_list_prod, List.map_map]
  rfl

theorem WeylTorus.lie_eq_of_regular (T : WeylTorus F n) {a : GeneralLinear n F}
    (ha : IsRegularSemisimple a) (hT : glCentralizer a = T.val)
    {t : T.val} (ht : t ∈ T.regularPoints) : weylTorusLie a = weylTorusLie t.val := by
  have hta : Commute t.val.val a.val := by
    have h : t.val ∈ glCentralizer a := hT.symm ▸ t.property
    rw [glCentralizer_eq_centralizer] at h
    exact (show Commute t.val a from Subgroup.mem_centralizer_singleton_iff.mp h).map
      (Units.coeHom _)
  obtain ⟨v, hv⟩ := regularCyclicBasis F n a.val ha
  obtain ⟨z, hz⟩ := regularCyclicBasis F n t.val.val ht
  ext x
  simp only [mem_ker_adjointDefect_iff]
  exact ⟨fun h => commute_of_commute_cyclicBasisMatrix hv h hta,
    fun h => commute_of_commute_cyclicBasisMatrix hz h hta.symm⟩

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [TopologicalSpace E] [IsTopologicalRing E] [IsModuleTopology F E]

/-- Differentiating a normalized local exact lift gives a section of the
additive trace with values in the extended matrix centralizer. -/
theorem WeylTorus.normLiftDifferential (T : WeylTorus F n) (hσ : IsCyclicAlgebra σ l)
    (lift : T.regularNormPoints σ l → T.points E)
    (hlift : ∀ t, cyclicNorm σ l (lift t).val = baseChange F E n t.val.val)
    {a : GeneralLinear n F} (t : T.regularNormPoints σ l) :
    letI : NontriviallyNormedField F := LocalGalois.localNormedField F
    letI : CompleteSpace F := LocalGalois.localNormedField_complete F
    letI : Module.Finite F E := hσ.1
    letI : Module.Finite F ME := inferInstanceAs (Module.Finite F (Fin n → Fin n → E))
    letI : IsModuleTopology F ME := inferInstanceAs (IsModuleTopology F (Fin n → Fin n → E))
    letI : NormedAddCommGroup MF := inferInstanceAs (NormedAddCommGroup (Fin n → Fin n → F))
    letI : NormedSpace F MF := inferInstanceAs (NormedSpace F (Fin n → Fin n → F))
    letI : NormedRing ME := finiteAlgebraNormedRing F ME
    letI : NormedAlgebra F ME := finiteAlgebraNormedAlgebra F ME
    ∀ (f : weylTorusLie a → ME) (s : weylTorusLie a →L[F] ME), f 0 = 1 →
      HasStrictFDerivAt f s 0 →
      (∀ᶠ x in 𝓝 (0 : weylTorusLie a), ∃ y : T.regularNormPoints σ l,
        y.val.val.val = (1 + x.val) * t.val.val.val ∧
        f x * (lift t).val.val = (lift y).val.val) →
      ∀ x : weylTorusLie a,
        Commute (s x) (baseChange F E n t.val.val).val ∧
        (∑ i : Fin l, matrixEntrywiseAut (σ ^ (i : ℕ)) (s x)) = weylTorusLieInclusion a x := by
  let : Module.Finite F E := hσ.1
  let : IsReduced E := hσ.2.2.1
  let : Nontrivial E := Module.finrank_pos_iff.mp (hσ.2.1 ▸ hσ.pos)
  let : NontriviallyNormedField F := LocalGalois.localNormedField F
  let : CompleteSpace F := LocalGalois.localNormedField_complete F
  let : Module.Finite F ME := inferInstanceAs (Module.Finite F (Fin n → Fin n → E))
  let : IsModuleTopology F ME := inferInstanceAs (IsModuleTopology F (Fin n → Fin n → E))
  let : NormedAddCommGroup MF := inferInstanceAs (NormedAddCommGroup (Fin n → Fin n → F))
  let : NormedSpace F MF := inferInstanceAs (NormedSpace F (Fin n → Fin n → F))
  let : NormedRing ME := finiteAlgebraNormedRing F ME
  let : NormedAlgebra F ME := finiteAlgebraNormedAlgebra F ME
  let : Module.Finite F MF := inferInstanceAs (Module.Finite F (Fin n → Fin n → F))
  intro f s h0 hf he
  let S := weylTorusLie a
  let g := baseChange F E n t.val.val
  let P := (weylTorusLieInclusion (E := E) a).toContinuousLinearMap
  let N := T.normToRational hσ
  have hN (y : T.regularNormPoints σ l) : N (lift y) = y.val := by
    apply Subtype.ext
    apply Units.ext
    exact matrixBaseChangeLinear_injective (congrArg (fun u : GeneralLinear n E => u.val)
      ((T.baseChange_normToRational hσ (lift y)).trans (hlift y)))
  let k (y : T.regularNormPoints σ l) : T.points E := lift y * (lift t)⁻¹
  have hlocal : ∀ᶠ x in 𝓝 (0 : S), ∃ y : T.regularNormPoints σ l,
      f x = (k y).val.val ∧ (cyclicNorm σ l (k y).val).val = 1 + P x := by
    filter_upwards [he] with x hx
    obtain ⟨y, hy, hfy⟩ := hx
    refine ⟨y, ?_, ?_⟩
    · have hh := congrArg (· * ((lift t).val⁻¹ : GeneralLinear n E).val) hfy
      change f x = (lift y).val.val * ((lift t).val⁻¹ : GeneralLinear n E).val
      rw [mul_assoc, show (lift t).val.val * ((lift t).val⁻¹ : GeneralLinear n E).val = 1 from
        (lift t).val.val_inv, mul_one] at hh
      exact hh
    · have hnorm : cyclicNorm σ l (k y).val = baseChange F E n (y.val * t.val⁻¹).val := by
        rw [← T.baseChange_normToRational hσ (k y)]
        change baseChange F E n (N (lift y * (lift t)⁻¹)).val = _
        rw [map_mul, map_inv, hN, hN]
      rw [hnorm]
      change (algebraMap F E).mapMatrix
        (y.val.val.val * (t.val.val⁻¹ : GeneralLinear n F).val) = _
      rw [hy, mul_assoc, show t.val.val.val * (t.val.val⁻¹ : GeneralLinear n F).val = 1 from
        t.val.val.val_inv, mul_one, map_add, map_one]
      rfl
  have hcomm : (fun x : S => f x * g.val) =ᶠ[𝓝 (0 : S)] (fun x : S => g.val * f x) := by
    filter_upwards [hlocal] with x hx
    obtain ⟨y, hy, _⟩ := hx
    rw [hy]
    have hh : (k y).val ∈ Subgroup.centralizer {g} :=
      (T.points_eq_centralizer (E := E) (γ := t.val) t.property.1) ▸ (k y).property
    exact congrArg (fun u : GeneralLinear n E => u.val) (Subgroup.mem_centralizer_singleton_iff.mp hh)
  have dcomm := (hf.mul_const' g.val).hasFDerivAt.unique
    (((hf.const_mul g.val).congr_of_eventuallyEq hcomm.symm).hasFDerivAt)
  let C (i : ℕ) : ME →L[F] ME := (matrixEntrywiseAut (σ ^ i)).toLinearMap.toContinuousLinearMap
  let h : S → ME := fun x => ((List.range l).map fun k => C k (f x)).prod
  have hd : HasStrictFDerivAt h (∑ i ∈ Finset.range l, (C i).comp s) 0 :=
    hasStrictFDerivAt_listRange_prod_at_one _ _ l
      (fun i => (C i).hasStrictFDerivAt.comp 0 hf)
      (fun i => by rw [h0]; exact map_one (matrixEntrywiseAut (σ ^ i)))
  have hnorm : h =ᶠ[𝓝 (0 : S)] fun x => 1 + P x := by
    filter_upwards [hlocal] with x hx
    obtain ⟨y, hy, hn⟩ := hx
    change ((List.range l).map fun k => matrixEntrywiseAut (σ ^ k) (f x)).prod = _
    rw [hy, ← cyclicNorm_val_eq_listRange (σ := σ) (l := l), hn]
  have htrace := (hd.congr_of_eventuallyEq hnorm).hasFDerivAt.unique
    (P.hasStrictFDerivAt.const_add (c := (1 : ME))).hasFDerivAt
  intro x
  refine ⟨DFunLike.congr_fun dcomm x, ?_⟩
  have hD := DFunLike.congr_fun htrace x
  rwa [_root_.sum_apply, Finset.sum_range] at hD

end Langlands.BaseChange
