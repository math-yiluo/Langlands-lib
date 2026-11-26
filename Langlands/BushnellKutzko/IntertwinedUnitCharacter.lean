import Langlands.BushnellKutzko.AdjointCentralizer
import Langlands.BushnellKutzko.IntertwinedUnitCharacterStatement
import Langlands.BushnellKutzko.CorestrictionLatticeDual
import Langlands.BushnellKutzko.FiltrationCoordinates
import Langlands.Group.GL.Maps
import Langlands.Group.GL.Transvection

/-! # Determinant factorization of intertwined unit characters -/

open ValuativeRel
open scoped BigOperators

noncomputable section

namespace Langlands.BushnellKutzko

universe uF uV

open Langlands.GeneralLinear LatticeChain

section Matrices

variable {F : Type uF} [Field F] {d : ℕ}

private def diagonalUnits : (Fin d → Fˣ) →* GeneralLinear d F where
  toFun v :=
    { val := Matrix.diagonal fun i => (v i : F)
      inv := Matrix.diagonal fun i => ((v i)⁻¹ : Fˣ)
      val_inv := by rw [Matrix.diagonal_mul_diagonal]; simp
      inv_val := by rw [Matrix.diagonal_mul_diagonal]; simp }
  map_one' := Units.ext (by simp)
  map_mul' _ _ := Units.ext (by
    simp [Matrix.diagonal_mul_diagonal])

private def scaleCoordinate (i : Fin d) : Fˣ →* GeneralLinear d F :=
  diagonalUnits.comp (MonoidHom.mulSingle (fun _ : Fin d => Fˣ) i)

private theorem coe_scaleCoordinate (i : Fin d) (c : Fˣ) :
    (scaleCoordinate i c : Matrix (Fin d) (Fin d) F) =
      Matrix.diagonal (fun j => if j = i then (c : F) else 1) := by
  change Matrix.diagonal (fun j => ((Pi.mulSingle (M := fun _ : Fin d => Fˣ) i c j : Fˣ) : F)) = _
  congr 1
  funext j
  by_cases h : j = i <;> simp [h, Pi.mulSingle_eq_of_ne]

private theorem scale_transvection_conj (i j : Fin d) (hij : i ≠ j) (c : Fˣ) (a : F) :
    scaleCoordinate i c * transvectionUnit i j hij a * (scaleCoordinate i c)⁻¹ =
      transvectionUnit i j hij ((c : F) * a) := by
  apply mul_inv_eq_iff_eq_mul.mpr
  apply Units.ext
  change (scaleCoordinate i c : Matrix (Fin d) (Fin d) F) * Matrix.transvection i j a =
    Matrix.transvection i j ((c : F) * a) * (scaleCoordinate i c : Matrix (Fin d) (Fin d) F)
  rw [coe_scaleCoordinate]
  ext k l
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hk : k = i
  · subst k
    by_cases hl : l = j
    · subst l
      simp [Matrix.transvection, Matrix.single, hij, hij.symm]
    · by_cases hli : l = i
      · subst l
        simp [Matrix.transvection, Matrix.single, hij.symm]
      · simp [Matrix.transvection, Matrix.single, hli, Ne.symm hli]
  · by_cases hkl : k = l
    · subst l
      simp [Matrix.transvection, Matrix.single, hk, Ne.symm hk]
    · simp [Matrix.transvection, Matrix.single, hk, Ne.symm hk, hkl]

private theorem scaleCoordinate_conj_swap (i j : Fin d) (c : Fˣ) :
    permutation d F (Equiv.swap i j) * scaleCoordinate i c *
      (permutation d F (Equiv.swap i j))⁻¹ = scaleCoordinate j c := by
  apply Units.ext
  ext a b
  rw [permutation_conjugate_entry]
  rw [coe_scaleCoordinate, coe_scaleCoordinate]
  simp only [Equiv.Perm.inv_def, Equiv.symm_swap, Matrix.diagonal_apply, EmbeddingLike.apply_eq_iff_eq]
  have h (b : Fin d) : Equiv.swap i j b = i ↔ b = j := by
    exact ⟨fun h => (Equiv.swap i j).injective (h.trans (Equiv.swap_apply_right i j).symm),
      fun h => h.symm ▸ Equiv.swap_apply_right i j⟩
  simp only [h]

end Matrices

section UnitFiltration

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {V : Type uV} [AddCommGroup V] [Module F V]

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem unitFiltration_iff_sub_one {L : LatticeChain 𝒪[F] F V} {k : ℕ} (hk : 1 ≤ k)
    (g : (Module.End F V)ˣ) : g ∈ L.unitFiltration k ↔
      (g : Module.End F V) - 1 ∈ L.endFiltration k := by
  refine ⟨fun h => h.2.2, fun h => ?_⟩
  obtain ⟨u, hu, he⟩ := L.exists_mem_unitFiltration hk h
  have : u = g := Units.ext (by rw [he]; abel)
  exact this ▸ hu

set_option maxHeartbeats 800000 in
private theorem character_kills_determinant_kernel (L : LatticeChain 𝒪[F] F V)
    {k : ℕ} (hk : 1 ≤ k) (χ : L.unitFiltration k →* ℂˣ)
    (hI : ∀ g, g ∈ characterSelfIntertwining χ) (g : L.unitFiltration k)
    (hg : (Units.map (LinearMap.det : Module.End F V →* F)) g.val = 1) : χ g = 1 := by
  classical
  let _ := L.finiteDimensional
  let _ := L.nontrivial_space
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  obtain ⟨d, B, hB⟩ := L.exists_basis_splits hπ
  let e := Units.mapEquiv (LinearMap.toMatrixAlgEquiv B).toMulEquiv
  let H := (L.unitFiltration k).comap e.symm.toMonoidHom
  let pull : H →* L.unitFiltration k :=
    { toFun := fun v => ⟨e.symm v.val, v.property⟩
      map_one' := Subtype.ext (map_one e.symm)
      map_mul' := fun a b => Subtype.ext (map_mul e.symm _ _) }
  let φ := χ.comp pull
  let D : GeneralLinear d F →* Fˣ := Matrix.GeneralLinearGroup.det
  have hdet (v : H) : D v.val = Units.map (LinearMap.det : Module.End F V →* F) (pull v).val := by
    apply Units.ext
    change v.val.val.det = LinearMap.det (e.symm v.val).val
    rw [← LinearMap.det_toMatrix B]
    exact congrArg Units.val (e.apply_symm_apply v.val).symm |> congrArg Matrix.det
  have hconj (s : GeneralLinear d F) (v w : H) (he : s * v.val * s⁻¹ = w.val) :
      φ w = φ v := by
    have he' : e.symm s * (pull v).val * (e.symm s)⁻¹ = (pull w).val := by
      change e.symm s * e.symm v.val * (e.symm s)⁻¹ = e.symm w.val
      simpa only [map_mul, map_inv] using congrArg e.symm he
    have hw := (pull w).property
    rw [← he'] at hw
    have hw' : (⟨_, hw⟩ : L.unitFiltration k) = pull w := Subtype.ext he'
    exact (congrArg χ hw').symm.trans (hI (e.symm s) (pull v) hw)
  have hsingle (i j : Fin d) (a : F) :
      (LinearMap.toMatrixAlgEquiv B) (elementaryEnd B i j a) = Matrix.single i j a := by
    ext p q
    rw [LinearMap.toMatrixAlgEquiv_apply, elementaryEnd_apply_basis]
    by_cases hq : j = q
    · subst q
      simp [Matrix.single, Module.Basis.repr_self, Finsupp.single_apply]
    · simp [Matrix.single, hq]
  have hmem (v : GeneralLinear d F) {i j : Fin d} {a : F}
      (hmat : v.val = 1 + Matrix.single i j a) :
      v ∈ H ↔ elementaryEnd B i j a ∈ L.endFiltration k := by
    change e.symm v ∈ L.unitFiltration k ↔ _
    rw [unitFiltration_iff_sub_one hk]
    have he : (e.symm v).val - 1 = elementaryEnd B i j a := by
      apply (LinearMap.toMatrixAlgEquiv B).injective
      rw [map_sub, map_one, hsingle]
      change (e (e.symm v)).val - 1 = _
      rw [e.apply_symm_apply, hmat, add_sub_cancel_left]
    rw [he]
  have hdiag_mem (i : Fin d) (c : Fˣ) :
      scaleCoordinate i c ∈ H ↔ elementaryEnd B i i ((c : F) - 1) ∈ L.endFiltration k := by
    apply hmem
    rw [coe_scaleCoordinate]
    ext p q
    by_cases hp : p = i
    · subst p
      by_cases hq : q = i
      · subst q
        simp [Matrix.single]
      · simp [Matrix.single, Ne.symm hq]
    · simp [Matrix.diagonal_apply, Matrix.single, hp, Ne.symm hp, Matrix.one_apply]
  have hdiag_move (i j : Fin d) (c : Fˣ) (hc : scaleCoordinate i c ∈ H) :
      scaleCoordinate j c ∈ H := by
    rw [hdiag_mem] at hc ⊢
    by_cases hz : (c : F) - 1 = 0
    · simp [hz, elementaryEnd_zero]
    · rw [L.elementaryEnd_mem_iff hπ hB _ _ hz] at hc ⊢
      omega
  have hentry (v : H) (i j : Fin d) :
      elementaryEnd B i j ((v.val.val - 1) i j) ∈ L.endFiltration k := by
    let z := (e.symm v.val).val - 1
    have hz : z ∈ L.endFiltration k := (pull v).property.2.2
    have he : (LinearMap.toMatrixAlgEquiv B) z = v.val.val - 1 := by
      rw [map_sub, map_one]
      change (e (e.symm v.val)).val - 1 = _
      rw [e.apply_symm_apply]
    rw [← he, LinearMap.toMatrixAlgEquiv_apply, ← entry, ← elementaryEnd_mul_mul]
    have hi := L.elementaryEnd_diag_mem_order hπ hB i
    have hj := L.elementaryEnd_diag_mem_order hπ hB j
    simpa only [zero_add, add_zero] using L.mul_mem_endFiltration (L.mul_mem_endFiltration hi hz) hj
  have hpivot (v : H) (i : Fin d) : IsUnit (v.val.val i i) ∧
      (v.val.val i i)⁻¹ ∈ 𝒪[F] := by
    have hzmem := hentry v i i
    rw [Matrix.sub_apply, Matrix.one_apply_eq] at hzmem
    have htrace := L.trace_mem_maximalIdealInField
      (L.endFiltration_antitone (by exact_mod_cast hk) hzmem)
    have he : LinearMap.trace F V (elementaryEnd B i i (v.val.val i i - 1)) = v.val.val i i - 1 := by
      rw [← one_mul (elementaryEnd B i i _), trace_mul_elementaryEnd]
      simp [entry, Module.Basis.repr_self]
    rw [he] at htrace
    obtain ⟨x, hx, heq⟩ := htrace
    have hu : IsUnit (x + 1 : 𝒪[F]) := IsLocalRing.notMem_maximalIdeal.mp (by
      intro h
      exact Ideal.one_notMem (IsLocalRing.maximalIdeal 𝒪[F])
        (by simpa using sub_mem h hx))
    obtain ⟨u, hu⟩ := hu
    have huval : ((u : 𝒪[F]) : F) = v.val.val i i := by
      rw [hu]
      change (x : F) + 1 = _
      change (x : F) = _ at heq
      rw [heq, sub_add_cancel]
    refine ⟨by rw [← huval]; exact IsUnit.map (algebraMap 𝒪[F] F) u.isUnit, ?_⟩
    rw [← huval, ← coe_unit_inv]
    exact (↑(u⁻¹) : 𝒪[F]).property
  have htrans (i j : Fin d) (hij : i ≠ j) (a : F)
      (ha : elementaryEnd B i j a ∈ L.endFiltration k) :
      φ ⟨transvectionUnit i j hij a, (hmem _ rfl).2 ha⟩ = 1 := by
    have hπunit : IsUnit (π - 1 : 𝒪[F]) := IsLocalRing.notMem_maximalIdeal.mp (by
      intro hm
      have hp : π ∈ 𝓂[F] := (IsLocalRing.mem_maximalIdeal _).mpr hπ.not_isUnit
      exact Ideal.one_notMem 𝓂[F] (by simpa using sub_mem hp hm))
    obtain ⟨c, hc⟩ := hπunit
    let b : F := ((c⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) • a
    have hb : elementaryEnd B i j b ∈ L.endFiltration k := by
      simpa [b, elementaryEnd, smul_smul] using
        (L.endFiltration k).smul_mem (↑c⁻¹ : 𝒪[F]) ha
    let t : H := ⟨transvectionUnit i j hij b, (hmem _ rfl).2 hb⟩
    let u : H := ⟨transvectionUnit i j hij a, (hmem _ rfl).2 ha⟩
    have hba : (π : F) * b = b + a := by
      have hca : ((c : 𝒪[F]) : F) * b = a := by
        change ((c : 𝒪[F]) : F) * ((((c⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) : F) * a) = _
        rw [← mul_assoc, ← Subring.coe_mul, Units.mul_inv, Subring.coe_one, one_mul]
      have hc' : ((c : 𝒪[F]) : F) = (π : F) - 1 := by exact_mod_cast hc
      rw [hc', sub_mul, one_mul] at hca
      exact sub_eq_iff_eq_add'.mp hca
    have he : scaleCoordinate i (uniformizerAsUnit hπ) * t.val *
        (scaleCoordinate i (uniformizerAsUnit hπ))⁻¹ = (t * u).val := by
      rw [show t.val = transvectionUnit i j hij b from rfl, scale_transvection_conj,
        coe_uniformizerAsUnit, hba]
      apply Units.ext
      exact (Matrix.transvection_mul_transvection_same _ _ hij _ _).symm
    have he' := hconj (scaleCoordinate i (uniformizerAsUnit hπ)) t (t * u) he
    rw [map_mul] at he'
    exact mul_left_cancel (he'.trans (mul_one (φ t)).symm)
  -- A left elementary operation stays inside the filtration and preserves the two values.
  have hrow (v : H) (i j : Fin d) (hij : i ≠ j) :
      ∃ w : H, φ w = φ v ∧ D w.val = D v.val ∧
        w.val.val i j = 0 ∧
        (∀ a b, a ≠ i → w.val.val a b = v.val.val a b) ∧
        (∀ b, v.val.val j b = 0 → w.val.val i b = v.val.val i b) := by
    let a := -(v.val.val j j)⁻¹ * v.val.val i j
    have hz : elementaryEnd B i j (v.val.val i j) ∈ L.endFiltration k := by
      simpa [Matrix.one_apply, hij] using hentry v i j
    have ha : elementaryEnd B i j a ∈ L.endFiltration k := by
      let c : 𝒪[F] := ⟨-(v.val.val j j)⁻¹, neg_mem (hpivot v j).2⟩
      have hs := (L.endFiltration k).smul_mem c hz
      change ((c : F) • elementaryEnd B i j (v.val.val i j)) ∈ _ at hs
      simpa only [a, c, elementaryEnd, smul_smul, smul_eq_mul] using hs
    let t : H := ⟨transvectionUnit i j hij a, (hmem _ rfl).2 ha⟩
    have htφ : φ t = 1 := htrans i j hij a ha
    have htD : D t.val = 1 := Units.ext (Matrix.det_transvection_of_ne i j hij a)
    refine ⟨t * v, by simp [htφ], by change D (t.val * v.val) = _; simp [htD], ?_, ?_, ?_⟩
    · change (Matrix.transvection i j a * v.val.val) i j = _
      rw [Matrix.transvection_mul_apply_same]
      have hn := (hpivot v j).1.ne_zero
      dsimp [a]
      field_simp
      ring
    · intro b c hb
      exact Matrix.transvection_mul_apply_of_ne _ _ _ _ hb _ _
    · intro b hb
      change (Matrix.transvection i j a * v.val.val) i b = _
      rw [Matrix.transvection_mul_apply_same, hb, mul_zero, add_zero]
  have hcols (s : Finset (Fin d)) (v : H) : ∃ w : H, φ w = φ v ∧ D w.val = D v.val ∧
      ∀ j ∈ s, ∀ i, i ≠ j → w.val.val i j = 0 := by
    induction s using Finset.induction with
    | empty => exact ⟨v, rfl, rfl, by simp⟩
    | @insert j s hjs ih =>
      obtain ⟨w, hwφ, hwD, hws⟩ := ih
      have hclear (t : Finset (Fin d)) (ht : j ∉ t) :
          ∃ w' : H, φ w' = φ w ∧ D w'.val = D w.val ∧
            (∀ c ∈ s, ∀ a, a ≠ c → w'.val.val a c = 0) ∧
            ∀ a ∈ t, w'.val.val a j = 0 := by
        induction t using Finset.induction with
        | empty => exact ⟨w, rfl, rfl, hws, by simp⟩
        | @insert i t hit iht =>
          obtain ⟨v', hvφ, hvD, hvs, hvt⟩ := iht (fun h => ht (Finset.mem_insert_of_mem h))
          have hij : i ≠ j := fun h => ht (h ▸ Finset.mem_insert_self _ _)
          obtain ⟨u, huφ, huD, hu0, hurest, hufix⟩ := hrow v' i j hij
          refine ⟨u, huφ.trans hvφ, huD.trans hvD, ?_, ?_⟩
          · intro c hc a hac
            by_cases hai : a = i
            · subst a
              rw [hufix c (hvs c hc j (fun h => hjs (h ▸ hc)))]
              exact hvs c hc i hac
            · rw [hurest a c hai]
              exact hvs c hc a hac
          · intro a ha
            rcases Finset.mem_insert.mp ha with rfl | ha
            · exact hu0
            · rw [hurest a j (fun h => hit (h ▸ ha))]
              exact hvt a ha
      obtain ⟨u, huφ, huD, hus, huj⟩ := hclear (Finset.univ.erase j) (Finset.notMem_erase _ _)
      refine ⟨u, huφ.trans hwφ, huD.trans hwD, ?_⟩
      intro c hc a hac
      rcases Finset.mem_insert.mp hc with rfl | hc
      · exact huj a (Finset.mem_erase.mpr ⟨hac, Finset.mem_univ a⟩)
      · exact hus c hc a hac
  let v : H := ⟨e g.val, by
    change e.symm (e g.val) ∈ L.unitFiltration k
    rw [e.symm_apply_apply]
    exact g.property⟩
  have hv : pull v = g := Subtype.ext (e.symm_apply_apply _)
  obtain ⟨w, hwφ, hwD, hw⟩ := hcols Finset.univ v
  have hw1 : D w.val = 1 := by rw [hwD, hdet, hv, hg]
  let c (i : Fin d) : Fˣ := Units.mk0 (w.val.val i i)
    (hpivot w i).1.ne_zero
  have hwdiag : w.val = diagonalUnits c := by
    apply Units.ext
    ext i j
    by_cases h : i = j
    · subst j
      simp [diagonalUnits, c]
    · change w.val.val i j = Matrix.diagonal (fun i => (c i : F)) i j
      rw [Matrix.diagonal_apply_ne _ h]
      exact hw j (Finset.mem_univ _) i h
  have hprod : ∏ i, c i = 1 := by
    apply Units.ext
    simpa [hwdiag, D, diagonalUnits, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_diagonal,
      map_prod] using congrArg Units.val hw1
  have hi (i : Fin d) : scaleCoordinate i (c i) ∈ H := by
    rw [hdiag_mem]
    simpa [c, Matrix.one_apply_eq] using hentry w i i
  let j := Classical.choice B.index_nonempty
  let M := H.comap diagonalUnits
  let φD : M →* ℂˣ := φ.comp ((diagonalUnits.comp M.subtype).codRestrict H (fun v => v.property))
  let a (i : Fin d) : M := ⟨Pi.mulSingle i (c i), hi i⟩
  let b (i : Fin d) : M := ⟨Pi.mulSingle j (c i), hdiag_move i j (c i) (hi i)⟩
  have hab (i : Fin d) : φD (a i) = φD (b i) :=
    (hconj (permutation d F (Equiv.swap i j)) ⟨scaleCoordinate i (c i), hi i⟩
      ⟨scaleCoordinate j (c i), hdiag_move i j (c i) (hi i)⟩
      (scaleCoordinate_conj_swap i j (c i))).symm
  have ha (hc : c ∈ M) : ∏ i, a i = (⟨c, hc⟩ : M) := by
    apply Subtype.ext
    change M.subtype (∏ i, a i) = c
    rw [map_prod]
    exact Finset.univ_prod_mulSingle c
  have hb : ∏ i, b i = 1 := by
    apply Subtype.ext
    change M.subtype (∏ i, b i) = 1
    rw [map_prod]
    change (∏ i, MonoidHom.mulSingle (fun _ : Fin d => Fˣ) j (c i)) = 1
    rw [← map_prod, hprod, map_one]
  have hc : c ∈ M := by change diagonalUnits c ∈ H; rw [← hwdiag]; exact w.property
  have hφw : φ w = φD (⟨c, hc⟩ : M) := congrArg φ (Subtype.ext hwdiag)
  calc
    χ g = φ v := by change χ g = χ (pull v); rw [hv]
    _ = φ w := hwφ.symm
    _ = φD (∏ i, a i) := hφw.trans (congrArg φD (ha hc).symm)
    _ = φD (∏ i, b i) := by simp only [map_prod, hab]
    _ = 1 := by rw [hb, map_one]

/-- An abstract-character extension of BK93 (2.4.11). A character of a positive unit
filtration subgroup intertwined by all ambient units factors through the determinant image. -/
private theorem factorsThroughDet (L : LatticeChain 𝒪[F] F V)
    {k : ℕ} (hk : 1 ≤ k) (χ : L.unitFiltration k →* ℂˣ)
    (hI : ∀ g, g ∈ characterSelfIntertwining χ) :
    let det := (Units.map (LinearMap.det : Module.End F V →* F)).comp
      (L.unitFiltration k).subtype
    ∃ η : det.range →* ℂˣ, ∀ g, χ g = η (det.rangeRestrict g) := by
  dsimp only
  let det := (Units.map (LinearMap.det : Module.End F V →* F)).comp (L.unitFiltration k).subtype
  let φ := QuotientGroup.lift det.ker χ (fun g hg =>
    character_kills_determinant_kernel L hk χ hI g hg)
  refine ⟨φ.comp (QuotientGroup.quotientKerEquivRange det).symm.toMonoidHom, fun g => ?_⟩
  have h := (QuotientGroup.quotientKerEquivRange det).symm_apply_apply
    (QuotientGroup.mk g)
  exact (congrArg φ h).symm

end UnitFiltration

/-- Determinant factorization for fully intertwined positive unit characters. -/
theorem intertwinedUnitCharacter : IntertwinedUnitCharacterStatement.{uF,uV} := by
  intro F _ _ _ _ V _ _ L k hk χ hI
  exact factorsThroughDet L hk χ hI

end Langlands.BushnellKutzko
