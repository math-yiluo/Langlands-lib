import Langlands.Representation.Unitary.LeviCuspidalRealUnitarizationStatement
import Langlands.Group.GL.BlockScalarCenter
import Langlands.Representation.Unitary.SquareIntegrableProof
import Langlands.Representation.CuspidalSupport.HarishChandraAssembly
import Langlands.Representation.CuspidalSupport.DeterminantUnitStructureProof
import Langlands.Representation.Smooth.Schur.Proof
import Langlands.Representation.Twist.SubquotientProof
import Langlands.LocalField.SmoothCharacterNormProof
import Langlands.Group.GL.CentralQuotientTopologyProof
import Langlands.Group.GL.CompactOpen
import Langlands.Topology.CompactOpen.NeighborhoodBasis
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Haar.Basic

/-!
# Real unitarization of irreducible cuspidal product-Levi representations

The real twist removes the norm of the Schur central character on the block
scalars. Harish-Chandra's compactness on the determinant-unit subgroup and its
finite index modulo the center make the twisted coefficient norms compactly
supported on the central quotient. Integrating coefficient products against a
right Haar measure gives the invariant positive form.
-/

noncomputable section

namespace Langlands

open GeneralLinear MeasureTheory
open scoped BigOperators

universe uG uF uV

section CompactModCenter

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- If a normal subgroup `H` together with the center has finite index, and the
coefficients of `ℓ` restricted to `H` are compactly supported, then the descended
coefficient norms are compactly supported on the central quotient. -/
theorem UnitaryCentralCharacter.hasCompactSupport_coefficientNorm_of_finiteIndex
    [T2Space (G ⧸ Subgroup.center G)]
    {ρ : Representation ℂ G V} (c : UnitaryCentralCharacter ρ)
    (H : Subgroup G) [H.Normal] [(H ⊔ Subgroup.center G).FiniteIndex]
    (ℓ : Module.Dual ℂ V)
    (hH : ∀ w : V, HasCompactSupport (matrixCoefficient (ρ.comp H.subtype) ℓ w))
    (v : V) : HasCompactSupport (c.coefficientNorm ℓ v) := by
  let N := H ⊔ Subgroup.center G
  let r : G ⧸ N → G := fun j => j.out
  let C : G ⧸ N → Set H := fun j =>
    tsupport (matrixCoefficient (ρ.comp H.subtype) ℓ (ρ (r j) v))
  let K : Set (G ⧸ Subgroup.center G) :=
    ⋃ j, (fun h : H => (QuotientGroup.mk ((h : G) * r j) : G ⧸ Subgroup.center G)) '' C j
  have hK : IsCompact K := by
    apply isCompact_iUnion
    intro j
    exact (hH (ρ (r j) v)).isCompact.image
      (continuous_quot_mk.comp (continuous_subtype_val.mul continuous_const))
  refine HasCompactSupport.intro hK ?_
  intro q hq
  induction q using QuotientGroup.induction_on with
  | H g =>
    by_contra hne
    apply hq
    let j : G ⧸ N := QuotientGroup.mk g
    obtain ⟨n0, hn0⟩ := QuotientGroup.mk_out_eq_mul N g
    have hn0' : r j = g * n0 := hn0
    have hmem : (n0 : G)⁻¹ ∈ N := N.inv_mem n0.2
    obtain ⟨h, hh, z, hz, hhz⟩ := Subgroup.mem_sup_of_normal_right.mp hmem
    let h' : G := r j * h * (r j)⁻¹
    have hh' : h' ∈ H := Subgroup.Normal.conj_mem inferInstance h hh (r j)
    have hg : g = h' * r j * z := by
      have : g = r j * (n0 : G)⁻¹ := by rw [hn0']; group
      rw [this, ← hhz]
      simp only [h']
      group
    have hzc : z ∈ Subgroup.center G := hz
    have hval : c.coefficientNorm ℓ v (QuotientGroup.mk g) =
        ‖matrixCoefficient (ρ.comp H.subtype) ℓ (ρ (r j) v) ⟨h', hh'⟩‖ := by
      rw [UnitaryCentralCharacter.coefficientNorm_mk, hg]
      rw [c.norm_matrixCoefficient_mul_center ℓ v (h' * r j) ⟨z, hzc⟩]
      change ‖ℓ (ρ (h' * r j) v)‖ = ‖ℓ (ρ h' (ρ (r j) v))‖
      rw [map_mul, Module.End.mul_apply]
    have hsupp : (⟨h', hh'⟩ : H) ∈ C j := by
      apply subset_tsupport
      intro h0
      apply hne
      rw [hval, h0, norm_zero]
    refine Set.mem_iUnion.2 ⟨j, ⟨h', hh'⟩, hsupp, ?_⟩
    change (QuotientGroup.mk (h' * r j) : G ⧸ Subgroup.center G) = QuotientGroup.mk g
    rw [QuotientGroup.eq, hg]
    simpa [mul_assoc] using hzc

end CompactModCenter

namespace LeviCuspidalRealUnitarization

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
  {n : ℕ} (D : BlockShape n)

/-- Block scalar tuples are central in the product Levi. -/
theorem blockScalarLevi_mem_center (a : Fin D.length → F.Carrierˣ) :
    D.blockScalarLevi F.Carrier a ∈ Subgroup.center (D.Levi F.Carrier) := by
  rw [Subgroup.center_pi, Subgroup.mem_pi]
  intro i _
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
  exact ⟨a i, rfl⟩

/-- Every central element of the product Levi is a tuple of block scalars. -/
theorem exists_blockScalarLevi_eq_of_mem_center {z : D.Levi F.Carrier}
    (hz : z ∈ Subgroup.center (D.Levi F.Carrier)) :
    ∃ a : Fin D.length → F.Carrierˣ, D.blockScalarLevi F.Carrier a = z := by
  rw [Subgroup.center_pi, Subgroup.mem_pi] at hz
  have h : ∀ i, ∃ c : F.Carrierˣ, GeneralLinear.scalar c = z i := by
    intro i
    have hi := hz i (Set.mem_univ i)
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hi
    exact hi
  choose a ha using h
  exact ⟨a, funext ha⟩

@[simp] theorem coe_blockScalarCenter (a : Fin D.length → F.Carrierˣ) :
    (Parabolic.blockScalarCenter D a : D.Levi F.Carrier) = D.blockScalarLevi F.Carrier a := rfl

theorem continuous_blockScalarCenter :
    letI := T.topology
    Continuous (Parabolic.blockScalarCenter (F := F) D) := by
  let := T.topology
  have hΦ : Continuous (D.blockScalarLevi F.Carrier) := continuous_pi fun i =>
    (GeneralLinear.scalarContinuous (n := D.size i)).continuous.comp (continuous_apply i)
  exact hΦ.subtype_mk _

/-- On the twisted representation, the twist restricted to the determinant-unit
subgroup is trivial. -/
theorem leviRealPowerTwist_comp_determinantUnitInclusion
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (t : Fin D.length → ℝ) (ρ : Representation ℂ (D.Levi F.Carrier) V) :
    (T.leviRealPowerTwist D t ρ).comp (CuspidalSupport.determinantUnitInclusion T D) =
      CuspidalSupport.determinantUnitRestriction T D ρ := by
  apply MonoidHom.ext
  intro h
  apply LinearMap.ext
  intro v
  have h1 : T.leviRealPowerCharacter D t (h : D.Levi F.Carrier) = 1 :=
    T.normOneLevi_le_ker_leviRealPowerCharacter D t
      ((T.mem_normOneLevi D _).2 ((CuspidalSupport.mem_determinantUnitSubgroup T D _).1 h.2))
  change (T.leviRealPowerCharacter D t (h : D.Levi F.Carrier) : ℂ) • ρ h v = ρ h v
  rw [h1, Units.val_one, one_smul]

/-- A real twist makes the Schur central character unitary on the block scalars,
and hence on the full center. -/
theorem exists_leviRealPowerTwist_unitaryCentralCharacter
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (D.Levi F.Carrier) V)
    (χ : Subgroup.center (D.Levi F.Carrier) →* ℂˣ)
    (hχ : letI := T.topology
      IsLocallyConstant (χ : Subgroup.center (D.Levi F.Carrier) → ℂˣ))
    (hact : ∀ (z : Subgroup.center (D.Levi F.Carrier)) (v : V),
      ρ (z : D.Levi F.Carrier) v = (χ z : ℂ) • v) :
    letI := T.topology
    ∃ t : Fin D.length → ℝ, Nonempty (UnitaryCentralCharacter (T.leviRealPowerTwist D t ρ)) := by
  let := T.topology
  let := T.leviTopologicalGroup D
  have hΦ := continuous_blockScalarCenter T D
  have hdec : ∀ i : Fin D.length, ∃ c : ℝ, ∀ a : F.Carrierˣ,
      ‖(χ (Parabolic.blockScalarCenter D (Pi.mulSingle i a)) : ℂ)‖ =
        T.normalizedAbs (a : F.Carrier) ^ c := by
    intro i
    let ψ : F.Carrierˣ →* ℂˣ :=
      χ.comp ((Parabolic.blockScalarCenter D).comp (MonoidHom.mulSingle (fun _ => F.Carrierˣ) i))
    have hψ : IsOpen (ψ.ker : Set F.Carrierˣ) := by
      have hlc : IsLocallyConstant (ψ : F.Carrierˣ → ℂˣ) :=
        hχ.comp_continuous (hΦ.comp (show Continuous
          (MonoidHom.mulSingle (fun _ : Fin D.length => F.Carrierˣ) i) from
            continuous_mulSingle (A := fun _ : Fin D.length => F.Carrierˣ) i))
      have he : (ψ.ker : Set F.Carrierˣ) = (ψ : F.Carrierˣ → ℂˣ) ⁻¹' {1} := by
        ext a
        simp [MonoidHom.mem_ker]
      rw [he]
      exact hlc.isOpen_fiber 1
    obtain ⟨c, hc, -⟩ := PadicField.TopologicalData.smoothCharacterNormDecomposition F T ψ hψ
    exact ⟨c, hc⟩
  choose c hc using hdec
  let t : Fin D.length → ℝ := fun i => -c i / (D.size i : ℝ)
  let ψt : Subgroup.center (D.Levi F.Carrier) →* ℂˣ :=
    (T.leviRealPowerCharacter D t).comp (Subgroup.center (D.Levi F.Carrier)).subtype
  refine ⟨t, ⟨{ character := ψt * χ, isOpen_ker := ?_, norm_eq_one := ?_, acts := ?_ }⟩⟩
  · have h1 : IsOpen (ψt.ker : Set (Subgroup.center (D.Levi F.Carrier))) := by
      have he : (ψt.ker : Set (Subgroup.center (D.Levi F.Carrier))) =
          Subtype.val ⁻¹' ((T.leviRealPowerCharacter D t).ker : Set (D.Levi F.Carrier)) := by
        ext z
        simp [ψt, MonoidHom.mem_ker]
      rw [he]
      exact (T.isOpen_ker_leviRealPowerCharacter D t).preimage continuous_subtype_val
    have h2 : IsOpen (χ.ker : Set (Subgroup.center (D.Levi F.Carrier))) := by
      have he : (χ.ker : Set (Subgroup.center (D.Levi F.Carrier))) =
          (χ : Subgroup.center (D.Levi F.Carrier) → ℂˣ) ⁻¹' {1} := by
        ext z
        simp [MonoidHom.mem_ker]
      rw [he]
      exact hχ.isOpen_fiber 1
    refine Subgroup.isOpen_mono (H₁ := ψt.ker ⊓ χ.ker) ?_ ?_
    · intro z hz
      rw [MonoidHom.mem_ker, MonoidHom.mul_apply, (MonoidHom.mem_ker).1 hz.1,
        (MonoidHom.mem_ker).1 hz.2, mul_one]
    · rw [Subgroup.coe_inf]
      exact h1.inter h2
  · intro z
    obtain ⟨a, ha⟩ := exists_blockScalarLevi_eq_of_mem_center D z.2
    have hz : z = Parabolic.blockScalarCenter D a := Subtype.ext ha.symm
    let φ : (Fin D.length → F.Carrierˣ) →* ℂˣ := χ.comp (Parabolic.blockScalarCenter D)
    have hprod : φ a = ∏ i, φ (Pi.mulSingle i (a i)) := by
      rw [← map_prod, Finset.univ_prod_mulSingle]
    have hψt : ‖(ψt z : ℂ)‖ =
        ∏ i, T.normalizedAbs (a i : F.Carrier) ^ ((D.size i : ℝ) * t i) := by
      change ‖(T.leviRealPowerCharacter D t (z : D.Levi F.Carrier) : ℂ)‖ = _
      rw [← ha, T.coe_leviRealPowerCharacter_blockScalar D t a, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (Finset.prod_nonneg fun i _ =>
          Real.rpow_nonneg (T.normalizedAbs_nonneg _) _)]
    have hχz : ‖(χ z : ℂ)‖ = ∏ i, T.normalizedAbs (a i : F.Carrier) ^ c i := by
      have hφ : χ z = φ a := by rw [hz]; rfl
      rw [hφ, hprod, Units.coe_prod, norm_prod]
      exact Finset.prod_congr rfl fun i _ => hc i (a i)
    change ‖((ψt z * χ z : ℂˣ) : ℂ)‖ = 1
    rw [Units.val_mul, norm_mul, hψt, hχz, ← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro i _
    have hpos : 0 < T.normalizedAbs (a i : F.Carrier) := T.normalizedAbs_pos (a i).ne_zero
    have hsize : (D.size i : ℝ) ≠ 0 := by exact_mod_cast (D.positive i).ne'
    rw [← Real.rpow_add hpos]
    have hexp : (D.size i : ℝ) * t i + c i = 0 := by
      simp only [t]
      field_simp
      ring
    rw [hexp, Real.rpow_zero]
  · intro z v
    change (T.leviRealPowerCharacter D t (z : D.Levi F.Carrier) : ℂ) • ρ z v = _
    rw [hact, smul_smul]
    rfl

end LeviCuspidalRealUnitarization

open LeviCuspidalRealUnitarization in
/-- Every irreducible cuspidal representation of an actual product Levi carries an
invariant positive form on its original carrier after a real determinant twist. -/
theorem leviCuspidalRealUnitarization :
    LeviCuspidalRealUnitarizationStatement.{uF, uV} := by
  intro p _ F T
  let := T.topology
  intro n _ D V _ _ ρ hirr hcusp
  let := T.leviTopologicalGroup D
  have hsm : IsSmooth ρ := hcusp.1.1
  obtain ⟨χ, ⟨hχlc, hχ⟩, -⟩ := admissibleSchur_centralCharacter ρ hcusp.1 hirr
  obtain ⟨t, ⟨c⟩⟩ := exists_leviRealPowerTwist_unitaryCentralCharacter T D ρ χ hχlc hχ
  refine ⟨t, ?_⟩
  have hωs : IsSmooth (T.leviRealPowerTwist D t ρ) :=
    (T.isSmooth_leviRealPowerTwist_iff D t ρ).2 hsm
  have hωi : Representation.IsIrreducible (T.leviRealPowerTwist D t ρ) :=
    (isIrreducible_twist_iff _ ρ).2 hirr
  have hcofinal : ∀ K : OpenSubgroup (D.Levi F.Carrier), ∃ L : OpenSubgroup (D.Levi F.Carrier),
      IsCompact (L : Set (D.Levi F.Carrier)) ∧ L ≤ K := by
    have := T.leviNonarchimedean D
    have := T.leviLocallyCompactSpace D
    intro K
    obtain ⟨L, hL, hLK⟩ := compactOpenSubgroupBasis (D.Levi F.Carrier)
      (K : Set (D.Levi F.Carrier)) K.mem_nhds_one
    exact ⟨L, hL, fun x hx => hLK hx⟩
  obtain ⟨ℓ, hℓ⟩ := exists_nonzero_smoothDual_of_irreducible_compact_cofinal hcofinal ρ hsm hirr
  have hHC := (CuspidalSupport.leviHarishChandraTheorem p F T n D (SmoothRep.of ρ hsm)).1
    hcusp.2
  have hℓH : IsSmoothVector (CuspidalSupport.determinantUnitRestriction T D ρ).dual ℓ.1 :=
    isSmoothVector_comp (CuspidalSupport.determinantUnitInclusion T D)
      (CuspidalSupport.continuous_determinantUnitInclusion T D) ℓ.2
  have hH : ∀ w : V, HasCompactSupport (matrixCoefficient
      ((T.leviRealPowerTwist D t ρ).comp
        (CuspidalSupport.determinantUnitSubgroup T D).subtype) ℓ.1 w) := by
    intro w
    have he := leviRealPowerTwist_comp_determinantUnitInclusion T D t ρ
    change HasCompactSupport (matrixCoefficient ((T.leviRealPowerTwist D t ρ).comp
      (CuspidalSupport.determinantUnitInclusion T D)) ℓ.1 w)
    rw [he]
    exact hHC w ℓ.1 hℓH
  obtain ⟨-, hFI, -⟩ := CuspidalSupport.leviDeterminantUnitStructure F T D
  obtain ⟨-, hQT2, hQlc, -, -⟩ := (glBlockCentralQuotientTopology p F T n).2 D
  have := hFI
  have := hQT2
  have := hQlc
  let Q := D.Levi F.Carrier ⧸ Subgroup.center (D.Levi F.Carrier)
  let : MeasurableSpace Q := borel Q
  have : BorelSpace Q := ⟨rfl⟩
  have hL2 : ∀ v : V, MemLp (c.coefficientNorm ℓ.1 v) 2 (Measure.haar : Measure Q).inv := by
    intro v
    exact (c.continuous_coefficientNorm ℓ.1 v (hωs v)).memLp_of_hasCompactSupport
      (c.hasCompactSupport_coefficientNorm_of_finiteIndex
        (CuspidalSupport.determinantUnitSubgroup T D) ℓ.1 hH v)
  exact ⟨c.coefficientProductForm hωs hωi ℓ.1 hℓ (Measure.haar : Measure Q).inv hL2⟩

end Langlands
