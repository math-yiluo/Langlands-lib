import Langlands.Global.Arithmetic.HenniartHarrisDatumExactStabilizerStatement
import Langlands.Global.Arithmetic.HarrisDatumCharacterRealizationProof
import Langlands.Global.Arithmetic.CMHalfWeightCharacterProof

/-! # Henniart's datum characters with exact Weil stabilizer -/

noncomputable section

universe uF uE uE' uL

namespace Langlands.Global

open NumberField IsDedekindDomain LocalFactor.CommonClosure GeneralPosition Harris
open AdelicFunctoriality HarrisDatum Weil.Local

set_option maxHeartbeats 1000000 in
/-- An auxiliary character `χs₀` of `F'ˣ` such that every character agreeing with it on the
norm-one units has exact Weil stabilizer for every normalized reciprocity family. -/
private theorem exists_exactWeilStabilizer_of_unitAgreement
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (F' : Extension F) :
    ∃ χs₀ : FieldCharacter F F', ∀ (e : ReciprocityFamily F), NormalizedReciprocity F e →
      ∀ χs : FieldCharacter F F',
        (∀ u : F'.fieldˣ, (F'.asPadicField (p := p)).canonicalNorm (u : F'.field) = 1 →
          χs u = χs₀ u) →
        HasExactWeilStabilizer F F' (weilCharacter F e F' χs) := by
  let := (fieldData F F').topology
  let := Algebra.charZero_of_charZero (Padic p) F.Carrier
  let M := galoisClosure F F'
  let h := le_galoisClosure F F'
  let L := IntermediateField.restrict h
  let a := Units.mapEquiv (IntermediateField.restrictAlgEquiv h).toMulEquiv
  let := (M.asPadicField (p := p)).algebra
  let : IsScalarTower (Padic p) F.Carrier M.field := IsScalarTower.of_algebraMap_eq' rfl
  let := (M.asPadicField (p := p)).canonicalNormedField
  have : IsGalois F.Carrier M.field := by
    change IsGalois F.Carrier
      (IntermediateField.normalClosure F.Carrier F'.field (AlgebraicClosure F.Carrier))
    infer_instance
  obtain ⟨χL, -, -, hstab⟩ := auxiliaryCharacterFirstOrder p F (M.asPadicField (p := p)) L 0
  let c : F'.fieldˣ →ₜ* Lˣ :=
    ⟨a.toMonoidHom, (Langlands.Global.restrictAlgEquiv_continuous F F' M h).units_map _⟩
  refine ⟨χL.comp c, fun e he χs hagree => ?_⟩
  -- Spectral norms are invariant under `F`-automorphisms of `M`.
  have hσ : ∀ (σ : M.field ≃ₐ[F.Carrier] M.field) (x : M.field), ‖σ x‖ = ‖x‖ := by
    intro σ x
    exact (spectralNorm_eq_of_equiv (σ.restrictScalars (Padic p)) x).symm
  -- Norms from `M` to `L` of norm-one elements have norm one.
  have hN : ∀ z : M.fieldˣ, ‖(z : M.field)‖ = 1 →
      ‖((Algebra.norm L (z : M.field) : L) : M.field)‖ = 1 := by
    intro z hz
    change ‖algebraMap L M.field (Algebra.norm L (z : M.field))‖ = 1
    rw [Algebra.norm_eq_prod_automorphisms, _root_.norm_prod]
    refine Finset.prod_eq_one fun σ _ => ?_
    change ‖(σ.restrictScalars F.Carrier) (z : M.field)‖ = 1
    rw [hσ, hz]
  have hagreeL : ∀ y : Lˣ, ‖((y : L) : M.field)‖ = 1 →
      χL.toMonoidHom y = (χs.toMonoidHom.comp a.symm.toMonoidHom) y := by
    intro y hy
    have hy' : (F'.asPadicField (p := p)).canonicalNorm ((a.symm y : F'.fieldˣ) : F'.field) = 1 := by
      rw [← Langlands.Global.restrictAlgEquiv_norm F F' M h]
      have hv : (IntermediateField.restrictAlgEquiv h) ((a.symm y : F'.fieldˣ) : F'.field) =
          (y : L) := congrArg (fun z : Lˣ => (z : L)) (a.apply_symm_apply y)
      rw [hv]
      exact hy
    change χL y = χs (a.symm y)
    rw [hagree _ hy']
    change χL y = χL (a (a.symm y))
    rw [a.apply_symm_apply]
  have hunit : HasExactUnitNormStabilizer L (χs.toMonoidHom.comp a.symm.toMonoidHom) :=
    hasExactUnitNormStabilizer_congr L _ _ hagreeL hN hσ hstab
  exact unitNormWeilStabilizerTransport p F F' e he χs hunit

set_option maxHeartbeats 1000000 in
/-- Realize the datum on any paired-place configuration with the exact Weil stabilizer
for the auxiliary character and the prescribed valuation-unit restriction at `P`. -/
theorem harrisDatumCharacterRealizationExactStabilizer :
    HarrisDatumCharacterRealizationExactStabilizerStatement.{uF, uE, uE', uL} := by
  intro p hp F F' E E' L _ _ _ _ _ _ _ _ _ _ _ _ K₀ P Ps φ φs θ hconf e he χ₀
  let _ := (fieldData F F').topology
  unfold IsPairedPlaceConfiguration at hconf
  obtain ⟨hST, hNC, hK₀, -, -, -, -, -, hpw, hplaces, hQ, hφc, hφc', hφsc, hφsc', -, hφ2, -,
    hφs2⟩ := hconf
  -- The four distinct places of `E`.
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil,
    or_false, forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true, ne_eq] at hpw
  obtain ⟨⟨h12, h13, h14⟩, ⟨h23, h24⟩, h34, -⟩ := hpw
  obtain ⟨hpP, huP⟩ := hplaces P.v (by simp)
  obtain ⟨hpcP, hucP⟩ := hplaces (conjPlace E P.v) (by simp)
  obtain ⟨hpPs, huPs⟩ := hplaces Ps.v (by simp)
  obtain ⟨hpcPs, hucPs⟩ := hplaces (conjPlace E Ps.v) (by simp)
  have hcompP := (hQ P (by simp)).1
  have hcompPs := (hQ Ps (by simp)).1
  -- An auxiliary unit prescription that forces the exact Weil stabilizer.
  obtain ⟨χs₀, hstab⟩ := exists_exactWeilStabilizer_of_unitAgreement F F'
  -- The finite set `S = {P.v', Ps.v'}` is disjoint from its conjugate.
  classical
  set c' := (IsCMField.complexConj E').toRingEquiv with hc'
  have hPPs : P.v' ≠ Ps.v' := ne_of_liesOver (v₁ := P.v) (v₂ := Ps.v) h13
  let S : Finset (FinitePlace E') := {P.v', Ps.v'}
  have hlo1 := conjPlace_liesOver P.v P.v'
  have hlo2 := conjPlace_liesOver Ps.v Ps.v'
  have hdisj : Disjoint S (S.map (finitePlaceEquiv c').toEmbedding) := by
    rw [Finset.disjoint_left]
    intro a ha hac
    simp only [S, Finset.mem_insert, Finset.mem_singleton, Finset.map_insert,
      Finset.map_singleton, Equiv.coe_toEmbedding] at ha hac
    rcases ha with rfl | rfl <;> rcases hac with h | h
    · exact ne_of_liesOver (v₁ := P.v) (v₂ := conjPlace E P.v) h12 h
    · exact ne_of_liesOver (v₁ := P.v) (v₂ := conjPlace E Ps.v) h14 h
    · exact ne_of_liesOver (v₁ := Ps.v) (v₂ := conjPlace E P.v) (Ne.symm h23) h
    · exact ne_of_liesOver (v₁ := Ps.v) (v₂ := conjPlace E Ps.v) h34 h
  -- The prescribed unit characters.
  let G : (w : FinitePlace E') → (w.adicCompletionIntegers E')ˣ →ₜ* ℂˣ := fun w =>
    if h : w = P.v' then (by subst h; exact unitCharacter (K' := F'.asPadicField (p := p)) P.v' φ hφc χ₀)
    else if h' : w = Ps.v' then (by subst h'; exact unitCharacter (K' := F'.asPadicField (p := p)) Ps.v' φs hφsc χs₀)
    else 1
  have hGP : G P.v' = unitCharacter (K' := F'.asPadicField (p := p)) P.v' φ hφc χ₀ := by simp [G]
  have hGPs : G Ps.v' = unitCharacter (K' := F'.asPadicField (p := p)) Ps.v' φs hφsc χs₀ := by simp [G, Ne.symm hPPs]
  -- The weights.
  have h2 : Module.finrank ℚ K₀ = 2 := hK₀.1
  have : IsTotallyComplex K₀ := hK₀.2.1
  let j : K₀ →+* E := K₀.val.toRingHom
  let τK : K₀ →+* ℂ := Classical.choice inferInstance
  obtain ⟨m, X, hm, hXc, hXinf, hXdist, hXunits⟩ :=
    cmRegularUnitPrescription.{uE', uE} K₀ h2 E' ((algebraMap E E').comp j) τK
      (regularWeights j τK) (regularWeights_anticyclotomic h2 j τK)
      (regularWeights_distinct j τK) S hdisj (fun w => G w.1)
  -- The weight-one twist, used when `[E' : E]` is even.
  have hn0 : 0 < Module.finrank E E' := Module.finrank_pos
  obtain ⟨ψ, hψc, hψu, hψY, hψalg⟩ : ∃ ψ : HeckeCharacter E',
      IsConjugateInverse ψ ∧ (∀ w ∈ S, ψ.IsUnramifiedAt w) ∧
      (∀ (τ : InfinitePlace E) (w w' : InfinitePlace E') [w.LiesOver τ] [w'.LiesOver τ]
        (x : (InfiniteCompletion E τ)ˣ),
        ψ.infiniteComponent w (Units.map (LiesOver.completionMap (v := τ) (w := w)).toMonoidHom x) =
          ψ.infiniteComponent w'
            (Units.map (LiesOver.completionMap (v := τ) (w := w')).toMonoidHom x)) ∧
      IsAlgebraicAfterTwist ((Module.finrank E E' - 1) % 2) (X * ψ) := by
    rcases Nat.even_or_odd (Module.finrank E E') with hev | hodd
    · obtain ⟨ψ, hψc, hψinf, hψu⟩ :=
        cmHalfWeightCharacter.{uE'} E' (halfWeights j τK) (halfWeights_pure h2 j τK) S hdisj
      refine ⟨ψ, hψc, hψu, fun τ w w' _ _ x => halfWeight_component_eq j τK ψ hψinf τ w w' x, ?_⟩
      have hmod : (Module.finrank E E' - 1) % 2 = 1 := by
        obtain ⟨k, hk⟩ := hev
        omega
      rw [hmod]
      exact isAlgebraicAfterTwist_one_of_types X ψ _ _ hXinf hψinf
    · refine ⟨1, fun x => by simp, fun w _ a _ => rfl, fun τ w w' _ _ x => rfl, ?_⟩
      have hmod : (Module.finrank E E' - 1) % 2 = 0 := by
        obtain ⟨k, hk⟩ := hodd
        omega
      have hX1 : X * (1 : HeckeCharacter E') = X := mul_one X
      rw [hmod, hX1]
      exact isAlgebraicAfterTwist_zero_of_type X _ hXinf
  -- The datum character and its local components.
  let ξ : HeckeCharacter E' := X * ψ
  let χ : FieldCharacter F F' := (ξ.finiteComponent P.v').comp
    ⟨Units.map φ.symm.toRingHom.toMonoidHom, hφc'.units_map _⟩
  let χs : FieldCharacter F F' := (ξ.finiteComponent Ps.v').comp
    ⟨Units.map φs.symm.toRingHom.toMonoidHom, hφsc'.units_map _⟩
  have hmemP : P.v' ∈ S := by simp [S]
  have hmemPs : Ps.v' ∈ S := by simp [S]
  have hXP : ∀ b : (P.v'.adicCompletionIntegers E')ˣ,
      X.finiteComponent P.v' (Units.map (P.v'.adicCompletionIntegers E').subtype.toMonoidHom b) =
        unitCharacter (K' := F'.asPadicField (p := p)) P.v' φ hφc χ₀ b := by
    intro b
    rw [hXunits ⟨P.v', hmemP⟩ b]
    change G P.v' b = _
    rw [hGP]
  have hXPs : ∀ b : (Ps.v'.adicCompletionIntegers E')ˣ,
      X.finiteComponent Ps.v'
          (Units.map (Ps.v'.adicCompletionIntegers E').subtype.toMonoidHom b) =
        unitCharacter (K' := F'.asPadicField (p := p)) Ps.v' φs hφsc χs₀ b := by
    intro b
    rw [hXunits ⟨Ps.v', hmemPs⟩ b]
    change G Ps.v' b = _
    rw [hGPs]
  have hagree : ∀ u : F'.fieldˣ, (F'.asPadicField (p := p)).canonicalNorm (u : F'.field) = 1 →
      χ u = χ₀ u := fun u hu =>
    finiteComponent_mul_eq P.v' (fieldData F F') rfl φ hφc X ψ χ₀ hXP (hψu _ hmemP) u hu
  have hagrees : ∀ u : F'.fieldˣ, (F'.asPadicField (p := p)).canonicalNorm (u : F'.field) = 1 →
      χs u = χs₀ u := fun u hu =>
    finiteComponent_mul_eq Ps.v' (fieldData F F') rfl φs hφsc X ψ χs₀ hXPs (hψu _ hmemPs) u hu
  -- The datum.
  have hA : InfinityType.IsAnticyclotomic
      (fun σ => (m : ℤ) * regularWeights (E := E) j τK σ : InfinityType E') := by
    intro σ
    simp only
    rw [regularWeights_anticyclotomic h2 j τK σ]
    ring
  refine ⟨χ, χs, ξ, ⟨hK₀, hST, hNC, hpP, hcompP, huP, hucP, hpPs, hcompPs, huPs, hucPs,
    Ne.symm h13, Ne.symm h23, hstab e he χs hagrees,
    isAlgebraicAfterTwist_of_mod_two ξ _ hψalg,
    isRelativelyRegular_of_weights X ψ _ hXinf hA hψY
      (fun τ w w' _ _ hne => weights_ne_of_distinct h2 j τK _ hA hXdist τ w w' hne),
    isConjugateInverse_mul X ψ hXc hψc, ?_, ?_⟩, ?_⟩
  · intro x y hy
    have hyx : (y : F'.field) = φ (x : FiniteCompletion E' P.v') :=
      Subtype.ext (hy.trans (hφ2 (x : FiniteCompletion E' P.v')).symm)
    change ξ.finiteComponent P.v' x = ξ.finiteComponent P.v' (Units.map φ.symm.toRingHom.toMonoidHom y)
    congr 1
    apply Units.ext
    change (x : FiniteCompletion E' P.v') = φ.symm (y : F'.field)
    rw [hyx, RingEquiv.symm_apply_apply]
  · intro x y hy
    have hyx : (y : F'.field) = φs (x : FiniteCompletion E' Ps.v') :=
      Subtype.ext (hy.trans (hφs2 (x : FiniteCompletion E' Ps.v')).symm)
    change ξ.finiteComponent Ps.v' x =
      ξ.finiteComponent Ps.v' (Units.map φs.symm.toRingHom.toMonoidHom y)
    congr 1
    apply Units.ext
    change (x : FiniteCompletion E' Ps.v') = φs.symm (y : F'.field)
    rw [hyx, RingEquiv.symm_apply_apply]
  · intro u hu
    exact hagree u ((discreteValuation_eq_one_iff (fieldData F F') _).mp hu)

end Langlands.Global
