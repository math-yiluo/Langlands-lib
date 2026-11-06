import Langlands.Global.Arithmetic.HenniartHarrisDatumReductionStatement
import Langlands.Global.Arithmetic.CMRegularUnitPrescriptionProof
import Langlands.Global.Arithmetic.HarrisDatumArchimedean
import Langlands.Global.Arithmetic.HarrisDatumLocal
import Langlands.Global.Arithmetic.HarrisDatumAuxiliary

/-! # The characters of Harris's Proposition 4.8 datum on a paired-place configuration -/

noncomputable section

universe uF uE uE' uL

namespace Langlands.Global.HarrisDatum

open NumberField IsDedekindDomain LocalFactor.CommonClosure GeneralPosition Harris
open AdelicFunctoriality

section Conjugation

variable {E E' : Type*} [Field E] [Field E'] [NumberField E] [NumberField E'] [IsCMField E]
  [IsCMField E'] [Algebra E E']

theorem complexConj_algebraMap (x : E) :
    IsCMField.complexConj E' (algebraMap E E' x) =
      algebraMap E E' (IsCMField.complexConj E x) := by
  let φ : E' →+* ℂ := Classical.choice inferInstance
  apply φ.injective
  rw [IsCMField.complexEmbedding_complexConj]
  have h := IsCMField.complexEmbedding_complexConj (K := E) (φ.comp (algebraMap E E')) x
  simp only [RingHom.comp_apply] at h
  rw [h]

theorem conjPlace_liesOver (v : FinitePlace E) (w : FinitePlace E')
    [w.asIdeal.LiesOver v.asIdeal] :
    (finitePlaceEquiv (IsCMField.complexConj E').toRingEquiv w).asIdeal.LiesOver
      (conjPlace E v).asIdeal := by
  constructor
  ext x
  have hv := Ideal.over_def w.asIdeal v.asIdeal
  change RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv x ∈ v.asIdeal ↔
    RingOfIntegers.mapRingEquiv (IsCMField.complexConj E').toRingEquiv (algebraMap _ _ x) ∈
      w.asIdeal
  rw [hv, Ideal.mem_comap]
  have heq : algebraMap (𝓞 E) (𝓞 E')
      (RingOfIntegers.mapRingEquiv (IsCMField.complexConj E).toRingEquiv x) =
      RingOfIntegers.mapRingEquiv (IsCMField.complexConj E').toRingEquiv
        (algebraMap (𝓞 E) (𝓞 E') x) := by
    apply RingOfIntegers.ext
    exact (complexConj_algebraMap (x : E)).symm
  rw [heq]

omit [NumberField E] [NumberField E'] [IsCMField E] [IsCMField E'] in
theorem ne_of_liesOver {v₁ v₂ : FinitePlace E} {w₁ w₂ : FinitePlace E'}
    [w₁.asIdeal.LiesOver v₁.asIdeal] [w₂.asIdeal.LiesOver v₂.asIdeal] (h : v₁ ≠ v₂) :
    w₁ ≠ w₂ := by
  rintro rfl
  apply h
  exact HeightOneSpectrum.ext ((Ideal.over_def w₁.asIdeal v₁.asIdeal).trans
    (Ideal.over_def w₁.asIdeal v₂.asIdeal).symm)

end Conjugation

set_option maxHeartbeats 1000000 in
/-- The character realization on a paired-place configuration, given the weight-one CM
characters (used only when `[E' : E]` is even). -/
theorem harrisDatumCharacterRealization_of_halfWeight
    (hHalf : CMHalfWeightCharacterStatement.{uE'}) :
    HarrisDatumCharacterRealizationStatement.{uF, uE, uE', uL} := by
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
  -- The auxiliary character in general position.
  obtain ⟨χs₀, hgp⟩ := exists_generalPosition_of_unitAgreement F F'
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
        hHalf E' (halfWeights j τK) (halfWeights_pure h2 j τK) S hdisj
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
    Ne.symm h13, Ne.symm h23, hgp e he χs hagrees,
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

end Langlands.Global.HarrisDatum

namespace Langlands.Global

/-- The exact target `HarrisDatumCharacterRealizationOfHalfWeightStatement`. -/
theorem harrisDatumCharacterRealizationOfHalfWeight :
    HarrisDatumCharacterRealizationOfHalfWeightStatement.{uF, uE, uE', uL} :=
  HarrisDatum.harrisDatumCharacterRealization_of_halfWeight

end Langlands.Global
