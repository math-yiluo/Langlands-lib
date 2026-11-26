import Langlands.Global.Arithmetic.HarrisProposition48SpacedData
import Langlands.Global.Arithmetic.HarrisDatumCharacterRealizationProof
import Langlands.Global.Arithmetic.HenniartCommonBaseRealizationProof
import Langlands.Global.Arithmetic.CMHalfWeightCharacterProof

/-!
# Henniart's Harris datum with even real degree and weights at distance at least two

The construction of the datum of Harris (1998), Proposition 4.8, in Henniart's
globalization (Henniart 2000, §§3.3–3.6), with the two clauses of
`IsProposition48SpacedDatum`: the common base field contains a square root of a positive
rational number that is not a square, so its real degree is even, and the inducing
character is built with the weights `2 · regularWeights`, which are at distance at least
two. The statements are proved here; the published `HenniartHarrisDatumStatement` and its
proof are unchanged.
-/

noncomputable section

universe uF uE uE' uL

namespace Langlands.Global

open NumberField LocalFactor.CommonClosure GeneralPosition Harris
open AdelicFunctoriality

namespace Harris

/-- The character realization of `HarrisDatumCharacterRealizationStatement` with weights
at distance at least two: on every paired-place configuration, for every normalized
reciprocity family `e` and every continuous character `χ₀` of `F'ˣ`, there are characters
`χ, χs` of `F'ˣ` and a Hecke character `ξ` of `E'` satisfying the published
`IsProposition48Datum e χ χs K₀ P Ps ξ`, with weights at distance at least two above every
archimedean place of `E` (`IsRelativelySpaced E ξ`), and with `χ` equal to `χ₀` on the
units of the valuation ring of `F'`. -/
def HarrisDatumCharacterRealizationSpacedStatement : Prop :=
  ∀ {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (F' : Extension F)
    (E : Type uE) (E' : Type uE') (L : Type uL)
    [Field E] [Field E'] [Field L] [NumberField E] [NumberField E'] [NumberField L]
    [IsCMField E] [IsCMField E'] [IsCMField L]
    [Algebra E E'] [Algebra E L] [Algebra E' L]
    (K₀ : IntermediateField ℚ E) (P Ps : PlaceDatum F F' E E' L)
    (φ : FiniteCompletion E' P.v' ≃+* F'.field)
    (φs : FiniteCompletion E' Ps.v' ≃+* F'.field)
    (θ : (L ≃ₐ[E] L) ≃*
      ((galoisClosure F F').field ≃ₐ[F.Carrier] (galoisClosure F F').field)),
    IsPairedPlaceConfiguration K₀ P Ps φ φs θ →
    ∀ (e : ReciprocityFamily F), NormalizedReciprocity F e →
    ∀ χ₀ : FieldCharacter F F',
      ∃ (χ χs : FieldCharacter F F') (ξ : HeckeCharacter E'),
        IsProposition48Datum e χ χs K₀ P Ps ξ ∧ IsRelativelySpaced E ξ ∧
        ∀ u : F'.fieldˣ, (fieldData F F').discreteValuation (u : F'.field) = 1 →
          χ u = χ₀ u

end Harris

/-- `HenniartHarrisDatumStatement` with `Harris.IsProposition48SpacedDatum` in place of
`IsProposition48Datum`: one CM field `E` with `ι₀ : E_{v₀} ≅ F` serves every intermediate
field `F'` of `M/F`, and for every normalized reciprocity family and every continuous
character `χ₀` of `F'ˣ` there is a paired-place configuration over `E` at `v₀` with data
of Harris's Proposition 4.8 on it whose base field has even real degree and whose
inducing character has weights at distance at least two. -/
def HenniartHarrisDatumSpacedStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (M : Extension F),
    letI := F.canonicalTopology
    ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : IsCMField E)
      (v₀ : FinitePlace E) (ι₀ : FiniteCompletion E v₀ ≃+* F.Carrier),
      Continuous ι₀ ∧ Continuous ι₀.symm ∧
      ∀ F' : Extension F, F'.field ≤ M.field →
      ∀ (e : ReciprocityFamily F), NormalizedReciprocity F e →
      ∀ χ₀ : FieldCharacter F F',
        ∃ (E' L : Type) (_ : Field E') (_ : Field L)
          (_ : NumberField E') (_ : NumberField L)
          (_ : IsCMField E') (_ : IsCMField L)
          (_ : Algebra E E') (_ : Algebra E L) (_ : Algebra E' L)
          (K₀ : IntermediateField ℚ E) (P Ps : PlaceDatum F F' E E' L)
          (φ : FiniteCompletion E' P.v' ≃+* F'.field)
          (φs : FiniteCompletion E' Ps.v' ≃+* F'.field)
          (θ : (L ≃ₐ[E] L) ≃*
            ((galoisClosure F F').field ≃ₐ[F.Carrier] (galoisClosure F F').field))
          (χ χs : FieldCharacter F F') (ξ : HeckeCharacter E'),
          IsPairedPlaceConfiguration K₀ P Ps φ φs θ ∧
          P.v = v₀ ∧
          (∀ x : E, P.iso (algebraMap E (FiniteCompletion E P.v) x) =
            ι₀ (algebraMap E (FiniteCompletion E v₀) x)) ∧
          IsProposition48SpacedDatum e χ χs K₀ P Ps ξ ∧
          ∀ u : F'.fieldˣ, (fieldData F F').discreteValuation (u : F'.field) = 1 →
            χ u = χ₀ u

end Langlands.Global

namespace Langlands.Global.HarrisDatum

open NumberField IsDedekindDomain LocalFactor.CommonClosure GeneralPosition Harris
open AdelicFunctoriality

set_option maxHeartbeats 1000000 in
/-- The character realization on a paired-place configuration with weights at distance at
least two, given the weight-one CM characters (used only when `[E' : E]` is even). The
argument is that of `harrisDatumCharacterRealization_of_halfWeight` with the weights
`2 · regularWeights` in place of `regularWeights`. -/
theorem harrisDatumCharacterRealizationSpaced_of_halfWeight
    (hHalf : CMHalfWeightCharacterStatement.{uE'}) :
    Harris.HarrisDatumCharacterRealizationSpacedStatement.{uF, uE, uE', uL} := by
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
  have hspacedA : InfinityType.IsAnticyclotomic
      (fun σ => 2 * regularWeights (E := E) (E' := E') j τK σ : InfinityType E') := by
    intro σ
    simp only
    rw [regularWeights_anticyclotomic h2 j τK σ]
    ring
  have hspacedD : InfinityType.DistinctWeightsAbove ((algebraMap E E').comp j) τK
      (fun σ => 2 * regularWeights (E := E) (E' := E') j τK σ : InfinityType E') := by
    intro σ σ' h
    apply regularWeights_distinct j τK
    exact mul_left_cancel₀ (two_ne_zero : (2 : ℤ) ≠ 0) h
  obtain ⟨m, X, hm, hXc, hXinf, hXdist, hXunits⟩ :=
    cmRegularUnitPrescription.{uE', uE} K₀ h2 E' ((algebraMap E E').comp j) τK
      (fun σ => 2 * regularWeights j τK σ) hspacedA hspacedD S hdisj (fun w => G w.1)
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
      (fun σ => (m : ℤ) * (2 * regularWeights (E := E) j τK σ) : InfinityType E') := by
    intro σ
    simp only
    rw [regularWeights_anticyclotomic h2 j τK σ]
    ring
  have hdist2 : ∀ (τ : InfinitePlace E) (w w' : InfinitePlace E') [w.LiesOver τ]
      [w'.LiesOver τ], w ≠ w' →
      2 ≤ |(fun σ => (m : ℤ) * (2 * regularWeights (E := E) j τK σ) : InfinityType E')
          (lift τ w) -
        (fun σ => (m : ℤ) * (2 * regularWeights (E := E) j τK σ) : InfinityType E')
          (lift τ w')| := by
    intro τ w w' _ _ hne
    have hne' := weights_ne_of_distinct h2 j τK _ hA hXdist τ w w' hne
    simp only at hne' ⊢
    set d : ℤ := (m : ℤ) * regularWeights (E := E) j τK (lift τ w) -
      (m : ℤ) * regularWeights (E := E) j τK (lift τ w') with hd
    have hd0 : d ≠ 0 := by
      intro h0
      apply hne'
      linear_combination 2 * h0
    have hrw : (m : ℤ) * (2 * regularWeights (E := E) j τK (lift τ w)) -
        (m : ℤ) * (2 * regularWeights (E := E) j τK (lift τ w')) = 2 * d := by
      rw [hd]
      ring
    rw [hrw, abs_mul]
    have : (1 : ℤ) ≤ |d| := Int.one_le_abs hd0
    simp only [abs_two]
    linarith
  refine ⟨χ, χs, ξ, ⟨hK₀, hST, hNC, hpP, hcompP, huP, hucP, hpPs, hcompPs, huPs, hucPs,
    Ne.symm h13, Ne.symm h23, hgp e he χs hagrees,
    isAlgebraicAfterTwist_of_mod_two ξ _ hψalg,
    isRelativelyRegular_of_weights X ψ _ hXinf hA hψY
      (fun τ w w' _ _ hne => weights_ne_of_distinct h2 j τK _ hA hXdist τ w w' hne),
    isConjugateInverse_mul X ψ hXc hψc, ?_, ?_⟩,
    Harris.isRelativelySpaced_of_weights X ψ _ hXinf hA hψY hdist2, ?_⟩
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

open NumberField CMRealization FieldRealization LocalFactor.CommonClosure GeneralPosition Harris

/-- The datum of Proposition 4.8 with even real degree and weights at distance at least two
is built over Henniart's common base: the argument of `henniartCommonBaseRealization`, with
the square root `sqrtPos` of the positive non-square `posSq` in the base field, followed by
`harrisDatumCharacterRealizationSpaced_of_halfWeight` and the published
`cmHalfWeightCharacter`. -/
theorem henniartHarrisDatumSpaced : HenniartHarrisDatumSpacedStatement.{uF} := by
  intro p hp F M
  let _ := F.canonicalTopology
  -- A finite Galois extension `Ω / ℚ_[p]` containing `M̃`.
  obtain ⟨Ω, _, _, _, _, _, aΩ, tΩ⟩ :=
    exists_galois_extension ((galoisClosure F M).asPadicField (p := p))
  let _ : Algebra ℚ_[p] (galoisClosure F M).field :=
    ((galoisClosure F M).asPadicField (p := p)).algebra
  have : IsScalarTower ℚ_[p] F.Carrier (galoisClosure F M).field :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let _ : Algebra F.Carrier Ω :=
    ((algebraMap (galoisClosure F M).field Ω).comp
      (algebraMap F.Carrier (galoisClosure F M).field)).toAlgebra
  have : IsScalarTower F.Carrier (galoisClosure F M).field Ω :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower ℚ_[p] F.Carrier Ω :=
    IsScalarTower.of_algebraMap_eq fun r => by
      rw [IsScalarTower.algebraMap_apply ℚ_[p] (galoisClosure F M).field Ω,
        IsScalarTower.algebraMap_apply ℚ_[p] F.Carrier (galoisClosure F M).field]
      rfl
  -- The CM rational Galois model of `Ω` and the CM base field `E`.
  let _ : Algebra (cmModel p Ω) Ω := (cmModelEmbedding p Ω).toRingHom.toAlgebra
  have hxaE : sqrtNeg p Ω ∈ modelField p Ω (cmModel p Ω) F.Carrier :=
    mem_modelField_of_padic p Ω (cmModel p Ω) F.Carrier (cmModelEmbedding_sqrtNeg p Ω)
  have : IsCMField (modelField p Ω (cmModel p Ω) F.Carrier) :=
    isCMField_of_sq_neg (M := cmModel p Ω)
      (modelField_central p Ω (cmModel p Ω) F.Carrier (conjQ (cmModel p Ω)) conjQ_central)
      (negSq_neg p) (x := ⟨sqrtNeg p Ω, hxaE⟩)
      ((algebraMap (modelField p Ω (cmModel p Ω) F.Carrier) (cmModel p Ω)).injective (by
        rw [map_pow, ← IsScalarTower.algebraMap_apply]
        exact sqrtNeg_sq p Ω))
  have key := pairedPlaceConfiguration_of_le F M Ω (cmModel p Ω) (cmModelEmbedding_adjoin p Ω)
    (negSq_neg p) (posSq_pos p Ω) (negSq_isSquare p) (sqrtNeg_sq p Ω) (sqrtPos_sq p Ω)
    (cmModelEmbedding_sqrtNeg p Ω) (cmModelEmbedding_sqrtPos p Ω) (flipPos p Ω)
    (flipPos_central p Ω) (flipPos_sqrtNeg p Ω) (flipPos_sqrtPos p Ω)
  -- The common place and completion isomorphism, read off at `F' = M`.
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, P₀, _, _, _, _, hconf₀, hv₀, hj₀⟩ :=
    key M le_rfl
  have hiso₀ : Continuous P₀.iso ∧ Continuous P₀.iso.symm := by
    unfold IsPairedPlaceConfiguration at hconf₀
    obtain ⟨-, -, -, -, -, -, -, -, -, -, hQ, -⟩ := hconf₀
    exact ⟨(hQ P₀ (by simp)).2.1, (hQ P₀ (by simp)).2.2.1⟩
  -- Even real degree: the base field contains a square root of `posSq`.
  have hxdE : sqrtPos p Ω ∈ modelField p Ω (cmModel p Ω) F.Carrier :=
    mem_modelField_of_padic p Ω (cmModel p Ω) F.Carrier (cmModelEmbedding_sqrtPos p Ω)
  have hns : ¬ IsSquare (posSq p Ω) := fun ⟨r, hr⟩ =>
    posSq_not_isSquare p Ω ⟨algebraMap ℚ _ r, by rw [hr, map_mul]⟩
  have heven : Harris.HasEvenRealDegree (modelField p Ω (cmModel p Ω) F.Carrier) :=
    Harris.hasEvenRealDegree_of_sq_pos (posSq_pos p Ω) hns (x := ⟨sqrtPos p Ω, hxdE⟩)
      ((algebraMap (modelField p Ω (cmModel p Ω) F.Carrier) (cmModel p Ω)).injective (by
        rw [map_pow, ← IsScalarTower.algebraMap_apply]
        exact sqrtPos_sq p Ω))
  refine ⟨modelField p Ω (cmModel p Ω) F.Carrier, inferInstance, inferInstance, inferInstance,
    P₀.v, P₀.iso, hiso₀.1, hiso₀.2, fun F' hF' e he χ₀ => ?_⟩
  obtain ⟨E', L, i₁, i₂, i₃, i₄, i₅, i₆, i₇, i₈, i₉, K₀, P, Ps, φ, φs, θ, hconf, hv, hj⟩ :=
    key F' hF'
  obtain ⟨χ, χs, ξ, hdatum, hspaced, hagree⟩ :=
    HarrisDatum.harrisDatumCharacterRealizationSpaced_of_halfWeight.{uF, 0, 0, 0}
      cmHalfWeightCharacter F F' (modelField p Ω (cmModel p Ω) F.Carrier) E' L K₀ P Ps φ φs θ
      hconf e he χ₀
  refine ⟨E', L, i₁, i₂, i₃, i₄, i₅, i₆, i₇, i₈, i₉, K₀, P, Ps, φ, φs, θ, χ, χs, ξ, hconf, ?_, ?_,
    ⟨hdatum, heven, hspaced⟩, hagree⟩
  · exact IsDedekindDomain.HeightOneSpectrum.ext (Ideal.ext fun b => (hv b).trans (hv₀ b).symm)
  · intro x
    rw [hj, hj₀]

end Langlands.Global
