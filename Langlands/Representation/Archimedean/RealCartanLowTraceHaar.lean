import Langlands.Representation.Archimedean.RealCartanBlockFilters
import Langlands.Representation.Archimedean.RealCartanProductAverage
import Langlands.Representation.Archimedean.RealLeviCompactChartSupport
import Langlands.Representation.Archimedean.RealSmallOrthogonalFourier

/-! # Weighted block Haar integration of the surviving real Cartan term -/

noncomputable section

open Matrix MeasureTheory
open scoped Matrix.Norms.Operator ContDiff Manifold

namespace Langlands.Archimedean.RealCartanLowTraceHaar

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean GramFormula PrincipalSeriesExtension
  RealBlockPosition RealBlockRotation RealBlockFourierFinite RealInducedStandardBound
  RealStandardCompactAverage RealCartanBlockLayout RealCartanBlockFilters RealCartanFilterSupport
  RealCartanProductAverage RealLeviChart RealLeviSlices RealLeviCompactChart
  RealSmallOrthogonalFourier RealSmallOrthogonalHaar

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

local notation "G" n:max => Langlands.GeneralLinear n ℝ
local notation "K" n:max => Matrix.unitaryGroup (Fin n) ℝ
local notation "Mat" n:max => Matrix (Fin n) (Fin n) ℝ

section Embedding

variable {c : ℕ} (sz : Fin c → ℕ) (i : Fin c)
local notation "N" => ∑ i, sz i

private theorem pos_injective (j : Fin c) : Function.Injective (pos sz j) :=
  fun _ _ h => (posFiberEquiv sz j).injective (Subtype.ext h)

private theorem embL_single (a b : Fin (sz i)) (r : ℝ) :
    embL sz i (single a b r) = single (pos sz i a) (pos sz i b) r := by
  ext p q
  have hpos (k : Fin N) : ∃ j : Fin c, ∃ u : Fin (sz j), pos sz j u = k :=
    ⟨cls sz k, pos_cls sz k⟩
  obtain ⟨j, u, hp⟩ := hpos p
  obtain ⟨k, v, hq⟩ := hpos q
  rw [← hp, ← hq]
  by_cases hjk : j = k
  · subst k
    rw [embL_apply, blockDiagHom_pos_pos_self]
    by_cases hji : j = i
    · subst j
      simp only [Pi.single_eq_same, Matrix.single_apply, (pos_injective sz i).eq_iff]
    · rw [Pi.single_eq_of_ne hji, Matrix.zero_apply, Matrix.single_apply,
        ite_eq_right (fun he => hji (by simpa only [cls_pos] using congrArg (cls sz) he.1.symm))]
  · rw [embL_apply, blockDiagHom_pos_pos_of_ne _ _ hjk, Matrix.single_apply]
    exact (ite_eq_right (fun he => hjk (by
      have h₁ : i = j := by simpa only [cls_pos] using congrArg (cls sz) he.1
      have h₂ : i = k := by simpa only [cls_pos] using congrArg (cls sz) he.2
      exact h₁.symm.trans h₂))).symm

private theorem signReflection_eq_one_sub {n : ℕ} (a : Fin n) :
    (signReflection n a : Mat n) = 1 - (2 : ℝ) • single a a 1 := by
  ext p q
  simp only [signReflection_val, Matrix.diagonal_apply, Matrix.sub_apply, Matrix.one_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.single_apply]
  split_ifs <;> (try norm_num) <;> aesop

/-- The Levi embedding sends each internal reflection to the corresponding position reflection. -/
theorem emb_signReflection (j : Fin (sz i)) :
    emb sz i (Unitary.toUnits (signReflection (sz i) j)) =
      Unitary.toUnits (signReflection N (pos sz i j)) := by
  apply Units.ext
  rw [emb_val]
  change embA sz i (signReflection (sz i) j : Mat (sz i)) = (signReflection N (pos sz i j) : Mat N)
  rw [signReflection_eq_one_sub, signReflection_eq_one_sub, embA_eq]
  have h : (1 - (2 : ℝ) • single j j (1 : ℝ) - 1 : Mat (sz i)) = -(2 : ℝ) • single j j 1 := by
    rw [neg_smul]
    abel
  rw [h, map_smul, embL_single, neg_smul, sub_eq_add_neg]

/-- The embedded rotation uses the consecutive coordinates at its block start. -/
theorem emb_blockRotation {p : ℕ} (hp : p + 1 < sz i) (θ : ℝ) :
    emb sz i (blockRotation (sz i) p θ) = blockRotation N (start sz i + p) θ := by
  let hn : start sz i + p + 1 < N := by
    have h := (pos sz i (ib hp)).2
    rw [val_pos] at h
    simpa only [ib, add_assoc] using h
  have ha : pos sz i (ia hp) = ia hn := Fin.ext (by rw [val_pos]; rfl)
  have hb : pos sz i (ib hp) = ib hn := Fin.ext (by rw [val_pos]; simp only [ib, add_assoc])
  apply Units.ext
  rw [emb_val, blockRotation_val_eq hp, blockRotation_val_eq hn, embA_eq]
  unfold rotMatrix
  rw [show (1 + (Real.cos θ - 1) • blockProj hp + Real.sin θ • rotationGenerator (sz i) p - 1 :
      Mat (sz i)) = (Real.cos θ - 1) • blockProj hp + Real.sin θ • rotationGenerator (sz i) p by abel]
  rw [map_add, map_smul, map_smul, rotationGenerator_eq hp, rotationGenerator_eq hn]
  unfold blockProj
  simp only [map_add, map_sub, embL_single, ha, hb]
  abel

private theorem continuous_emb_toUnits : Continuous fun k : K (sz i) => emb sz i (Unitary.toUnits k) := by
  rw [show (fun k : K (sz i) => emb sz i (Unitary.toUnits k)) =
      fun k => Unitary.toUnits (embK sz i k) from funext fun k => (toUnits_embK sz i k).symm]
  apply continuous_unitary_toUnits.comp
  exact ((contDiff_embA sz i).continuous.comp continuous_subtype_val).subtype_mk _

end Embedding

section Cast

/-- Transport the compact group across equality of matrix ranks. -/
def orthogonalCast {n m : ℕ} (h : n = m) : K n ≃* K m := by
  cases h
  exact MulEquiv.refl _

theorem continuous_orthogonalCast {n m : ℕ} (h : n = m) : Continuous (orthogonalCast h) := by
  cases h
  exact continuous_id

@[simp]
theorem orthogonalCast_signReflection {n m : ℕ} (h : n = m) (j : Fin n) :
    orthogonalCast h (signReflection n j) = signReflection m (Fin.cast h j) := by
  cases h
  rfl

private theorem toUnits_orthogonalCast_rotation {m : ℕ} (h : 2 = m) (θ : ℝ) :
    Unitary.toUnits (orthogonalCast h (rotation θ)) = blockRotation m 0 θ := by
  cases h
  exact toUnits_rotation θ

private theorem list_ofFn_cast {α : Type*} {n m : ℕ} (h : n = m) (f : Fin n → α) :
    List.ofFn f = List.ofFn (fun j : Fin m => f (Fin.cast h.symm j)) := by
  cases h
  rfl

private theorem integral_orthogonalCast {n m : ℕ} (h : n = m) (f : K n → ℂ) :
    (∫ k, f k ∂compactHaar n) = ∫ k, f (orthogonalCast h.symm k) ∂compactHaar m := by
  cases h
  rfl

end Cast

section Average

open RealPrincipalSeriesDuality RealLeviLimit

attribute [local instance] measurableSpaceK RealLeviBlockHaar.secondCountableTopology_O
  RealLeviBlockHaar.secondCountableTopology_GL
local instance borelSpaceK (n : ℕ) : BorelSpace (unitaryCompact ℝ n) := ⟨rfl⟩
local instance locallyCompactGL (n : ℕ) : LocallyCompactSpace (G n) :=
  Units.isOpenEmbedding_val.locallyCompactSpace

/-- The determinant weight of a line or the parity-window weight of a plane. -/
def blockDensity (d : RealBlock) : C(K d.rank, ℂ) :=
  match d with
  | .character a => determinantWeight ((-1 : ℂ) ^ a.parity.val)
  | .induced a => pairDensity a.weight.natAbs

private theorem blockDensity_cast {d e : RealBlock} (h : d = e) (k : K e.rank) :
    blockDensity d (orthogonalCast (congrArg RealBlock.rank h).symm k) = blockDensity e k := by
  cases h
  rfl

variable {c : ℕ} (b : Fin c → RealBlock)
local notation "sz" => blockSizes b
local notation "N" => ∑ i, blockSizes b i
local notation "ds" => List.ofFn b

/-- The continuous within-block weight on the compact factor of the Levi chart. -/
def frameDensity (i : Fin c) : C(unitaryCompact ℝ (sz i), ℂ) :=
  (blockDensity (b i)).comp ⟨compactEquiv (sz i), continuous_compactEquiv (sz i)⟩

private def blockHom : LeviFrame sz →* G N :=
  (Unitary.toUnits : K N →* G N).comp (blockFrame sz)

private theorem continuous_blockHom : Continuous (blockHom b) :=
  continuous_unitary_toUnits.comp (continuous_blockFrame sz)

private theorem blockHom_mulSingle (i : Fin c) (k : unitaryCompact ℝ (sz i)) :
    blockHom b (Pi.mulSingle i k) = emb sz i (Unitary.toUnits (compactEquiv (sz i) k)) := by
  rw [blockHom, MonoidHom.comp_apply, toUnits_blockFrame, emb_eq]
  change blockDiagGL sz
    (fun j => ((Pi.mulSingle (M := fun l => unitaryCompact ℝ (sz l)) i k j :
      unitaryCompact ℝ (sz j)) : G (sz j))) = _
  congr 1
  funext j
  by_cases hj : j = i
  · subst j
    simp only [Pi.mulSingle_eq_same]
    exact Units.ext rfl
  · simp [Pi.mulSingle_eq_of_ne hj]

private def localTest (i : Fin c) (f : C(G N, ℂ)) (x : G N) : C(K (sz i), ℂ) where
  toFun k := f (emb sz i (Unitary.toUnits k) * x)
  continuous_toFun := f.continuous.comp ((continuous_emb_toUnits sz i).mul continuous_const)

private theorem factorAverage_eq_integral (i : Fin c) (f : C(G N, ℂ)) (x : G N) :
    factorAverage (blockHom b) (continuous_blockHom b) (fun j => haarK (sz j))
      (frameDensity b) i f x =
        ∫ k, blockDensity (b i) k * localTest b i f x k ∂compactHaar (sz i) := by
  rw [factorAverage_apply, compactHaar]
  let F (k : K (sz i)) := blockDensity (b i) k * localTest b i f x k
  have hF : Continuous F := (blockDensity (b i)).continuous.mul (localTest b i f x).continuous
  change _ = ∫ k, F k ∂Measure.map (compactEquiv (sz i)) (haarK (sz i))
  rw [integral_map (continuous_compactEquiv (sz i)).measurable.aemeasurable hF.aestronglyMeasurable]
  simp only [blockHom_mulSingle]
  rfl

private theorem sign_character (i : Fin c) (d : RealCharacterData) (hi : b i = .character d)
    (h : sz i = 1) :
    realPositionCharacter ds (pos sz i (Fin.cast h.symm 0)) (-1) = (-1 : ℂ) ^ d.parity.val := by
  rw [character_pos, Fin.val_cast, Fin.val_zero, hi, RealBlockPosition.realPositionCharacter_neg_one]
  rfl

private theorem blockFilter_character (i : Fin c) (d : RealCharacterData) (hi : b i = .character d)
    (f : C(G N, ℂ)) (x : G N) :
    blockFilter b i f x = ∫ k, blockDensity (b i) k * localTest b i f x k ∂compactHaar (sz i) := by
  let h : sz i = 1 := congrArg RealBlock.rank hi
  let F : C(K 1, ℂ) := (localTest b i f x).comp ⟨orthogonalCast h.symm,
    continuous_orthogonalCast h.symm⟩
  have hl : List.ofFn (pos sz i) = [pos sz i (Fin.cast h.symm 0)] := by
    rw [list_ofFn_cast h (pos sz i)]
    simp [List.ofFn_succ]
  rw [integral_orthogonalCast h]
  have hd (k : K 1) : blockDensity (b i) (orthogonalCast h.symm k) =
      determinantWeight ((-1 : ℂ) ^ d.parity.val) k := blockDensity_cast hi k
  change _ = ∫ k : K 1, blockDensity (b i) (orthogonalCast h.symm k) * F k ∂compactHaar 1
  simp only [hd]
  rw [integral_determinantWeight_one]
  have h₁ : F 1 = f x := by
    change f (emb sz i (Unitary.toUnits (orthogonalCast h.symm 1)) * x) = _
    rw [map_one, map_one, map_one, one_mul]
  have hs : F signOne = f (Unitary.toUnits (signReflection N (pos sz i (Fin.cast h.symm 0))) * x) := by
    change f (emb sz i (Unitary.toUnits (orthogonalCast h.symm (signReflection 1 0))) * x) = _
    rw [orthogonalCast_signReflection, emb_signReflection]
  rw [h₁, hs, blockFilter, blockLow, blockSlot_character b i d hi]
  change blockSigns b i f x = _
  rw [blockSigns, hl, signFilters_cons, signFilters_nil, signFilter_apply, sign_character b i d hi h]
  ring

private theorem blockFilter_induced (i : Fin c) (d : ComplexCharacterData) (hi : b i = .induced d)
    (f : C(G N, ℂ)) (x : G N) :
    blockFilter b i f x = ∫ k, blockDensity (b i) k * localTest b i f x k ∂compactHaar (sz i) := by
  let h : sz i = 2 := congrArg RealBlock.rank hi
  let F : C(K 2, ℂ) := (localTest b i f x).comp ⟨orthogonalCast h.symm,
    continuous_orthogonalCast h.symm⟩
  let p₀ := pos sz i (Fin.cast h.symm 0)
  let p₁ := pos sz i (Fin.cast h.symm 1)
  let a := Unitary.toUnits (signReflection N p₀)
  let v := Unitary.toUnits (signReflection N p₁)
  let m := d.weight.natAbs
  let p := start sz i
  have hl : List.ofFn (pos sz i) = [p₀, p₁] := by
    rw [list_ofFn_cast h (pos sz i)]
    simp [List.ofFn_succ, p₀, p₁]
  have hχ₀ : realPositionCharacter ds p₀ (-1) = inducedSign m := by
    change realPositionCharacter ds (pos sz i (Fin.cast h.symm 0)) (-1) = _
    rw [character_pos, Fin.val_cast, Fin.val_zero, hi, inducedSign_eq_pow]
    simp [realPositionCharacter, realInducedFirstCharacter, m]
  have hχ₁ : realPositionCharacter ds p₁ (-1) = 1 := by
    change realPositionCharacter ds (pos sz i (Fin.cast h.symm 1)) (-1) = _
    rw [character_pos, Fin.val_cast, hi]
    simp [realPositionCharacter, realInducedSecondCharacter]
  let E : K 2 →* G N := (emb sz i).comp (Unitary.toUnits.comp (orthogonalCast h.symm).toMonoidHom)
  have hE₀ : E reflectTwo = a := by
    change emb sz i (Unitary.toUnits (orthogonalCast h.symm (signReflection 2 0))) = _
    rw [orthogonalCast_signReflection, emb_signReflection]
  have hE₁ : E (signReflection 2 1) = v := by
    change emb sz i (Unitary.toUnits (orthogonalCast h.symm (signReflection 2 1))) = _
    rw [orthogonalCast_signReflection, emb_signReflection]
  have hrot (θ : ℝ) : E (rotation θ) = blockRotation N p θ := by
    change emb sz i (Unitary.toUnits (orthogonalCast h.symm (rotation θ))) = _
    rw [toUnits_orthogonalCast_rotation h.symm θ]
    have hp' : 0 + 1 < sz i := by rw [h]; decide
    simpa only [add_zero] using emb_blockRotation sz i hp' θ
  have hav : a * v = v * a := by
    simpa only [map_mul] using congrArg Unitary.toUnits (signReflection_mul_comm p₀ p₁)
  obtain ⟨hp, hs⟩ := blockSlot_induced b i d hi
  rw [integral_orthogonalCast h]
  have hd (k : K 2) : blockDensity (b i) (orthogonalCast h.symm k) = pairDensity m k :=
    blockDensity_cast hi k
  change _ = ∫ k : K 2, blockDensity (b i) (orthogonalCast h.symm k) * F k ∂compactHaar 2
  simp only [hd]
  rw [← integral_pairDensity, blockFilter, blockLow, hs]
  change lowProjection (mkSlot ds N p hp d) (blockSigns b i f) x = _
  rw [lowProjection_apply]
  simp only [mkSlot, lowModes, blockFourierCoefficient_eq_coeff]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  funext θ
  simp only [blockSigns, hl, signFilters_cons, signFilters_nil, signFilter_apply, hχ₀, hχ₁,
    pairSignAverage]
  change (2 : ℂ)⁻¹ * ((2 : ℂ)⁻¹ * (f (blockRotation N p θ * x) + 1 * f (v * (blockRotation N p θ * x))) +
    inducedSign m * ((2 : ℂ)⁻¹ * (f (a * (blockRotation N p θ * x)) +
      1 * f (v * (a * (blockRotation N p θ * x)))))) =
    (f (E (rotation θ) * x) + inducedSign m * f (E (reflectTwo * rotation θ) * x) +
      f (E (signReflection 2 1 * rotation θ) * x) +
      inducedSign m * f (E (reflectTwo * signReflection 2 1 * rotation θ) * x)) / 4
  simp only [map_mul, hE₀, hE₁, hrot, ← mul_assoc, hav]
  ring

private theorem blockFilter_eq_factorAverage (i : Fin c) :
    blockFilter b i = factorAverage (blockHom b) (continuous_blockHom b) (fun j => haarK (sz j))
      (frameDensity b) i := by
  apply LinearMap.ext
  intro f
  apply ContinuousMap.ext
  intro x
  rw [factorAverage_eq_integral]
  have hcase : (∃ d, b i = .character d) ∨ ∃ d, b i = .induced d := by
    cases b i with
    | character d => exact .inl ⟨d, rfl⟩
    | induced d => exact .inr ⟨d, rfl⟩
  rcases hcase with ⟨d, hd⟩ | ⟨d, hd⟩
  · exact blockFilter_character b i d hd f x
  · exact blockFilter_induced b i d hd f x

/-- The full low and sign projections are the weighted probability Haar integral on the Levi factors. -/
theorem lowProjections_signFilters_eq_integral (f : C(G N, ℂ)) (x : G N) :
    lowProjections (slots ds N) (signFilters ds (List.ofFn id) f) x =
      ∫ h : LeviFrame sz, (∏ i, frameDensity b i (h i)) * f (Unitary.toUnits (blockFrame sz h) * x)
        ∂frameMeasure sz := by
  have h := realCartanBlockFilters c b
  change ((lowProjections (slots ds N) * signFilters (n := N) ds (List.ofFn id)) f) x = _
  rw [h]
  have he : blockFilter b = fun i => factorAverage (blockHom b) (continuous_blockHom b)
      (fun j => haarK (sz j)) (frameDensity b) i := funext (blockFilter_eq_factorAverage b)
  rw [he]
  exact realCartanProductAverage c (fun i => unitaryCompact ℝ (sz i)) (blockHom b)
    (continuous_blockHom b) (fun i => haarK (sz i)) (frameDensity b) f x

private theorem signedOrthogonalPart_toUnits (k : K N) : signedOrthogonalPart (Unitary.toUnits k) = k := by
  have h1 := compactFrame_zero sz (1 : LeviFrame sz)
  rw [compactFrame_eq_mul_blockFrame, map_one, mul_one, RealLeviLimit.lowerGL_zero] at h1
  have hk := orthogonalPart_mul_right (1 : G N) k
  simpa only [one_mul, h1] using hk

/-- The surviving low-mode compact trace as a double integral over orthogonal frames and the Levi. -/
def RealCartanLowTraceHaarStatement : Prop :=
  ∀ (t : ℕ) (blocks : Fin t → RealBlock),
    let sizes := blockSizes blocks
    let n := ∑ i, sizes i
    ∀ (μ : Measure (K n)) (g : G n) (φ : C(K n, ℂ)),
      compactLowTrace μ (List.ofFn blocks) g φ =
        ∫ y, extension (shiftedExponent n (realPositionExponent (List.ofFn blocks))) 1
            (Unitary.toUnits y * g) *
          (∫ h : LeviFrame sizes, (∏ i, frameDensity blocks i (h i)) *
            φ (RealCartanCompactSupport.compactArgument g y (blockFrame sizes h))
            ∂frameMeasure sizes) ∂μ

theorem realCartanLowTraceHaar : RealCartanLowTraceHaarStatement := by
  intro t b sizes n μ g φ
  unfold compactLowTrace
  refine integral_congr_ae (ae_of_all _ fun y => ?_)
  change _ * lowProjections (slots (List.ofFn b) (∑ i, blockSizes b i))
    (signFilters (List.ofFn b) (List.ofFn id) (continuousColumn φ y))
    (Unitary.toUnits (signedOrthogonalPart (Unitary.toUnits y * g))) = _ * _
  rw [lowProjections_signFilters_eq_integral b]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun h => ?_)
  simp only [continuousColumn_apply, ← map_mul, signedOrthogonalPart_toUnits b, _root_.mul_inv_rev,
    RealCartanCompactSupport.compactArgument, mul_assoc, sizes]
  rfl

end Average

end Langlands.Archimedean.RealCartanLowTraceHaar
