import Langlands.BaseChange.TwistedCharacter.FiniteTwistInterpolation
import Langlands.BaseChange.UnramifiedDeterminant
import Langlands.LocalField.SuppliedPadicExtension
import Langlands.Representation.Classification.ProductLeviCentralCharacter
import Langlands.Representation.Smooth.Schur.Proof

/-! # Interpolation on determinant twists of Levi trace distributions -/

noncomputable section

namespace Langlands.BaseChange

open GeneralLinear HarmonicAnalysis HarishChandraSchwartz MeasureTheory

universe v z uI

section Degree

variable (E : Type v) [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E] {n : ℕ} (B : BlockShape n)

/-- The determinant orders of all the blocks of a standard Levi product. -/
def leviDeterminantOrder : B.Levi E →* (Fin B.length → Multiplicative ℤ) :=
  MonoidHom.pi fun i => (determinantOrderHom E (B.size i)).comp (Pi.evalMonoidHom _ i)

/-- The determinant-order map is locally constant. -/
theorem isLocallyConstant_leviDeterminantOrder : IsLocallyConstant (leviDeterminantOrder E B) := by
  let : TopologicalSpace (Multiplicative ℤ) := inferInstanceAs (TopologicalSpace ℤ)
  let : DiscreteTopology (Multiplicative ℤ) := inferInstanceAs (DiscreteTopology ℤ)
  let T := LocalFieldData.ofInstances E
  apply (IsLocallyConstant.iff_continuous _).mpr
  apply continuous_pi
  intro i
  exact ((AllField.RankinSelberg.continuous_ord_units T).comp
    (T.generalLinearDeterminant (B.size i)).continuous).comp (continuous_apply i)

/-- Every character pulled back from the determinant-order lattice is unramified. -/
theorem isUnramifiedCharacter_comp_leviDeterminantOrder
    (χ : (Fin B.length → Multiplicative ℤ) →* ℂˣ) :
    IsUnramifiedCharacter (χ.comp (leviDeterminantOrder E B)) := by
  intro K hK g hg
  have hp : leviDeterminantOrder E B g = 1 := by
    funext i
    let e := Pi.evalMonoidHom (fun i => GeneralLinear (B.size i) E) i
    change determinantOrderHom E (B.size i) (e g) = 1
    apply determinantOrderHom_eq_one_of_mem_compact E _ (K.map e) ?_ ⟨g, hg, rfl⟩
    rw [Subgroup.coe_map]
    exact hK.image (continuous_apply i)
  rw [MonoidHom.comp_apply, hp, map_one]

private theorem leviDeterminantOrder_surjective :
    Function.Surjective (leviDeterminantOrder E B) := by
  intro x
  let T := LocalFieldData.ofInstances E
  have hdet (i : Fin B.length) :
      ∃ g : GeneralLinear (B.size i) E, determinant g = T.uniformizerUnit ^ (x i).toAdd := by
    let : Nonempty (Fin (B.size i)) := ⟨⟨0, B.positive i⟩⟩
    exact Matrix.GeneralLinearGroup.det_surjective _
  choose g hg using hdet
  refine ⟨g, ?_⟩
  funext i
  apply Multiplicative.toAdd.injective
  change (T.ordUnits (determinant (g i))).toAdd = _
  rw [hg, map_zpow, toAdd_zpow, T.ordUnits_apply, T.uniformizerUnit_val, T.ord_uniformizer]
  simp

/-- Each unramified character of the Levi product is pulled back from the
determinant lattice. -/
theorem exists_character_comp_leviDeterminantOrder
    (ψ : B.Levi E →* ℂˣ) (hψ : IsUnramifiedCharacter ψ) :
    ∃ χ : (Fin B.length → Multiplicative ℤ) →* ℂˣ, χ.comp (leviDeterminantOrder E B) = ψ := by
  let p := leviDeterminantOrder E B
  have hk : p.ker ≤ ψ.ker := by
    intro g hg
    apply MonoidHom.mem_ker.mpr
    have hp (i : Fin B.length) : determinantOrderHom E (B.size i) (g i) = 1 :=
      congrFun (MonoidHom.mem_ker.mp hg) i
    have hψi := (isUnramifiedCharacter_pi_iff ψ).mp hψ
    have hi (i : Fin B.length) : ψ (Pi.mulSingle i (g i)) = 1 := by
      apply MonoidHom.mem_ker.mp
      exact ((isUnramifiedCharacter_iff_detOrderKer_le E ⟨0, B.positive i⟩ _).mp (hψi i))
        (MonoidHom.mem_ker.mpr (hp i))
    calc
      ψ g = ψ (Finset.univ.noncommProd (fun i => Pi.mulSingle i (g i))
          (fun i _ j _ _ => Pi.mulSingle_apply_commute g i j)) :=
        congrArg ψ (Finset.noncommProd_mulSingle g).symm
      _ = ∏ i, ψ (Pi.mulSingle i (g i)) :=
        (Finset.map_noncommProd _ _ _ ψ).trans (Finset.noncommProd_eq_prod _ _)
      _ = 1 := Finset.prod_eq_one fun i _ => hi i
  let χ := p.liftOfSurjective (leviDeterminantOrder_surjective E B) ⟨ψ, hk⟩
  refine ⟨χ, MonoidHom.ext (fun g => ?_)⟩
  exact MonoidHom.liftOfRightInverse_comp_apply p _
    (Function.rightInverse_surjInv (leviDeterminantOrder_surjective E B)) ⟨ψ, hk⟩ g

private theorem ord_ringEquiv_of_continuous (σ : E ≃+* E) (hσ : Continuous σ)
    (x : E) (hx : x ≠ 0) :
    (LocalFieldData.ofInstances E).ord (σ x) = (LocalFieldData.ofInstances E).ord x := by
  let T := LocalFieldData.ofInstances E
  let v := ValuativeRel.valuation E
  have hord {a b : E} (ha : a ≠ 0) (hb : b ≠ 0) :
      T.ord a ≤ T.ord b ↔ v b ≤ v a := by
    change -WithZero.log (T.discreteValuation a) ≤ -WithZero.log (T.discreteValuation b) ↔ _
    rw [neg_le_neg_iff, WithZero.log_le_log (T.discreteValuation.ne_zero_iff.mpr hb)
      (T.discreteValuation.ne_zero_iff.mpr ha)]
    exact map_le_map_iff (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt E)
  have hcmp {a b : E} (ha : a ≠ 0) (hb : b ≠ 0) :
      T.ord (σ a) ≤ T.ord (σ b) ↔ T.ord a ≤ T.ord b := by
    have hva : 0 < v a := pos_iff_ne_zero.mpr (v.ne_zero_iff.mpr ha)
    have hσa := (map_ne_zero σ).mpr ha
    have hvσa : 0 < v (σ a) := pos_iff_ne_zero.mpr (v.ne_zero_iff.mpr hσa)
    rw [hord hσa ((map_ne_zero σ).mpr hb), hord ha hb]
    have he := LocalField.mem_integers_map_iff_of_continuous σ.toRingHom hσ (b / a)
    change v (σ (b / a)) ≤ 1 ↔ v (b / a) ≤ 1 at he
    simpa only [map_div₀, div_le_one₀ hva, div_le_one₀ hvσa] using he
  have heq {a b : E} (ha : a ≠ 0) (hb : b ≠ 0) (h : T.ord a = T.ord b) :
      T.ord (σ a) = T.ord (σ b) :=
    le_antisymm ((hcmp ha hb).mpr h.le) ((hcmp hb ha).mpr h.ge)
  let π := T.uniformizer
  have hπ : π ≠ 0 := by simpa only [π, T.uniformizerUnit_val] using T.uniformizerUnit.ne_zero
  have hscale (a : E) (ha : a ≠ 0) : T.ord (σ a) = T.ord a * T.ord (σ π) := by
    calc
      T.ord (σ a) = T.ord (σ (π ^ T.ord a)) := heq ha (zpow_ne_zero _ hπ)
        (by rw [T.ord_zpow, show T.ord π = 1 from T.ord_uniformizer, mul_one])
      _ = _ := by rw [map_zpow₀, T.ord_zpow]
  have hpos : 0 < T.ord (σ π) := by
    have hle := not_le.mpr (show T.ord (1 : E) < T.ord π by
      rw [T.ord_one, show T.ord π = 1 from T.ord_uniformizer]
      decide)
    have h := mt (hcmp hπ one_ne_zero).mp hle
    simpa only [map_one, T.ord_one, not_le] using h
  have hm : T.ord (σ.symm π) * T.ord (σ π) = 1 := by
    rw [← hscale _ ((map_ne_zero σ.symm).mpr hπ), RingEquiv.apply_symm_apply]
    exact T.ord_uniformizer
  have hsymm : 1 ≤ T.ord (σ.symm π) := by
    by_contra! h
    have hn : T.ord (σ.symm π) ≤ 0 := by omega
    have := mul_nonpos_of_nonpos_of_nonneg hn hpos.le
    omega
  have hone : T.ord (σ π) = 1 := by
    have hn : 0 ≤ (T.ord (σ.symm π) - 1) * (T.ord (σ π) - 1) :=
      mul_nonneg (by omega) (by omega)
    nlinarith
  simpa only [hone, mul_one] using hscale x hx

/-- The block determinant orders are invariant under the entrywise action
of a field automorphism continuous for the supplied topology. -/
theorem leviDeterminantOrder_leviAut
    {F : Type*} [CommRing F] [Algebra F E] (σ : E ≃ₐ[F] E) (hσ : Continuous σ)
    (g : B.Levi E) : leviDeterminantOrder E B (leviAut σ B g) = leviDeterminantOrder E B g := by
  funext i
  apply Multiplicative.toAdd.injective
  let T := LocalFieldData.ofInstances E
  change T.ord (determinant (entrywiseAut σ _ (g i)) : E) = T.ord (determinant (g i) : E)
  have he : (determinant (entrywiseAut σ _ (g i)) : E) = σ (determinant (g i) : E) :=
    (σ.map_det (g i : Matrix (Fin (B.size i)) (Fin (B.size i)) E)).symm
  rw [he]
  exact ord_ringEquiv_of_continuous E σ.toRingEquiv hσ _ (determinant (g i)).ne_zero

/-- Block scalar uniformizer powers give a homomorphism from the lattice into
the center of the Levi product. -/
def leviUniformizerCenter : (Fin B.length → Multiplicative ℤ) →* Subgroup.center (B.Levi E) :=
  (B.blockScalarToCenter E).comp (MonoidHom.pi fun i =>
    (zpowersHom Eˣ (LocalFieldData.ofInstances E).uniformizerUnit).comp (Pi.evalMonoidHom _ i))

private theorem leviDeterminantOrder_uniformizerCenter
    (x : Fin B.length → Multiplicative ℤ) (i : Fin B.length) :
    (leviDeterminantOrder E B (leviUniformizerCenter E B x) i).toAdd =
      (B.size i : ℤ) * (x i).toAdd := by
  let T := LocalFieldData.ofInstances E
  change (T.ordUnits (Matrix.GeneralLinearGroup.det
    (Matrix.GeneralLinearGroup.scalar (Fin (B.size i)) (T.uniformizerUnit ^ (x i).toAdd)))).toAdd = _
  rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, map_pow, map_zpow]
  have hp : (T.ordUnits T.uniformizerUnit).toAdd = 1 := by
    rw [T.ordUnits_apply, T.uniformizerUnit_val, T.ord_uniformizer]
  simp only [toAdd_pow, toAdd_zpow, hp, zsmul_eq_mul, mul_one, nsmul_eq_mul, Int.cast_id]

private theorem injective_leviDeterminantOrder_on_uniformizerCenter :
    Function.Injective ((leviDeterminantOrder E B).comp
      ((Subgroup.center (B.Levi E)).subtype.comp (leviUniformizerCenter E B))) := by
  intro x y h
  ext i
  apply Multiplicative.toAdd.injective
  have he := congrArg (fun z : Fin B.length → Multiplicative ℤ => (z i).toAdd) h
  change (leviDeterminantOrder E B (leviUniformizerCenter E B x) i).toAdd =
    (leviDeterminantOrder E B (leviUniformizerCenter E B y) i).toAdd at he
  rw [leviDeterminantOrder_uniformizerCenter, leviDeterminantOrder_uniformizerCenter] at he
  exact mul_left_cancel₀ (show (B.size i : ℤ) ≠ 0 by exact_mod_cast (B.positive i).ne') he

private theorem finite_leviDeterminantOrder_quotient :
    Finite ((Fin B.length → Multiplicative ℤ) ⧸
      (((Subgroup.center (B.Levi E)).subtype.comp (leviUniformizerCenter E B)).range.map
        (leviDeterminantOrder E B))) := by
  classical
  let L := Fin B.length → Multiplicative ℤ
  let c := (Subgroup.center (B.Levi E)).subtype.comp (leviUniformizerCenter E B)
  let p := leviDeterminantOrder E B
  let Q := L ⧸ c.range.map p
  let r (k : ∀ i, Fin (B.size i)) : L := fun i => Multiplicative.ofAdd (k i : ℕ)
  refine Finite.of_surjective (fun k => (r k : Q)) ?_
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (c.range.map p) q
  have hpos (i : Fin B.length) : (0 : ℤ) < B.size i := by exact_mod_cast B.positive i
  let m (i : Fin B.length) := (x i).toAdd % (B.size i : ℤ)
  have hm (i : Fin B.length) : 0 ≤ m i := Int.emod_nonneg _ (hpos i).ne'
  let k (i : Fin B.length) : Fin (B.size i) :=
    ⟨(m i).toNat, by
      have h : m i < (B.size i : ℤ) := Int.emod_lt_of_pos (x i).toAdd (hpos i)
      rw [← Int.toNat_of_nonneg (hm i)] at h
      exact_mod_cast h⟩
  let y : L := fun i => Multiplicative.ofAdd (-((x i).toAdd / (B.size i : ℤ)))
  refine ⟨k, QuotientGroup.eq_iff_div_mem.mpr ?_⟩
  refine ⟨c y, ⟨y, rfl⟩, ?_⟩
  funext i
  apply Multiplicative.toAdd.injective
  change (p (leviUniformizerCenter E B y) i).toAdd = ((k i : ℕ) : ℤ) - (x i).toAdd
  rw [leviDeterminantOrder_uniformizerCenter, show ((k i : ℕ) : ℤ) = m i from
    Int.toNat_of_nonneg (hm i)]
  change (B.size i : ℤ) * (-((x i).toAdd / (B.size i : ℤ))) = m i - (x i).toAdd
  rw [mul_neg]
  have he : m i + (B.size i : ℤ) * ((x i).toAdd / (B.size i : ℤ)) = (x i).toAdd :=
    Int.emod_add_mul_ediv _ _
  linarith only [he]

end Degree

section CentralNormalization

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {L : Type*} [CommGroup L] (p : G →* L) (hp : IsLocallyConstant p)

include hp in
omit [IsTopologicalGroup G] in
private theorem open_ker_comp_degree (χ : L →* ℂˣ) :
    IsOpen ((χ.comp p).ker : Set G) :=
  (hp.comp χ).isOpen_fiber 1

local notation "M[" χ "]" =>
  characterMultiplyTest (MonoidHom.comp χ p) (open_ker_comp_degree p hp χ)
local notation "D[" χ "]" =>
  characterTwistDistribution (MonoidHom.comp χ p) (open_ker_comp_degree p hp χ)

private theorem degreeTwist_mul (χ η : L →* ℂˣ) (d : Distribution G) :
    D[χ] (D[η] d) = D[χ * η] d := by
  ext f
  change d (M[η] (M[χ] f)) = d (M[χ * η] f)
  apply congrArg (d : SchwartzBruhat G → ℂ)
  apply Hecke.TestFunction.ext
  intro g
  simp only [characterMultiplyTest_apply, MonoidHom.comp_apply, MonoidHom.mul_apply, Units.val_mul]
  rw [← mul_assoc, mul_comm (η (p g) : ℂ)]

private theorem characterMultiplyTest_leftTests (χ : L →* ℂˣ) (g : G)
    (f : SchwartzBruhat G) :
    M[χ] (GroupAction.leftTests g f) = (χ (p g) : ℂ) • GroupAction.leftTests g (M[χ] f) := by
  apply Hecke.TestFunction.ext
  intro x
  change (χ (p x) : ℂ) * f (g⁻¹ * x) =
    (χ (p g) : ℂ) * ((χ (p (g⁻¹ * x)) : ℂ) * f (g⁻¹ * x))
  rw [← mul_assoc, ← Units.val_mul, ← map_mul, ← map_mul, mul_inv_cancel_left]

private theorem finiteTwistFamilyInterpolation_of_centralCharacters
    {A : Type*} [CommGroup A] (c : A →* Subgroup.center G)
    (hc : Function.Injective (p.comp ((Subgroup.center G).subtype.comp c)))
    (hF : Finite (L ⧸ (((Subgroup.center G).subtype.comp c).range.map p)))
    (hSep : Function.Injective (twistParameterEvaluation (L := L)))
    {I : Type uI} [Finite I] (d : I → Distribution G) (ω : I → A →* ℂˣ)
    (hω : ∀ i a f, d i (GroupAction.leftTests (c a : G) f) = (ω i a : ℂ) * d i f)
    (Φ : Module.Dual ℂ (Distribution G)) (P : I → L →₀ ℂ)
    (hP : ∀ i χ, Φ (D[χ] (d i)) = finsuppCharacterSum (P i) χ) :
    ∃ f : SchwartzBruhat G, ∀ i χ, D[χ] (d i) f = Φ (D[χ] (d i)) := by
  classical
  let C := ((Subgroup.center G).subtype.comp c).range
  have hext (i : I) : ∃ η : L →* ℂˣ, η.comp (p.comp ((Subgroup.center G).subtype.comp c)) =
      (ω i)⁻¹ :=
    Topology.exists_complex_character_extension _ hc (ω i)⁻¹
  choose η hη using hext
  let d' (i : I) := D[η i] (d i)
  have hC (i : I) (g : G) (hg : g ∈ C) (f : SchwartzBruhat G) :
      d' i (GroupAction.leftTests g f) = d' i f := by
    obtain ⟨a, ha⟩ := hg
    change (c a : G) = g at ha
    subst g
    have he := DFunLike.congr_fun (hη i) a
    change η i (p (c a : G)) = (ω i a)⁻¹ at he
    change d i (M[η i] (GroupAction.leftTests (c a : G) f)) = d i (M[η i] f)
    rw [characterMultiplyTest_leftTests p hp, map_smul, smul_eq_mul, hω, he,
      ← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  let Q (i : I) := Finsupp.onFinset (P i).support (fun a => P i a * (η i a : ℂ))
    (fun a ha => Finsupp.mem_support_iff.mpr (left_ne_zero_of_mul ha))
  have hQ (i : I) : (Q i).support = (P i).support := by
    ext a
    simp [Q, Finsupp.mem_support_iff, Units.ne_zero]
  have hP' (i : I) (χ : L →* ℂˣ) : Φ (D[χ] (d' i)) = finsuppCharacterSum (Q i) χ := by
    rw [show d' i = D[η i] (d i) from rfl, degreeTwist_mul p hp, hP]
    simp only [finsuppCharacterSum, Finsupp.sum, hQ, Q, Finsupp.onFinset_apply,
      MonoidHom.mul_apply, Units.val_mul]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  obtain ⟨f, hf⟩ := finiteTwistFamilyInterpolation p hp C hF hSep I d' Φ Q hC hP'
  refine ⟨f, fun i χ => ?_⟩
  have he' : (χ * (η i)⁻¹) * η i = χ := by
    apply MonoidHom.ext
    intro a
    change χ a * (η i a)⁻¹ * η i a = χ a
    rw [mul_assoc, inv_mul_cancel, mul_one]
  have hback : D[χ * (η i)⁻¹] (d' i) = D[χ] (d i) :=
    (degreeTwist_mul p hp (χ * (η i)⁻¹) (η i) (d i)).trans
      (congrArg (fun ψ => D[ψ] (d i)) he')
  simpa only [hback] using hf i (χ * (η i)⁻¹)

end CentralNormalization

section LeviTraces

variable (E : Type v) [Field E] [ValuativeRel E] [TopologicalSpace E]
  [IsNonarchimedeanLocalField E] {n : ℕ} (B : BlockShape n)
  [T2Space (B.Levi E)] [LocallyCompactSpace (B.Levi E)] [TotallyDisconnectedSpace (B.Levi E)]
  [MeasurableSpace (B.Levi E)] [BorelSpace (B.Levi E)]
  (μ : Measure (B.Levi E)) [IsFiniteMeasureOnCompacts μ] [μ.IsMulLeftInvariant]

local notation "p" => leviDeterminantOrder E B
local notation "D[" χ "]" => characterTwistDistribution (MonoidHom.comp χ p)
  (open_ker_comp_degree p (isLocallyConstant_leviDeterminantOrder E B) χ)

private theorem determinantLatticeCharacters_separate :
    Function.Injective (twistParameterEvaluation (L := Fin B.length → Multiplicative ℤ)) := by
  intro x y h
  let t : ℂˣ := Units.mk0 2 (by norm_num)
  funext i
  apply Multiplicative.toAdd.injective
  let χ := (zpowersHom ℂˣ t).comp (Pi.evalMonoidHom (fun _ : Fin B.length => Multiplicative ℤ) i)
  have he := DFunLike.congr_fun h χ
  change t ^ (x i).toAdd = t ^ (y i).toAdd at he
  have hnorm := congrArg (fun a : ℂˣ => ‖(a : ℂ)‖) he
  simp only [Units.val_zpow_eq_zpow_val, norm_zpow, t, Units.val_mk0] at hnorm
  apply (zpow_right_injective₀ (a := ‖(2 : ℂ)‖) (by norm_num) (by norm_num)) hnorm

/-- A linear form regular on finitely many determinant-twist families of irreducible
Levi traces is evaluation at one test on those families. -/
def LeviDeterminantTwistInterpolationStatement : Prop :=
  ∀ (I : Type uI) [Finite I] (W : I → Type z) [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
    (π : ∀ i, Representation ℂ (B.Levi E) (W i)) (hπ : ∀ i, IsAdmissible (π i)),
    (∀ i, (π i).IsIrreducible) →
    ∀ (A : ∀ i, Module.End ℂ (W i)) (Φ : Module.Dual ℂ (Distribution (B.Levi E)))
      (P : I → (Fin B.length → Multiplicative ℤ) →₀ ℂ),
      (∀ i χ, Φ (D[χ] (twistedDistribution μ (π i) (hπ i) (A i))) =
        finsuppCharacterSum (P i) χ) →
      ∃ f : SchwartzBruhat (B.Levi E), ∀ i χ,
        D[χ] (twistedDistribution μ (π i) (hπ i) (A i)) f =
          Φ (D[χ] (twistedDistribution μ (π i) (hπ i) (A i)))

/-- Extend each inverse central character from the uniformizer lattice and
apply finite twist interpolation to the normalized traces. -/
theorem leviDeterminantTwistInterpolation :
    LeviDeterminantTwistInterpolationStatement.{v,z,uI} E B μ := by
  intro I _ W _ _ π hπ hirr A Φ P hP
  choose χ hχ using (fun i => (admissibleSchur_centralCharacter (π i) (hπ i) (hirr i)).exists)
  let c := leviUniformizerCenter E B
  let ω (i : I) := (χ i).comp c
  let d (i : I) := twistedDistribution μ (π i) (hπ i) (A i)
  have hω (i : I) a (f : SchwartzBruhat (B.Levi E)) :
      d i (GroupAction.leftTests (c a : B.Levi E) f) = (ω i a : ℂ) * d i f := by
    change twistedDistribution μ (π i) (hπ i) (A i)
        (Hecke.TestFunction.leftTranslate (c a : B.Levi E) f) =
      (ω i a : ℂ) * twistedDistribution μ (π i) (hπ i) (A i) f
    rw [twistedDistribution_apply, twistedDistribution_apply, ← smul_eq_mul, ← map_smul]
    apply congrArg FiniteRankEnd.trace
    apply Subtype.ext
    apply LinearMap.ext
    intro x
    change Hecke.integratedAction μ (π i) (hπ i).1
      (Hecke.TestFunction.leftTranslate (c a : B.Levi E) f)
      (A i x) = (ω i a : ℂ) • Hecke.integratedAction μ (π i) (hπ i).1 f (A i x)
    rw [Hecke.integratedAction_leftTranslate, (hχ i).2]
    rfl
  exact finiteTwistFamilyInterpolation_of_centralCharacters p
    (isLocallyConstant_leviDeterminantOrder E B) c
    (injective_leviDeterminantOrder_on_uniformizerCenter E B)
    (finite_leviDeterminantOrder_quotient E B) (determinantLatticeCharacters_separate B)
    d ω hω Φ P hP

end LeviTraces

end Langlands.BaseChange
