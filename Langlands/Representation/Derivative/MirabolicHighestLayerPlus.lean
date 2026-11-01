import Langlands.Representation.Derivative.MirabolicHighestLayerLift
import Langlands.Representation.Derivative.MirabolicHighestLayerPlusMaps
import Langlands.Representation.Derivative.MirabolicPlusNormalization
import Langlands.Representation.RankinSelberg.EqualRankFrobeniusProof

/-! # The highest mirabolic layer as an iterated plus induction

For a smooth representation `B` of `P_(m+2)`, the orbit map `w ↦ (x ↦ [x · w])` sends
the radical relations of `B` isomorphically onto normalized `Φ⁺(Φ⁻ B)`.
-/

noncomputable section

open CategoryTheory

namespace Langlands.Derivative.Mirabolic.HighestLayer

open GeneralLinear GeneralLinear.Mirabolic HarmonicAnalysis RankinSelberg Topology
open Jacquet.Localization
open scoped Matrix

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-! ## Conjugating radical elements -/

/-- Moving a radical element to the left of a mirabolic element. -/
theorem mul_radicalElement {n : ℕ} (x : mirabolic n F.Carrier) (c : Fin n → F.Carrier) :
    x * (radicalElement c).val = (radicalElement ((projection x).val *ᵥ c)).val * x := by
  conv_lhs => rw [eq_radicalElement_mul_levi x]
  conv_rhs => rw [eq_radicalElement_mul_levi x]
  rw [projection_radicalElement_mul_levi, mul_assoc, levi_mul_radicalElement, ← mul_assoc,
    ← mul_assoc, ← Subgroup.coe_mul, ← Subgroup.coe_mul, ← radicalElement_add,
    ← radicalElement_add, add_comm (lastColumn x)]

/-! ## The orbit function -/

section Orbit

variable (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (m : ℕ)

/-- The orbit function `x ↦ [x · w]` of a vector `w`, valued in `Φ⁻ B`. -/
def orbitFun :
    letI := T.topology
    (B : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + 1) F.Carrier)) → B →
      mirabolic (m + 1) F.Carrier → (phiMinus T ψ m).obj B := by
  letI := T.topology
  exact fun B w x => phiMinusQuotient T ψ m B (B.representation x w)

theorem orbitFun_apply :
    letI := T.topology
    ∀ (B : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + 1) F.Carrier)) (w : B)
      (x : mirabolic (m + 1) F.Carrier),
      orbitFun T ψ m B w x = phiMinusQuotient T ψ m B (B.representation x w) :=
  fun _ _ _ => rfl

theorem orbitFun_mul :
    letI := T.topology
    ∀ (B : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + 1) F.Carrier)) (w : B)
      (x g : mirabolic (m + 1) F.Carrier),
      orbitFun T ψ m B w (x * g) = orbitFun T ψ m B (B.representation g w) x := by
  let := T.topology
  intro B w x g
  rw [orbitFun_apply, orbitFun_apply, map_mul, Module.End.mul_apply]

/-- A radical translate multiplies the orbit function by `ψ(row(x) · c)`, where
`row(x)` is the last row of the Levi part of `x`. -/
theorem orbitFun_radicalElement :
    letI := T.topology
    ∀ (B : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + 1) F.Carrier)) (w : B)
      (c : Fin (m + 1) → F.Carrier) (x : mirabolic (m + 1) F.Carrier),
      orbitFun T ψ m B (B.representation (radicalElement c).val w) x =
        ψ.complex (((projection x).val *ᵥ c) (Fin.last m)) • orbitFun T ψ m B w x := by
  let := T.topology
  intro B w c x
  rw [← orbitFun_mul, mul_radicalElement, orbitFun_apply, map_mul, Module.End.mul_apply,
    phiMinusQuotient_radical]
  congr 1
  exact theta_radicalElement ψ m _

/-- The orbit function has the covariance of normalized `Φ⁺(Φ⁻ B)`. -/
theorem orbitFun_plus_mul :
    letI := T.topology
    ∀ (B : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + 1) F.Carrier)) (w : B)
      (q : plusSubgroup m F.Carrier) (x : mirabolic (m + 1) F.Carrier),
      orbitFun T ψ m B w ((q : mirabolic (m + 1) F.Carrier) * x) =
        (thetaPlus ψ m q : ℂ) • phiMinusQuotient T ψ m B
          (B.representation (successor (plusProjection q)) (B.representation x w)) := by
  let := T.topology
  intro B w q x
  have hq : (q : mirabolic (m + 1) F.Carrier) * x =
      (radicalElement (lastColumn q.val)).val * (successor (plusProjection q) * x) := by
    rw [← mul_assoc, ← plus_eq_radicalElement_mul_successor q]
  rw [hq, orbitFun_apply, map_mul, Module.End.mul_apply, phiMinusQuotient_radical, map_mul,
    Module.End.mul_apply]
  congr 1
  rw [thetaPlus_apply]
  exact theta_radicalElement ψ m _

theorem phiMinus_orbitFun :
    letI := T.topology
    ∀ (B : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + 1) F.Carrier)) (w : B)
      (g : mirabolic m F.Carrier) (x : mirabolic (m + 1) F.Carrier),
      ((phiMinus T ψ m).obj B).representation g (orbitFun T ψ m B w x) =
        (phiMinusCharacter T m g : ℂ) • phiMinusQuotient T ψ m B
          (B.representation (successor g) (B.representation x w)) := by
  let := T.topology
  intro B w g x
  exact phiMinus_action T ψ m B g _

theorem phiPlusCharacter_smul_phiMinusCharacter_smul :
    letI := T.topology
    ∀ (B : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + 1) F.Carrier)) (g : mirabolic m F.Carrier)
      (v : (phiMinus T ψ m).obj B),
      (phiPlusCharacter T m g : ℂ) • (phiMinusCharacter T m g : ℂ) • v = v := by
  let := T.topology
  intro B g v
  have hchar : (phiPlusCharacter T m g : ℂ) * (phiMinusCharacter T m g : ℂ) = 1 := by
    have h := congrArg (fun χ : mirabolic m F.Carrier →* ℂˣ => (χ g : ℂ))
      (phiPlusCharacter_mul_phiMinusCharacter T m)
    simpa using h
  rw [smul_smul, hchar, one_smul]

/-- The orbit function has the covariance of normalized `Φ⁺(Φ⁻ B)`. -/
theorem orbitFun_covariant :
    letI := T.topology
    ∀ (B : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + 1) F.Carrier)) (w : B)
      (q : plusSubgroup m F.Carrier) (x : mirabolic (m + 1) F.Carrier),
      orbitFun T ψ m B w ((q : mirabolic (m + 1) F.Carrier) * x) =
        (thetaPlus ψ m q : ℂ) • (phiPlusCharacter T m (plusProjection q) : ℂ) •
          ((phiMinus T ψ m).obj B).representation (plusProjection q)
            (orbitFun T ψ m B w x) := by
  let := T.topology
  intro B w q x
  rw [orbitFun_plus_mul, phiMinus_orbitFun]
  exact congrArg (fun v => (thetaPlus ψ m q : ℂ) • v)
    (phiPlusCharacter_smul_phiMinusCharacter_smul T ψ m B _ _).symm


theorem orbitFun_add :
    letI := T.topology
    ∀ (B : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + 1) F.Carrier)) (w w' : B)
      (x : mirabolic (m + 1) F.Carrier),
      orbitFun T ψ m B (w + w') x = orbitFun T ψ m B w x + orbitFun T ψ m B w' x := by
  let := T.topology
  intro B w w' x
  rw [orbitFun_apply, orbitFun_apply, orbitFun_apply, map_add, map_add]
  rfl

theorem orbitFun_smul :
    letI := T.topology
    ∀ (B : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + 1) F.Carrier)) (a : ℂ) (w : B)
      (x : mirabolic (m + 1) F.Carrier),
      orbitFun T ψ m B (a • w) x = a • orbitFun T ψ m B w x := by
  let := T.topology
  intro B a w x
  rw [orbitFun_apply, orbitFun_apply, map_smul, map_smul]
  rfl

theorem orbitFun_zero :
    letI := T.topology
    ∀ (B : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + 1) F.Carrier))
      (x : mirabolic (m + 1) F.Carrier), orbitFun T ψ m B 0 x = 0 := by
  let := T.topology
  intro B x
  rw [orbitFun_apply, map_zero, map_zero]
  rfl

theorem orbitFun_sub :
    letI := T.topology
    ∀ (B : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + 1) F.Carrier)) (w w' : B)
      (x : mirabolic (m + 1) F.Carrier),
      orbitFun T ψ m B (w - w') x = orbitFun T ψ m B w x - orbitFun T ψ m B w' x := by
  let := T.topology
  intro B w w' x
  rw [orbitFun_apply, orbitFun_apply, orbitFun_apply, map_sub, map_sub]
  rfl

theorem orbitFun_sum :
    letI := T.topology
    ∀ (B : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + 1) F.Carrier)) {ι : Type*} (s : Finset ι)
      (w : ι → B) (x : mirabolic (m + 1) F.Carrier),
      orbitFun T ψ m B (∑ i ∈ s, w i) x = ∑ i ∈ s, orbitFun T ψ m B (w i) x := by
  let := T.topology
  intro B ι s w x
  rw [orbitFun_apply, map_sum, map_sum]
  rfl

end Orbit


/-! ## Last rows of Levi parts -/

section Row

variable {K : Type*} [Field K] {n : ℕ}

/-- The last row of the Levi part of an element of `P_(n+2)`. -/
def projectionRow (x : mirabolic (n + 1) K) : Fin (n + 1) → K :=
  lastRow (projection x)

theorem projectionRow_mul (x g : mirabolic (n + 1) K) :
    projectionRow (x * g) = Matrix.vecMul (projectionRow x) (projection g).val := by
  rw [projectionRow, map_mul]
  exact lastRow_mul_eq_vecMul _ _

theorem projectionRow_plus_mul (q : plusSubgroup n K) (x : mirabolic (n + 1) K) :
    projectionRow ((q : mirabolic (n + 1) K) * x) = projectionRow x := by
  rw [projectionRow, map_mul]
  exact EqualRankFrobenius.lastRow_mirabolic_mul q.property

theorem projectionRow_levi (g : Langlands.GeneralLinear (n + 1) K) :
    projectionRow (levi g) = lastRow g := by
  rw [projectionRow, projection_levi]

theorem projectionRow_ne_zero (x : mirabolic (n + 1) K) : projectionRow x ≠ 0 :=
  lastRow_ne_zero _

theorem mulVec_last_eq_dotProduct (x : mirabolic (n + 1) K) (c : Fin (n + 1) → K) :
    ((projection x).val *ᵥ c) (Fin.last n) = projectionRow x ⬝ᵥ c :=
  rfl

/-- An element whose Levi last row is the last row of `g` lies in `Q · levi g`. -/
theorem exists_plus_mul_levi {x : mirabolic (n + 1) K} {g : Langlands.GeneralLinear (n + 1) K}
    (h : lastRow g = projectionRow x) :
    ∃ q : plusSubgroup n K, x = (q : mirabolic (n + 1) K) * levi g := by
  refine ⟨⟨x * (levi g)⁻¹, ?_⟩, by simp⟩
  rw [mem_plusSubgroup, map_mul, map_inv, projection_levi]
  exact EqualRankFrobenius.mul_inv_mem_mirabolic_of_lastRow_eq h.symm

end Row

/-! ## Supports of orbit functions -/

section Support

variable (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (m : ℕ)

theorem exists_openSubgroup_fixing :
    letI := T.topology
    ∀ (B : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + 1) F.Carrier)) (w : B),
      ∃ K : OpenSubgroup (mirabolic (m + 1) F.Carrier), ∀ k ∈ K, B.representation k w = w := by
  let := T.topology
  intro B w
  obtain ⟨K, hK⟩ := B.isSmooth w
  exact ⟨K, fun k hk => (Representation.mem_invariants _ w).mp hK ⟨k, hk⟩⟩

/-- A lattice box of radical elements fixes a given vector. -/
theorem exists_latticeBox_fixing :
    letI := T.topology
    ∀ (B : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + 1) F.Carrier)) (w : B),
      ∃ l : ℤ, ∀ c ∈ latticeBox T (m + 1) l,
        B.representation (radicalElement c : mirabolic (m + 1) F.Carrier) w = w := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro B w
  obtain ⟨K, hK⟩ := exists_openSubgroup_fixing T m B w
  have hrad0 : {d : Fin (m + 1) → F.Carrier |
      (radicalElement d : mirabolic (m + 1) F.Carrier) ∈ K} ∈
        𝓝 (0 : Fin (m + 1) → F.Carrier) := by
    apply (K.isOpen.preimage (continuous_subtype_val.comp continuous_radicalElement)).mem_nhds
    simp only [Set.mem_preimage, Function.comp_apply, radicalElement_zero]
    exact K.one_mem
  obtain ⟨l, hl⟩ := exists_latticeBox_subset T hrad0
  exact ⟨l, fun c hc => hK _ (hl hc)⟩

/-- The orbit function of a vector fixed by the radical box `l` is supported where the
Levi last row lies in the dual box. -/
theorem projectionRow_mem_of_orbitFun_ne_zero :
    letI := T.topology
    ∀ (B : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + 1) F.Carrier)) (w : B) (l : ℤ),
      (∀ c ∈ latticeBox T (m + 1) l,
        B.representation (radicalElement c : mirabolic (m + 1) F.Carrier) w = w) →
      ∀ x : mirabolic (m + 1) F.Carrier, orbitFun T ψ m B w x ≠ 0 →
        projectionRow x ∈ latticeBox T (m + 1) (T.additiveConductor ψ - l) := by
  let := T.topology
  intro B w l hl x hx
  apply mem_latticeBox_of_forall_character_eq_one T ψ
  intro y hy
  have h := orbitFun_radicalElement T ψ m B w y x
  rw [hl y hy] at h
  have h1 := eq_one_of_smul_eq_self h.symm hx
  rw [mulVec_last_eq_dotProduct, UnitaryAdditiveCharacter.complex_apply] at h1
  rw [dotProduct_comm]
  exact Circle.coe_eq_one.mp h1

/-- The orbit function of a radical relation vanishes near the zero row. -/
theorem exists_orbitFun_eq_zero_of_mem_relations :
    letI := T.topology
    ∀ (B : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + 1) F.Carrier)) (w : B),
      w ∈ relations B.representation (radical (m + 1) F.Carrier) 1 →
        ∃ N : ℤ, ∀ x : mirabolic (m + 1) F.Carrier,
          projectionRow x ∈ latticeBox T (m + 1) N → orbitFun T ψ m B w x = 0 := by
  let := T.topology
  intro B w hw
  induction hw using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨⟨u, v⟩, rfl⟩ := hv
    obtain ⟨M, hM⟩ := exists_mem_latticeBox T (radicalCoordinates u)
    refine ⟨T.additiveConductor ψ - M, fun x hx => ?_⟩
    have hu : (u : mirabolic (m + 1) F.Carrier) =
        (radicalElement (radicalCoordinates u) : mirabolic (m + 1) F.Carrier) := by
      rw [radicalElement_coordinates]
    have h1 : ψ (projectionRow x ⬝ᵥ radicalCoordinates u) = 1 :=
      character_dotProduct_eq_one T ψ hx hM
    simp only [MonoidHom.one_apply, Units.val_one, one_smul]
    rw [orbitFun_sub, hu, orbitFun_radicalElement, mulVec_last_eq_dotProduct,
      UnitaryAdditiveCharacter.complex_apply, h1, Circle.coe_one, one_smul, sub_self]
  | zero => exact ⟨0, fun x _ => orbitFun_zero T ψ m B x⟩
  | add a b _ _ ha hb =>
    obtain ⟨N, hN⟩ := ha
    obtain ⟨N', hN'⟩ := hb
    refine ⟨min N N', fun x hx => ?_⟩
    rw [orbitFun_add, hN x (latticeBox_mono T (min_le_left N N') hx),
      hN' x (latticeBox_mono T (min_le_right N N') hx), add_zero]
  | smul a b _ hb =>
    obtain ⟨N, hN⟩ := hb
    exact ⟨N, fun x hx => by rw [orbitFun_smul, hN x hx, smul_zero]⟩

/-- A function on `P_(n+2)` whose support is left `Q`-stable, right invariant under an
open subgroup, and has Levi last rows in a compact set avoiding zero has compact
projected support in `Q \ P_(n+2)`. -/
theorem isCompact_quotientSupport_of_projectionRow :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (m + 1 + 1)
    ∀ {V : Type*} [AddCommGroup V] (f : mirabolic (m + 1) F.Carrier → V),
      (∀ (q : plusSubgroup m F.Carrier) (x : mirabolic (m + 1) F.Carrier),
        f x = 0 → f ((q : mirabolic (m + 1) F.Carrier) * x) = 0) →
      ∀ K : OpenSubgroup (mirabolic (m + 1) F.Carrier),
      (∀ (k : K) (x : mirabolic (m + 1) F.Carrier),
        f (x * (k : mirabolic (m + 1) F.Carrier)) = f x) →
      ∀ C : Set (Fin (m + 1) → F.Carrier), IsCompact C → (0 : Fin (m + 1) → F.Carrier) ∉ C →
      (∀ x, f x ≠ 0 → projectionRow x ∈ C) →
      IsCompact (Induction.quotientSupport (plusSubgroup m F.Carrier) f) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (m + 1 + 1)
  let := T.valuativeRel
  let := T.localField
  have : T2Space F.Carrier := T.fieldT2
  intro V _ f hinv K hK C hC h0 hsupp
  have hclosed : IsClosed (Induction.quotientSupport (plusSubgroup m F.Carrier) f) := by
    apply (isQuotientMap_quotient_mk'
      (s := QuotientGroup.rightRel (plusSubgroup m F.Carrier))).isCoinducing.isClosed_preimage.mp
    change IsClosed (Induction.quotientMap (plusSubgroup m F.Carrier) ⁻¹'
      Induction.quotientSupport (plusSubgroup m F.Carrier) f)
    have hpre : Induction.quotientMap (plusSubgroup m F.Carrier) ⁻¹'
        Induction.quotientSupport (plusSubgroup m F.Carrier) f = Function.support f := by
      ext x
      constructor
      · rintro ⟨y, hy, hxy⟩ hx
        have hp : y * x⁻¹ ∈ plusSubgroup m F.Carrier :=
          QuotientGroup.rightRel_apply.mp (Quotient.exact hxy.symm)
        apply hy
        have h := hinv ⟨y * x⁻¹, hp⟩ x hx
        simpa using h
      · intro hx
        exact ⟨x, hx, rfl⟩
    rw [hpre, ← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro x hx
    refine ⟨(fun k => x * k) '' (K : Set (mirabolic (m + 1) F.Carrier)), ?_,
      isOpenMap_mul_left x _ K.isOpen, ⟨1, K.one_mem, mul_one x⟩⟩
    rintro _ ⟨k, hk, rfl⟩
    simp only [Set.mem_compl_iff, Function.mem_support, not_not] at hx ⊢
    rw [hK ⟨k, hk⟩ x]
    exact hx
  let J : Subgroup (Langlands.GeneralLinear (m + 1) F.Carrier) :=
    GeneralLinearGroup.integralSubgroup (Fin (m + 1)) T.Integers
  have hJo : IsOpen (J : Set (Langlands.GeneralLinear (m + 1) F.Carrier)) :=
    GeneralLinearGroup.isOpen_integralSubgroup _ _ T.isOpen_integers
  have hJc : IsCompact (J : Set (Langlands.GeneralLinear (m + 1) F.Carrier)) :=
    GeneralLinearGroup.isCompact_integralSubgroup _ _ T.isCompact_integers
  have hcover : C ⊆ ⋃ y ∈ C, EqualRankFrobenius.orbitSet J (EqualRankFrobenius.lift y) := by
    intro y hy
    refine Set.mem_biUnion hy ?_
    have h := EqualRankFrobenius.lastRow_mem_orbitSet J (EqualRankFrobenius.lift y)
    rwa [EqualRankFrobenius.lastRow_lift y (fun h => h0 (h ▸ hy))] at h
  obtain ⟨t, -, htf, htcover⟩ := hC.elim_finite_subcover_image
    (fun y _ => EqualRankFrobenius.isOpen_orbitSet hJo _) hcover
  let D : Set (mirabolic (m + 1) F.Carrier) :=
    ⋃ y ∈ t, (fun j => levi (EqualRankFrobenius.lift y * j)) ''
      (J : Set (Langlands.GeneralLinear (m + 1) F.Carrier))
  have hD : IsCompact D := htf.isCompact_biUnion fun y _ =>
    hJc.image (continuous_levi.comp (continuous_const.mul continuous_id))
  refine (hD.image (continuous_quotient_mk'
    (s := QuotientGroup.rightRel (plusSubgroup m F.Carrier)))).of_isClosed_subset hclosed ?_
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨y, hyt, hy⟩ := Set.mem_iUnion₂.mp (htcover (hsupp x hx))
  obtain ⟨j, hj, hjx⟩ := EqualRankFrobenius.mem_orbitSet.mp hy
  obtain ⟨q, hq⟩ := exists_plus_mul_levi hjx
  refine ⟨levi (EqualRankFrobenius.lift y * j), Set.mem_iUnion₂.mpr ⟨y, hyt, j, hj, rfl⟩, ?_⟩
  apply Quotient.sound
  refine QuotientGroup.rightRel_apply.mpr ?_
  rw [hq, mul_inv_cancel_right]
  exact q.property

end Support


/-! ## The orbit map -/

section Theta

variable (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (m : ℕ)

theorem mem_liftStep_top :
    letI := T.topology
    ∀ (B : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + 1) F.Carrier)) (v : B),
      v ∈ liftStep T ψ m B ⊤ ↔ v ∈ relations B.representation (radical (m + 1) F.Carrier) 1 := by
  let := T.topology
  intro B v
  rw [mem_liftStep]
  exact ⟨fun h => h.1, fun h => ⟨h, fun _ => Submodule.mem_top⟩⟩

/-- The orbit function of a radical relation has compact projected support. -/
theorem orbitFun_isCompact :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup (m + 1 + 1)
    ∀ (B : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + 1) F.Carrier)) (w : B),
      w ∈ relations B.representation (radical (m + 1) F.Carrier) 1 →
      IsCompact (Induction.quotientSupport (plusSubgroup m F.Carrier) (orbitFun T ψ m B w)) := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (m + 1 + 1)
  intro B w hw
  obtain ⟨K, hK⟩ := exists_openSubgroup_fixing T m B w
  obtain ⟨l, hl⟩ := exists_latticeBox_fixing T m B w
  obtain ⟨N, hN⟩ := exists_orbitFun_eq_zero_of_mem_relations T ψ m B w hw
  refine isCompact_quotientSupport_of_projectionRow T m (orbitFun T ψ m B w) ?_ K ?_
    ((latticeBox T (m + 1) (T.additiveConductor ψ - l) : Set (Fin (m + 1) → F.Carrier)) \
      (latticeBox T (m + 1) N : Set (Fin (m + 1) → F.Carrier))) ?_ ?_ ?_
  · intro q x hx
    rw [orbitFun_covariant, hx, map_zero, smul_zero, smul_zero]
  · intro k x
    rw [orbitFun_mul, hK k k.property]
  · exact (isCompact_latticeBox T _ _).diff (isOpen_latticeBox T _ _)
  · intro h
    exact h.2 (latticeBox T (m + 1) N).zero_mem
  · intro x hx
    exact ⟨projectionRow_mem_of_orbitFun_ne_zero T ψ m B w l hl x hx, fun h => hx (hN x h)⟩

/-- The orbit function of a radical relation, as a vector of normalized `Φ⁺(Φ⁻ B)`. -/
def thetaFun :
    letI := T.topology
    (B : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + 1) F.Carrier)) → (w : B) →
      w ∈ relations B.representation (radical (m + 1) F.Carrier) 1 →
        (phiPlus T ψ m).obj ((phiMinus T ψ m).obj B) := by
  letI := T.topology
  letI := T.generalLinearTopologicalGroup (m + 1 + 1)
  exact fun B w hw => phiPlusNormalizedMk T ψ m ((phiMinus T ψ m).obj B) (orbitFun T ψ m B w)
    (orbitFun_covariant T ψ m B w) (Classical.choose (exists_openSubgroup_fixing T m B w))
    (fun k x => by
      rw [orbitFun_mul, Classical.choose_spec (exists_openSubgroup_fixing T m B w) k k.property])
    (orbitFun_isCompact T ψ m B w hw)

theorem thetaFun_eval :
    letI := T.topology
    ∀ (B : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + 1) F.Carrier)) (w : B)
      (hw : w ∈ relations B.representation (radical (m + 1) F.Carrier) 1),
      phiPlusNormalizedEval T ψ m ((phiMinus T ψ m).obj B) (thetaFun T ψ m B w hw) =
        orbitFun T ψ m B w :=
  fun _ _ _ => rfl

/-- The orbit map `R(B) → Φ⁺(Φ⁻ B)` on radical relations. -/
def theta :
    letI := T.topology
    (B : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + 1) F.Carrier)) →
      Representation.IntertwiningMap (liftStep T ψ m B ⊤).toRepresentation
        ((phiPlus T ψ m).obj ((phiMinus T ψ m).obj B)).representation := by
  letI := T.topology
  intro B
  refine
    { toLinearMap :=
        { toFun := fun w => thetaFun T ψ m B w.1 ((mem_liftStep_top T ψ m B w.1).mp w.2)
          map_add' := ?_
          map_smul' := ?_ }
      isIntertwining' := ?_ }
  · intro a b
    apply phiPlusNormalizedEval_injective T ψ m _
    funext x
    exact orbitFun_add T ψ m B a.1 b.1 x
  · intro c a
    apply phiPlusNormalizedEval_injective T ψ m _
    funext x
    exact orbitFun_smul T ψ m B c a.1 x
  · intro g
    apply LinearMap.ext
    intro w
    apply phiPlusNormalizedEval_injective T ψ m _
    funext x
    exact (orbitFun_mul T ψ m B w.1 x g).symm

theorem theta_eval :
    letI := T.topology
    ∀ (B : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + 1) F.Carrier))
      (w : (liftStep T ψ m B ⊤).toSubmodule) (x : mirabolic (m + 1) F.Carrier),
      phiPlusNormalizedEval T ψ m ((phiMinus T ψ m).obj B) (theta T ψ m B w) x =
        orbitFun T ψ m B w.1 x :=
  fun _ _ _ => rfl

theorem liftStep_bot :
    letI := T.topology
    ∀ B : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + 1) F.Carrier), liftStep T ψ m B ⊥ = ⊥ := by
  let := T.topology
  intro B
  have h := liftStep_imageStep T ψ m B ⊥ bot_le
  rwa [imageStep_bot] at h

theorem theta_injective :
    letI := T.topology
    ∀ B : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + 1) F.Carrier),
      Function.Injective (theta T ψ m B) := by
  let := T.topology
  intro B a b hab
  have hsub : theta T ψ m B (a - b) = 0 := by rw [map_sub, hab, sub_self]
  have hmem : (a - b).1 ∈ liftStep T ψ m B ⊥ := by
    refine (mem_liftStep T ψ m B ⊥ _).mpr ⟨((mem_liftStep_top T ψ m B _).mp (a - b).2), ?_⟩
    intro g
    have h := congrArg (fun φ => phiPlusNormalizedEval T ψ m ((phiMinus T ψ m).obj B) φ g) hsub
    change orbitFun T ψ m B (a - b).1 g = 0 at h
    rw [orbitFun_apply] at h
    rw [h]
    exact Submodule.zero_mem _
  rw [liftStep_bot] at hmem
  have h0 : (a - b).1 = 0 := (Submodule.mem_bot ℂ).mp hmem
  exact sub_eq_zero.mp (Subtype.ext h0)

end Theta

/-! ## Surjectivity of the orbit map -/

section Surjective

variable (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)

open Classical in
/-- A finite character sum over a quotient of lattice boxes. -/
theorem sum_character_out (k : ℕ) (M l : ℤ)
    [Fintype (latticeBox T k M ⧸ (latticeBox T k l).addSubgroupOf (latticeBox T k M))]
    (y : Fin k → F.Carrier) (hy : y ∈ latticeBox T k (T.additiveConductor ψ - l)) :
    letI := T.topology
    ∑ c : latticeBox T k M ⧸ (latticeBox T k l).addSubgroupOf (latticeBox T k M),
        ψ.complex (y ⬝ᵥ ((c.out : latticeBox T k M) : Fin k → F.Carrier)) =
      if y ∈ latticeBox T k (T.additiveConductor ψ - M) then
        (Fintype.card (latticeBox T k M ⧸ (latticeBox T k l).addSubgroupOf (latticeBox T k M)) : ℂ)
      else 0 := by
  classical
  let := T.topology
  let G := latticeBox T k M
  let L := (latticeBox T k l).addSubgroupOf G
  let χ : AddChar G ℂ := ψ.complex.compAddMonoidHom
    ((AddMonoidHom.mk' (fun d : Fin k → F.Carrier => y ⬝ᵥ d)
      (fun a b => dotProduct_add y a b)).comp G.subtype)
  have hχ : ∀ c : G, χ c = ψ.complex (y ⬝ᵥ (c : Fin k → F.Carrier)) := fun _ => rfl
  split_ifs with hyM
  · calc ∑ c : G ⧸ L, ψ.complex (y ⬝ᵥ ((c.out : G) : Fin k → F.Carrier))
        = ∑ _c : G ⧸ L, (1 : ℂ) := Finset.sum_congr rfl fun c _ => by
          rw [UnitaryAdditiveCharacter.complex_apply,
            character_dotProduct_eq_one T ψ hyM (c.out).2, Circle.coe_one]
      _ = Fintype.card (G ⧸ L) := by simp
  · obtain ⟨c₁, hc₁M, hc₁⟩ : ∃ c ∈ latticeBox T k M, ψ (c ⬝ᵥ y) ≠ 1 := by
      by_contra hall
      push Not at hall
      exact hyM (mem_latticeBox_of_forall_character_eq_one T ψ hall)
    calc ∑ c : G ⧸ L, ψ.complex (y ⬝ᵥ ((c.out : G) : Fin k → F.Carrier))
        = ∑ c : G ⧸ L, χ c.out := Finset.sum_congr rfl fun c _ => (hχ _).symm
      _ = 0 := by
        refine sum_out_eq_zero L χ ?_ (c₁ := ⟨c₁, hc₁M⟩) ?_
        · intro c hc
          rw [hχ, UnitaryAdditiveCharacter.complex_apply,
            character_dotProduct_eq_one T ψ hy (AddSubgroup.mem_addSubgroupOf.mp hc),
            Circle.coe_one]
        · rw [hχ, UnitaryAdditiveCharacter.complex_apply]
          intro h
          apply hc₁
          rw [dotProduct_comm]
          exact Circle.coe_eq_one.mp h

variable (m : ℕ)

/-- Near a nonzero row, a vector of `Φ⁺(Φ⁻ B)` agrees with an orbit function. -/
theorem exists_orbitFun_eq_near :
    letI := T.topology
    ∀ (B : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + 1) F.Carrier))
      (φ : (phiPlus T ψ m).obj ((phiMinus T ψ m).obj B)) (y : Fin (m + 1) → F.Carrier), y ≠ 0 →
      ∃ (w : B) (r : ℤ), ∀ x : mirabolic (m + 1) F.Carrier,
        projectionRow x - y ∈ latticeBox T (m + 1) r →
          orbitFun T ψ m B w x = phiPlusNormalizedEval T ψ m ((phiMinus T ψ m).obj B) φ x := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (m + 1 + 1)
  let := T.valuativeRel
  let := T.localField
  have : T2Space F.Carrier := T.fieldT2
  intro B φ y hy
  obtain ⟨Kφ, hKφ⟩ := phiPlusNormalizedEval_exists_openSubgroup T ψ m _ φ
  let g0 : Langlands.GeneralLinear (m + 1) F.Carrier := EqualRankFrobenius.lift y
  let x0 : mirabolic (m + 1) F.Carrier := levi g0
  obtain ⟨w₀, hw₀⟩ := phiMinusQuotient_surjective T ψ m B
    (phiPlusNormalizedEval T ψ m ((phiMinus T ψ m).obj B) φ x0)
  let w : B := B.representation x0⁻¹ w₀
  obtain ⟨Kw, hKw⟩ := exists_openSubgroup_fixing T m B w
  have hw0 : orbitFun T ψ m B w x0 =
      phiPlusNormalizedEval T ψ m ((phiMinus T ψ m).obj B) φ x0 := by
    have h : B.representation x0 w = w₀ := by
      change B.representation x0 (B.representation x0⁻¹ w₀) = w₀
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    exact (congrArg (phiMinusQuotient T ψ m B) h).trans hw₀
  let J : Subgroup (Langlands.GeneralLinear (m + 1) F.Carrier) :=
    (Kφ : Subgroup (mirabolic (m + 1) F.Carrier)).comap levi ⊓
      (Kw : Subgroup (mirabolic (m + 1) F.Carrier)).comap levi
  have hJo : IsOpen (J : Set (Langlands.GeneralLinear (m + 1) F.Carrier)) := by
    rw [Subgroup.coe_inf, Subgroup.coe_comap, Subgroup.coe_comap]
    exact (Kφ.isOpen.preimage continuous_levi).inter (Kw.isOpen.preimage continuous_levi)
  have hO := EqualRankFrobenius.isOpen_orbitSet hJo g0
  have hyO : y ∈ EqualRankFrobenius.orbitSet J g0 := by
    have h := EqualRankFrobenius.lastRow_mem_orbitSet J g0
    rwa [EqualRankFrobenius.lastRow_lift y hy] at h
  have hnhds : {d : Fin (m + 1) → F.Carrier | y + d ∈ EqualRankFrobenius.orbitSet J g0} ∈
      𝓝 (0 : Fin (m + 1) → F.Carrier) := by
    refine IsOpen.mem_nhds ?_ ?_
    · exact hO.preimage (continuous_const.add continuous_id)
    · show y + 0 ∈ EqualRankFrobenius.orbitSet J g0
      rw [add_zero]
      exact hyO
  obtain ⟨r, hr⟩ := exists_latticeBox_subset T hnhds
  refine ⟨w, r, fun x hx => ?_⟩
  have hxO : projectionRow x ∈ EqualRankFrobenius.orbitSet J g0 := by
    have h : y + (projectionRow x - y) ∈ EqualRankFrobenius.orbitSet J g0 := hr hx
    rwa [add_sub_cancel] at h
  obtain ⟨j, hj, hjx⟩ := EqualRankFrobenius.mem_orbitSet.mp hxO
  obtain ⟨q, hq⟩ := exists_plus_mul_levi hjx
  have hjφ : levi j ∈ Kφ := (Subgroup.mem_inf.mp hj).1
  have hjw : levi j ∈ Kw := (Subgroup.mem_inf.mp hj).2
  have hlevi : levi (g0 * j) = x0 * levi j := map_mul levi g0 j
  have hφj : phiPlusNormalizedEval T ψ m ((phiMinus T ψ m).obj B) φ (x0 * levi j) =
      phiPlusNormalizedEval T ψ m ((phiMinus T ψ m).obj B) φ x0 := hKφ ⟨levi j, hjφ⟩ x0
  have hw' : orbitFun T ψ m B w (levi (g0 * j)) =
      phiPlusNormalizedEval T ψ m ((phiMinus T ψ m).obj B) φ (levi (g0 * j)) := by
    rw [hlevi, orbitFun_mul, hKw _ hjw, hw0, hφj]
  rw [hq, orbitFun_covariant, phiPlusNormalizedEval_covariant, hw']

open Classical in
/-- The Fourier cutoff of an orbit function to a coset of a lattice box avoiding zero is
the orbit function of a radical relation. -/
theorem exists_cutoff :
    letI := T.topology
    ∀ (B : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + 1) F.Carrier)) (w : B)
      (z : Fin (m + 1) → F.Carrier) (r : ℤ), z ∉ latticeBox T (m + 1) r →
      ∃ w' : B, w' ∈ relations B.representation (radical (m + 1) F.Carrier) 1 ∧
        ∀ x, orbitFun T ψ m B w' x =
          if projectionRow x - z ∈ latticeBox T (m + 1) r then orbitFun T ψ m B w x else 0 := by
  let := T.topology
  intro B w z r hz
  obtain ⟨M, rfl⟩ : ∃ M, T.additiveConductor ψ - M = r := ⟨_, sub_sub_cancel _ r⟩
  obtain ⟨l₀, hl₀⟩ := exists_latticeBox_fixing T m B w
  obtain ⟨Nz, hNz⟩ := exists_mem_latticeBox T z
  let l := min l₀ (T.additiveConductor ψ - Nz)
  have hll₀ : l ≤ l₀ := min_le_left _ _
  have hlz : Nz ≤ T.additiveConductor ψ - l := by
    have := min_le_right l₀ (T.additiveConductor ψ - Nz)
    linarith
  let G := latticeBox T (m + 1) M
  let L := (latticeBox T (m + 1) l).addSubgroupOf G
  have : Finite (G ⧸ L) := finite_latticeBox_quotient T (m + 1) M l
  let : Fintype (G ⧸ L) := Fintype.ofFinite _
  let cut : B := ∑ c : G ⧸ L, ψ.complex (-(z ⬝ᵥ ((c.out : G) : Fin (m + 1) → F.Carrier))) •
    B.representation (radicalElement ((c.out : G) : Fin (m + 1) → F.Carrier)).val w
  have hkey : ∀ x, orbitFun T ψ m B cut x =
      (∑ c : G ⧸ L,
        ψ.complex ((projectionRow x - z) ⬝ᵥ ((c.out : G) : Fin (m + 1) → F.Carrier))) •
        orbitFun T ψ m B w x := by
    intro x
    simp only [cut]
    rw [orbitFun_sum, Finset.sum_smul]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [orbitFun_smul, orbitFun_radicalElement, mulVec_last_eq_dotProduct, smul_smul,
      sub_dotProduct, sub_eq_add_neg, AddChar.map_add_eq_mul, mul_comm]
  have hsum : ∑ c : G ⧸ L, ψ.complex (-(z ⬝ᵥ ((c.out : G) : Fin (m + 1) → F.Carrier))) = 0 := by
    have h := sum_character_out T ψ (m + 1) M l (-z) (neg_mem (latticeBox_mono T hlz hNz))
    have hn : -z ∉ latticeBox T (m + 1) (T.additiveConductor ψ - M) :=
      fun h' => hz (by simpa using neg_mem h')
    simp only [hn, ↓reduceIte] at h
    simpa only [neg_dotProduct] using h
  have hgen : ∀ c : Fin (m + 1) → F.Carrier,
      B.representation (radicalElement c).val w - w ∈
        relations B.representation (radical (m + 1) F.Carrier) 1 := by
    intro c
    have h := sub_mem_relations B.representation (radical (m + 1) F.Carrier) 1
      (radicalElement c) w
    simpa only [MonoidHom.one_apply, Units.val_one, one_smul] using h
  have hcutR : cut ∈ relations B.representation (radical (m + 1) F.Carrier) 1 := by
    have hcut : cut = ∑ c : G ⧸ L,
        ψ.complex (-(z ⬝ᵥ ((c.out : G) : Fin (m + 1) → F.Carrier))) •
          (B.representation (radicalElement ((c.out : G) : Fin (m + 1) → F.Carrier)).val w - w) := by
      simp only [smul_sub, Finset.sum_sub_distrib]
      rw [← Finset.sum_smul, hsum, zero_smul, sub_zero]
    rw [hcut]
    exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (hgen _)
  have hcard : (Fintype.card (G ⧸ L) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  refine ⟨(Fintype.card (G ⧸ L) : ℂ)⁻¹ • cut, Submodule.smul_mem _ _ hcutR, fun x => ?_⟩
  rw [orbitFun_smul, hkey]
  by_cases hfx : orbitFun T ψ m B w x = 0
  · rw [hfx, smul_zero, smul_zero]
    split_ifs <;> rfl
  · have hrow := projectionRow_mem_of_orbitFun_ne_zero T ψ m B w l₀ hl₀ x hfx
    have hy : projectionRow x - z ∈ latticeBox T (m + 1) (T.additiveConductor ψ - l) :=
      sub_mem (latticeBox_mono T (by linarith) hrow) (latticeBox_mono T hlz hNz)
    rw [sum_character_out T ψ (m + 1) M l _ hy]
    split_ifs with h
    · rw [smul_smul, inv_mul_cancel₀ hcard, one_smul]
    · rw [zero_smul, smul_zero]

/-- The Levi last rows of the support of a vector of `Φ⁺(Φ⁻ B)` lie in a compact set
avoiding zero. -/
theorem exists_compact_rows :
    letI := T.topology
    ∀ (B : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + 1) F.Carrier))
      (φ : (phiPlus T ψ m).obj ((phiMinus T ψ m).obj B)),
      ∃ C : Set (Fin (m + 1) → F.Carrier), IsCompact C ∧ (0 : Fin (m + 1) → F.Carrier) ∉ C ∧
        ∀ x, phiPlusNormalizedEval T ψ m ((phiMinus T ψ m).obj B) φ x ≠ 0 →
          projectionRow x ∈ C := by
  let := T.topology
  let := T.generalLinearTopologicalGroup (m + 1 + 1)
  intro B φ
  let rowBar : Induction.LeftQuotient (plusSubgroup m F.Carrier) → (Fin (m + 1) → F.Carrier) :=
    Quotient.lift projectionRow (fun a b hab => by
      have h := projectionRow_plus_mul ⟨b * a⁻¹, QuotientGroup.rightRel_apply.mp hab⟩ a
      simpa using h.symm)
  have hcont : Continuous rowBar :=
    Continuous.quotient_lift (continuous_lastRow.comp continuous_projection) _
  refine ⟨rowBar '' Induction.quotientSupport (plusSubgroup m F.Carrier)
      (phiPlusNormalizedEval T ψ m ((phiMinus T ψ m).obj B) φ),
    (phiPlusNormalizedEval_isCompact_quotientSupport T ψ m _ φ).image hcont, ?_, ?_⟩
  · rintro ⟨_, ⟨x, -, rfl⟩, h0⟩
    exact projectionRow_ne_zero x h0
  · intro x hx
    exact ⟨Induction.quotientMap (plusSubgroup m F.Carrier) x, ⟨x, hx, rfl⟩, rfl⟩

open Classical in
/-- Every vector of `Φ⁺(Φ⁻ B)` is the orbit function of a radical relation. -/
theorem exists_relation_orbitFun_eq :
    letI := T.topology
    ∀ (B : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + 1) F.Carrier))
      (φ : (phiPlus T ψ m).obj ((phiMinus T ψ m).obj B)),
      ∃ w : B, w ∈ relations B.representation (radical (m + 1) F.Carrier) 1 ∧
        ∀ x, orbitFun T ψ m B w x = phiPlusNormalizedEval T ψ m ((phiMinus T ψ m).obj B) φ x := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have : T2Space F.Carrier := T.fieldT2
  intro B φ
  let f := phiPlusNormalizedEval T ψ m ((phiMinus T ψ m).obj B) φ
  obtain ⟨C, hCc, hC0, hfC⟩ := exists_compact_rows T ψ m B φ
  have hnear := exists_orbitFun_eq_near T ψ m B φ
  have : Nonempty B := ⟨0⟩
  choose! W R hWR using hnear
  -- A finite cover of `C` by boxes on which `f` is an orbit function.
  obtain ⟨t, htC, hCt⟩ := hCc.elim_nhds_subcover
    (fun y => {z | z - y ∈ (latticeBox T (m + 1) (R y) : Set (Fin (m + 1) → F.Carrier))})
    (fun y _ => by
      refine IsOpen.mem_nhds ?_ ?_
      · exact (isOpen_latticeBox T _ _).preimage (continuous_id.sub continuous_const)
      · show y - y ∈ (latticeBox T (m + 1) (R y) : Set (Fin (m + 1) → F.Carrier))
        rw [sub_self]
        exact (latticeBox T (m + 1) (R y)).zero_mem)
  -- A box containing `C`.
  obtain ⟨N1, hN1⟩ := hCc.elim_directed_cover
    (fun N : ℤ => (latticeBox T (m + 1) N : Set (Fin (m + 1) → F.Carrier)))
    (fun N => isOpen_latticeBox T _ N)
    (fun z _ => Set.mem_iUnion.mpr (exists_mem_latticeBox T z))
    (Monotone.directed_le fun a b h => SetLike.coe_subset_coe.mpr (latticeBox_mono T h))
  -- A box avoiding `C`.
  obtain ⟨r₀, hr₀⟩ := exists_latticeBox_subset T (hCc.isClosed.isOpen_compl.mem_nhds hC0)
  obtain ⟨M, hM⟩ := (t.image fun y => -R y).exists_le
  let r := min r₀ (-M)
  have hrR : ∀ y ∈ t, r ≤ R y := fun y hy => by
    have h1 := hM _ (Finset.mem_image_of_mem _ hy)
    have h2 := min_le_right r₀ (-M)
    linarith
  have hrr₀ : r ≤ r₀ := min_le_left _ _
  let G := latticeBox T (m + 1) N1
  let L := (latticeBox T (m + 1) r).addSubgroupOf G
  have : Finite (G ⧸ L) := finite_latticeBox_quotient T (m + 1) N1 r
  let : Fintype (G ⧸ L) := Fintype.ofFinite _
  -- Each coset piece of `f` is the orbit function of a radical relation.
  have hpiece : ∀ c : G ⧸ L, ∃ w : B,
      w ∈ relations B.representation (radical (m + 1) F.Carrier) 1 ∧ ∀ x,
        orbitFun T ψ m B w x =
          if projectionRow x - ((c.out : G) : Fin (m + 1) → F.Carrier) ∈ latticeBox T (m + 1) r
          then f x else 0 := by
    intro c
    by_cases hp : ∃ p ∈ C, p - ((c.out : G) : Fin (m + 1) → F.Carrier) ∈ latticeBox T (m + 1) r
    · obtain ⟨p, hpC, hpz⟩ := hp
      obtain ⟨y, hyt, hpy⟩ := Set.mem_iUnion₂.mp (hCt hpC)
      have hpy' : p - y ∈ latticeBox T (m + 1) (R y) := hpy
      have hy0 : y ≠ 0 := fun h => hC0 (h ▸ htC y hyt)
      have hz : ((c.out : G) : Fin (m + 1) → F.Carrier) ∉ latticeBox T (m + 1) r := by
        intro hz
        have hp' : p ∈ latticeBox T (m + 1) r₀ :=
          latticeBox_mono T hrr₀ (by simpa using add_mem hpz hz)
        exact hr₀ hp' hpC
      obtain ⟨w', hw'R, hw'⟩ := exists_cutoff T ψ m B (W y) _ r hz
      refine ⟨w', hw'R, fun x => ?_⟩
      rw [hw']
      split_ifs with hx
      · apply hWR y hy0 x
        have h1 : projectionRow x - y = (projectionRow x - ((c.out : G) : Fin (m + 1) → F.Carrier)) -
            (p - ((c.out : G) : Fin (m + 1) → F.Carrier)) + (p - y) := by abel
        rw [h1]
        exact add_mem (latticeBox_mono T (hrR y hyt) (sub_mem hx hpz)) hpy'
      · rfl
    · refine ⟨0, Submodule.zero_mem _, fun x => ?_⟩
      rw [orbitFun_zero]
      split_ifs with hx
      · by_contra hfx
        exact hp ⟨projectionRow x, hfC x (fun h => hfx h.symm), hx⟩
      · rfl
  choose w hwR hw using hpiece
  refine ⟨∑ c, w c, Submodule.sum_mem _ fun c _ => hwR c, fun x => ?_⟩
  change orbitFun T ψ m B (∑ c, w c) x = f x
  rw [orbitFun_sum]
  simp only [hw]
  by_cases hfx : f x = 0
  · simp only [hfx, ite_self, Finset.sum_const_zero]
  · have hN : projectionRow x ∈ latticeBox T (m + 1) N1 := hN1 (hfC x hfx)
    let c₀ : G ⧸ L := ((⟨projectionRow x, hN⟩ : G) : G ⧸ L)
    rw [Finset.sum_eq_single c₀]
    · have hmem : projectionRow x - ((c₀.out : G) : Fin (m + 1) → F.Carrier) ∈
          latticeBox T (m + 1) r := by
        have h0 : ((c₀.out : G) : G ⧸ L) = ((⟨projectionRow x, hN⟩ : G) : G ⧸ L) :=
          QuotientAddGroup.out_eq' c₀
        have h := AddSubgroup.mem_addSubgroupOf.mp (QuotientAddGroup.eq.mp h0)
        rw [AddSubgroup.coe_add, AddSubgroup.coe_neg] at h
        rw [sub_eq_neg_add]
        exact h
      simp only [hmem, ↓reduceIte]
    · intro b _ hb
      have hbx : projectionRow x - ((b.out : G) : Fin (m + 1) → F.Carrier) ∉
          latticeBox T (m + 1) r := by
        intro hbx
        apply hb
        rw [← QuotientAddGroup.out_eq' b]
        apply QuotientAddGroup.eq.mpr
        rw [AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_add, AddSubgroup.coe_neg,
          ← sub_eq_neg_add]
        exact hbx
      simp only [hbx, ↓reduceIte]
    · intro h
      exact absurd (Finset.mem_univ _) h

/-- The orbit map is surjective. -/
theorem theta_surjective :
    letI := T.topology
    ∀ B : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + 1) F.Carrier),
      Function.Surjective (theta T ψ m B) := by
  let := T.topology
  intro B φ
  obtain ⟨w, hwR, hw⟩ := exists_relation_orbitFun_eq T ψ m B φ
  refine ⟨⟨w, (mem_liftStep_top T ψ m B w).mpr hwR⟩, ?_⟩
  apply phiPlusNormalizedEval_injective T ψ m _
  funext x
  exact hw x

end Surjective

/-! ## One plus step of the layer -/

section OneStep

variable (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology) (m : ℕ)

/-- The inclusion of the radical relations into `B`. -/
def relationsSubtype :
    letI := T.topology
    (B : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + 1) F.Carrier)) →
      Representation.IntertwiningMap (liftStep T ψ m B ⊤).toRepresentation B.representation := by
  letI := T.topology
  exact fun B =>
    { toLinearMap := (liftStep T ψ m B ⊤).toSubmodule.subtype
      isIntertwining' := fun _ => LinearMap.ext fun _ => rfl }

theorem relationsSubtype_apply :
    letI := T.topology
    ∀ (B : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + 1) F.Carrier))
      (w : (liftStep T ψ m B ⊤).toSubmodule), relationsSubtype T ψ m B w = w.1 :=
  fun _ _ => rfl

/-- The inverse of the orbit map. -/
def thetaInv :
    letI := T.topology
    (B : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + 1) F.Carrier)) →
      Representation.IntertwiningMap
        ((phiPlus T ψ m).obj ((phiMinus T ψ m).obj B)).representation
        (liftStep T ψ m B ⊤).toRepresentation := by
  letI := T.topology
  exact fun B => ((theta T ψ m B).ofBijective
    ⟨theta_injective T ψ m B, theta_surjective T ψ m B⟩).symm.toIntertwiningMap

theorem theta_thetaInv :
    letI := T.topology
    ∀ (B : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + 1) F.Carrier))
      (φ : (phiPlus T ψ m).obj ((phiMinus T ψ m).obj B)),
      theta T ψ m B (thetaInv T ψ m B φ) = φ := by
  let := T.topology
  intro B φ
  exact ((theta T ψ m B).ofBijective
    ⟨theta_injective T ψ m B, theta_surjective T ψ m B⟩).apply_symm_apply φ

theorem thetaInv_theta :
    letI := T.topology
    ∀ (B : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + 1) F.Carrier))
      (w : (liftStep T ψ m B ⊤).toSubmodule),
      thetaInv T ψ m B (theta T ψ m B w) = w := by
  let := T.topology
  intro B w
  exact theta_injective T ψ m B (theta_thetaInv T ψ m B _)

/-- A radical relation whose orbit lies in the range of `E` comes from `Φ⁺` of the source. -/
theorem exists_phiPlusPost_eq_of_mem :
    letI := T.topology
    ∀ (B : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + 1) F.Carrier))
      {τ : SmoothRep.{0, uF, uW} ℂ (mirabolic m F.Carrier)}
      (E : Representation.IntertwiningMap τ.representation
        ((phiMinus T ψ m).obj B).representation) (hE : Function.Injective E)
      (w : (liftStep T ψ m B ⊤).toSubmodule),
      (∀ g : mirabolic (m + 1) F.Carrier,
        phiMinusQuotient T ψ m B (B.representation g w.1) ∈ E.range) →
      ∃ φ, thetaInv T ψ m B (phiPlusPost T ψ m E hE φ) = w := by
  let := T.topology
  intro B τ E hE w hw
  obtain ⟨φ, hφ⟩ := (mem_range_phiPlusPost T ψ m E hE (theta T ψ m B w)).mpr
    (fun x => by rw [theta_eval, orbitFun_apply]; exact hw x)
  refine ⟨φ, ?_⟩
  rw [show phiPlusPost T ψ m E hE φ = theta T ψ m B w from hφ, thetaInv_theta]

/-- The composite `Φ⁺ τ → Φ⁺(Φ⁻ B) ≅ R(B) ⊆ B` attached to an injective `E : τ → Φ⁻ B`. -/
def plusStepMap :
    letI := T.topology
    (B : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + 1) F.Carrier)) →
      {τ : SmoothRep.{0, uF, uW} ℂ (mirabolic m F.Carrier)} →
      (E : Representation.IntertwiningMap τ.representation
        ((phiMinus T ψ m).obj B).representation) → Function.Injective E →
      Representation.IntertwiningMap ((phiPlus T ψ m).obj τ).representation
        B.representation := by
  letI := T.topology
  exact fun B _ E hE =>
    (relationsSubtype T ψ m B).comp ((thetaInv T ψ m B).comp (phiPlusPost T ψ m E hE))

theorem plusStepMap_apply :
    letI := T.topology
    ∀ (B : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + 1) F.Carrier))
      {τ : SmoothRep.{0, uF, uW} ℂ (mirabolic m F.Carrier)}
      (E : Representation.IntertwiningMap τ.representation
        ((phiMinus T ψ m).obj B).representation) (hE : Function.Injective E)
      (φ : (phiPlus T ψ m).obj τ),
      plusStepMap T ψ m B E hE φ = (thetaInv T ψ m B (phiPlusPost T ψ m E hE φ)).1 :=
  fun _ _ _ _ _ => rfl

theorem plusStepMap_injective :
    letI := T.topology
    ∀ (B : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + 1) F.Carrier))
      {τ : SmoothRep.{0, uF, uW} ℂ (mirabolic m F.Carrier)}
      (E : Representation.IntertwiningMap τ.representation
        ((phiMinus T ψ m).obj B).representation) (hE : Function.Injective E),
      Function.Injective (plusStepMap T ψ m B E hE) := by
  let := T.topology
  intro B τ E hE a b hab
  have h1 : (thetaInv T ψ m B (phiPlusPost T ψ m E hE a)).1 =
      (thetaInv T ψ m B (phiPlusPost T ψ m E hE b)).1 :=
    (plusStepMap_apply T ψ m B E hE a).symm.trans (hab.trans (plusStepMap_apply T ψ m B E hE b))
  have h2 := congrArg (theta T ψ m B) (Subtype.ext h1)
  rw [theta_thetaInv, theta_thetaInv] at h2
  exact phiPlusPost_injective T ψ m E hE h2

theorem mem_range_plusStepMap :
    letI := T.topology
    ∀ (B : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + 1) F.Carrier))
      {τ : SmoothRep.{0, uF, uW} ℂ (mirabolic m F.Carrier)}
      (E : Representation.IntertwiningMap τ.representation
        ((phiMinus T ψ m).obj B).representation) (hE : Function.Injective E) (v : B),
      v ∈ (plusStepMap T ψ m B E hE).range ↔ v ∈ liftStep T ψ m B E.range := by
  let := T.topology
  intro B τ E hE v
  rw [Representation.IntertwiningMap.mem_range, mem_liftStep]
  constructor
  · rintro ⟨φ, rfl⟩
    rw [plusStepMap_apply]
    refine ⟨(mem_liftStep_top T ψ m B _).mp (thetaInv T ψ m B (phiPlusPost T ψ m E hE φ)).2,
      fun g => ⟨phiPlusNormalizedEval T ψ m τ φ g, ?_⟩⟩
    have h := congrArg (fun η => phiPlusNormalizedEval T ψ m ((phiMinus T ψ m).obj B) η g)
      (theta_thetaInv T ψ m B (phiPlusPost T ψ m E hE φ))
    exact h.symm
  · rintro ⟨hvR, hvX⟩
    obtain ⟨φ, hφ⟩ := exists_phiPlusPost_eq_of_mem T ψ m B E hE
      ⟨v, (mem_liftStep_top T ψ m B v).mpr hvR⟩ hvX
    exact ⟨φ, (plusStepMap_apply T ψ m B E hE φ).trans (congrArg Subtype.val hφ)⟩

/-- One plus step: an injective intertwining map into `Φ⁻ B` with range `X` gives an
injective intertwining map from its normalized `Φ⁺` into `B` with range the lift of `X`. -/
theorem exists_plusStep :
    letI := T.topology
    ∀ (B : SmoothRep.{0, uF, uV} ℂ (mirabolic (m + 1) F.Carrier))
      {τ : SmoothRep.{0, uF, uW} ℂ (mirabolic m F.Carrier)}
      (E : Representation.IntertwiningMap τ.representation
        ((phiMinus T ψ m).obj B).representation),
      Function.Injective E →
        ∃ E' : Representation.IntertwiningMap ((phiPlus T ψ m).obj τ).representation
            B.representation,
          Function.Injective E' ∧ E'.range = liftStep T ψ m B E.range := by
  let := T.topology
  intro B τ E hE
  exact ⟨plusStepMap T ψ m B E hE, plusStepMap_injective T ψ m B E hE,
    SetLike.ext (mem_range_plusStepMap T ψ m B E hE)⟩

end OneStep

end Langlands.Derivative.Mirabolic.HighestLayer
