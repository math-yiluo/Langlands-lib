import Langlands.Representation.Whittaker.TwoBlockCellSectionStatement
import Langlands.Representation.Geometric.OrbitSectionExtensionProof
import Langlands.Representation.Shahidi.RadicalMeasures
import Langlands.Representation.Shahidi.TwoBlocks
import Langlands.Group.GL.OppositeBlocks
import Langlands.Group.GL.BlockIwahoriBasis
import Langlands.Group.GL.CountabilityProof
import Langlands.Representation.Hecke.CommonInvarianceProof
import Langlands.Representation.Twist.SmoothProof
import Langlands.Representation.Smooth.Transfer.PullbackProof
import Langlands.Representation.Tensor.Finite
import Langlands.Representation.Shahidi.IntertwiningInduced
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected

/-!
# Proof of the two-block cell sections

For smooth `π₁`, `π₂`, every function `x ↦ Ψ(x) v` is the restriction
`x ↦ f(w n(x))` of an element `f` of the cell submodule `D`. The function
`q ↦ Ψ(lowerCoordinates q) v` on the opposite radical `Q` is extended from the
open `P`-orbit of the base coset by the Library's orbit-section extension, and
the result is right translated by `w⁻¹`. Openness of `P Q` comes from the block
Iwahori factorization.
-/

noncomputable section

namespace Langlands.Whittaker

open GeneralLinear

universe uF uV u

section Lower

variable (m n : ℕ) (hm : 0 < m) (hn : 0 < n) (R : Type u) [Field R]

theorem lower_zero : Shahidi.lower m n R 0 = 1 := by
  simp [Shahidi.lower]

theorem lower_add (x y : Matrix (Fin n) (Fin m) R) :
    Shahidi.lower m n R (x + y) = Shahidi.lower m n R x * Shahidi.lower m n R y := by
  simp only [Shahidi.lower, Shahidi.intertwiningUnipotent_add]
  group

theorem lower_mem_oppositeUnipotentSubgroup (x : Matrix (Fin n) (Fin m) R) :
    Shahidi.lower m n R x ∈ (Shahidi.twoBlocks m n hm hn).oppositeUnipotentSubgroup R := by
  rw [BlockShape.mem_oppositeUnipotentSubgroup_iff, BlockShape.mem_oppositeParabolic_iff]
  refine ⟨fun i j a b hij => ?_, fun i a b => ?_⟩
  · fin_cases i <;> fin_cases j
    · exact False.elim ((lt_irrefl _) hij)
    · change Shahidi.lower m n R x ((Shahidi.twoBlocks m n hm hn).index 0 a)
        ((Shahidi.twoBlocks m n hm hn).index 1 b) = 0
      exact (congrArg₂ (fun i j : Fin (m + n) => Shahidi.lower m n R x i j)
        (Shahidi.twoBlocks_index_first hm hn a) (Shahidi.twoBlocks_index_second hm hn b)).trans
        (Shahidi.lower_first_second m n R x a b)
    · exact False.elim (by simp at hij)
    · exact False.elim ((lt_irrefl _) hij)
  · fin_cases i
    · change Shahidi.lower m n R x ((Shahidi.twoBlocks m n hm hn).index 0 a)
        ((Shahidi.twoBlocks m n hm hn).index 0 b) = if a = b then 1 else 0
      exact (congrArg₂ (fun i j : Fin (m + n) => Shahidi.lower m n R x i j)
        (Shahidi.twoBlocks_index_first hm hn a) (Shahidi.twoBlocks_index_first hm hn b)).trans
        (Shahidi.lower_first_first m n R x a b)
    · change Shahidi.lower m n R x ((Shahidi.twoBlocks m n hm hn).index 1 a)
        ((Shahidi.twoBlocks m n hm hn).index 1 b) = if a = b then 1 else 0
      exact (congrArg₂ (fun i j : Fin (m + n) => Shahidi.lower m n R x i j)
        (Shahidi.twoBlocks_index_second hm hn a) (Shahidi.twoBlocks_index_second hm hn b)).trans
        (Shahidi.lower_second_second m n R x a b)

theorem eq_lower_of_mem_oppositeUnipotentSubgroup {g : Langlands.GeneralLinear (m + n) R}
    (hg : g ∈ (Shahidi.twoBlocks m n hm hn).oppositeUnipotentSubgroup R) :
    g = Shahidi.lower m n R (Shahidi.lowerCoordinates m n g) := by
  rw [BlockShape.mem_oppositeUnipotentSubgroup_iff, BlockShape.mem_oppositeParabolic_iff] at hg
  obtain ⟨hlow, hdiag⟩ := hg
  apply Units.ext
  ext i j
  induction i using Fin.addCases <;> induction j using Fin.addCases
  · rename_i a b
    have h := hdiag 0 a b
    rw [Shahidi.twoBlocks_index_first, Shahidi.twoBlocks_index_first] at h
    rw [Shahidi.lower_first_first]
    exact h
  · rename_i a b
    have h := hlow 0 1 a b (by change (0 : Fin 2) < 1; decide)
    rw [Shahidi.twoBlocks_index_first, Shahidi.twoBlocks_index_second] at h
    rw [Shahidi.lower_first_second]
    exact h
  · rename_i a b
    rw [Shahidi.lower_second_first]
    rfl
  · rename_i a b
    have h := hdiag 1 a b
    rw [Shahidi.twoBlocks_index_second, Shahidi.twoBlocks_index_second] at h
    rw [Shahidi.lower_second_second]
    exact h

theorem eq_one_of_mem_parabolic_of_mem_oppositeUnipotentSubgroup
    {g : Langlands.GeneralLinear (m + n) R}
    (hP : g ∈ (Shahidi.twoBlocks m n hm hn).parabolic R)
    (hQ : g ∈ (Shahidi.twoBlocks m n hm hn).oppositeUnipotentSubgroup R) : g = 1 := by
  rw [eq_lower_of_mem_oppositeUnipotentSubgroup m n hm hn R hQ]
  have h0 : Shahidi.lowerCoordinates m n g = 0 := by
    ext i j
    exact (Shahidi.twoBlocks_mem_parabolic_iff hm hn R g).mp hP i j
  rw [h0, lower_zero]

theorem lowerCoordinates_one :
    Shahidi.lowerCoordinates m n (1 : Langlands.GeneralLinear (m + n) R) = 0 := by
  rw [← lower_zero m n R, Shahidi.lowerCoordinates_lower]

theorem lowerCoordinates_mul {g h : Langlands.GeneralLinear (m + n) R}
    (hg : g ∈ (Shahidi.twoBlocks m n hm hn).oppositeUnipotentSubgroup R)
    (hh : h ∈ (Shahidi.twoBlocks m n hm hn).oppositeUnipotentSubgroup R) :
    Shahidi.lowerCoordinates m n (g * h) =
      Shahidi.lowerCoordinates m n g + Shahidi.lowerCoordinates m n h := by
  conv_lhs => rw [eq_lower_of_mem_oppositeUnipotentSubgroup m n hm hn R hg,
    eq_lower_of_mem_oppositeUnipotentSubgroup m n hm hn R hh, ← lower_add,
    Shahidi.lowerCoordinates_lower]

/-- The rectangular coordinate of the opposite radical, as a homomorphism. -/
def oppositeCoordinateHom :
    (Shahidi.twoBlocks m n hm hn).oppositeUnipotentSubgroup R →*
      Multiplicative (Matrix (Fin n) (Fin m) R) where
  toFun q := Multiplicative.ofAdd (Shahidi.lowerCoordinates m n q.val)
  map_one' := by
    rw [OneMemClass.coe_one, lowerCoordinates_one]
    rfl
  map_mul' q r := by
    rw [Subgroup.coe_mul, lowerCoordinates_mul m n hm hn R q.property r.property]
    rfl

end Lower

section Topology

/-- If an open subgroup lies in the product set `P Q`, then `P Q` is open. -/
theorem isOpen_mul_of_openSubgroup {G : Type u} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (P Q : Subgroup G) (K : OpenSubgroup G)
    (hK : ∀ k ∈ K, ∃ p ∈ P, ∃ q ∈ Q, k = p * q) :
    IsOpen {g : G | ∃ p ∈ P, ∃ q ∈ Q, g = p * q} := by
  rw [isOpen_iff_forall_mem_open]
  rintro _ ⟨p, hp, q, hq, rfl⟩
  refine ⟨(fun x => p * x * q) '' (K : Set G), ?_, ?_, ⟨1, K.one_mem, by simp⟩⟩
  · rintro _ ⟨k, hk, rfl⟩
    obtain ⟨p', hp', q', hq', rfl⟩ := hK k hk
    exact ⟨p * p', P.mul_mem hp hp', q' * q, Q.mul_mem hq' hq, by simp only [mul_assoc]⟩
  · exact ((isOpenMap_mul_right q).comp (isOpenMap_mul_left p)) _ K.isOpen

/-- The orbit of the base coset under `Q` is open when `P Q` is open. -/
theorem isOpen_cosetOrbit_one {G : Type u} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (P Q : Subgroup G)
    (h : IsOpen {g : G | ∃ p ∈ P, ∃ q ∈ Q, g = p * q}) :
    IsOpen (Geometric.cosetOrbit P Q 1) := by
  apply (isQuotientMap_quotient_mk' (s := QuotientGroup.rightRel P)).isOpen_preimage.mp
  convert h using 1
  ext g
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, Geometric.cosetOrbit, Set.mem_range]
  constructor
  · rintro ⟨q, hq⟩
    have hr := QuotientGroup.rightRel_apply.mp (Quotient.exact hq)
    exact ⟨g * (1⁻¹ * (q : G))⁻¹, hr, q, q.property, by group⟩
  · rintro ⟨p, hp, q, hq, rfl⟩
    refine ⟨⟨q, hq⟩, Quotient.sound (QuotientGroup.rightRel_apply.mpr ?_)⟩
    simpa using hp

end Topology

section Invariance

variable {X : Type u} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
  [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X]

/-- A Schwartz–Bruhat function is invariant under translation by an open subgroup,
written multiplicatively. -/
theorem SchwartzBruhat.exists_openSubgroup_invariant
    (f : HarmonicAnalysis.SchwartzBruhat X) :
    ∃ H : OpenSubgroup (Multiplicative X), ∀ h ∈ H, ∀ x : X,
      f (x + Multiplicative.toAdd h) = f x := by
  classical
  let : T2Space (Multiplicative X) := ‹T2Space X›
  let : LocallyCompactSpace (Multiplicative X) := ‹LocallyCompactSpace X›
  let : TotallyDisconnectedSpace (Multiplicative X) := ‹TotallyDisconnectedSpace X›
  let fm : HarmonicAnalysis.SchwartzBruhat (Multiplicative X) :=
    ⟨fun x => f x.toAdd, f.property⟩
  obtain ⟨K, _, _, hKf⟩ :=
    Hecke.TestFunction.commonCompactOpenBiInvariance (Multiplicative X) {fm} ⊤
  refine ⟨K, fun h hh x => ?_⟩
  rw [add_comm]
  exact (hKf fm (Finset.mem_singleton_self fm)).1 ⟨h, hh⟩ (Multiplicative.ofAdd x)

end Invariance

private theorem fieldTotallyDisconnected {p : ℕ} [Fact p.Prime]
    {F : PadicField.{uF} p} (T : F.TopologicalData) :
    letI := T.topology
    TotallyDisconnectedSpace F.Carrier := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier using 1
    exact Valuation.toTopologicalSpace_eq (ValuativeRel.valuation F.Carrier)
  infer_instance

section Cell

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (a b : ℕ)

/-- The point `w n(x) w⁻¹` of the opposite radical with lower-left block `x`. -/
def oppositeLower (x : Matrix (Fin (b + 1)) (Fin (a + 1)) F.Carrier) :
    (twoBlockShape a b).oppositeUnipotentSubgroup F.Carrier :=
  ⟨Shahidi.lower (a + 1) (b + 1) F.Carrier x,
    lower_mem_oppositeUnipotentSubgroup (a + 1) (b + 1) (Nat.succ_pos a) (Nat.succ_pos b)
      F.Carrier x⟩

/-- The block Iwahori factorization puts an open subgroup inside `P Q`. -/
theorem exists_openSubgroup_subset_parabolic_mul_opposite :
    letI := F.canonicalTopologicalData.topology
    ∃ K : OpenSubgroup (Langlands.GeneralLinear (a + 1 + (b + 1)) F.Carrier),
      ∀ k ∈ K, ∃ p ∈ twoBlockParabolic F a b,
        ∃ q ∈ (twoBlockShape a b).oppositeUnipotentSubgroup F.Carrier, k = p * q := by
  let := F.canonicalTopologicalData.topology
  obtain ⟨K, -, -, hK⟩ :=
    (twoBlockShape a b).exists_compactOpenSubgroup_hasBlockIwahoriFactorization
      F.canonicalTopologicalData (U := Set.univ) Filter.univ_mem
  refine ⟨K, fun k hk => ?_⟩
  obtain ⟨⟨l, m, u⟩, hlmu⟩ :=
    (BlockShape.HasBlockIwahoriFactorization.bijective _ _ hK).2 ⟨k⁻¹, K.inv_mem hk⟩
  have hk' : l.val * m.val * u.val = k⁻¹ := congrArg Subtype.val hlmu
  have hl := ((twoBlockShape a b).mem_iwahoriLower F.Carrier K.toSubgroup l.val).mp l.property
  have hm := ((twoBlockShape a b).mem_iwahoriLevi F.Carrier K.toSubgroup m.val).mp m.property
  have hu := ((twoBlockShape a b).mem_iwahoriUpper F.Carrier K.toSubgroup u.val).mp u.property
  rw [BlockShape.unipotentSubgroup, Subgroup.mem_map] at hu
  rw [BlockShape.leviSubgroup, MonoidHom.mem_range] at hm
  obtain ⟨u', -, hu'⟩ := hu.2
  obtain ⟨m', hm'⟩ := hm.2
  refine ⟨u.val⁻¹ * m.val⁻¹, (twoBlockParabolic F a b).mul_mem
      ((twoBlockParabolic F a b).inv_mem ?_) ((twoBlockParabolic F a b).inv_mem ?_),
    l.val⁻¹, ((twoBlockShape a b).oppositeUnipotentSubgroup F.Carrier).inv_mem hl.2, ?_⟩
  · rw [← hu']
    exact u'.property
  · rw [← hm']
    exact ((twoBlockShape a b).leviInParabolic F.Carrier m').property
  · rw [← inv_inv k, ← hk']
    group

end Cell

/-- JPSS (9.1), section step: every `x ↦ Ψ(x) v` is the restriction of an element
of the cell submodule. -/
theorem twoBlockCellSection : TwoBlockCellSectionStatement.{uF, uV} := by
  intro p _ F a b V₁ V₂ _ _ _ _ π₁ π₂ hπ₁ hπ₂ Ψ v
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := fieldTotallyDisconnected T
  let := T.generalLinearTopologicalGroup (a + 1 + (b + 1))
  let := T.generalLinearNonarchimedean (a + 1 + (b + 1))
  let := T.generalLinearLocallyCompactSpace (a + 1 + (b + 1))
  let := T.generalLinearT2Space (a + 1 + (b + 1))
  let := T.generalLinearSigmaCompactSpace (a + 1 + (b + 1))
  let : TotallyDisconnectedSpace (Matrix (Fin (b + 1)) (Fin (a + 1)) F.Carrier) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin (b + 1) → Fin (a + 1) → F.Carrier))
  let : LocallyCompactSpace (Matrix (Fin (b + 1)) (Fin (a + 1)) F.Carrier) :=
    inferInstanceAs (LocallyCompactSpace (Fin (b + 1) → Fin (a + 1) → F.Carrier))
  let P := twoBlockParabolic F a b
  let Q := (twoBlockShape a b).oppositeUnipotentSubgroup F.Carrier
  let w := Shahidi.blockWeyl (a + 1) (b + 1) F.Carrier
  have hP : IsClosed (P : Set (Langlands.GeneralLinear (a + 1 + (b + 1)) F.Carrier)) :=
    (twoBlockShape a b).isClosed_parabolic F.Carrier
  have hQ : IsClosed (Q : Set (Langlands.GeneralLinear (a + 1 + (b + 1)) F.Carrier)) :=
    (twoBlockShape a b).isClosed_oppositeUnipotentSubgroup F.Carrier
  have hρ : IsSmooth (twoBlockInducingRepresentation F a b π₁ π₂) :=
    (isSmooth_twist_iff _ _ (T.isOpen_ker_parabolicHalfModulus (twoBlockShape a b))).2
      (isSmooth_comp _ ((twoBlockShape a b).leviProjectionContinuous F.Carrier).continuous
        (Shahidi.isSmooth_pairRepresentation (Nat.succ_pos a) (Nat.succ_pos b) hπ₁ hπ₂))
  let A : Induction.SmoothRep.{0, uF, uV} ℂ P :=
    Langlands.SmoothRep.of (twoBlockInducingRepresentation F a b π₁ π₂) hρ
  let S := Geometric.orbitStabilizer P Q 1
  let σ := A.obj.ρ.comp (Geometric.stabilizerToInducing P Q 1)
  have hS : ∀ s : S, s = 1 := by
    intro s
    have hs := (Geometric.stabilizerToInducing P Q 1 s).property
    rw [Geometric.stabilizerToInducing_apply, inv_one, one_mul, mul_one] at hs
    exact Subtype.ext (Subtype.ext
      (eq_one_of_mem_parabolic_of_mem_oppositeUnipotentSubgroup (a + 1) (b + 1)
        (Nat.succ_pos a) (Nat.succ_pos b) F.Carrier hs s.val.property))
  let f0 : Q → PiTensorProduct ℂ (Shahidi.pairCarrier V₁ V₂) :=
    fun q => Ψ (Shahidi.lowerCoordinates (a + 1) (b + 1) q.val) • v
  have hcov : ∀ (s : S) (q : Q), f0 ((s : Q) * q) = σ s (f0 q) := by
    intro s q
    rw [hS s]
    simp
  obtain ⟨H, hH⟩ := SchwartzBruhat.exists_openSubgroup_invariant Ψ
  have hcoord : Continuous (oppositeCoordinateHom (a + 1) (b + 1) (Nat.succ_pos a)
      (Nat.succ_pos b) F.Carrier) :=
    continuous_ofAdd.comp
      ((Shahidi.continuous_lowerCoordinates (a + 1) (b + 1)).comp continuous_subtype_val)
  let K : OpenSubgroup Q := H.comap _ hcoord
  have hK : ∀ (k : K) (q : Q), f0 (q * (k : Q)) = f0 q := by
    intro k q
    simp only [f0, Subgroup.coe_mul]
    rw [lowerCoordinates_mul (a + 1) (b + 1) (Nat.succ_pos a) (Nat.succ_pos b) F.Carrier
      q.property (k : Q).property]
    exact congrArg (· • v) (hH _ k.property _)
  have hsupp : Function.support f0 =
      oppositeLower F a b '' Function.support (fun x => Ψ x • v) := by
    ext q
    constructor
    · intro hq
      refine ⟨Shahidi.lowerCoordinates (a + 1) (b + 1) q.val, hq, Subtype.ext ?_⟩
      exact (eq_lower_of_mem_oppositeUnipotentSubgroup (a + 1) (b + 1) (Nat.succ_pos a)
        (Nat.succ_pos b) F.Carrier q.property).symm
    · rintro ⟨x, hx, rfl⟩
      change Ψ (Shahidi.lowerCoordinates (a + 1) (b + 1)
        (Shahidi.lower (a + 1) (b + 1) F.Carrier x)) • v ≠ 0
      rwa [Shahidi.lowerCoordinates_lower]
  have hφ : IsCompact (Function.support (fun x => Ψ x • v)) := by
    have hlc : IsLocallyConstant (fun x => Ψ x • v) :=
      Ψ.locallyConstant.comp (fun c : ℂ => c • v)
    exact (Ψ.hasCompactSupport.smul_right (f' := fun _ => v)).isCompact.of_isClosed_subset
      (hlc.isOpen_fiber 0).isClosed_compl (subset_tsupport _)
  have hc : IsCompact (Induction.quotientSupport S f0) := by
    rw [Induction.quotientSupport, hsupp, Set.image_image]
    refine hφ.image ?_
    exact continuous_quotient_mk'.comp
      ((Shahidi.continuous_lower (a + 1) (b + 1) F.Carrier).subtype_mk _)
  let g := Induction.compactFunctionOf S σ f0 hcov K hK hc
  have hU : IsOpen (Geometric.cosetOrbit P Q 1) := by
    obtain ⟨K₀, hK₀⟩ := exists_openSubgroup_subset_parabolic_mul_opposite F a b
    exact isOpen_cosetOrbit_one P Q (isOpen_mul_of_openSubgroup P Q K₀ hK₀)
  have hZ : IsClosed ((fun x : Geometric.cosetOrbit P Q 1 =>
      (x : Induction.LeftQuotient P)) ⁻¹' Geometric.cosetOrbit P Q 1) := by
    rw [Subtype.coe_preimage_self]
    exact isClosed_univ
  obtain ⟨f, hfU, hfQ⟩ := Geometric.closedOrbitSectionExtension.{uF, uV}
    (Langlands.GeneralLinear (a + 1 + (b + 1)) F.Carrier) P Q hP hQ 1
    (Geometric.cosetOrbit P Q 1) hU subset_rfl hZ A g
  let f' : TwoBlockInducedCarrier F a b π₁ π₂ := twoBlockInduced F a b π₁ π₂ w⁻¹ f.val
  have hrestr : ∀ x, twoBlockRestriction F a b π₁ π₂ f' x = Ψ x • v := by
    intro x
    calc twoBlockRestriction F a b π₁ π₂ f' x
        = Induction.eval P A.obj.ρ f.val (1⁻¹ * (oppositeLower F a b x : _)) := by
          rw [inv_one, one_mul]
          rfl
      _ = f0 (oppositeLower F a b x) := hfQ _
      _ = Ψ x • v := by
          change Ψ (Shahidi.lowerCoordinates (a + 1) (b + 1)
            (Shahidi.lower (a + 1) (b + 1) F.Carrier x)) • v = Ψ x • v
          rw [Shahidi.lowerCoordinates_lower]
  refine ⟨f', ⟨?_, ?_⟩, hrestr⟩
  · intro x hx
    have hx' : Induction.eval P A.obj.ρ f.val (x * w⁻¹) ≠ 0 := hx
    obtain ⟨q, hq⟩ := hfU _ hx'
    have hr := QuotientGroup.rightRel_apply.mp (Quotient.exact hq)
    rw [inv_one, one_mul] at hr
    have hq' := eq_lower_of_mem_oppositeUnipotentSubgroup (a + 1) (b + 1) (Nat.succ_pos a)
      (Nat.succ_pos b) F.Carrier q.property
    have key : ∀ y, (q : Langlands.GeneralLinear (a + 1 + (b + 1)) F.Carrier) =
        w * Shahidi.intertwiningUnipotent (a + 1) (b + 1) F.Carrier y * w⁻¹ →
        x = x * w⁻¹ * (q : Langlands.GeneralLinear (a + 1 + (b + 1)) F.Carrier)⁻¹ * w *
          Shahidi.intertwiningUnipotent (a + 1) (b + 1) F.Carrier y := by
      intro y hy
      rw [hy]
      group
    exact ⟨⟨_, hr⟩, _, key _ hq'⟩
  · rw [show twoBlockRestriction F a b π₁ π₂ f' = fun x => Ψ x • v from funext hrestr]
    exact Ψ.hasCompactSupport.smul_right

end Langlands.Whittaker
