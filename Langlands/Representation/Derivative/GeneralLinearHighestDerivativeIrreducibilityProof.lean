import Langlands.Representation.Derivative.GeneralLinearHighestDerivativeIrreducibilityStatement
import Langlands.Representation.Derivative.HighestDerivativeChainSegmentProduct
import Langlands.Representation.Classification.MultisegmentSocleExhaustionProof
import Langlands.Representation.Classification.MultisegmentConstituentContragredientProof
import Langlands.Representation.Classification.MultisegmentConstituentRealTwistCompatibilityProof
import Langlands.Representation.Aubert.SegmentProductClass
import Langlands.Representation.CuspidalSupport.CuspidalEmbeddingProof
import Langlands.Representation.Smooth.Admissibility.FiniteLengthReduction

/-!
# Irreducibility of the highest general-linear derivative

The first assertion of Zelevinsky 1980, Theorem 8.1. The highest derivatives of
`π` and `|det| π̃` are smooth dual to one another, by applying the highest-derivative
pairing theorem in both directions. A proper nonzero quotient of the highest
derivative of `π` would both lose and retain the same iterated derivative chain:
it loses it by exactness on the ordered segment product and retains it by pairing
with its smooth dual inside the corresponding product for `|det| π̃`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory
open scoped NNReal

namespace Langlands.Derivative

open GeneralLinear HarmonicAnalysis PadicField.TopologicalData Classification
open Classification.MirabolicDerivativeContragredient HighestDerivativeChain

universe uF uV uG

section SmoothDuality

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

private theorem eq_zero_of_forall_smoothDual (hG : CompactOpenCofinal G)
    (X : SmoothRep.{0, uG, uV} ℂ G) (x : X) (hx : ∀ ℓ : X.contragredient, ℓ.val x = 0) :
    x = 0 := by
  apply smoothBidual_injective_of_compact_cofinal hG X.representation X.isSmooth
  rw [map_zero]
  exact Subtype.ext (LinearMap.ext hx)

private theorem pairingHom_injective {X Y : SmoothRep.{0, uG, uV} ℂ G}
    (γ : InvariantBilinear.forms X.representation Y.representation (fun _ => (1 : ℂ)))
    (hγ : ∀ y : Y, (∀ x : X, γ.val x y = 0) → y = 0) :
    Function.Injective (SmoothRep.hom
      (pairingContragredientHom γ (Representation.IntertwiningMap.id X.representation))) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro y hy
  apply hγ y
  intro x
  exact congrArg (fun ℓ : X.contragredient => ℓ.val x) hy

/-- Two one-sided pairings suffice: smooth duality gives a surjection from `Y` onto
`X̃` and an injection from `Y` into `X̃`. Finite length forces the latter to be onto. -/
private theorem dualIso_of_pairings (hG : CompactOpenCofinal G)
    {X Y : SmoothRep.{0, uG, uV} ℂ G} (hY : Y.HasFiniteLength) (hadm : Y.IsAdmissible)
    (γ₁ : InvariantBilinear.forms X.representation Y.representation (fun _ => (1 : ℂ)))
    (h₁ : ∀ x : X, (∀ y : Y, γ₁.val x y = 0) → x = 0)
    (γ₂ : InvariantBilinear.forms Y.representation X.representation (fun _ => (1 : ℂ)))
    (h₂ : ∀ y : Y, (∀ x : X, γ₂.val y x = 0) → y = 0) :
    Nonempty (Y ≅ X.contragredient) := by
  let γ₁' := InvariantBilinear.flipEquiv _ _ _ γ₁
  let a := pairingContragredientHom γ₁' (Representation.IntertwiningMap.id Y.representation)
  have ha : Function.Injective (SmoothRep.hom a) := pairingHom_injective γ₁' h₁
  have ha' := contragredientMap_surjective_of_injective_of_compact_cofinal hG
    X.isSmooth Y.contragredient.isSmooth (SmoothRep.hom a) ha
  let b := pairingContragredientHom γ₁ (Representation.IntertwiningMap.id X.representation)
  have hb : Function.Surjective (SmoothRep.hom b) := by
    intro ℓ
    obtain ⟨z, hz⟩ := ha' ℓ
    obtain ⟨y, rfl⟩ := (SmoothRep.smoothBidual_bijective hG Y hadm).2 z
    exact ⟨y, hz⟩
  let γ₂' := InvariantBilinear.flipEquiv _ _ _ γ₂
  let f := pairingContragredientHom γ₂' (Representation.IntertwiningMap.id X.representation)
  have hf : Function.Injective (SmoothRep.hom f) := pairingHom_injective γ₂' h₂
  let f₀ := Representation.IntertwiningMap.equivLinearMapAsModule _ _ (SmoothRep.hom f)
  let b₀ := Representation.IntertwiningMap.equivLinearMapAsModule _ _ (SmoothRep.hom b)
  have hf₀ : Function.Injective f₀ := hf
  have hb₀ : Function.Surjective b₀ := hb
  have hfin := IsFiniteLength.of_surjective hY hb₀
  obtain ⟨hnoeth, hart⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hfin
  have hf₀' : Function.Surjective f₀ := by
    apply LinearMap.range_eq_top.mp
    by_contra h
    have hlt := Submodule.length_lt h
    have hle := Module.length_le_of_surjective b₀ hb₀
    have heq := (LinearEquiv.ofInjective f₀ hf₀).length_eq
    exact (not_lt_of_ge hle) (heq.trans_lt hlt)
  exact ⟨SmoothRep.mkIso ((SmoothRep.hom f).ofBijective ⟨hf, hf₀'⟩)⟩

end SmoothDuality

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

private theorem highestOrder_eq_totalRank (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    {n : ℕ} (c : T.SegmentProductDatum.{max uF uV, uF} n)
    (ho : c.IsPrecedenceOrdered) (hs : c.HasSegmentSocles) (hc : c.multisegment ≠ 0) :
    letI := T.topology
    ∀ {A : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)} (f : A ⟶ c.induced),
      Function.Injective (SmoothRep.hom f) → Nontrivial A →
      ∀ hd : GeneralLinearHighestDerivativeOrderData T ψ A,
        hd.order = (c.multisegment.map Segment.rank).sum := by
  let := T.topology
  intro A f hf hA hd
  obtain ⟨hk, -, -, -, -, -, hvan, hnt⟩ := segmentProduct_step F T ψ c ho hs hc _ rfl
  rcases lt_trichotomy hd.order (c.multisegment.map Segment.rank).sum with hlt | heq | hgt
  · exact absurd (hd.higher_vanish _ hk.2 hlt)
      (not_subsingleton_iff_nontrivial.mpr (hnt A f hf hA))
  · exact heq
  · have := hvan hd.order hd.le_rank hgt
    have hinj := LevelCalculus.map_injective_of_exact
      (generalLinearDerivativeExactness.{uF, max uF uV} F T ψ n _ hd.le_rank) f hf
    exact absurd hinj.subsingleton (not_subsingleton_iff_nontrivial.mpr hd.nonzero)

/-- The pairing theorem for the mirabolic restrictions, expressed on the actual
`GL` derivatives. -/
private theorem gl_pairing_of_highest (ψ : @UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (M k : ℕ) (hk : 0 < k ∧ k ≤ M + 1) :
    letI := T.topology
    ∀ (A B : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (M + 1) F.Carrier)),
      Nontrivial ((generalLinearDerivative T ψ (M + 1) k hk.2).obj A) →
      (∀ (j : ℕ) (hj : j ≤ M + 1), k < j →
        Subsingleton ((generalLinearDerivative T ψ (M + 1) j hj).obj A)) →
      ∀ β : InvariantBilinear.forms ((generalLinearRestriction T M).obj A).representation
          ((generalLinearRestriction T M).obj B).representation
          (fun g => ((((T.determinantNorm (M + 1)) g.val : ℝ≥0) : ℝ) : ℂ)),
        (∀ a, (∀ b, β.val a b = 0) → a = 0) →
        ∃ γ : InvariantBilinear.forms
            ((generalLinearDerivative T ψ (M + 1) k hk.2).obj A).representation
            ((generalLinearDerivative T ψ (M + 1) k hk.2).obj B).representation (fun _ => (1 : ℂ)),
          ∀ a, (∀ b, γ.val a b = 0) → a = 0 := by
  let := T.topology
  intro A B hnt hvan β hβ
  rw [← mirabolicDerivativeOfOrder_restriction ψ M k hk A,
    ← mirabolicDerivativeOfOrder_restriction ψ M k hk B]
  refine mirabolicHighestDerivativePairing.{uF, max uF uV, max uF uV} F T ψ M _ _ k hk
    ?_ ?_ β hβ
  · rwa [mirabolicDerivativeOfOrder_restriction]
  · intro j hj hkj
    rw [mirabolicDerivativeOfOrder_restriction]
    exact hvan j hj.2 hkj

/-- Zelevinsky 1980, Theorem 8.1 (irreducibility assertion). -/
theorem generalLinearHighestDerivativeIrreducibility :
    GeneralLinearHighestDerivativeIrreducibility.{uF, uV} F T := by
  let := T.topology
  let : ∀ r : ℕ, IsTopologicalGroup (GeneralLinear r F.Carrier) := T.generalLinearTopologicalGroup
  intro N hN ψ π hπ hd
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  obtain ⟨a, -, ha⟩ := multisegmentSocleExhaustion.{uF, uV} F T (M + 1) π hπ
  have ha₀ := ha
  obtain ⟨d, hdms, hod, hsd, -, j, hj, -⟩ := ha₀
  let f := SmoothRep.ofHom j
  have hf : Function.Injective (SmoothRep.hom f) := hj
  have hd0 : d.multisegment ≠ 0 := fun h => by
    have := eq_zero_of_multisegment_eq_zero d h
    omega
  let k := hd.order
  have hk : 0 < k ∧ k ≤ M + 1 := ⟨hd.positive, hd.le_rank⟩
  have hkdef : k = (d.multisegment.map Segment.rank).sum :=
    highestOrder_eq_totalRank.{uF, uV} F T ψ d hod hsd hd0 f hf
      (SegmentHeadSupport.nontrivial_of_isIrreducible hπ) hd
  obtain ⟨_, d', hod', hsd', hd'ms, ⟨ed⟩, -, -⟩ := segmentProduct_step F T ψ d hod hsd hd0 k hkdef
  -- The dual and real-twist realizations preserve ranks and lengths of segments.
  let π' := π.contragredient.twist (T.determinantPowerCharacter (M + 1) 1)
    (T.isOpen_ker_determinantPowerCharacter (M + 1) 1)
  have hπ' := (multisegmentConstituentRealTwistCompatibility.{uF, max uF uV} F T (M + 1) hN
      (a.map Segment.dual) 1 π.contragredient).1.mp
    (Multisegment.IsZelevinskySocle.contragredient hN ha)
  obtain ⟨c, hcms, hoc, hsc, hirr', j', hj', -⟩ := hπ'
  let f' := SmoothRep.ofHom j'
  have hf' : Function.Injective (SmoothRep.hom f') := hj'
  have hc0 : c.multisegment ≠ 0 := fun h => by
    have := eq_zero_of_multisegment_eq_zero c h
    omega
  have hlevels : levelSequence c.multisegment = levelSequence d.multisegment := by
    rw [hcms, hdms, Multisegment.twist,
      levelSequence_map _ (Segment.twist_length _) (Segment.twist_rank _),
      levelSequence_map _ Segment.dual_length Segment.dual_rank]
  have hcons := (levelSequence_eq_cons hc0).symm.trans (hlevels.trans (levelSequence_eq_cons hd0))
  have hkc : k = (c.multisegment.map Segment.rank).sum := hkdef.trans (List.cons.inj hcons).1.symm
  obtain ⟨_, c', hoc', hsc', hc'ms, ⟨ec⟩, hvan, hnt⟩ :=
    segmentProduct_step F T ψ c hoc hsc hc0 k hkc
  have htail : levelSequence c'.multisegment = levelSequence d'.multisegment := by
    rw [hc'ms, hd'ms]
    exact (List.cons.inj hcons).2
  let D := generalLinearDerivative.{uF, max uF uV} T ψ (M + 1) k hk.2
  let X := D.obj π
  let Y := D.obj π'
  have hX : Nontrivial X := hd.nonzero
  have hY : Nontrivial Y := hnt _ f' hf' (SegmentHeadSupport.nontrivial_of_isIrreducible hirr')
  have hvan' (j : ℕ) (hj : j ≤ M + 1) (hlt : k < j) :
      Subsingleton ((generalLinearDerivative T ψ (M + 1) j hj).obj π') := by
    have := hvan j hj hlt
    exact (LevelCalculus.map_injective_of_exact
      (generalLinearDerivativeExactness.{uF, max uF uV} F T ψ (M + 1) j hj) f' hf').subsingleton
  -- Evaluation against the twisted smooth dual is covariant by `|det|` on the mirabolic.
  let β : InvariantBilinear.forms ((generalLinearRestriction T M).obj π).representation
      ((generalLinearRestriction T M).obj π').representation
      (fun g => ((((T.determinantNorm (M + 1)) g.val : ℝ≥0) : ℝ) : ℂ)) :=
    ⟨(smoothDualPairing π.representation).flip, fun g v ℓ => by
      change smoothDualPairing π.representation
          ((T.determinantPowerCharacter (M + 1) 1 g.val : ℂ) •
            smoothContragredient π.representation g.val ℓ) (π.representation g.val v) =
        _ * smoothDualPairing π.representation ℓ v
      rw [map_smul, LinearMap.smul_apply, smoothDualPairing_invariant, smul_eq_mul,
        coe_realPowerCharacter, Real.rpow_one]⟩
  let β' := InvariantBilinear.flipEquiv _ _ _ β
  obtain ⟨γ₁, h₁⟩ := gl_pairing_of_highest.{uF, uV} F T ψ M k hk π π' hX
    hd.higher_vanish β (fun v hv => eq_zero_of_forall_smoothDual (compactOpen_cofinal F T _) π v hv)
  obtain ⟨γ₂, h₂⟩ := gl_pairing_of_highest.{uF, uV} F T ψ M k hk π' π hY hvan' β'
    (fun ℓ hℓ => Subtype.ext (LinearMap.ext hℓ))
  let iX : X ⟶ d'.induced := D.map f ≫ ed.hom
  let iY : Y ⟶ c'.induced := D.map f' ≫ ec.hom
  have hDex := generalLinearDerivativeExactness.{uF, max uF uV} F T ψ (M + 1) k hk.2
  have hiX : Function.Injective (SmoothRep.hom iX) :=
    (LevelCalculus.iso_hom_injective ed).comp (LevelCalculus.map_injective_of_exact hDex f hf)
  have hiY : Function.Injective (SmoothRep.hom iY) :=
    (LevelCalculus.iso_hom_injective ec).comp (LevelCalculus.map_injective_of_exact hDex f' hf')
  have hYfin := Aubert.ZelevinskyHighestDerivative.hasFiniteLength_of_injective iY hiY
    (Aubert.SegmentProductClass.hasFiniteLength_induced F T c' hsc')
  have hadm : Y.IsAdmissible := SmoothRep.isAdmissible_of_finiteLength_of_irreducible
    (fun A hA => (CuspidalSupport.cuspidalEmbedding F T _ A hA).1) Y hYfin
  have hG := compactOpen_cofinal F T (M + 1 - k)
  obtain ⟨e⟩ := dualIso_of_pairings hG (X := X) (Y := Y) hYfin hadm γ₁ h₁ γ₂ h₂
  -- A nonzero proper quotient would lose the chain on `d'` but retain it on `c'`.
  change X.representation.IsIrreducible
  have hbot : (⊥ : Subrepresentation X.representation) ≠ ⊤ := by
    obtain ⟨x, hx⟩ := exists_ne (0 : X)
    intro h
    have hmem : x ∈ (⊤ : Subrepresentation X.representation) := Submodule.mem_top
    rw [← h] at hmem
    exact hx ((Submodule.mem_bot ℂ).mp hmem)
  refine { exists_pair_ne := ⟨⊥, ⊤, hbot⟩, eq_bot_or_eq_top := ?_ }
  intro S
  by_contra! hS
  let V := X.subrepresentation S
  let W := X.quotient S
  let i := X.subtype S
  let q := X.mkQ S
  have hseq : LevelCalculus.IsShortExact i q := by
    refine ⟨SmoothRep.subtype_injective X S, SmoothRep.mkQ_surjective X S, ?_⟩
    change LinearMap.range S.toSubmodule.subtype = LinearMap.ker S.toSubmodule.mkQ
    rw [Submodule.range_subtype, Submodule.ker_mkQ]
  have hV : Nontrivial V := by
    by_contra! h
    apply hS.1
    apply Subrepresentation.toSubmodule_injective
    apply eq_bot_iff.mpr
    intro v hv
    let : Subsingleton S.toSubmodule := h
    exact (Submodule.mem_bot ℂ).mpr
      (congrArg Subtype.val (Subsingleton.elim (⟨v, hv⟩ : S.toSubmodule) 0))
  have hW : Nontrivial W := by
    by_contra! h
    exact hS.2 (Subrepresentation.toSubmodule_injective (Submodule.Quotient.subsingleton_iff.mp h))
  have hfail := not_derivativeChain_of_quotient.{uF, uV} F T ψ _ d' hod' hsd' iX hiX i q hseq hV
  let aW : W.contragredient ⟶ c'.induced := SmoothRep.contragredientHom q ≫ e.inv ≫ iY
  have haW : Function.Injective (SmoothRep.hom aW) :=
    (hiY.comp (LevelCalculus.iso_hom_injective e.symm)).comp
      (contragredientMap_injective_of_surjective (SmoothRep.hom q) hseq.surjective)
  have hWdual : Nontrivial W.contragredient := by
    obtain ⟨w, hw⟩ := exists_ne (0 : W)
    obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : W.contragredient, ℓ.val w ≠ 0 := by
      by_contra! h
      exact hw (eq_zero_of_forall_smoothDual hG W w h)
    exact ⟨ℓ, 0, fun h => hℓ (congrArg (fun l : W.contragredient => l.val w) h)⟩
  let γW : InvariantBilinear.forms W.contragredient.representation W.representation (fun _ => (1 : ℂ)) :=
    ⟨smoothDualPairing W.representation, fun g ℓ w => by
      change smoothDualPairing W.representation (smoothContragredient W.representation g ℓ)
          (W.representation g w) = 1 * smoothDualPairing W.representation ℓ w
      rw [one_mul, smoothDualPairing_invariant]⟩
  have hkeep := derivativeChain_of_pairing.{uF, uV} F T ψ _ c' hoc' hsc' aW haW hWdual γW
    (fun ℓ hℓ => Subtype.ext (LinearMap.ext hℓ))
  rw [htail] at hkeep
  exact hfail hkeep

end Langlands.Derivative
