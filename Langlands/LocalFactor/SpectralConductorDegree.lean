import Langlands.LocalFactor.SpectralConductorInduction
import Langlands.LocalFactor.SpectralConductorEpsilon
import Mathlib.Data.ZMod.QuotientGroup
import Langlands.LocalField.Uniformizer
import Langlands.LocalField.CanonicalTransport

/-!
# The residue degree of an intermediate field in the induction identity

The factor `[W_F : W_L] |I(M/L)| / |I(M/F)|` of the induction identity is the
degree of a Weil element of `L` whose reciprocity image is a uniformizer, and
the normalization of the supplied reciprocity family gives
`log q_L = f log q_F` for that degree `f`.
-/

noncomputable section

namespace Langlands.LocalFactor.SpectralConductor

section Group

variable {G : Type*} [Group G]

/-- The second isomorphism theorem for indices, with the normal subgroup on the
right: `[H N : H] = [N : H ∩ N]`. -/
theorem relIndex_sup_normal (H N : Subgroup G) [hN : N.Normal] :
    H.relIndex (H ⊔ N) = H.relIndex N := by
  symm
  let i : N →* (H ⊔ N : Subgroup G) := Subgroup.inclusion le_sup_right
  have key : ∀ x y : N, QuotientGroup.leftRel (H.subgroupOf N) x y ↔
      QuotientGroup.leftRel (H.subgroupOf (H ⊔ N)) (i x) (i y) := by
    intro x y
    simp only [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf]
    rfl
  unfold Subgroup.relIndex Subgroup.index
  refine Nat.card_congr (Equiv.ofBijective (Quotient.map' i fun x y => (key x y).mp) ⟨?_, ?_⟩)
  · simp_rw [← Quotient.eq''] at key
    refine Quotient.ind' fun x => ?_
    refine Quotient.ind' fun y => ?_
    exact (key x y).mpr
  · refine Quotient.ind' fun k => ?_
    have hk : (k : G) ∈ N ⊔ H := by
      rw [sup_comm]
      exact k.2
    obtain ⟨z, hz, y, hy, hzy⟩ := (Subgroup.mem_sup_of_normal_left (s := N) (t := H)).mp hk
    refine ⟨Quotient.mk'' ⟨z, hz⟩, ?_⟩
    change Quotient.mk'' (i ⟨z, hz⟩) = Quotient.mk'' k
    rw [Quotient.eq'', QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf]
    change (z⁻¹ * (k : G)) ∈ H
    rw [← hzy, inv_mul_cancel_left]
    exact hy

end Group

section Normalization

universe uF

open CommonClosure CommonClosureSpectral CommonClosureSpectralAnalytic Weil.Local

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (e : ReciprocityFamily F)
  (L : Extension F)

/-- Geometric normalization at `L`: valuation of the reciprocity image against
the base degree. -/
theorem ord_mul_log (he : NormalizedReciprocity F e) (w : weilSubgroup F L) :
    ((fieldData F L).ord (reciprocityUnits F e L w : L.field) : ℝ) *
        Real.log ((fieldData F L).residueCardinality : ℝ) =
      ((localDegree F w.val).toAdd : ℝ) * Real.log (baseCardinality F) := by
  let := (fieldData F L).topology
  have hn : (fieldData F L).normalizedAbs (reciprocityUnits F e L w : L.field) =
      baseCardinality F ^ (-(localDegree F w.val).toAdd) :=
    he.2 L (LocalClassField.abelianizationProjection (weilSubgroup F L) w)
  rw [(fieldData F L).normalizedAbs_of_ne_zero (Units.ne_zero _)] at hn
  have h := congrArg Real.log hn
  rw [Real.log_zpow, Real.log_zpow] at h
  push_cast at h
  linarith

/-- A Weil element of `L` whose reciprocity image is the chosen uniformizer. -/
def uniformizerWeil : weilSubgroup F L :=
  letI := (fieldData F L).topology
  Classical.choose (CommonClosure.reciprocityUnits_surjective F e L
    (PadicAbelian.uniformizerUnit (fieldData F L)))

theorem reciprocityUnits_uniformizerWeil :
    letI := (fieldData F L).topology
    reciprocityUnits F e L (uniformizerWeil e L) =
      PadicAbelian.uniformizerUnit (fieldData F L) :=
  letI := (fieldData F L).topology
  Classical.choose_spec (CommonClosure.reciprocityUnits_surjective F e L
    (PadicAbelian.uniformizerUnit (fieldData F L)))

/-- The base degree of that element: the residue degree of `L` over `F`. -/
def residueDegreeL : ℤ := (localDegree F (uniformizerWeil e L).val).toAdd

theorem log_residueCardinality (he : NormalizedReciprocity F e) :
    Real.log ((fieldData F L).residueCardinality : ℝ) =
      (residueDegreeL e L : ℝ) * Real.log (baseCardinality F) := by
  have h := ord_mul_log e L he (uniformizerWeil e L)
  rw [reciprocityUnits_uniformizerWeil, PadicAbelian.uniformizerUnit_ord] at h
  simpa [residueDegreeL] using h

theorem log_baseCardinality_pos : 0 < Real.log (baseCardinality F) := by
  apply Real.log_pos
  change (1 : ℝ) < (F.canonicalTopologicalData.residueCardinality : ℝ)
  exact_mod_cast F.canonicalTopologicalData.residueCardinality_gt_one

theorem residueDegreeL_pos (he : NormalizedReciprocity F e) : 0 < residueDegreeL e L := by
  have h := log_residueCardinality e L he
  have hL : 0 < Real.log ((fieldData F L).residueCardinality : ℝ) := by
    apply Real.log_pos
    exact_mod_cast (fieldData F L).residueCardinality_gt_one
  have hF := log_baseCardinality_pos (F := F)
  have : (0 : ℝ) < residueDegreeL e L := by
    by_contra hc
    push Not at hc
    nlinarith
  exact_mod_cast this

theorem degree_eq_ord_mul (he : NormalizedReciprocity F e) (w : weilSubgroup F L) :
    (localDegree F w.val).toAdd =
      (fieldData F L).ord (reciprocityUnits F e L w : L.field) * residueDegreeL e L := by
  have h := ord_mul_log e L he w
  rw [log_residueCardinality e L he] at h
  have hF := log_baseCardinality_pos (F := F)
  have h2 : ((localDegree F w.val).toAdd : ℝ) * Real.log (baseCardinality F) =
      (((fieldData F L).ord (reciprocityUnits F e L w : L.field) : ℝ) * residueDegreeL e L) *
        Real.log (baseCardinality F) := by
    rw [← h]
    ring
  have h3 := mul_right_cancel₀ hF.ne' h2
  exact_mod_cast h3

end Normalization

section Index

universe uF

open CommonClosure CommonClosureSpectral CommonClosureSpectralAnalytic Weil.Local
open ConductorExponent Ramification.Padic

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (e : ReciprocityFamily F)
  (L : Extension F)

/-- The base degrees of `W_L` are the multiples of the residue degree. -/
theorem map_degree_weilSubgroup (he : NormalizedReciprocity F e) :
    (weilSubgroup F L).map (localDegree F).toMonoidHom =
      AddSubgroup.toSubgroup (AddSubgroup.zmultiples (residueDegreeL e L)) := by
  ext x
  change _ ↔ Multiplicative.toAdd x ∈ AddSubgroup.zmultiples (residueDegreeL e L)
  rw [AddSubgroup.mem_zmultiples_iff]
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨(fieldData F L).ord (reciprocityUnits F e L ⟨w, hw⟩ : L.field), ?_⟩
    rw [smul_eq_mul]
    exact (degree_eq_ord_mul e L he ⟨w, hw⟩).symm
  · rintro ⟨k, hk⟩
    refine ⟨((uniformizerWeil e L : weilSubgroup F L) : localWeilGroup F) ^ k,
      (weilSubgroup F L).zpow_mem (uniformizerWeil e L).2 k, ?_⟩
    apply Multiplicative.toAdd.injective
    change Multiplicative.toAdd ((localDegree F) (((uniformizerWeil e L : weilSubgroup F L) :
      localWeilGroup F) ^ k)) = _
    rw [map_zpow, toAdd_zpow, ← hk, smul_eq_mul, smul_eq_mul, residueDegreeL]

theorem index_sup_localInertia (he : NormalizedReciprocity F e) :
    (weilSubgroup F L ⊔ localInertia F).index = (residueDegreeL e L).natAbs := by
  have hker : localInertia F = (localDegree F).toMonoidHom.ker := rfl
  rw [hker, ← Subgroup.comap_map_eq,
    Subgroup.index_comap_of_surjective _ (localDegree_surjective F),
    map_degree_weilSubgroup e L he, AddSubgroup.index_toSubgroup, Int.index_zmultiples]

theorem index_weilSubgroup (he : NormalizedReciprocity F e) :
    (weilSubgroup F L).index =
      (weilSubgroup F L).relIndex (localInertia F) * (residueDegreeL e L).natAbs := by
  rw [← Subgroup.relIndex_mul_index (le_sup_left : weilSubgroup F L ≤ _ ⊔ localInertia F),
    relIndex_sup_normal, index_sup_localInertia e L he]

variable (M : FiniteGaloisIntermediateField F.Carrier (AlgebraicClosure F.Carrier))
  (hLM : L.field ≤ M.toIntermediateField)

include hLM in
theorem relIndex_localInertia :
    (weilSubgroup F L).relIndex (localInertia F) =
      ((fixingM F M L).subgroupOf (inertiaM F M)).index := by
  have h : (weilSubgroup F L).subgroupOf (localInertia F) =
      ((fixingM F M L).subgroupOf (inertiaM F M)).comap
        (weilInertiaRestriction F M).toMonoidHom := by
    ext s
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_subgroupOf,
      mem_weilSubgroup_iff F M L hLM]
    rfl
  rw [Subgroup.relIndex, h,
    Subgroup.index_comap_of_surjective _
      (Ramification.HerbrandBridge.weilInertiaRestriction_surjective F M)]

theorem card_inertiaL_mul_index :
    Nat.card (inertiaL F M L) * ((fixingM F M L).subgroupOf (inertiaM F M)).index =
      Nat.card (inertiaM F M) := by
  rw [← Subgroup.card_mul_index ((fixingM F M L).subgroupOf (inertiaM F M))]
  congr 1
  apply Nat.card_congr
  exact
  { toFun := fun x => ⟨⟨x.1, x.2.2⟩, x.2.1⟩
    invFun := fun y => ⟨y.1.1, y.2, y.1.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

omit M hLM in
theorem card_cosets_nestedL :
    Fintype.card (FiniteRepresentation.Induction.Cosets (nestedL F L)) =
      (weilSubgroup F L).index := by
  rw [Fintype.card_eq_nat_card,
    Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel _)]
  change (weilSubgroup F L).relIndex (weilSubgroup F (base F)) = _
  have htop : weilSubgroup F (base F) = ⊤ :=
    eq_top_iff.mpr fun w _ => mem_weilSubgroup_base F w
  rw [htop, Subgroup.relIndex_top_right]

omit e L in
/-- The bottom field has the residue cardinality of `F`. -/
theorem residueCardinality_base :
    (fieldData F (base F)).residueCardinality = F.canonicalTopologicalData.residueCardinality := by
  let _ := ((base F).asPadicField (p := p)).algebra
  exact PadicField.CanonicalTransport.residueCardinality_eq F _
    (AlgEquiv.ofRingEquiv
      (f := (IntermediateField.botEquiv F.Carrier (AlgebraicClosure F.Carrier)).symm.toRingEquiv)
      (fun x => (IntermediateField.botEquiv F.Carrier (AlgebraicClosure F.Carrier)).symm.commutes
        (algebraMap (Padic p) F.Carrier x)))

include hLM in
/-- The factor of the induction identity times `log q_F` is `log q_L`. -/
theorem inductionFactor_mul_logCardinality (he : NormalizedReciprocity F e) :
    (Fintype.card (FiniteRepresentation.Induction.Cosets (nestedL F L)) : ℂ) *
        (Nat.card (inertiaL F M L) : ℂ) / (Nat.card (inertiaM F M) : ℂ) *
        logCardinality (base F) = logCardinality L := by
  have h4 := card_inertiaL_mul_index L M
  have hpos := residueDegreeL_pos e L he
  have hG0 : (Nat.card (inertiaM F M) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := inertiaM F M)).ne'
  have hnat : ((residueDegreeL e L).natAbs : ℂ) = (residueDegreeL e L : ℂ) := by
    have h := Int.natAbs_of_nonneg hpos.le
    have h' := congrArg (fun z : ℤ => (z : ℂ)) h
    simpa using h'
  rw [card_cosets_nestedL, index_weilSubgroup e L he, relIndex_localInertia L M hLM]
  unfold logCardinality
  rw [residueCardinality_base, log_residueCardinality e L he]
  have h4' : (Nat.card (inertiaL F M L) : ℂ) *
      (((fixingM F M L).subgroupOf (inertiaM F M)).index : ℂ) = Nat.card (inertiaM F M) := by
    exact_mod_cast h4
  push_cast
  rw [hnat]
  field_simp
  rw [← h4']
  have hb : ((Real.log (baseCardinality F) : ℝ) : ℂ) =
      Complex.log (F.canonicalTopologicalData.residueCardinality : ℂ) := by
    change ((Real.log (F.canonicalTopologicalData.residueCardinality : ℝ) : ℝ) : ℂ) = _
    rw [Complex.ofReal_log (Nat.cast_nonneg _), Complex.ofReal_natCast]
  rw [hb]
  ring

end Index

end Langlands.LocalFactor.SpectralConductor
