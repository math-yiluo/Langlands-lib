import Langlands.Global.AdelicAdjunctionIwasawaMeasure
import Langlands.Global.AdelicIntertwiningLeftInvariance
import Langlands.Global.AdelicIntertwiningRadicalIntersection
import Langlands.Global.AdelicIntertwiningAdjunctionReduction

/-! # The common quotient of the two intertwining pairings -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Topology Set
open scoped CategoryTheory.MonObj CompactlySupported

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions
open EisensteinConstantTerm ParabolicIwasawaMeasure

variable {F : Type} [Field F] [NumberField F]
  {G P U M Q V M' : GroupScheme (Spec (CommRingCat.of F))}
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom] [IsAffine U.X.left]
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
  [IsAffine Q.X.left] [LocallyOfFiniteType Q.X.hom] [IsAffine V.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
  [IsClosedImmersion (iU ≫ p).hom.hom.left]
  {q : Q ⟶ G} [IsClosedImmersion q.hom.hom.left] (iV : V ⟶ Q) (l' : M' ⟶ Q)
  [IsClosedImmersion (iV ≫ q).hom.hom.left]
  {a : A.toGrp ⟶ M} (r : ParabolicRootPresentation p l a)
  (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) {c : M' ⟶ M}
  (hw : IsWeylConjugation p l q l' w c)

local notation "Gₐ" => (AdelicGroupPoints F G)
local notation "wA" => (innerAdelicPoint F G w)
local notation "Uq" => (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV ≫ q)))
local notation "Prange" => (MonoidHom.range (ContinuousMonoidHom.toMonoidHom (map F P G p)))
local notation "Qrange" => (MonoidHom.range (ContinuousMonoidHom.toMonoidHom (map F Q G q)))

/-- The principal subgroup in the intersection of the target parabolic with the conjugate of
 the source parabolic. -/
def adjunctionRationalSubgroup (W : Gₐ) : Subgroup Gₐ :=
  rationalSubgroup F G ⊓ (Qrange ⊓ Subgroup.comap (MulAut.conj W⁻¹).toMonoidHom Prange)

theorem mem_adjunctionRationalSubgroup_iff (W g : Gₐ) :
    g ∈ adjunctionRationalSubgroup (p := p) (q := q) W ↔
      g ∈ rationalSubgroup F G ∧ g ∈ Qrange ∧ W⁻¹ * g * W ∈ Prange := by
  simp [adjunctionRationalSubgroup]

/-- A rational point in the adelic radical image lies in its principal subgroup. -/
theorem mem_adelicRadical_rational_iff (u : Uq) :
    u ∈ AdelicSubgroupPoints.rationalSubgroup F G (SubgroupFunctor.range (iV ≫ q)) ↔
      u.val ∈ rationalSubgroup F G := by
  rw [mem_rationalSubgroup_range_iff]
  constructor
  · exact fun h => rationalImage_le_rationalSubgroup (iV ≫ q) h
  · rintro ⟨d, hd⟩
    have hv : rational F G d ∈ Uq := hd.symm ▸ u.property
    obtain ⟨z, hz⟩ := (rational_mem_adelicPoints_range_iff
      (inferInstance : IsClosedImmersion (iV ≫ q).hom.hom.left) d).mp hv
    exact ⟨z, (map_rational (iV ≫ q) (show RationalGroupPoints F V from z)).trans
      ((congrArg (rational F G) hz).trans hd)⟩

private theorem range_radical_le_parabolic (u : Uq) : u.val ∈ Qrange := by
  obtain ⟨x, hx⟩ := u.property
  exact ⟨map F V Q iV x, (map_comp_apply_of_hom iV _).symm.trans hx⟩

include hw r in
/-- The intersection cuts out exactly the rational subgroup of the intertwining radical. -/
theorem mem_intertwiningRationalSubgroup_iff_adjunction (hG : IsConnectedReductive G)
    (hU : LeviSubgroup.IsGeometricUnipotentRadical iU)
    (hq : IsParabolicSubgroup q) (hV : LeviSubgroup.IsGeometricUnipotentRadical iV)
    (hmul : IsIso (subgroupMultiplication l' iV)) (u : Uq) :
    u ∈ intertwiningRationalSubgroup F p iU (iV ≫ q) wA ↔
      u.val ∈ adjunctionRationalSubgroup (p := p) (q := q) wA := by
  rw [mem_intertwiningRationalSubgroup_iff, mem_adelicRadical_rational_iff,
    mem_adjunctionRationalSubgroup_iff, and_iff_right (range_radical_le_parabolic iV u), and_congr_right_iff]
  intro _
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨map F U P iU z, (map_comp_apply_of_hom iU _).symm.trans hz⟩
  · exact conj_mem_parabolicUnipotentImage r w hG hU hq hV hmul hw u.property

include hw in
/-- The principal target Levi is contained in the common subgroup. -/
theorem map_levi_mem_adjunctionRationalSubgroup (m : AdelicGroupPoints F M')
    (hm : m ∈ rationalSubgroup F M') :
    map F Q G q (map F M' Q l' m) ∈ adjunctionRationalSubgroup (p := p) (q := q) wA := by
  rw [mem_adjunctionRationalSubgroup_iff, ← hw.adelic_comp_eq]
  refine ⟨?_, ⟨_, rfl⟩, ⟨_, rfl⟩⟩
  obtain ⟨d, rfl⟩ := hm
  rw [map_rational, map_rational]
  exact ⟨_, rfl⟩

/-- A principal point in a parabolic lies in `U(𝔸) M(F)`. -/
theorem mem_parabolicQuotientSubgroup_of_rational_range [IsIso (subgroupMultiplication l iU)]
    (hU : LeviSubgroup.IsGeometricUnipotentRadical iU) {g : Gₐ}
    (hr : g ∈ rationalSubgroup F G) (hpr : g ∈ Prange) :
    g ∈ parabolicQuotientSubgroup F p iU l := by
  obtain ⟨x, rfl⟩ := hpr
  obtain ⟨⟨u, m⟩, rfl⟩ := (coordinates p iU l hU).surjective x
  have hx := mem_rationalSubgroup_of_map p _ hr
  have hm := proj_mem_rationalSubgroup iU l hU hx
  rw [proj_coordinates] at hm
  change (map F P G p).toMonoidHom (coordinates p iU l hU (u, m)) ∈ _
  rw [map_coordinates]
  apply Subgroup.mul_mem _ (Subgroup.mem_sup_left u.property)
  apply Subgroup.mem_sup_right
  obtain ⟨d, rfl⟩ := hm
  exact ⟨d, map_comp_apply_of_hom l _⟩

theorem innerPoint_inv : innerAdelicPoint F G w⁻¹ = wA⁻¹ := by
  simp only [innerAdelicPoint_eq_rational, ← map_inv]
  rfl

/-- Left translation by the inverse Weyl point takes the forward common quotient to the
reverse common quotient and preserves their counting-normalized measures. -/
theorem exists_measurePreserving_adjunctionTranslate :
    let Γ := adjunctionRationalSubgroup (p := p) (q := q) wA
    let Γ' := adjunctionRationalSubgroup (p := q) (q := p) (innerAdelicPoint F G w⁻¹)
    let hΓ : IsDiscrete (Γ : Set Gₐ) := (isDiscrete_rationalSubgroup F G).mono inf_le_left
    let hΓ' : IsDiscrete (Γ' : Set Gₐ) := (isDiscrete_rationalSubgroup F G).mono inf_le_left
    ∃ e : LeftCosetSpace Γ ≃ᵐ LeftCosetSpace Γ',
      (∀ g, e (LeftCosetSpace.mk Γ g) = LeftCosetSpace.mk Γ' (wA⁻¹ * g)) ∧
      MeasurePreserving e (LeftCosetSpace.discreteQuotientMeasure Γ hΓ Measure.haar)
        (LeftCosetSpace.discreteQuotientMeasure Γ' hΓ' Measure.haar) := by
  intro Γ Γ' hΓ hΓ'
  let s : Gₐ ≃ₜ Gₐ := Homeomorph.mulLeft wA⁻¹
  let α := MulAut.conj wA⁻¹
  have hwR : wA ∈ rationalSubgroup F G := ⟨_, (innerAdelicPoint_eq_rational F G w).symm⟩
  have hαval (x : Gₐ) : α x = wA⁻¹ * x * wA := by simp [α]
  have hα (x : Gₐ) : α x ∈ Γ' ↔ x ∈ Γ := by
    rw [hαval]
    change wA⁻¹ * x * wA ∈ adjunctionRationalSubgroup (p := q) (q := p) (innerAdelicPoint F G w⁻¹) ↔
      x ∈ adjunctionRationalSubgroup (p := p) (q := q) wA
    rw [innerPoint_inv, mem_adjunctionRationalSubgroup_iff, mem_adjunctionRationalSubgroup_iff,
      inv_inv, show wA * (wA⁻¹ * x * wA) * wA⁻¹ = x by group]
    have hR : wA⁻¹ * x * wA ∈ rationalSubgroup F G ↔ x ∈ rationalSubgroup F G := by
      constructor
      · intro h
        have h' := mul_mem (mul_mem hwR h) (inv_mem hwR)
        simpa only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_right, mul_inv_cancel_left] using h'
      · exact fun hx => mul_mem (mul_mem (inv_mem hwR) hx) hwR
    rw [hR, and_comm (a := _ ∈ Prange)]
  let eΓ : Γ ≃ Γ' := (Equiv.ofBijective (fun x : Γ => (⟨α x.val, (hα x.val).2 x.property⟩ : Γ'))
    ⟨fun x y h => Subtype.ext (α.injective (congrArg Subtype.val h)), fun x =>
      ⟨⟨α.symm x.val, (hα _).1 (by simp only [MulEquiv.apply_symm_apply]; exact x.property)⟩,
        Subtype.ext (α.apply_symm_apply _)⟩⟩)
  have hr (x y : Gₐ) : (QuotientGroup.rightRel Γ) x y ↔ (QuotientGroup.rightRel Γ') (s x) (s y) := by
    rw [QuotientGroup.rightRel_apply, QuotientGroup.rightRel_apply]
    change y * x⁻¹ ∈ Γ ↔ (wA⁻¹ * y) * (wA⁻¹ * x)⁻¹ ∈ Γ'
    rw [show (wA⁻¹ * y) * (wA⁻¹ * x)⁻¹ = α (y * x⁻¹) by rw [hαval]; group]
    exact (hα _).symm
  let e : LeftCosetSpace Γ ≃ᵐ LeftCosetSpace Γ' :=
    { toEquiv := (Homeomorph.Quotient.congr s hr).toEquiv
      measurable_toFun := measurable_from_quotient.mpr ((LeftCosetSpace.measurable_mk Γ').comp s.continuous.measurable)
      measurable_invFun := measurable_from_quotient.mpr ((LeftCosetSpace.measurable_mk Γ).comp s.symm.continuous.measurable) }
  let D := LeftCosetSpace.fundamentalDomain Γ hΓ
  have hD : MeasurableSet (s '' D) :=
    s.toMeasurableEquiv.measurableEmbedding.measurableSet_image' (LeftCosetSpace.measurableSet_fundamentalDomain Γ hΓ)
  have hs (d : Γ) (g : Gₐ) : s (d.val * g) = (eΓ d).val * s g := by
    change wA⁻¹ * (d.val * g) = α d.val * (wA⁻¹ * g)
    rw [hαval]
    group
  have huniq (g : Gₐ) : ∃! d : Γ', d.val * g ∈ s '' D := by
    obtain ⟨d, hd, hu⟩ := LeftCosetSpace.fundamentalDomain_unique Γ hΓ (s.symm g)
    have he (δ : Γ) : (eΓ δ).val * g ∈ s '' D ↔ δ.val * s.symm g ∈ D := by
      rw [← s.apply_symm_apply g, ← hs, s.injective.mem_set_image, s.symm_apply_apply]
    refine ⟨eΓ d, (he _).2 hd, ?_⟩
    intro δ hδ
    apply eΓ.symm.injective
    rw [eΓ.symm_apply_apply]
    exact hu _ ((he (eΓ.symm δ)).1 (by simpa only [Equiv.apply_symm_apply] using hδ))
  refine ⟨e, fun _ => rfl, ⟨e.measurable, ?_⟩⟩
  have hFD : IsFundamentalDomain Γ' (s '' D) (Measure.haar : Measure Gₐ) :=
    IsFundamentalDomain.mk' hD.nullMeasurableSet huniq
  have hS : MeasurePreserving s (Measure.haar : Measure Gₐ) Measure.haar :=
    measurePreserving_mul_left Measure.haar _
  ext T hT
  rw [Measure.map_apply e.measurable hT, LeftCosetSpace.discreteQuotientMeasure_eq _ _ _ hFD]
  change LeftCosetSpace.quotientMeasure Γ Measure.haar D (e ⁻¹' T) = _
  rw [LeftCosetSpace.quotientMeasure_apply _ _ _ (e.measurable hT),
    LeftCosetSpace.quotientMeasure_apply _ _ _ hT]
  conv_rhs => rw [← hS.map_eq]
  rw [Measure.map_apply hS.measurable (((LeftCosetSpace.measurable_mk Γ') hT).inter hD)]
  congr 1
  ext g
  simp only [mem_inter_iff, mem_preimage, s.injective.mem_set_image]
  rfl

end Langlands.Global.AdelicGroupPoints
