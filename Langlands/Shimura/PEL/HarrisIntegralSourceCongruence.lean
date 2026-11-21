import Langlands.Shimura.PEL.HarrisIntegralSourceLevels

/-! # Principal congruence on the actual integral Harris source -/

noncomputable section

open scoped TensorProduct

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.Shimura.PEL.HarrisPolarizedWeilLevel

open NumberField _root_.Algebra

variable {E F A : Type}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field F] [NumberField F] [IsTotallyComplex F]
  [Algebra E F] [IsQuadraticExtension E F]
  [Ring A] [Algebra E A] [Algebra F A] [IsScalarTower E F A]
  [Algebra ℚ A] [IsScalarTower ℚ E A]
  {n : ℕ} (D : CentralSimpleUnitaryData E F A n)
  {Φ : (E →+* ℝ) → (F →+* ℂ)}
  (C : HarrisSignatureCharts D.toSecondKindInvolution n Φ)

local notation "Af" => Global.FiniteAdeles ℚ
local notation "Rf" => Global.integralFiniteAdeles ℚ
local notation "Vf" => Af ⊗[ℚ] A
local notation "L" => D.harrisHodgePELIntegralLattice C
local notation "Λf" => D.harrisHodgePELIntegralAdeleSpan C
local notation "G" => ScalarExtensionSimilitudePoints A A Af (D.harrisHodgePELForm C)
local notation "Stab" => (harrisIntegralAdeleStabilizer D C : Subgroup G)
local notation "op" => ScalarExtensionSimilitudePoints.operator

local instance : Module Rf Vf := Module.compHom _ (Rf).subtype
local instance : TopologicalSpace Vf := moduleTopology Af Vf

/-- The submodule of `m`-multiples in the actual source span. -/
def harrisIntegralSourceMultiples (m : ℕ) : Submodule Rf Λf :=
  LinearMap.range ((m : Rf) • (LinearMap.id : Λf →ₗ[Rf] Λf))

local notation "multiples" => harrisIntegralSourceMultiples D C

/-- The actual integral source span modulo its `m`-multiples. -/
abbrev HarrisIntegralSourceMod (m : ℕ) := Λf ⧸ multiples m

/-- The source stabilizer acts on the integral source span by its actual operators. -/
def harrisIntegralSourceOperator (g : Stab) : Λf →ₗ[Rf] Λf where
  toFun x := ⟨op g.val (x : Vf), (g.property _).mpr x.property⟩
  map_add' x y := Subtype.ext (map_add (op g.val) (x : Vf) (y : Vf))
  map_smul' r x := Subtype.ext (map_smul (op g.val) (r : Af) (x : Vf))

local notation "integralOp" => harrisIntegralSourceOperator D C

private theorem integralOp_preserves_multiples (m : ℕ) (g : Stab) :
    multiples m ≤ (multiples m).comap (integralOp g) := by
  rintro x ⟨y, rfl⟩
  exact ⟨integralOp g y, (map_smul (integralOp g) (m : Rf) y).symm⟩

/-- Reduction of the source stabilizer action on the actual source quotient. -/
def harrisIntegralSourceReduction (m : ℕ) : Stab →* Module.End Rf (HarrisIntegralSourceMod D C m) where
  toFun g := (multiples m).mapQ (multiples m) (integralOp g)
    (integralOp_preserves_multiples D C m g)
  map_one' := by
    apply LinearMap.ext
    intro x
    obtain ⟨v, rfl⟩ := (multiples m).mkQ_surjective x
    rfl
  map_mul' g k := by
    apply LinearMap.ext
    intro x
    obtain ⟨v, rfl⟩ := (multiples m).mkQ_surjective x
    rfl

/-- The principal congruence subgroup in the actual adelic similitude group. -/
def harrisIntegralAdeleCongruence (m : ℕ) : Subgroup G :=
  (harrisIntegralSourceReduction D C m).ker.map (Stab).subtype

local notation "K" => harrisIntegralAdeleCongruence D C

/-- The congruence subgroup consists of source stabilizers acting as the identity on
`Λf / mΛf`, expressed as an ambient difference in the image of multiplication by `m`. -/
theorem mem_harrisIntegralAdeleCongruence (m : ℕ) (g : G) :
    g ∈ K m ↔ g ∈ Stab ∧
      ∀ v : Vf, v ∈ Λf → op g v - v ∈ (fun w : Vf => m • w) '' (Λf : Set Vf) := by
  rw [harrisIntegralAdeleCongruence, Subgroup.mem_map]
  constructor
  · rintro ⟨g', hg', rfl⟩
    refine ⟨g'.property, fun v hv => ?_⟩
    let x : Λf := ⟨v, hv⟩
    have eq : (multiples m).mkQ (integralOp g' x) = (multiples m).mkQ x :=
      DFunLike.congr_fun (show harrisIntegralSourceReduction D C m g' = 1 from hg')
        ((multiples m).mkQ x)
    have hx : integralOp g' x - x ∈ multiples m := (Submodule.Quotient.eq _).mp eq
    obtain ⟨y, hy⟩ := hx
    refine ⟨y, y.property, ?_⟩
    have hy' := congrArg Subtype.val hy
    change (m : Rf) • (y : Vf) = op g'.val v - v at hy'
    change m • (y : Vf) = op g'.val v - v
    simpa only [Nat.cast_smul_eq_nsmul] using hy'
  · rintro ⟨hg, h⟩
    let g' : Stab := ⟨g, hg⟩
    refine ⟨g', ?_, rfl⟩
    change harrisIntegralSourceReduction D C m g' = 1
    apply LinearMap.ext
    intro y
    obtain ⟨x, rfl⟩ := (multiples m).mkQ_surjective y
    change (multiples m).mkQ (integralOp g' x) = (multiples m).mkQ x
    apply (Submodule.Quotient.eq _).mpr
    obtain ⟨w, hw, he⟩ := h x x.property
    refine ⟨⟨w, hw⟩, Subtype.ext ?_⟩
    change (m : Rf) • w = op g (x : Vf) - (x : Vf)
    simpa only [Nat.cast_smul_eq_nsmul] using he

private def sourceGenerator (i : Fin (Module.finrank ℤ L)) : Vf :=
  (1 : Af) ⊗ₜ[ℚ] ((Module.finBasis ℤ L i : L) : A)

private theorem sourceSpan_eq_span : Λf = Submodule.span Rf (Set.range (sourceGenerator D C)) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    rw [← (Module.finBasis ℤ L).sum_repr x]
    simp only [Submodule.coe_sum, Submodule.coe_smul, TensorProduct.tmul_sum,
      TensorProduct.tmul_smul]
    apply Submodule.sum_mem
    intro i _
    exact (Submodule.span Rf (Set.range (sourceGenerator D C))).toAddSubgroup.zsmul_mem
      (Submodule.subset_span ⟨i, rfl⟩) _
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact D.harrisHodgePELIntegralAdeleSpan_tmul C (Module.finBasis ℤ L i)

private theorem mulSourceImage_isOpen (m : ℕ) (hm : m ≠ 0) :
    IsOpen ((fun w : Vf => m • w) '' (Λf : Set Vf)) := by
  let : ContinuousSMul Af Vf := IsModuleTopology.toContinuousSMul Af Vf
  let u : Afˣ := Units.map (algebraMap ℚ Af).toMonoidHom
    (Units.mk0 (m : ℚ) (Nat.cast_ne_zero.mpr hm))
  have hu (w : Vf) : u • w = m • w := by
    change (algebraMap ℚ Af (m : ℚ)) • w = m • w
    rw [map_natCast, Nat.cast_smul_eq_nsmul]
  have h := (Homeomorph.smul u).isOpenMap _ (harrisHodgePELIntegralAdeleSpan_isOpen D C)
  change IsOpen ((fun w : Vf => u • w) '' (Λf : Set Vf)) at h
  simpa only [hu] using h

private theorem congruence_iff_generators (m : ℕ) (g : G) : g ∈ K m ↔
    g ∈ Stab ∧ ∀ i, op g (sourceGenerator D C i) - sourceGenerator D C i ∈
      (fun w : Vf => m • w) '' (Λf : Set Vf) := by
  rw [mem_harrisIntegralAdeleCongruence]
  constructor
  · rintro ⟨hg, h⟩
    exact ⟨hg, fun i => h _ (D.harrisHodgePELIntegralAdeleSpan_tmul C (Module.finBasis ℤ L i))⟩
  · rintro ⟨hg, h⟩
    refine ⟨hg, ?_⟩
    let f : Vf →ₗ[Rf] Vf :=
      ((op g).toLinearMap - LinearMap.id).restrictScalars Rf
    let M : Submodule Rf Vf := (Λf).map ((m : Rf) • (LinearMap.id : Vf →ₗ[Rf] Vf))
    have hM : (M : Set Vf) = (fun w : Vf => m • w) '' (Λf : Set Vf) := by
      ext v
      change (∃ w ∈ Λf, (m : Rf) • w = v) ↔ (∃ w ∈ Λf, m • w = v)
      simp only [Nat.cast_smul_eq_nsmul]
    intro v hv
    rw [← hM]
    change v ∈ M.comap f
    have hsub : Λf ≤ M.comap f := by
      rw [sourceSpan_eq_span D C, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      change (op g (sourceGenerator D C i) - sourceGenerator D C i) ∈ (M : Set Vf)
      rw [hM]
      exact h i
    exact hsub hv

/-- The congruence condition can be imposed inside the actual open source stabilizer. -/
theorem harrisIntegralAdeleCongruence_isOpen (m : ℕ) (hm : m ≠ 0) :
    IsOpen ((K m : Subgroup G) : Set G) := by
  let : IsTopologicalAddGroup Vf := IsModuleTopology.isTopologicalAddGroup Af Vf
  have heq : ((K m : Subgroup G) : Set G) = {g : G | g ∈ Stab} ∩
      ⋂ i, {g : G | op g (sourceGenerator D C i) - sourceGenerator D C i ∈
        (fun w : Vf => m • w) '' (Λf : Set Vf)} := by
    ext g
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq, SetLike.mem_coe]
    exact congruence_iff_generators D C m g
  rw [heq]
  apply (harrisIntegralAdeleStabilizer_isOpen D C).inter
  apply isOpen_iInter_of_finite
  intro i
  exact (mulSourceImage_isOpen D C m hm).preimage
    ((ScalarExtensionSimilitudePoints.continuous_apply _).sub continuous_const)

/-- Positive integral radii give actual open subgroups in Hodge coordinates. -/
def harrisIntegralAdeleOpenCongruence (m : ℕ) (hm : m ≠ 0) : OpenSubgroup G where
  toSubgroup := K m
  isOpen' := harrisIntegralAdeleCongruence_isOpen D C m hm

/-- The principal congruence subgroup always lies inside the source stabilizer. -/
theorem harrisIntegralAdeleCongruence_le (m : ℕ) : K m ≤ Stab :=
  fun g hg => ((mem_harrisIntegralAdeleCongruence D C m g).mp hg).1

/-- The congruence subgroup is normal inside the integral source stabilizer. -/
theorem harrisIntegralAdeleCongruence_normal (m : ℕ) : ((K m).subgroupOf Stab).Normal := by
  change (((harrisIntegralSourceReduction D C m).ker.map (Stab).subtype).comap
    (Stab).subtype).Normal
  rw [Subgroup.comap_map_eq_self_of_injective (Stab).subtype_injective]
  infer_instance

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
