import Langlands.Shimura.PEL.HarrisIntegralSourceCongruence
import Langlands.Global.RationalProfiniteIntegerComparison

/-! # Ordered residues of the actual integral Harris source span -/

noncomputable section

open scoped TensorProduct BigOperators

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false

namespace Langlands.Shimura.PEL.HarrisPolarizedWeilLevel

open NumberField _root_.Algebra Langlands.Global

private theorem profiniteInteger_reduction_eq_zero_iff (m : ℕ+) (x : ProfiniteIntegerRing) :
    ProfiniteIntegerRing.reduction m x = 0 ↔
      ∃ y : ProfiniteIntegerRing, (m.val : ProfiniteIntegerRing) * y = x := by
  constructor
  · intro hx
    let a (n : ℕ+) := (ProfiniteIntegerRing.reduction n x).val
    let j (n : ℕ+) := m * n
    have hred {n k : ℕ+} (h : n.val ∣ k.val) : (a k : ZMod n.val) =
        ProfiniteIntegerRing.reduction n x := by
      have : NeZero k.val := ⟨k.property.ne'⟩
      calc
        _ = ResidueLimit.transition h (a k : ZMod k.val) := (map_natCast _ _).symm
        _ = _ := (congrArg (ResidueLimit.transition h) (ZMod.natCast_zmod_val
          (ProfiniteIntegerRing.reduction k x))).trans (ResidueLimit.compatible x n k h)
    have hd (n : ℕ+) : m.val ∣ a (j n) :=
      (ZMod.natCast_eq_zero_iff _ _).mp ((hred (dvd_mul_right m.val n.val)).trans hx)
    let y : ProfiniteIntegerRing := ⟨fun n => ((a (j n) / m.val : ℕ) : ZMod n.val), by
      intro n k hnk
      have he := congrArg ZMod.val (hred (n := j n) (k := j k) (Nat.mul_dvd_mul_left m.val hnk))
      rw [ZMod.val_natCast] at he
      change a (j k) % (m.val * n.val) = a (j n) at he
      change ResidueLimit.transition hnk ((a (j k) / m.val : ℕ) : ZMod k.val) =
        ((a (j n) / m.val : ℕ) : ZMod n.val)
      rw [map_natCast, ← he, Nat.mod_mul_right_div_self, ZMod.natCast_mod]⟩
    refine ⟨y, ?_⟩
    apply ResidueLimit.ext
    intro n
    rw [map_mul, map_natCast]
    change (m.val : ZMod n.val) * ((a (j n) / m.val : ℕ) : ZMod n.val) = _
    rw [← Nat.cast_mul, Nat.mul_div_cancel' (hd n)]
    exact hred (dvd_mul_left n.val m.val)
  · rintro ⟨y, rfl⟩
    rw [map_mul, map_natCast]
    simp

/-- Reduction of actual rational integral adeles via the existing profinite-integer comparison. -/
def harrisIntegralAdeleResidue (h : RationalProfiniteIntegerAdeleComparison) (m : ℕ+) :
    integralFiniteAdeles ℚ →+* ZMod m.val :=
  (ProfiniteIntegerRing.reduction m).comp (Classical.choose h).symm.toRingHom

theorem harrisIntegralAdeleResidue_surjective (h : RationalProfiniteIntegerAdeleComparison)
    (m : ℕ+) : Function.Surjective (harrisIntegralAdeleResidue h m) :=
  (ResidueLimit.reduction_surjective m).comp (Classical.choose h).symm.surjective

theorem harrisIntegralAdeleResidue_eq_zero_iff (h : RationalProfiniteIntegerAdeleComparison)
    (m : ℕ+) (r : integralFiniteAdeles ℚ) :
    harrisIntegralAdeleResidue h m r = 0 ↔
      ∃ u : integralFiniteAdeles ℚ, (m.val : integralFiniteAdeles ℚ) * u = r := by
  let e := Classical.choose h
  change ProfiniteIntegerRing.reduction m (e.symm r) = 0 ↔ _
  rw [profiniteInteger_reduction_eq_zero_iff]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨e y, ?_⟩
    simpa only [map_mul, map_natCast, RingEquiv.apply_symm_apply] using congrArg e hy
  · rintro ⟨u, hu⟩
    refine ⟨e.symm u, ?_⟩
    simpa only [map_mul, map_natCast] using congrArg e.symm hu

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
local notation "Ixs" => Fin (Module.finrank ℤ L)
local instance sourceResiduesIntegralScalars : Module Rf Vf := Module.compHom _ (Rf).subtype

private def harrisIntegralBasis : Module.Basis Ixs ℤ L := Module.finBasis ℤ L

/-- The actual adelic basis obtained from a finite integer basis of the existing lattice. -/
def harrisIntegralSourceAdelicBasis : Module.Basis Ixs Af Vf :=
  ((harrisIntegralBasis D C).extendOfIsLattice ℚ).baseChange Af

local notation "basis" => harrisIntegralSourceAdelicBasis D C

private theorem harrisIntegralSourceAdelicBasis_apply (i : Ixs) :
    basis i = (1 : Af) ⊗ₜ[ℚ] ((harrisIntegralBasis D C i : L) : A) := by
  simp only [harrisIntegralSourceAdelicBasis, Module.Basis.baseChange_apply,
    Module.Basis.extendOfIsLattice_apply]

private theorem span_harrisIntegralSourceAdelicBasis : Submodule.span Rf (Set.range basis) = Λf := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    rw [harrisIntegralSourceAdelicBasis_apply]
    exact D.harrisHodgePELIntegralAdeleSpan_tmul C (harrisIntegralBasis D C i)
  · apply Submodule.span_le.mpr
    rintro _ ⟨x, rfl⟩
    rw [← (harrisIntegralBasis D C).sum_repr x]
    simp only [Submodule.coe_sum, Submodule.coe_smul, TensorProduct.tmul_sum,
      TensorProduct.tmul_smul]
    apply Submodule.sum_mem
    intro i _
    apply (Submodule.span Rf (Set.range basis)).toAddSubgroup.zsmul_mem
    rw [← harrisIntegralSourceAdelicBasis_apply]
    exact Submodule.subset_span ⟨i, rfl⟩

private theorem mem_harrisIntegralSource_iff (v : Vf) :
    v ∈ Λf ↔ ∀ i, (basis).repr v i ∈ Rf := by
  classical
  rw [← span_harrisIntegralSourceAdelicBasis D C]
  constructor
  · intro hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨j, rfl⟩ := hv
      intro i
      rw [Module.Basis.repr_self, Finsupp.single_apply]
      split_ifs
      · exact (Rf).one_mem
      · exact (Rf).zero_mem
    | zero => intro i; simpa only [map_zero, Finsupp.zero_apply] using (Rf).zero_mem
    | add x y _ _ hx hy => intro i; simpa using (Rf).add_mem (hx i) (hy i)
    | smul r x _ hx =>
      intro i
      change (basis).repr ((r : Af) • x) i ∈ Rf
      simpa using (Rf).mul_mem r.property (hx i)
  · intro h
    rw [← (basis).sum_repr v]
    apply Submodule.sum_mem
    intro i _
    change (⟨(basis).repr v i, h i⟩ : Rf) • basis i ∈ Submodule.span Rf (Set.range basis)
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/-- Restrict the actual adelic basis coordinates to the existing integral span. -/
def harrisIntegralSourceCoordinates : Λf ≃ₗ[Rf] (Ixs → Rf) where
  toFun v := fun i => ⟨(basis).repr v.val i, (mem_harrisIntegralSource_iff D C v.val).mp v.property i⟩
  invFun r := ⟨(basis).equivFun.symm (fun i => (r i : Af)), by
    apply (mem_harrisIntegralSource_iff D C _).mpr
    intro i
    change (basis).equivFun ((basis).equivFun.symm (fun j => (r j : Af))) i ∈ Rf
    rw [LinearEquiv.apply_symm_apply]
    exact (r i).property⟩
  left_inv v := by
    apply Subtype.ext
    exact (basis).equivFun.symm_apply_apply v.val
  right_inv r := by
    funext i
    apply Subtype.ext
    exact congrFun ((basis).equivFun.apply_symm_apply (fun i => (r i : Af))) i
  map_add' v w := by
    funext i
    apply Subtype.ext
    exact congrArg (fun f => f i) ((basis).repr.map_add v.val w.val)
  map_smul' r v := by
    funext i
    apply Subtype.ext
    exact congrArg (fun f => f i) ((basis).repr.map_smul (r : Af) v.val)

local notation "coords" => harrisIntegralSourceCoordinates D C
local notation "multiples" => harrisIntegralSourceMultiples D C

variable (h : RationalProfiniteIntegerAdeleComparison) (m : ℕ+)

private def sourceResidues : Λf →+ (Ixs → ZMod m.val) :=
  AddMonoidHom.pi fun i => (harrisIntegralAdeleResidue h m).toAddMonoidHom.comp
    ((LinearMap.proj i).comp (coords).toLinearMap).toAddMonoidHom

private theorem sourceResidues_eq_zero_iff (v : Λf) :
    sourceResidues D C h m v = 0 ↔ v ∈ multiples m.val := by
  constructor
  · intro hv
    have hr (i : Ixs) : ∃ u : Rf, (m.val : Rf) * u = coords v i :=
      (harrisIntegralAdeleResidue_eq_zero_iff h m _).mp (congrFun hv i)
    choose u hu using hr
    refine ⟨(coords).symm u, (coords).injective ?_⟩
    change coords ((m.val : Rf) • (coords).symm u) = coords v
    rw [map_smul, LinearEquiv.apply_symm_apply]
    exact funext hu
  · rintro ⟨w, rfl⟩
    funext i
    change harrisIntegralAdeleResidue h m (coords ((m.val : Rf) • w) i) = 0
    rw [map_smul]
    exact (harrisIntegralAdeleResidue_eq_zero_iff h m _).mpr ⟨coords w i, rfl⟩

/-- Identify the actual Harris source quotient with the ordered residue coordinates
coming from the chosen integral (basis). -/
def harrisIntegralReducedSourceCoordinates : HarrisIntegralSourceMod D C m.val ≃+
    (Ixs → ZMod m.val) := by
  let r := sourceResidues D C h m
  let f : HarrisIntegralSourceMod D C m.val →+ (Ixs → ZMod m.val) :=
    QuotientAddGroup.lift (multiples m.val).toAddSubgroup r
      (fun v hv => (sourceResidues_eq_zero_iff D C h m v).mpr hv)
  refine AddEquiv.ofBijective f ⟨?_, ?_⟩
  · intro a b he
    obtain ⟨v, rfl⟩ := (multiples m.val).mkQ_surjective a
    obtain ⟨w, rfl⟩ := (multiples m.val).mkQ_surjective b
    change r v = r w at he
    apply (Submodule.Quotient.eq _).mpr
    apply (sourceResidues_eq_zero_iff D C h m _).mp
    change r (v - w) = 0
    rw [map_sub, he, sub_self]
  · intro y
    choose v hv using fun i => harrisIntegralAdeleResidue_surjective h m (y i)
    refine ⟨(multiples m.val).mkQ ((coords).symm v), funext (fun i => ?_)⟩
    change harrisIntegralAdeleResidue h m (coords ((coords).symm v) i) = y i
    rw [LinearEquiv.apply_symm_apply, hv]

@[simp] theorem harrisIntegralReducedSourceCoordinates_mkQ (v : Λf) (i : Ixs) :
    harrisIntegralReducedSourceCoordinates D C h m ((multiples m.val).mkQ v) i =
      harrisIntegralAdeleResidue h m (coords v i) := rfl

end Langlands.Shimura.PEL.HarrisPolarizedWeilLevel
