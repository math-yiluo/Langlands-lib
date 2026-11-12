import Langlands.Shimura.Unitary.DefiniteDoubleCosets
import Langlands.Shimura.Unitary.DefinitePositivity
import Langlands.Global.IntegralFiniteAdeles

/-!
# Finiteness of definite double cosets for open levels

For an involution `σ` of a finite-dimensional `ℚ`-algebra whose real scalar extension is
positive, the double coset space `GJ(ℚ) \ GJ(𝔸_f) / K` is finite for every open subgroup `K` of
`GJ(𝔸_f)` (`finite_doubleCosets_of_isOpen`, `FiniteOpenDoubleCosets`). The lattice levels `K₀` of
`DefiniteDoubleCosets` are compact and open (`isCompact_latticeLevel`, `isOpen_latticeLevel`), so
`K ∩ K₀` has finite index in `K₀`, and finiteness passes from `K₀` to `K`
(`finite_doubleCosets_of_finite_quotient`). For Harris's definite group the positivity hypothesis
is supplied by `SecondKindInvolution.isPositive_of_hasDefiniteSignature`
(`SecondKindInvolution.finite_doubleCosets_of_isOpen`, `SecondKindInvolution.finiteOpenDoubleCosets`).
-/

noncomputable section

open scoped TensorProduct Matrix RestrictedProduct
open Module Matrix Topology

namespace Langlands.Shimura

namespace DefiniteDoubleCosets

section Group

variable {Γ G : Type*} [Group Γ] [Group G]

/-- If `ι Γ \ G / K₀` is finite and `K ∩ K₀` has finite index in `K₀`, then `ι Γ \ G / K` is
finite: every class of `ι Γ \ G / K` contains `y k` for a representative `y` of a class of
`ι Γ \ G / K₀` and a representative `k` of a coset of `K ∩ K₀` in `K₀`. -/
theorem finite_doubleCosets_of_finite_quotient (ι : Γ →* G) {K₀ K : Subgroup G}
    [Finite (EquivariantForms.DoubleCosets ι K₀)] [Finite (K₀ ⧸ K.subgroupOf K₀)] :
    Finite (EquivariantForms.DoubleCosets ι K) := by
  classical
  let F : EquivariantForms.DoubleCosets ι K₀ × (K₀ ⧸ K.subgroupOf K₀) →
      EquivariantForms.DoubleCosets ι K :=
    fun p => DoubleCoset.mk ι.range K (p.1.out * ((p.2.out : K₀) : G))
  refine Finite.of_surjective F fun p => ?_
  obtain ⟨h, hh, k, hk, e⟩ := DoubleCoset.mk_out_eq_mul ι.range K₀ p.out
  obtain ⟨k₁, e₁⟩ := QuotientGroup.mk_out_eq_mul (K.subgroupOf K₀) (⟨k, hk⟩⁻¹ : K₀)
  refine ⟨(DoubleCoset.mk ι.range K₀ p.out, QuotientGroup.mk (⟨k, hk⟩⁻¹ : K₀)), ?_⟩
  have hk₁ : (((k₁ : K₀) : G)) ∈ K := Subgroup.mem_subgroupOf.1 k₁.2
  change DoubleCoset.mk ι.range K
    ((DoubleCoset.mk ι.range K₀ p.out).out * (((QuotientGroup.mk (⟨k, hk⟩⁻¹ : K₀) :
      K₀ ⧸ K.subgroupOf K₀).out : K₀) : G)) = p
  rw [e, e₁]
  calc DoubleCoset.mk ι.range K (h * p.out * k * ((⟨k, hk⟩⁻¹ * (k₁ : K₀) : K₀) : G)) =
        DoubleCoset.mk ι.range K p.out := by
        rw [DoubleCoset.eq]
        refine ⟨h⁻¹, inv_mem hh, ((k₁ : K₀) : G)⁻¹, inv_mem hk₁, ?_⟩
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
    _ = p := DoubleCoset.out_eq' p

end Group

section Compact

local notation "𝔸f" => Langlands.Global.FiniteAdeles ℚ
local notation "Ẑ" => Langlands.Global.integralFiniteAdeles ℚ
local notation "ϕ" => algebraMap ℚ (Langlands.Global.FiniteAdeles ℚ)

open Langlands.Global.RationalLattice (IsIntegral)

variable {A : Type*} [Ring A] [Algebra ℚ A] [Module.Finite ℚ A]
variable {σ : AlgebraInvolution ℚ A} {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Basis ι ℚ A)

/-- `D⁻¹ Ẑ` is compact for a nonzero integer `D`. -/
theorem isCompact_scaled_integralFiniteAdeles {D : ℤ} (hD : D ≠ 0) :
    IsCompact {t : 𝔸f | (D : 𝔸f) * t ∈ Ẑ} := by
  have hD' : (D : 𝔸f) * ϕ (D : ℚ)⁻¹ = 1 := by
    rw [← map_intCast ϕ D, ← map_mul, mul_inv_cancel₀ (Int.cast_ne_zero.2 hD), map_one]
  have e : {t : 𝔸f | (D : 𝔸f) * t ∈ Ẑ} = (fun z => ϕ (D : ℚ)⁻¹ * z) '' Ẑ := by
    ext t
    constructor
    · intro ht
      refine ⟨(D : 𝔸f) * t, ht, ?_⟩
      change ϕ (D : ℚ)⁻¹ * ((D : 𝔸f) * t) = t
      rw [← mul_assoc, mul_comm (ϕ _), hD', one_mul]
    · rintro ⟨z, hz, rfl⟩
      change (D : 𝔸f) * (ϕ (D : ℚ)⁻¹ * z) ∈ Ẑ
      rw [← mul_assoc, hD', one_mul]
      exact hz
  rw [e]
  exact (Langlands.Global.isCompact_integralFiniteAdeles ℚ).image (continuous_const.mul continuous_id)

/-- **Compactness of the lattice level.** The map `g = (x, c) ↦ ((x, x⁻¹), (c, c⁻¹))` is a
topological embedding of `GJ(𝔸_f)`; it carries the lattice level onto a closed subset of a product
of compact boxes, since the coordinates of `x` have denominators bounded by those of `1`. -/
theorem isCompact_latticeLevel : IsCompact (latticeLevel σ b : Set σ.FiniteAdelicPoints) := by
  classical
  let : TopologicalSpace (𝔸f ⊗[ℚ] A) := moduleTopology 𝔸f (𝔸f ⊗[ℚ] A)
  have : IsModuleTopology 𝔸f (𝔸f ⊗[ℚ] A) := ⟨rfl⟩
  have : IsTopologicalRing (𝔸f ⊗[ℚ] A) := IsModuleTopology.isTopologicalRing 𝔸f _
  have : T2Space 𝔸f := inferInstanceAs (T2Space (Πʳ v : IsDedekindDomain.HeightOneSpectrum
    (NumberField.RingOfIntegers ℚ), [v.adicCompletion ℚ, v.adicCompletionIntegers ℚ]))
  set f := Algebra.TensorProduct.basis 𝔸f b with hf
  have hlin : ∀ φ : (𝔸f ⊗[ℚ] A) →ₗ[𝔸f] 𝔸f, Continuous φ := fun φ =>
    IsModuleTopology.continuous_of_linearMap φ
  have hrepr : Continuous fun y : 𝔸f ⊗[ℚ] A => f.equivFun y :=
    continuous_pi fun i => hlin (f.coord i)
  have : T2Space (𝔸f ⊗[ℚ] A) := T2Space.of_injective_continuous f.equivFun.injective hrepr
  have hZhat : IsClosed (Ẑ : Set 𝔸f) := (Langlands.Global.isCompact_integralFiniteAdeles ℚ).isClosed
  have hentry : ∀ i j, Continuous fun y : 𝔸f ⊗[ℚ] A => Algebra.leftMulMatrix f y i j := by
    intro i j
    have e : (fun y : 𝔸f ⊗[ℚ] A => Algebra.leftMulMatrix f y i j) =
        (f.coord i).comp (LinearMap.mulRight 𝔸f (f j)) := by
      funext y
      rw [Algebra.leftMulMatrix_eq_repr_mul]
      rfl
    rw [e]
    exact hlin _
  have hσ : Continuous fun y : 𝔸f ⊗[ℚ] A => (σ.baseChange 𝔸f) y :=
    IsModuleTopology.continuous_of_linearMap (σ.baseChange 𝔸f).linear
  have halg : Continuous (algebraMap 𝔸f (𝔸f ⊗[ℚ] A)) :=
    IsModuleTopology.continuous_of_linearMap (Algebra.linearMap 𝔸f (𝔸f ⊗[ℚ] A))
  -- The embedding `g = (x, c) ↦ ((x, x⁻¹), (c, c⁻¹))`.
  let E : σ.FiniteAdelicPoints → ((𝔸f ⊗[ℚ] A) × (𝔸f ⊗[ℚ] A)) × (𝔸f × 𝔸f) := fun g =>
    ((((g.1.1 : (𝔸f ⊗[ℚ] A)ˣ) : 𝔸f ⊗[ℚ] A), ((g.1.1⁻¹ : (𝔸f ⊗[ℚ] A)ˣ) : 𝔸f ⊗[ℚ] A)),
      (((g.1.2 : 𝔸fˣ) : 𝔸f), ((g.1.2⁻¹ : 𝔸fˣ) : 𝔸f)))
  have hE : IsInducing E := by
    let Φ := Homeomorph.prodCongr
      (Homeomorph.prodCongr (Homeomorph.refl (𝔸f ⊗[ℚ] A))
        (MulOpposite.opHomeomorph (M := 𝔸f ⊗[ℚ] A)).symm)
      (Homeomorph.prodCongr (Homeomorph.refl 𝔸f) (MulOpposite.opHomeomorph (M := 𝔸f)).symm)
    exact (Φ.isInducing.comp (Units.isInducing_embedProduct.prodMap
      Units.isInducing_embedProduct)).comp IsInducing.subtypeVal
  -- Its image of the lattice level.
  set Z : Set (((𝔸f ⊗[ℚ] A) × (𝔸f ⊗[ℚ] A)) × (𝔸f × 𝔸f)) := {p |
    p.1.1 * p.1.2 = 1 ∧ p.1.2 * p.1.1 = 1 ∧ p.2.1 * p.2.2 = 1 ∧
    p.1.1 * (σ.baseChange 𝔸f) p.1.1 = algebraMap 𝔸f (𝔸f ⊗[ℚ] A) p.2.1 ∧
    IsIntegral (Algebra.leftMulMatrix f p.1.1) ∧ IsIntegral (Algebra.leftMulMatrix f p.1.2) ∧
    p.2.1 ∈ Ẑ ∧ p.2.2 ∈ Ẑ} with hZdef
  have hEZ : E '' (latticeLevel σ b : Set σ.FiniteAdelicPoints) = Z := by
    ext p
    constructor
    · rintro ⟨g, ⟨h1, h2, h3, h4⟩, rfl⟩
      exact ⟨Units.mul_inv _, Units.inv_mul _, Units.mul_inv _,
        ((σ.baseChange 𝔸f).mem_similitudes_iff g.1).1 g.2, h1, h2, h3, h4⟩
    · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
      let y : (𝔸f ⊗[ℚ] A)ˣ := ⟨p.1.1, p.1.2, h1, h2⟩
      let c : 𝔸fˣ := ⟨p.2.1, p.2.2, h3, by rw [mul_comm]; exact h3⟩
      have hm : (y, c) ∈ (σ.baseChange 𝔸f).similitudes :=
        ((σ.baseChange 𝔸f).mem_similitudes_iff (y, c)).2 h4
      exact ⟨⟨(y, c), hm⟩, ⟨h5, h6, h7, h8⟩, rfl⟩
  have hint : ∀ φ : ((𝔸f ⊗[ℚ] A) × (𝔸f ⊗[ℚ] A)) × (𝔸f × 𝔸f) → 𝔸f ⊗[ℚ] A, Continuous φ →
      IsClosed {x | IsIntegral (Algebra.leftMulMatrix f (φ x))} := by
    intro φ hφ
    have e : {x | IsIntegral (Algebra.leftMulMatrix f (φ x))} =
        ⋂ i, ⋂ j, (fun x => Algebra.leftMulMatrix f (φ x) i j) ⁻¹' Ẑ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage]
      rfl
    rw [e]
    exact isClosed_iInter fun i => isClosed_iInter fun j => hZhat.preimage ((hentry i j).comp hφ)
  have hZ : IsClosed Z := by
    have c11 : Continuous fun p : ((𝔸f ⊗[ℚ] A) × (𝔸f ⊗[ℚ] A)) × (𝔸f × 𝔸f) => p.1.1 :=
      continuous_fst.comp continuous_fst
    have c12 : Continuous fun p : ((𝔸f ⊗[ℚ] A) × (𝔸f ⊗[ℚ] A)) × (𝔸f × 𝔸f) => p.1.2 :=
      continuous_snd.comp continuous_fst
    have c21 : Continuous fun p : ((𝔸f ⊗[ℚ] A) × (𝔸f ⊗[ℚ] A)) × (𝔸f × 𝔸f) => p.2.1 :=
      continuous_fst.comp continuous_snd
    have c22 : Continuous fun p : ((𝔸f ⊗[ℚ] A) × (𝔸f ⊗[ℚ] A)) × (𝔸f × 𝔸f) => p.2.2 :=
      continuous_snd.comp continuous_snd
    exact (isClosed_eq (c11.mul c12) continuous_const).inter
      ((isClosed_eq (c12.mul c11) continuous_const).inter
      ((isClosed_eq (c21.mul c22) continuous_const).inter
      ((isClosed_eq (c11.mul (hσ.comp c11)) (halg.comp c21)).inter
      ((hint _ c11).inter ((hint _ c12).inter
      ((hZhat.preimage c21).inter (hZhat.preimage c22)))))))
  -- A compact box containing `Z`.
  obtain ⟨D, hD0, hD⟩ := Langlands.Global.RationalLattice.exists_intCast_smul_isIntegral
    (Matrix.of fun i (_ : Unit) => ϕ (b.repr 1 i))
  set Box : Set (𝔸f ⊗[ℚ] A) := {y | ∀ i, (D : 𝔸f) * f.repr y i ∈ Ẑ} with hBoxdef
  have hBox : IsCompact Box := by
    have e : Box = f.equivFun.symm '' Set.pi Set.univ fun _ => {t : 𝔸f | (D : 𝔸f) * t ∈ Ẑ} := by
      ext y
      constructor
      · intro hy
        exact ⟨f.equivFun y, fun i _ => hy i, f.equivFun.symm_apply_apply y⟩
      · rintro ⟨v, hv, rfl⟩ i
        have e := congrFun (f.equivFun.apply_symm_apply v) i
        rw [Basis.equivFun_apply] at e
        rw [e]
        exact hv i (Set.mem_univ i)
    rw [e]
    exact (isCompact_univ_pi fun _ => isCompact_scaled_integralFiniteAdeles hD0).image
      (IsModuleTopology.continuous_of_linearMap f.equivFun.symm.toLinearMap)
  have hrepr1 : ∀ j, f.repr 1 j = ϕ (b.repr 1 j) := by
    intro j
    rw [Algebra.TensorProduct.one_def, Algebra.TensorProduct.basis_repr_tmul, one_smul]
    rfl
  have hBoxmem : ∀ y : 𝔸f ⊗[ℚ] A, IsIntegral (Algebra.leftMulMatrix f y) → y ∈ Box := by
    intro y hy i
    have e : f.repr y i = (Algebra.leftMulMatrix f y *ᵥ f.repr 1) i := by
      rw [Algebra.leftMulMatrix_mulVec_repr, mul_one]
    rw [e, Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Subring.sum_mem _ fun j _ => ?_
    rw [hrepr1, mul_left_comm]
    have hj := hD j ()
    simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul] at hj
    exact Subring.mul_mem _ (hy i j) hj
  have hZC : Z ⊆ (Box ×ˢ Box) ×ˢ ((Ẑ : Set 𝔸f) ×ˢ (Ẑ : Set 𝔸f)) := by
    rintro p ⟨-, -, -, -, h5, h6, h7, h8⟩
    exact ⟨⟨hBoxmem _ h5, hBoxmem _ h6⟩, ⟨h7, h8⟩⟩
  rw [hE.isCompact_iff, hEZ]
  exact ((hBox.prod hBox).prod ((Langlands.Global.isCompact_integralFiniteAdeles ℚ).prod
    (Langlands.Global.isCompact_integralFiniteAdeles ℚ))).of_isClosed_subset hZ hZC

omit [Module.Finite ℚ A] in
/-- **Openness of the lattice level.** The lattice level is defined by integrality conditions,
and `Ẑ` is open in `𝔸_f`. -/
theorem isOpen_latticeLevel : IsOpen (latticeLevel σ b : Set σ.FiniteAdelicPoints) := by
  classical
  let : TopologicalSpace (𝔸f ⊗[ℚ] A) := moduleTopology 𝔸f (𝔸f ⊗[ℚ] A)
  have : IsModuleTopology 𝔸f (𝔸f ⊗[ℚ] A) := ⟨rfl⟩
  set f := Algebra.TensorProduct.basis 𝔸f b with hf
  have hentry : ∀ i j, Continuous fun y : 𝔸f ⊗[ℚ] A => Algebra.leftMulMatrix f y i j := by
    intro i j
    have e : (fun y : 𝔸f ⊗[ℚ] A => Algebra.leftMulMatrix f y i j) =
        (f.coord i).comp (LinearMap.mulRight 𝔸f (f j)) := by
      funext y
      rw [Algebra.leftMulMatrix_eq_repr_mul]
      rfl
    rw [e]
    exact IsModuleTopology.continuous_of_linearMap _
  have hZo := Langlands.Global.isOpen_integralFiniteAdeles ℚ
  have hx : Continuous fun g : σ.FiniteAdelicPoints =>
      ((g.1.1 : (𝔸f ⊗[ℚ] A)ˣ) : 𝔸f ⊗[ℚ] A) :=
    Units.continuous_val.comp (continuous_fst.comp continuous_subtype_val)
  have hxi : Continuous fun g : σ.FiniteAdelicPoints =>
      ((g.1.1⁻¹ : (𝔸f ⊗[ℚ] A)ˣ) : 𝔸f ⊗[ℚ] A) :=
    Units.continuous_coe_inv.comp (continuous_fst.comp continuous_subtype_val)
  have hc : Continuous fun g : σ.FiniteAdelicPoints => ((g.1.2 : 𝔸fˣ) : 𝔸f) :=
    Units.continuous_val.comp (continuous_snd.comp continuous_subtype_val)
  have hci : Continuous fun g : σ.FiniteAdelicPoints => ((g.1.2⁻¹ : 𝔸fˣ) : 𝔸f) :=
    Units.continuous_coe_inv.comp (continuous_snd.comp continuous_subtype_val)
  have hint : ∀ φ : σ.FiniteAdelicPoints → 𝔸f ⊗[ℚ] A, Continuous φ →
      IsOpen {g | IsIntegral (Algebra.leftMulMatrix f (φ g))} := by
    intro φ hφ
    have e : {g | IsIntegral (Algebra.leftMulMatrix f (φ g))} =
        ⋂ i, ⋂ j, (fun g => Algebra.leftMulMatrix f (φ g) i j) ⁻¹' Ẑ := by
      ext g
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage]
      rfl
    rw [e]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j =>
      hZo.preimage ((hentry i j).comp hφ)
  exact (hint _ hx).inter ((hint _ hxi).inter ((hZo.preimage hc).inter (hZo.preimage hci)))

end Compact

section Open

variable {A : Type*} [Ring A] [Algebra ℚ A] [Module.Finite ℚ A] {σ : AlgebraInvolution ℚ A}

omit [Module.Finite ℚ A] in
variable (σ) in
/-- The double coset space `GJ(ℚ) \ GJ(𝔸_f) / K` is finite for every open subgroup `K` of
`GJ(𝔸_f)`. -/
def FiniteOpenDoubleCosets : Prop :=
  ∀ K : Subgroup σ.FiniteAdelicPoints, IsOpen (K : Set σ.FiniteAdelicPoints) →
    Finite (EquivariantForms.DoubleCosets σ.finiteAdelicDiagonal K)

/-- **Finiteness of definite double cosets for open levels.** For an involution `σ` of a
finite-dimensional `ℚ`-algebra whose real scalar extension is positive, `GJ(ℚ) \ GJ(𝔸_f) / K` is
finite for every open subgroup `K` of `GJ(𝔸_f)`. -/
theorem finite_doubleCosets_of_isOpen (hpos : (σ.baseChange ℝ).IsPositive)
    {K : Subgroup σ.FiniteAdelicPoints} (hK : IsOpen (K : Set σ.FiniteAdelicPoints)) :
    Finite (EquivariantForms.DoubleCosets σ.finiteAdelicDiagonal K) := by
  classical
  let b := Module.finBasis ℚ A
  have h₀ := finite_doubleCosets_latticeLevel b hpos
  have hc : CompactSpace (latticeLevel σ b) :=
    isCompact_iff_compactSpace.mp (isCompact_latticeLevel b)
  have ho : IsOpen ((K.subgroupOf (latticeLevel σ b)) : Set (latticeLevel σ b)) :=
    hK.preimage continuous_subtype_val
  have hq : Finite (latticeLevel σ b ⧸ K.subgroupOf (latticeLevel σ b)) :=
    Subgroup.quotient_finite_of_isOpen _ ho
  exact finite_doubleCosets_of_finite_quotient σ.finiteAdelicDiagonal (K₀ := latticeLevel σ b)

/-- Positive involutions satisfy `FiniteOpenDoubleCosets`. -/
theorem finiteOpenDoubleCosets_of_isPositive (hpos : (σ.baseChange ℝ).IsPositive) :
    FiniteOpenDoubleCosets σ :=
  fun _ hK => finite_doubleCosets_of_isOpen hpos hK

end Open

end DefiniteDoubleCosets

namespace SecondKindInvolution

variable {E : Type*} {K : Type*} {A : Type*}
  [Field E] [NumberField E] [NumberField.IsTotallyReal E]
  [Field K] [NumberField K] [NumberField.IsTotallyComplex K]
  [Algebra E K] [_root_.Algebra.IsQuadraticExtension E K]
  [Ring A] [Algebra E A] [Algebra K A]
  [Algebra ℚ A] [IsScalarTower ℚ E A]
  {σ : SecondKindInvolution E K A} {n : ℕ}

/-- **Harris's definite double cosets are finite.** For an involution of the second kind on an
algebra finite over `E` with the definite signature at every real place, `GJ(ℚ) \ GJ(𝔸_f) / K` is
finite for every open subgroup `K` of `GJ(𝔸_f)`. -/
theorem finite_doubleCosets_of_isOpen [Module.Finite E A] (h : HasDefiniteSignature σ n)
    {L : Subgroup σ.rationalInvolution.FiniteAdelicPoints}
    (hL : IsOpen (L : Set σ.rationalInvolution.FiniteAdelicPoints)) :
    Finite (EquivariantForms.DoubleCosets σ.rationalInvolution.finiteAdelicDiagonal L) := by
  let : Module.Finite ℚ A := Module.Finite.trans E A
  exact DefiniteDoubleCosets.finite_doubleCosets_of_isOpen
    (isPositive_of_hasDefiniteSignature h) hL

/-- Harris's definite group satisfies `FiniteOpenDoubleCosets`. -/
theorem finiteOpenDoubleCosets [Module.Finite E A] (h : HasDefiniteSignature σ n) :
    DefiniteDoubleCosets.FiniteOpenDoubleCosets σ.rationalInvolution :=
  fun _ hL => finite_doubleCosets_of_isOpen h hL

end SecondKindInvolution

end Langlands.Shimura
