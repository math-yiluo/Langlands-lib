import Langlands.Representation.CuspidalSupport.RationalNormKernelHeckeStructureStatement
import Langlands.Representation.CuspidalSupport.NormalHeckeLines
import Langlands.Representation.CuspidalSupport.RationalNormKernelEndSeparationProof
import Langlands.Representation.CuspidalSupport.RationalNormKernelCentralFiniteIndex
import Langlands.Representation.Plancherel.RationalImageLattice
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.Algebra.Group.UniqueProds.Basic

/-! Renard VI.4.3: the structure of `A = H(G, ρ)` for the common norm kernel `⁰G`. The
generic results of `NormalHeckeLines` apply to the open normal subgroup `⁰G`; the quotient
`G ⧸ ⁰G` has the two-unique-products property and is commutative, and the lattice statements
come from the valuation `G → Λ(G)`, whose image is a finite free `ℤ`-module with kernel `⁰G`. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology Langlands.Plancherel
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

section Lattice

/-- A submodule of a finite free `ℤ`-module `L` containing `k • L` for some `k ≠ 0` has a
basis indexed by `Fin (finrank ℤ L)`. -/
theorem exists_basis_of_smul_mem {L : Type*} [AddCommGroup L] [Module.Free ℤ L]
    [Module.Finite ℤ L] [Module.IsTorsionFree ℤ L] (M : Submodule ℤ L) {k : ℤ} (hk : k ≠ 0)
    (hM : ∀ v : L, k • v ∈ M) : Nonempty (Module.Basis (Fin (Module.finrank ℤ L)) ℤ M) := by
  obtain ⟨m, b⟩ := Submodule.basisOfPid (Module.Free.chooseBasis ℤ L) M
  have h1 : Module.finrank ℤ M = m := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  have h2 : Module.finrank ℤ M ≤ Module.finrank ℤ L := Submodule.finrank_le M
  have h3 : Module.finrank ℤ L ≤ Module.finrank ℤ M := by
    refine LinearMap.finrank_le_finrank_of_injective
      (f := LinearMap.codRestrict M (k • LinearMap.id) hM) ?_
    intro v w hvw
    exact smul_right_injective L hk (congrArg Subtype.val hvw)
  exact ⟨b.reindex (finCongr (by omega))⟩

/-- Let `f : G → C` be a surjective homomorphism with kernel `H` onto a commutative group `C`
which is a finite free `ℤ`-module, and let `N` be a subgroup of finite index of `G`. Then
there are `x_1, …, x_n ∈ N`, with `n` the rank of `C`, such that every `g ∈ N` is
`x_1^{e_1} ⋯ x_n^{e_n}` modulo `H` for exactly one `e ∈ ℤⁿ`. -/
theorem exists_latticeBasis {G C : Type*} [Group G] [CommGroup C]
    [Module.Free ℤ (Additive C)] [Module.Finite ℤ (Additive C)]
    [Module.IsTorsionFree ℤ (Additive C)] (f : G →* C) (hf : Function.Surjective f)
    (H : Subgroup G) (hker : f.ker = H) (N : Subgroup G) [N.FiniteIndex] :
    ∃ x : Fin (Module.finrank ℤ (Additive C)) → G, (∀ i, x i ∈ N) ∧
      ∀ g ∈ N, ∃! e : Fin (Module.finrank ℤ (Additive C)) → ℤ,
        g * ((List.ofFn fun i => x i ^ e i).prod)⁻¹ ∈ H := by
  let K : Subgroup C := N.map f
  let M : Submodule ℤ (Additive C) := AddSubgroup.toIntSubmodule (Subgroup.toAddSubgroup K)
  have hK : K.index ≠ 0 :=
    ne_zero_of_dvd_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H := N))
      (Subgroup.index_map_dvd (H := N) hf)
  have hM : ∀ v : Additive C, ((K.index : ℕ) : ℤ) • v ∈ M := by
    intro v
    rw [natCast_zsmul]
    change Additive.toMul (K.index • v) ∈ K
    rw [toMul_nsmul]
    exact Subgroup.pow_index_mem K _
  obtain ⟨b⟩ := exists_basis_of_smul_mem M (Int.natCast_ne_zero.mpr hK) hM
  have hb : ∀ i, Additive.toMul (b i : Additive C) ∈ N.map f := fun i => (b i).2
  choose x hxN hfx using fun i => Subgroup.mem_map.mp (hb i)
  have key : ∀ (g : G) (e : Fin (Module.finrank ℤ (Additive C)) → ℤ),
      g * ((List.ofFn fun i => x i ^ e i).prod)⁻¹ ∈ H ↔
        Additive.ofMul (f g) = ((b.equivFun.symm e : M) : Additive C) := by
    intro g e
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one, map_list_prod,
      List.map_ofFn, List.prod_ofFn, Module.Basis.equivFun_symm_apply, Submodule.coe_sum,
      ← Additive.ofMul.apply_eq_iff_eq, ofMul_prod]
    simp only [Function.comp_apply, map_zpow, hfx, ofMul_zpow, ofMul_toMul,
      Submodule.coe_smul]
  refine ⟨x, hxN, fun g hg => ?_⟩
  have hv : Additive.ofMul (f g) ∈ M := Subgroup.mem_map_of_mem f hg
  refine ⟨b.equivFun ⟨_, hv⟩, ?_, fun e he => ?_⟩
  · exact (key g _).mpr (by rw [LinearEquiv.symm_apply_apply])
  · have : (⟨_, hv⟩ : M) = b.equivFun.symm e := Subtype.ext ((key g e).mp he)
    rw [this, LinearEquiv.apply_symm_apply]

end Lattice

section

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] (G : GroupScheme (Spec (CommRingCat.of F)))

/-- `G ⧸ ⁰G` has the two-unique-products property: the valuation `g ↦ (χ ↦ ord χ(g))`
identifies it with a subgroup of `Multiplicative (X*(G) → ℤ)`. -/
theorem rationalNormKernelQuotient_twoUniqueProds :
    TwoUniqueProds (GroupScheme.rationalPoints G ⧸ rationalCommonNormKernel G) := by
  let f : (GroupScheme.rationalPoints G ⧸ rationalCommonNormKernel G) →*
      Multiplicative (GroupScheme.rationalCharacters G → ℤ) :=
    (AddMonoidHom.toMultiplicative (AddMonoidHom.coeFn (GroupScheme.rationalCharacters G) ℤ)).comp
      ((rationalCharacterValuationImage G).subtype.comp
        (rationalNormKernelQuotientEquiv G).toMonoidHom)
  have hf : Function.Injective f := by
    intro a b h
    apply (rationalNormKernelQuotientEquiv G).injective
    apply Subtype.ext
    apply Multiplicative.toAdd.injective
    exact DFunLike.coe_injective (congrArg Multiplicative.toAdd h)
  exact TwoUniqueProds.of_injective_mulHom f.toMulHom hf inferInstance

/-- `G ⧸ ⁰G` is commutative: `a b (b a)⁻¹ ∈ ⁰G` for all `a, b`. -/
theorem mul_mul_inv_mem_rationalCommonNormKernel (a b : GroupScheme.rationalPoints G) :
    a * b * (b * a)⁻¹ ∈ rationalCommonNormKernel G := by
  rw [← rationalValuationImageProjection_ker G, MonoidHom.mem_ker, map_mul, map_inv,
    mul_inv_eq_one, map_mul, map_mul, mul_comm]

end

/-- Renard VI.4.3: the structure of `A = H(G, ρ)`. -/
theorem rationalNormKernelHecke_structure :
    RationalNormKernelHeckeStructureStatement.{uF, uV} := by
  intro F _ _ _ _ G hG
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have := hG.smooth
  let : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
  have : SecondCountableTopology F :=
    HarmonicAnalysis.GeneralLocalField.secondCountableTopology F
  let : TopologicalSpace (G.affinePoints (CommAlgCat.of (CommRingCat.of F) F)) :=
    G.affinePointsTopologicalSpace _
  have : SecondCountableTopology (G.affinePoints (CommAlgCat.of (CommRingCat.of F) F)) :=
    G.affinePointsSecondCountableTopology (CommAlgCat.of (CommRingCat.of F) F)
  have : SecondCountableTopology (GroupScheme.rationalPoints G) :=
    (GroupScheme.rationalPointsAffineHomeomorph G).isEmbedding.secondCountableTopology
  have : IsTopologicalGroup (GroupScheme.rationalPoints G) :=
    rationalPoint_isTopologicalGroup F G
  have : SecondCountableTopology (rationalCommonNormKernel G) :=
    TopologicalSpace.Subtype.secondCountableTopology _
  intro ρ hρ H A conv InF IsTwistHom InN IsLatticeBasis
  have : ρ.representation.IsIrreducible := hρ
  have hrank := Whittaker.MirabolicRigidity.rank_le_aleph0 ρ.representation ρ.isSmooth hρ
  have hH := isOpen_rationalCommonNormKernel G
  have := rationalNormKernelQuotient_twoUniqueProds G
  obtain ⟨_, _⟩ := rationalReductiveImage_free_finite G hG
  have : (NormalHecke.stabSubgroup (rationalCommonNormKernel G) ρ).FiniteIndex := by
    have := rationalCommonNormKernel_sup_center_finiteIndex F G hG
    exact Subgroup.finiteIndex_of_le
      (sup_le (NormalHecke.le_stabSubgroup _ ρ) (NormalHecke.center_le_stabSubgroup _ ρ))
  obtain ⟨xb, hxN, hx⟩ := exists_latticeBasis (rationalValuationImageProjection G)
    (rationalValuationImageProjection_surjective G) _ (rationalValuationImageProjection_ker G)
    (NormalHecke.stabSubgroup (rationalCommonNormKernel G) ρ)
  obtain ⟨yb, -, hy⟩ := exists_latticeBasis (rationalValuationImageProjection G)
    (rationalValuationImageProjection_surjective G) _ (rationalValuationImageProjection_ker G) ⊤
  refine ⟨NormalHecke.unitHecke _ ρ hH, NormalHecke.inLine_unitHecke hH,
    NormalHecke.unitHecke_one hH,
    fun φ hφ => ⟨NormalHecke.unitHecke_conv hH hφ, NormalHecke.conv_unitHecke hH hφ⟩,
    fun x => ⟨fun φ hφ h0 => NormalHecke.eq_zero_of_inLine hφ h0, fun T =>
      ⟨fun hT => NormalHecke.exists_inLine_of_isTwistHom hT, ?_⟩⟩,
    fun x => ⟨fun φ ψ hφ hψ h0 => NormalHecke.exists_eq_smul_of_inLine hrank hφ hψ h0,
      NormalHecke.exists_inLine_ne_zero_iff⟩,
    fun φ hφ g hg => NormalHecke.inStab_of_apply_ne_zero hφ hg,
    fun x y φ ψ hφ hψ => NormalHecke.inLine_conv hH hφ hψ,
    fun x φ hφ h0 => NormalHecke.exists_conv_inverse hH hφ h0,
    fun x y φ ψ hφ hψ hφ0 hψ0 => NormalHecke.exists_conv_eq_smul hH hrank
      (mul_mul_inv_mem_rationalCommonNormKernel G) hφ hψ hφ0 hψ0,
    ⟨NormalHecke.stabSubgroup _ ρ, fun g => Iff.rfl, NormalHecke.le_stabSubgroup _ ρ, _,
      ⟨yb, fun g _ => hy g (Subgroup.mem_top g)⟩, ⟨xb, hxN, hx⟩⟩,
    NormalHecke.heckeSubmodule_eq_span _ ρ,
    fun φ hφ => NormalHecke.isUnit_iff_inLine hH hφ⟩
  rintro ⟨φ, hφ, rfl⟩
  exact NormalHecke.isTwistHom_apply hφ.1 x

end Langlands.CuspidalSupport
