import Langlands.RingTheory.Coalgebra.SeparablyClosedGroupLikeSpanningStatement
import Langlands.RingTheory.Coalgebra.Subcoalgebra.ScalarExtension
import Langlands.RingTheory.Coalgebra.Subcoalgebra.LocalFiniteness
import Langlands.RingTheory.Coalgebra.ConvolutionDualGroupLike
import Langlands.RingTheory.Coalgebra.ConvolutionBaseChange
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dual.Basis

open scoped TensorProduct
open Module

universe u v w

namespace Langlands.CoalgebraDescent

variable {k : Type u} [Field k]
variable {C : Type v} [AddCommGroup C] [Module k C] [Coalgebra k C]

theorem groupLike_subtype_iff (D : Subcoalgebra k C) (x : D) :
    IsGroupLikeElem k x ↔ IsGroupLikeElem k (x : C) := by
  constructor
  · exact fun h => h.map D.subtype
  · intro h
    refine ⟨h.counit_eq_one, ?_⟩
    apply D.tensorSquareInclusion_injective
    change TensorProduct.map D.subtype.toLinearMap D.subtype.toLinearMap
      (Coalgebra.comul (R := k) (A := D) x) =
        TensorProduct.map D.subtype.toLinearMap D.subtype.toLinearMap (x ⊗ₜ[k] x)
    calc
      _ = Coalgebra.comul (R := k) (D.subtype x) :=
        CoalgHomClass.map_comp_comul_apply D.subtype x
      _ = _ := by
        simp only [TensorProduct.map_tmul]
        change Coalgebra.comul (R := k) (x : C) = (x : C) ⊗ₜ[k] (x : C)
        exact h.comul_eq_tmul_self

theorem coordinate_contraction {ι : Type*} (b : Basis ι k C)
    (hb : ∀ i, IsGroupLikeElem k (b i)) (i : ι) (x : C) :
    TensorProduct.lid k C
      (TensorProduct.map (b.coord i) LinearMap.id (Coalgebra.comul x)) =
        b.repr x i • b i := by
  classical
  have h :
      (TensorProduct.lid k C).toLinearMap ∘ₗ
        TensorProduct.map (b.coord i) LinearMap.id ∘ₗ Coalgebra.comul =
          (b.coord i).smulRight (b i) := by
    apply b.ext
    intro j
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, (hb j).comul_eq_tmul_self,
      TensorProduct.map_tmul, LinearMap.id_apply, TensorProduct.lid_tmul,
      LinearMap.smulRight_apply, Basis.coord_apply]
    by_cases hj : j = i
    · subst j
      rfl
    · simp [Basis.repr_self, hj]
  exact LinearMap.congr_fun h x

theorem coordinate_smul_mem_subcoalgebra {ι : Type*} (b : Basis ι k C)
    (hb : ∀ i, IsGroupLikeElem k (b i)) (D : Subcoalgebra k C)
    {x : C} (hx : x ∈ D) (i : ι) : b.repr x i • b i ∈ D := by
  rw [← coordinate_contraction b hb]
  obtain ⟨z, hz⟩ := D.comul_mem hx
  rw [← hz]
  clear hz
  change TensorProduct.lid k C
    (TensorProduct.map (b.coord i) LinearMap.id
      (TensorProduct.map D.carrier.subtype D.carrier.subtype z)) ∈ D.toSubmodule
  induction z using TensorProduct.inductionOn with
  | tmul a c =>
    simpa using D.toSubmodule.smul_mem (b.coord i (a : C)) c.property
  | add a c ha hc =>
    simpa only [map_add] using D.toSubmodule.add_mem ha hc

theorem basis_mem_subcoalgebra_of_coord_ne_zero {ι : Type*} (b : Basis ι k C)
    (hb : ∀ i, IsGroupLikeElem k (b i)) (D : Subcoalgebra k C)
    {x : C} (hx : x ∈ D) {i : ι} (hi : b.repr x i ≠ 0) : b i ∈ D := by
  have h := D.toSubmodule.smul_mem (b.repr x i)⁻¹
    (coordinate_smul_mem_subcoalgebra b hb D hx i)
  simpa [smul_smul, hi] using h

theorem subcoalgebra_groupLike_spanning_of_basis {ι : Type*} (b : Basis ι k C)
    (hb : ∀ i, IsGroupLikeElem k (b i)) (D : Subcoalgebra k C) :
    Submodule.span k {x : D | IsGroupLikeElem k x} = ⊤ := by
  classical
  apply top_unique
  intro x _
  let S := Submodule.span k {x : D | IsGroupLikeElem k x}
  suffices (x : C) ∈ S.map D.carrier.subtype by
    obtain ⟨y, hy, hyx⟩ := this
    have he : y = x := Subtype.ext hyx
    exact he ▸ hy
  rw [← b.linearCombination_repr (x : C), Finsupp.linearCombination_apply, Finsupp.sum]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  have hbi := basis_mem_subcoalgebra_of_coord_ne_zero b hb D x.property
    (Finsupp.mem_support_iff.mp hi)
  exact ⟨⟨b i, hbi⟩, Submodule.subset_span
    ((groupLike_subtype_iff D ⟨b i, hbi⟩).mpr (hb i)), rfl⟩

theorem subcoalgebra_groupLike_spanning
    (h : Submodule.span k {x : C | IsGroupLikeElem k x} = ⊤)
    (D : Subcoalgebra k C) :
    Submodule.span k {x : D | IsGroupLikeElem k x} = ⊤ := by
  let b : Basis {x : C | IsGroupLikeElem k x} k C :=
    Basis.mk linearIndepOn_isGroupLikeElem.linearIndependent (by simpa using h.ge)
  apply subcoalgebra_groupLike_spanning_of_basis b
  intro i
  change IsGroupLikeElem k ((Basis.mk _ _) i)
  rw [Basis.mk_apply]
  exact i.property

theorem isCocomm_of_groupLike_spanning
    (h : Submodule.span k {x : C | IsGroupLikeElem k x} = ⊤) :
    Coalgebra.IsCocomm k C := by
  refine ⟨LinearMap.ext_on h ?_⟩
  intro x hx
  simp [hx.comul_eq_tmul_self]

theorem nonempty_convolutionDualEquivPi_of_basis {ι : Type*} [Finite ι]
    (b : Basis ι k C) (hb : ∀ i, IsGroupLikeElem k (b i)) :
    Nonempty (WithConv (C →ₗ[k] k) ≃ₐ[k] (ι → k)) := by
  classical
  let e := (WithConv.linearEquiv k (C →ₗ[k] k)).trans b.dualBasis.equivFun
  have he (φ : WithConv (C →ₗ[k] k)) (i : ι) : e φ i = φ (b i) :=
    b.dualBasis_equivFun φ.ofConv i
  refine ⟨AlgEquiv.ofLinearEquiv e ?_ ?_⟩
  · ext i
    rw [he]
    simpa using (hb i).counit_eq_one
  · intro φ ψ
    ext i
    simp only [he, Pi.mul_apply, LinearMap.convMul_apply,
      (hb i).comul_eq_tmul_self, TensorProduct.map_tmul, LinearMap.mul'_apply]

theorem exists_finite_convolutionDualEquivPi [FiniteDimensional k C]
    (h : Submodule.span k {x : C | IsGroupLikeElem k x} = ⊤) :
    ∃ (ι : Type v), Nonempty (Fintype ι) ∧
      Nonempty (WithConv (C →ₗ[k] k) ≃ₐ[k] (ι → k)) := by
  let b : Basis {x : C | IsGroupLikeElem k x} k C :=
    Basis.mk linearIndepOn_isGroupLikeElem.linearIndependent (by simpa using h.ge)
  let := FiniteDimensional.fintypeBasisIndex b
  refine ⟨{x : C | IsGroupLikeElem k x}, ⟨inferInstance⟩,
    nonempty_convolutionDualEquivPi_of_basis b ?_⟩
  intro i
  change IsGroupLikeElem k ((Basis.mk _ _) i)
  rw [Basis.mk_apply]
  exact i.property

theorem mul_comm_of_tensorProduct_equiv_pi
    {A : Type*} [Ring A] [Algebra k A]
    (K : Type w) [Field K] [Algebra k K] {ι : Type*}
    (e : K ⊗[k] A ≃ₐ[K] (ι → K)) (a b : A) : a * b = b * a := by
  apply Algebra.TensorProduct.includeRight_injective (A := K) (algebraMap k K).injective
  apply e.injective
  simp only [map_mul]
  exact mul_comm _ _

theorem isCocomm_of_convolution_comm [FiniteDimensional k C]
    (h : ∀ φ ψ : WithConv (C →ₗ[k] k), φ * ψ = ψ * φ) :
    Coalgebra.IsCocomm k C := by
  constructor
  ext x
  apply tensor_eq_of_forall_dual
  intro φ ψ
  have hs :
      LinearMap.mul' k k ∘ₗ TensorProduct.map φ ψ ∘ₗ
        (TensorProduct.comm k C C).toLinearMap =
          LinearMap.mul' k k ∘ₗ TensorProduct.map ψ φ := by
    ext a b
    simp [mul_comm]
  calc
    _ = LinearMap.mul' k k (TensorProduct.map ψ φ (Coalgebra.comul x)) :=
      LinearMap.congr_fun hs (Coalgebra.comul x)
    _ = _ := congrArg (fun f : WithConv (C →ₗ[k] k) => f x)
      (h (WithConv.toConv ψ) (WithConv.toConv φ))

theorem groupLike_spanning_of_surjective
    {E : Type*} [AddCommGroup E] [Module k E] [Coalgebra k E]
    (f : C →ₗc[k] E) (hf : Function.Surjective f)
    (h : Submodule.span k {x : C | IsGroupLikeElem k x} = ⊤) :
    Submodule.span k {x : E | IsGroupLikeElem k x} = ⊤ := by
  apply top_unique
  intro y _
  obtain ⟨x, rfl⟩ := hf y
  have hx : x ∈ Submodule.span k {x : C | IsGroupLikeElem k x} := by
    rw [h]
    trivial
  have hm : Submodule.span k {x : C | IsGroupLikeElem k x} ≤
      (Submodule.span k {x : E | IsGroupLikeElem k x}).comap f.toLinearMap :=
    Submodule.span_le.mpr fun x hx => Submodule.subset_span (hx.map f)
  exact hm hx

theorem baseChange_subcoalgebra_groupLike_spanning
    (K : Type w) [Field K] [Algebra k K]
    (h : Submodule.span K {x : K ⊗[k] C | IsGroupLikeElem K x} = ⊤)
    (D : Subcoalgebra k C) :
    Submodule.span K {x : K ⊗[k] D | IsGroupLikeElem K x} = ⊤ :=
  groupLike_spanning_of_surjective (C := Subcoalgebra.baseChange K D)
    (Subcoalgebra.baseChangeEquiv K D).symm.toCoalgHom
    (Subcoalgebra.baseChangeEquiv K D).symm.surjective
    (subcoalgebra_groupLike_spanning h (Subcoalgebra.baseChange K D))

theorem mem_groupLike_span_of_mem_subcoalgebra (D : Subcoalgebra k C)
    (h : Submodule.span k {x : D | IsGroupLikeElem k x} = ⊤)
    {x : C} (hx : x ∈ D) :
    x ∈ Submodule.span k {x : C | IsGroupLikeElem k x} := by
  have hdx : (⟨x, hx⟩ : D) ∈ Submodule.span k {x : D | IsGroupLikeElem k x} := by
    rw [h]
    trivial
  have hm : Submodule.span k {x : D | IsGroupLikeElem k x} ≤
      (Submodule.span k {x : C | IsGroupLikeElem k x}).comap D.subtype.toLinearMap :=
    Submodule.span_le.mpr fun y hy => Submodule.subset_span (hy.map D.subtype)
  exact hm hdx

theorem finite_groupLike_spanning_descent [IsSepClosed k]
    [FiniteDimensional k C] (K : Type w) [Field K] [Algebra k K]
    (h : Submodule.span K {x : K ⊗[k] C | IsGroupLikeElem K x} = ⊤) :
    Submodule.span k {x : C | IsGroupLikeElem k x} = ⊤ := by
  obtain ⟨ι, ⟨fi⟩, ⟨ePi⟩⟩ := exists_finite_convolutionDualEquivPi h
  let := fi
  let e := (convolutionDualBaseChangeEquiv k C K).trans ePi
  let := isCocomm_of_convolution_comm
    (fun φ ψ => mul_comm_of_tensorProduct_equiv_pi K e φ ψ)
  exact span_isGroupLikeElem_eq_top_of_tensorProduct_algEquiv_pi K e

theorem groupLike_spanning_descent_of_local_finiteness [IsSepClosed k]
    (K : Type w) [Field K] [Algebra k K]
    (hlocal : ∀ c : C, ∃ D : Subcoalgebra k C, c ∈ D ∧ FiniteDimensional k D)
    (h : Submodule.span K {x : K ⊗[k] C | IsGroupLikeElem K x} = ⊤) :
    Submodule.span k {x : C | IsGroupLikeElem k x} = ⊤ := by
  apply top_unique
  intro c _
  obtain ⟨D, hc, hfin⟩ := hlocal c
  let := hfin
  exact mem_groupLike_span_of_mem_subcoalgebra D
    (finite_groupLike_spanning_descent K (baseChange_subcoalgebra_groupLike_spanning K h D)) hc

/-- Group-like spanning descends along every field extension of a separably closed field. -/
theorem separablyClosedGroupLikeSpanning :
    SeparablyClosedGroupLikeSpanningStatement.{u, v, w} := by
  intro k _ _ C _ _ _ K _ _ h
  exact groupLike_spanning_descent_of_local_finiteness K
    (Subcoalgebra.localFiniteness k C) h

end Langlands.CoalgebraDescent
