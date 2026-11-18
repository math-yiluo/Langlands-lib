import Mathlib.RingTheory.HopfAlgebra.GroupLike
import Mathlib.RingTheory.HopfAlgebra.TensorProduct
import Mathlib.RingTheory.Bialgebra.Primitive
import Mathlib.RingTheory.Coalgebra.GroupLike
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Ideal.IdempotentFG
import Mathlib.LinearAlgebra.Dual.Lemmas
import Langlands.RingTheory.Coalgebra.ConvolutionDualGroupLike

/-! # Primitive elements, group-like spans and scalar extension -/

noncomputable section

open Coalgebra TensorProduct

namespace Langlands.CoetaleHopf

section Span

variable {K H : Type*} [Field K] [Ring H] [Bialgebra K H]

/-- A primitive element lying in the span of the group-like elements is zero. -/
theorem eq_zero_of_isPrimitiveElem_of_mem_span {p : H}
    (hp : Bialgebra.IsPrimitiveElem K p)
    (hspan : p ∈ Submodule.span K {g : H | IsGroupLikeElem K g}) : p = 0 := by
  classical
  have hS : LinearIndepOn K id {g : H | IsGroupLikeElem K g} := linearIndepOn_isGroupLikeElem
  let b := Module.Basis.extend hS
  have hidem : ∀ i, ∀ g : H, IsGroupLikeElem K g → b.coord i g * b.coord i g = b.coord i g := by
    intro i g hg
    have hg' : g = b ⟨g, Module.Basis.subset_extend hS hg⟩ := by simp [b]
    rw [hg', Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs <;> simp
  refine b.forall_coord_eq_zero_iff.mp fun i => ?_
  set f := b.coord i with hf
  let R : H →ₗ[K] K := LinearMap.mul' K K ∘ₗ TensorProduct.map f f ∘ₗ comul
  have hRf : Set.EqOn R f (Submodule.span K {g : H | IsGroupLikeElem K g}) := by
    refine LinearMap.eqOn_span' fun g hg => ?_
    change LinearMap.mul' K K (TensorProduct.map f f (comul g)) = f g
    rw [(show IsGroupLikeElem K g from hg).comul_eq_tmul_self, TensorProduct.map_tmul,
      LinearMap.mul'_apply]
    exact hidem i g hg
  have hR' : R p = f 1 * f p + f p * f 1 := by
    change LinearMap.mul' K K (TensorProduct.map f f (comul p)) = _
    rw [hp.comul_eq_tmul_add_tmul, map_add, TensorProduct.map_tmul, TensorProduct.map_tmul,
      map_add, LinearMap.mul'_apply, LinearMap.mul'_apply]
  have hR : f p = f 1 * f p + f p * f 1 := (hRf hspan).symm.trans hR'
  have h1 : f 1 * f 1 = f 1 := hidem i 1 IsGroupLikeElem.one
  linear_combination (1 - 2 * f 1) * hR - 4 * f p * h1

end Span

section Hopf

variable {K H : Type*} [Field K] [Ring H] [HopfAlgebra K H]

/-- In a Hopf algebra without nonzero primitive elements, every element that is skew-primitive
for a group-like element `a`, in the sense `Δ b = a ⊗ b + b ⊗ a`, is zero. -/
theorem eq_zero_of_comul_eq_of_isGroupLikeElem
    (hP : ∀ x : H, Bialgebra.IsPrimitiveElem K x → x = 0) {a b : H}
    (ha : IsGroupLikeElem K a) (hb : comul (R := K) b = a ⊗ₜ[K] b + b ⊗ₜ[K] a) : b = 0 := by
  have hSa : IsGroupLikeElem K (HopfAlgebra.antipode K a) := ha.antipode
  have hc : Bialgebra.IsPrimitiveElem K (HopfAlgebra.antipode K a * b) := by
    rw [Bialgebra.isPrimitiveElem_iff_comul_eq_tmul_add_tmul, Bialgebra.comul_mul,
      hSa.comul_eq_tmul_self, hb, mul_add, Algebra.TensorProduct.tmul_mul_tmul,
      Algebra.TensorProduct.tmul_mul_tmul, ha.antipode_mul_cancel]
  have h0 := hP _ hc
  calc b = (a * HopfAlgebra.antipode K a) * b := by rw [ha.mul_antipode_cancel, one_mul]
    _ = a * (HopfAlgebra.antipode K a * b) := mul_assoc _ _ _
    _ = 0 := by rw [h0, mul_zero]

end Hopf

section BaseChange

/-- Moving a scalar across the tensor product of two scalar extensions. -/
theorem tmul_tmul_comm {k K M : Type*} [CommRing k] [CommRing K] [Algebra k K]
    [AddCommGroup M] [Module k M] (c : K) (y z : M) :
    ((c ⊗ₜ[k] y) ⊗ₜ[K] ((1 : K) ⊗ₜ[k] z) : (K ⊗[k] M) ⊗[K] (K ⊗[k] M)) =
      ((1 : K) ⊗ₜ[k] y) ⊗ₜ[K] (c ⊗ₜ[k] z) := by
  have e (w : M) : (c ⊗ₜ[k] w : K ⊗[k] M) = c • ((1 : K) ⊗ₜ[k] w) := by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rw [e y, e z, TensorProduct.smul_tmul]

variable {k K A : Type*} [Field k] [Field K] [Algebra k K] [CommRing A] [Bialgebra k A]

/-- Comultiplication of a scalar extension, through the distributivity equivalence. -/
theorem distribBaseChange_tmul_comul (c : K) (a : A) :
    TensorProduct.AlgebraTensorModule.distribBaseChange k K A A (c ⊗ₜ[k] comul (R := k) a) =
      comul (R := K) (c ⊗ₜ[k] a) := by
  rw [TensorProduct.comul_tmul, CommSemiring.comul_apply]
  induction comul (R := k) a using TensorProduct.inductionOn with
  | tmul y z =>
    rw [TensorProduct.AlgebraTensorModule.distribBaseChange_tmul,
      TensorProduct.AlgebraTensorModule.tensorTensorTensorComm_tmul, tmul_tmul_comm]
  | add y z hy hz => rw [tmul_add, map_add, hy, hz, tmul_add, map_add]

/-- If a bialgebra over `k` has no nonzero primitive element, neither has any scalar extension
to a field. -/
theorem eq_zero_of_isPrimitiveElem_baseChange
    (hP : ∀ x : A, Bialgebra.IsPrimitiveElem k x → x = 0) (x : K ⊗[k] A)
    (hx : Bialgebra.IsPrimitiveElem K x) : x = 0 := by
  let ψ : A →ₗ[k] A ⊗[k] A :=
    comul - TensorProduct.mk k A A (1 : A) - (TensorProduct.mk k A A).flip (1 : A)
  have hψ : Function.Injective ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro m hm
    apply hP
    rw [Bialgebra.isPrimitiveElem_iff_comul_eq_tmul_add_tmul]
    have h : comul (R := k) m - (1 : A) ⊗ₜ[k] m - m ⊗ₜ[k] (1 : A) = 0 := hm
    rw [sub_sub, sub_eq_zero] at h
    exact h
  let Ψ : K ⊗[k] A →ₗ[K] (K ⊗[k] A) ⊗[K] (K ⊗[k] A) :=
    (TensorProduct.AlgebraTensorModule.distribBaseChange k K A A).toLinearMap ∘ₗ ψ.baseChange K
  have hΨ : Function.Injective Ψ := by
    refine (TensorProduct.AlgebraTensorModule.distribBaseChange k K A A).injective.comp ?_
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap ψ hψ
  have key : ∀ y : K ⊗[k] A, Ψ y = comul (R := K) y - 1 ⊗ₜ[K] y - y ⊗ₜ[K] 1 := by
    intro y
    induction y using TensorProduct.inductionOn with
    | tmul c a =>
      change TensorProduct.AlgebraTensorModule.distribBaseChange k K A A
        (c ⊗ₜ[k] (comul (R := k) a - (1 : A) ⊗ₜ[k] a - a ⊗ₜ[k] (1 : A))) = _
      rw [tmul_sub, tmul_sub, map_sub, map_sub, distribBaseChange_tmul_comul,
        TensorProduct.AlgebraTensorModule.distribBaseChange_tmul,
        TensorProduct.AlgebraTensorModule.distribBaseChange_tmul,
        Algebra.TensorProduct.one_def, tmul_tmul_comm]
    | add y z hy hz =>
      rw [map_add, hy, hz, map_add, add_tmul, tmul_add]
      abel
  apply hΨ
  rw [key, map_zero, hx.comul_eq_tmul_add_tmul]
  abel

end BaseChange

section Core

open WithConv

/-- Over an algebraically closed field, every maximal ideal of a finite commutative algebra is the
kernel of an algebra homomorphism to the field. -/
theorem exists_algHom_ker_eq {K B : Type*} [Field K] [IsAlgClosed K] [CommRing B] [Algebra K B]
    [Module.Finite K B] (m : Ideal B) [m.IsMaximal] :
    ∃ φ : B →ₐ[K] K, RingHom.ker φ = m := by
  let := Ideal.Quotient.field m
  have : Module.Finite K (B ⧸ m) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ K m).toLinearMap Ideal.Quotient.mk_surjective
  have : Algebra.IsIntegral K (B ⧸ m) := Algebra.IsIntegral.of_finite K _
  let ι := AlgEquiv.ofBijective (Algebra.ofId K (B ⧸ m))
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  refine ⟨ι.symm.toAlgHom.comp (Ideal.Quotient.mkₐ K m), ?_⟩
  ext x
  simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]

/-- In a commutative noetherian ring whose maximal ideals are idempotent, an element lying in
every maximal ideal is zero. -/
theorem eq_zero_of_forall_mem_maximal {B : Type*} [CommRing B] [IsNoetherianRing B]
    (hidem : ∀ m : Ideal B, m.IsMaximal → m ≤ m ^ 2) {x : B}
    (hx : ∀ m : Ideal B, m.IsMaximal → x ∈ m) : x = 0 := by
  by_contra hx0
  let J : Ideal B := (Submodule.span B {x}).annihilator
  have hJ : J ≠ ⊤ := by
    intro h
    have h1 : (1 : B) ∈ J := h ▸ Submodule.mem_top
    rw [Submodule.mem_annihilator_span_singleton, one_smul] at h1
    exact hx0 h1
  obtain ⟨m, hm, hJm⟩ := Ideal.exists_le_maximal J hJ
  have hfg : m.FG := IsNoetherian.noetherian m
  have hmm : IsIdempotentElem m :=
    le_antisymm Ideal.mul_le_right (by simpa [pow_two] using hidem m hm)
  obtain ⟨e, he, hme⟩ := (Ideal.isIdempotentElem_iff_of_fg m hfg).mp hmm
  have hxm := hx m hm
  rw [hme, Ideal.mem_span_singleton'] at hxm
  obtain ⟨r, hr⟩ := hxm
  have h1e : (1 - e) ∈ J := by
    rw [Submodule.mem_annihilator_span_singleton, smul_eq_mul, ← hr]
    calc (1 - e) * (r * e) = r * (e - e * e) := by ring
      _ = 0 := by rw [he.eq, sub_self, mul_zero]
  have hem : e ∈ m := hme ▸ Ideal.mem_span_singleton_self e
  have h1 : (1 : B) ∈ m := by simpa using m.add_mem (hJm h1e) hem
  exact hm.ne_top ((Ideal.eq_top_iff_one m).mpr h1)

variable {K E : Type*} [Field K] [IsAlgClosed K] [AddCommGroup E] [Module K E] [Coalgebra K E]
  [FiniteDimensional K E] [Coalgebra.IsCocomm K E]

/-- Over an algebraically closed field, a finite-dimensional cocommutative coalgebra in which
every element that is skew-primitive for a group-like element vanishes is spanned by its
group-like elements. -/
theorem span_isGroupLikeElem_eq_top_of_skewPrimitive
    (hSP : ∀ a b : E, IsGroupLikeElem K a → comul (R := K) b = a ⊗ₜ[K] b + b ⊗ₜ[K] a →
      b = 0) :
    Submodule.span K {d : E | IsGroupLikeElem K d} = ⊤ := by
  classical
  have hfinB : Module.Finite K (WithConv (E →ₗ[K] K)) :=
    Module.Finite.equiv (WithConv.linearEquiv K (E →ₗ[K] K)).symm
  have : IsNoetherianRing (WithConv (E →ₗ[K] K)) :=
    isNoetherian_of_tower K (inferInstance : IsNoetherian K (WithConv (E →ₗ[K] K)))
  have hidem : ∀ m : Ideal (WithConv (E →ₗ[K] K)), m.IsMaximal → m ≤ m ^ 2 := by
    intro m hm
    obtain ⟨φ, hφ⟩ := exists_algHom_ker_eq (K := K) m
    intro y hy
    by_contra hy2
    obtain ⟨l, hly, hlm⟩ := Submodule.exists_dual_map_eq_bot_of_notMem
      (p := (m ^ 2).restrictScalars K) hy2 inferInstance
    let δ : WithConv (E →ₗ[K] K) →ₗ[K] K :=
      l ∘ₗ (LinearMap.id - (Algebra.linearMap K (WithConv (E →ₗ[K] K))) ∘ₗ φ.toLinearMap)
    have hδ : ∀ u, δ u = l (u - algebraMap K _ (φ u)) := fun u => rfl
    have hsq : ∀ u v : WithConv (E →ₗ[K] K), u ∈ m → v ∈ m → l (u * v) = 0 := by
      intro u v hu hv
      have huv : u * v ∈ (m ^ 2).restrictScalars K := by
        rw [Submodule.restrictScalars_mem, pow_two]
        exact Ideal.mul_mem_mul hu hv
      have := Submodule.mem_map_of_mem (f := l) huv
      rw [hlm] at this
      exact (Submodule.mem_bot K).mp this
    have hsub : ∀ u, u - algebraMap K _ (φ u) ∈ m := by
      intro u
      rw [← hφ, RingHom.mem_ker, map_sub, AlgHom.commutes, Algebra.algebraMap_self,
        RingHom.id_apply, sub_self]
    have hder : ∀ u v, δ (u * v) = φ u * δ v + δ u * φ v := by
      intro u v
      have e : u * v - algebraMap K _ (φ (u * v)) =
          φ u • (v - algebraMap K _ (φ v)) + φ v • (u - algebraMap K _ (φ u)) +
            (u - algebraMap K _ (φ u)) * (v - algebraMap K _ (φ v)) := by
        simp only [map_mul, Algebra.smul_def]
        ring
      rw [hδ, e, map_add, map_add, hsq _ _ (hsub u) (hsub v), add_zero, map_smul, map_smul,
        smul_eq_mul, smul_eq_mul, hδ, hδ, mul_comm (φ v)]
    obtain ⟨a, ha, hφa⟩ := Langlands.CoalgebraDescent.exists_isGroupLikeElem_of_algHom φ
    let ℓ : Module.Dual K (Module.Dual K E) :=
      δ ∘ₗ (WithConv.linearEquiv K (E →ₗ[K] K)).symm.toLinearMap
    let b : E := (Module.evalEquiv K E).symm ℓ
    have hb : ∀ f : E →ₗ[K] K, δ (toConv f) = f b := fun f => by
      rw [Module.apply_evalEquiv_symm_apply]
      rfl
    have hcomul : comul (R := K) b = a ⊗ₜ[K] b + b ⊗ₜ[K] a := by
      refine Langlands.CoalgebraDescent.tensor_eq_of_forall_dual fun f g => ?_
      have h := hder (toConv f) (toConv g)
      rw [hφa, hφa, hb, hb, ← toConv_ofConv (toConv f * toConv g), hb,
        LinearMap.convMul_apply] at h
      rw [h, map_add, TensorProduct.map_tmul, TensorProduct.map_tmul, map_add,
        LinearMap.mul'_apply, LinearMap.mul'_apply]
    have hb0 := hSP a b ha hcomul
    have hδy : δ y = 0 := by
      rw [← toConv_ofConv y, hb, hb0, map_zero]
    have hφy : φ y = 0 := by
      rw [← RingHom.mem_ker, hφ]
      exact hy
    rw [hδ, hφy, map_zero, sub_zero] at hδy
    exact hly hδy
  refine Langlands.CoalgebraDescent.span_isGroupLikeElem_eq_top_of_algHom_separating
    fun x hx => eq_zero_of_forall_mem_maximal hidem fun m hm => ?_
  obtain ⟨φ, hφ⟩ := exists_algHom_ker_eq (K := K) m
  rw [← hφ, RingHom.mem_ker]
  exact hx φ

end Core

end Langlands.CoetaleHopf
