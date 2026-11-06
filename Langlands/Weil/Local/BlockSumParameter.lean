import Langlands.Weil.Local.RepresentationProof
import Langlands.Weil.Local.Parameters
import Langlands.WeilDeligne.ParameterRelations
import Langlands.WeilDeligne.SpecialBlocks
import Langlands.WeilDeligne.DirectSum
import Langlands.Weil.Representation.InertiaOperations
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.RingTheory.Radical.Basic

/-!
# Sums of special blocks on irreducible local Weil representations are parameters

For continuous irreducible representations `σ_i` of the actual local Weil group and
lengths `m_i`, the direct sum `⨁_i σ_i ⊗ Sp(m_i)` of the published uncentered special
blocks has open inertia kernel and semisimple Weil action at every element. Hence it is
a Frobenius-semisimple parameter. The semisimplicity of `σ_i(g)` comes from the proved
reduction of continuous irreducibles to unramified twists of finite-image
representations.
-/

noncomputable section

open Polynomial

namespace Langlands

namespace BlockSumParameter

section LinearAlgebra

variable {K : Type*} [Field K]

/-- An endomorphism of finite order is semisimple in characteristic zero. -/
theorem isSemisimple_of_pow_eq_one [CharZero K] {M : Type*} [AddCommGroup M] [Module K M]
    {f : Module.End K M} {n : ℕ} (hn : n ≠ 0) (h : f ^ n = 1) : Module.End.IsSemisimple f := by
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero (p := X ^ n - C 1)
  · exact (separable_X_pow_sub_C (1 : K) (by exact_mod_cast hn) one_ne_zero).squarefree
  · simp [h]

/-- `f ⊗ 1` is semisimple when `f` is. -/
theorem isSemisimple_rTensor {M N : Type*} [AddCommGroup M] [Module K M]
    [FiniteDimensional K M] [AddCommGroup N] [Module K N] {f : Module.End K M}
    (hf : Module.End.IsSemisimple f) : Module.End.IsSemisimple (LinearMap.rTensor N f) := by
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero hf.minpoly_squarefree
  change aeval (Module.End.rTensorAlgHom K M N f) (minpoly K f) = 0
  rw [aeval_algHom_apply, minpoly.aeval, map_zero]

/-- `1 ⊗ g` is semisimple when `g` is. -/
theorem isSemisimple_lTensor {M N : Type*} [AddCommGroup M] [Module K M]
    [AddCommGroup N] [Module K N] [FiniteDimensional K N] {g : Module.End K N}
    (hg : Module.End.IsSemisimple g) : Module.End.IsSemisimple (LinearMap.lTensor M g) := by
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero hg.minpoly_squarefree
  change aeval (Module.End.lTensorAlgHom K N M g) (minpoly K g) = 0
  rw [aeval_algHom_apply, minpoly.aeval, map_zero]

/-- The tensor product of semisimple endomorphisms is semisimple over a perfect field:
it is the product of the commuting semisimple maps `f ⊗ 1` and `1 ⊗ g`. -/
theorem isSemisimple_tensorMap [PerfectField K] {M N : Type*} [AddCommGroup M] [Module K M]
    [FiniteDimensional K M] [AddCommGroup N] [Module K N] [FiniteDimensional K N]
    {f : Module.End K M} {g : Module.End K N} (hf : Module.End.IsSemisimple f) (hg : Module.End.IsSemisimple g) :
    Module.End.IsSemisimple (TensorProduct.map f g) := by
  have hcomm : Commute (LinearMap.rTensor N f) (LinearMap.lTensor M g) := by
    change LinearMap.rTensor N f ∘ₗ LinearMap.lTensor M g =
      LinearMap.lTensor M g ∘ₗ LinearMap.rTensor N f
    rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
  rw [← LinearMap.rTensor_comp_lTensor]
  exact Module.End.IsSemisimple.mul_of_commute hcomm (isSemisimple_rTensor hf)
    (isSemisimple_lTensor hg)

/-- Polynomials in a componentwise map act componentwise. -/
theorem aeval_lmap_apply {ι : Type*} [DecidableEq ι] {V : ι → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] (f : ∀ i, Module.End K (V i))
    (P : K[X]) (x : DirectSum ι V) (i : ι) :
    aeval (DirectSum.lmap f) P x i = aeval (f i) P (x i) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    simp only [map_add, LinearMap.add_apply, DirectSum.add_apply, hP, hQ]
  | monomial n c =>
    simp only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      DirectSum.smul_apply, WeilDeligneRepresentation.lmap_pow, DirectSum.lmap_apply]

/-- A componentwise map with semisimple finite-dimensional components is semisimple:
the radical of the product of the minimal polynomials is squarefree and kills every
component. -/
theorem isSemisimple_lmap {ι : Type*} [Fintype ι] [DecidableEq ι] {V : ι → Type*}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)] [∀ i, FiniteDimensional K (V i)]
    {f : ∀ i, Module.End K (V i)} (hf : ∀ i, Module.End.IsSemisimple (f i)) :
    Module.End.IsSemisimple (DirectSum.lmap f) := by
  classical
  let P : K[X] := UniqueFactorizationMonoid.radical (∏ i, minpoly K (f i))
  have hprod : ∏ i, minpoly K (f i) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => minpoly.ne_zero (Algebra.IsIntegral.isIntegral (f i))
  have hdvd : ∀ i, minpoly K (f i) ∣ P := fun i =>
    (UniqueFactorizationMonoid.dvd_radical_iff (hf i).minpoly_squarefree.isRadical hprod).mpr
      (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    (UniqueFactorizationMonoid.squarefree_radical (a := ∏ i, minpoly K (f i)))
  apply LinearMap.ext
  intro x
  apply DirectSum.ext
  intro i
  rw [aeval_lmap_apply]
  obtain ⟨Q, hQ⟩ := hdvd i
  change aeval (f i) P (x i) = 0
  rw [hQ, map_mul, minpoly.aeval, zero_mul, LinearMap.zero_apply]

end LinearAlgebra

section Special

variable {K : Type*} [Field K] {G : Type*} [Group G]

/-- The weight action `diag(1, ν(g), …, ν(g)^(m-1))` is semisimple: it is
multiplication by an element of `K^m`. -/
theorem isSemisimple_specialAction (ν : G →* Kˣ) (m : ℕ) (g : G) :
    Module.End.IsSemisimple (WeilDeligneRepresentation.Special.action ν m g) := by
  classical
  let c : Fin m → K := fun j => (ν g : K) ^ j.val
  have hc : WeilDeligneRepresentation.Special.action ν m g = Algebra.lmul K (Fin m → K) c := by
    apply LinearMap.ext
    intro v
    funext j
    simp [c]
  let s : Finset K := Finset.univ.image c
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero (p := ∏ a ∈ s, (X - C a))
  · exact ((separable_prod_X_sub_C_iff' (f := id)).mpr fun x _ y _ h => h).squarefree
  · rw [hc, aeval_algHom_apply]
    have hzero : aeval c (∏ a ∈ s, (X - C a)) = 0 := by
      funext j
      rw [aeval_pi_apply₂, Pi.zero_apply, map_prod]
      exact Finset.prod_eq_zero (Finset.mem_image_of_mem c (Finset.mem_univ j)) (by simp)
    rw [hzero, map_zero]

end Special

end BlockSumParameter

namespace FiniteRepresentation

/-- An element of a representation with finite image acts with finite order. -/
theorem exists_pow_eq_one_of_hasFiniteImage {G : Type*} [Group G]
    {A : FiniteRepresentation ℂ G} (hA : A.HasFiniteImage) (g : G) :
    ∃ N : ℕ, 0 < N ∧ A.representation g ^ N = 1 := by
  let u := A.representation.asGroupHom g
  have hu : ∀ n : ℕ, ((u ^ n : (Module.End ℂ A)ˣ) : Module.End ℂ A) =
      A.representation (g ^ n) := by
    intro n
    rw [Units.val_pow_eq_pow_val, Representation.asGroupHom_apply, map_pow]
  have : Finite (Set.range A.representation) := hA.to_subtype
  have hni : ¬ Function.Injective fun n : ℕ => u ^ n := by
    intro hinj
    obtain ⟨i, j, hij, h⟩ := Finite.exists_ne_map_eq_of_infinite
      (fun n : ℕ => (⟨A.representation (g ^ n), g ^ n, rfl⟩ : Set.range A.representation))
    apply hij
    apply hinj
    apply Units.ext
    rw [hu, hu]
    exact congrArg Subtype.val h
  rw [injective_pow_iff_not_isOfFinOrder, not_not, isOfFinOrder_iff_pow_eq_one] at hni
  obtain ⟨N, hN, h⟩ := hni
  refine ⟨N, hN, ?_⟩
  rw [← map_pow, ← hu, h, Units.val_one]

/-- Every element of a representation with finite image acts semisimply. -/
theorem isSemisimple_of_hasFiniteImage {G : Type*} [Group G]
    {A : FiniteRepresentation ℂ G} (hA : A.HasFiniteImage) (g : G) :
    Module.End.IsSemisimple (A.representation g) := by
  obtain ⟨N, hN, h⟩ := exists_pow_eq_one_of_hasFiniteImage hA g
  exact BlockSumParameter.isSemisimple_of_pow_eq_one hN.ne' h

end FiniteRepresentation

namespace Weil.Local

universe u v uι

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

/-- A continuous irreducible representation of the local Weil group acts semisimply
at every element: it is equivalent to an unramified twist of a representation with
finite image. -/
theorem isSemisimple_of_isContinuous_isIrreducible {A : LocalWeilRepresentation.{u, v} F}
    (hc : A.IsContinuous) (hi : A.IsIrreducible) (g : localWeilGroup F) :
    Module.End.IsSemisimple (A.representation g) := by
  obtain ⟨z, B, -, -, hB, -, ⟨e⟩⟩ := (localWeilIrreducibleReductionFor.{u, v} F A hc hi).1
  have hB' : Module.End.IsSemisimple (((localUnramifiedCharacter F z g : ℂˣ) : ℂ) • B.representation g) :=
    Module.End.IsSemisimple_smul _ (FiniteRepresentation.isSemisimple_of_hasFiniteImage hB g)
  refine (LinearEquiv.isSemisimple_iff (A.representation g) _ e.toLinearEquiv ?_).mpr hB'
  exact e.toIntertwiningMap.2 g

/-- The weight action of the local norm character is trivial on inertia. -/
theorem specialAction_inertia (m : ℕ) (i : localInertia F) :
    WeilDeligneRepresentation.Special.action (localNormCharacter F).toMonoidHom m (i : _) = 1 := by
  have hker : (localNormCharacter F).toMonoidHom.ker = localInertia F :=
    (localNormFaithfulnessFor F).1
  have hi : (localNormCharacter F).toMonoidHom (i : localWeilGroup F) = 1 := by
    rw [← MonoidHom.mem_ker, hker]
    exact i.2
  have hi' : ((((localNormCharacter F).toMonoidHom (i : localWeilGroup F)) : ℂˣ) : ℂ) = 1 := by
    rw [hi, Units.val_one]
  apply LinearMap.ext
  intro v
  funext j
  rw [WeilDeligneRepresentation.Special.action_apply, hi', one_pow, one_mul]
  rfl

/-- A block on a continuous representation has open inertia kernel. -/
theorem block_hasOpenInertiaKernel {A : LocalWeilRepresentation.{u, v} F}
    (hc : A.IsContinuous) (m : ℕ) :
    (WeilDeligneRepresentation.block (localNormCharacter F).toMonoidHom A
      m).toFiniteRepresentation.HasOpenInertiaKernel (localInertia F) := by
  apply FiniteRepresentation.hasOpenInertiaKernel_tensor
  · exact ((localWeilContinuity.{u, v} F A).2.2.1).mp hc
  · have htop : (WeilDeligneRepresentation.specialBlock (localNormCharacter F).toMonoidHom
        m).toFiniteRepresentation.inertiaKernel (localInertia F) = ⊤ := by
      rw [eq_top_iff]
      intro i _
      exact specialAction_inertia F m i
    unfold FiniteRepresentation.HasOpenInertiaKernel
    rw [htop]
    exact isOpen_univ

/-- A block on a continuous irreducible representation is a Frobenius-semisimple
parameter. -/
theorem isLocalFrobeniusSemisimpleParameter_block {A : LocalWeilRepresentation.{u, v} F}
    (hc : A.IsContinuous) (hi : A.IsIrreducible) (m : ℕ) :
    IsLocalFrobeniusSemisimpleParameter F
      (WeilDeligneRepresentation.block (localNormCharacter F).toMonoidHom A m) := by
  refine ⟨block_hasOpenInertiaKernel F hc m, fun g _ => ?_⟩
  exact BlockSumParameter.isSemisimple_tensorMap
    (isSemisimple_of_isContinuous_isIrreducible F hc hi g)
    (BlockSumParameter.isSemisimple_specialAction _ m g)

/-- A finite direct sum of Frobenius-semisimple parameters is one. -/
theorem isLocalFrobeniusSemisimpleParameter_directSum {ι : Type uι} [Fintype ι]
    [DecidableEq ι] {A : ι → LocalWeilDeligneRepresentation.{u, v} F}
    (hA : ∀ i, IsLocalFrobeniusSemisimpleParameter F (A i)) :
    IsLocalFrobeniusSemisimpleParameter F (WeilDeligneRepresentation.directSum A) :=
  ⟨FiniteRepresentation.hasOpenInertiaKernel_directSum (localInertia F) fun i => (hA i).1,
    fun g hg => BlockSumParameter.isSemisimple_lmap fun i => (hA i).2 g hg⟩

/-- The sum `⨁_i σ_i ⊗ Sp(m_i)` of blocks on continuous irreducible representations is
a Frobenius-semisimple parameter. -/
theorem isLocalFrobeniusSemisimpleParameter_blockSum {ι : Type uι} [Fintype ι]
    [DecidableEq ι] {B : ι → LocalWeilRepresentation.{u, v} F}
    (hB : ∀ i, (B i).IsContinuous ∧ (B i).IsIrreducible) (m : ι → ℕ) :
    IsLocalFrobeniusSemisimpleParameter F
      (WeilDeligneRepresentation.directSum fun i =>
        WeilDeligneRepresentation.block (localNormCharacter F).toMonoidHom (B i) (m i)) :=
  isLocalFrobeniusSemisimpleParameter_directSum F fun i =>
    isLocalFrobeniusSemisimpleParameter_block F (hB i).1 (hB i).2 (m i)

/-- The Frobenius-semisimple parameter class of `⨁_i B_i ⊗ Sp(m_i)`, for continuous
irreducible `B_i`, in its rank `∑_i rank(B_i) * m_i`. -/
def blockSumParameterClass {r : ℕ} (B : Fin r → LocalWeilRepresentation.{u, v} F)
    (hB : ∀ i, (B i).IsContinuous ∧ (B i).IsIrreducible) (m : Fin r → ℕ) :
    LocalFrobeniusSemisimpleParameterClassesOfRank.{u, v} F (∑ i, (B i).rank * m i) :=
  ⟨Quotient.mk _ ⟨WeilDeligneRepresentation.directSum fun i =>
      WeilDeligneRepresentation.block (localNormCharacter F).toMonoidHom (B i) (m i),
    isLocalFrobeniusSemisimpleParameter_blockSum F hB m⟩, by
    change (WeilDeligneRepresentation.directSum fun i =>
      WeilDeligneRepresentation.block (localNormCharacter F).toMonoidHom (B i) (m i)).rank = _
    rw [WeilDeligneRepresentation.rank_directSum]
    simp only [WeilDeligneRepresentation.rank_block]⟩

/-- The underlying pair class of `blockSumParameterClass` is the class of the block sum. -/
theorem forget_blockSumParameterClass {r : ℕ} (B : Fin r → LocalWeilRepresentation.{u, v} F)
    (hB : ∀ i, (B i).IsContinuous ∧ (B i).IsIrreducible) (m : Fin r → ℕ) :
    WeilDeligneRepresentation.ParameterRelations.forget (blockSumParameterClass F B hB m) =
      WeilDeligneRepresentation.classOf (WeilDeligneRepresentation.directSum fun i =>
        WeilDeligneRepresentation.block (localNormCharacter F).toMonoidHom (B i) (m i)) :=
  rfl

end Weil.Local

end Langlands
