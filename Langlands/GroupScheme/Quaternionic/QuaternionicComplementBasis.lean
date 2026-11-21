import Langlands.GroupScheme.Quaternionic.SkewHermitianComplement
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # Quaternion bases from the complementary quadratic-field subspace -/

noncomputable section

universe u v w

namespace Langlands.GroupScheme.KneserThree.QuatData

open QuadField Quaternionic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1700000

variable {F D : Type u} [Field F] [DivisionRing D] [Algebra F D] (Q : QuatData F D)
  {V : Type v} [AddCommGroup V] [Module D V]
  {I : Type w} [Fintype I]

local notation "E" => field Q.c

private instance componentModule : Module (field Q.c) V := Module.compHom V Q.ι.toRingHom

variable (W : Submodule (field Q.c) V)

/-- The two coefficient projections are exactly the two subspace components of a
  quaternionic linear combination. -/
private theorem quaternionicCombination_decompose (b : Module.Basis I E W) (x : I → D) :
    Fintype.linearCombination D (fun i => (b i : V)) x =
      (b.equivFun.symm (Q.fst ∘ x) : V) + Q.jAction (b.equivFun.symm (Q.snd ∘ x) : V) := by
  rw [Fintype.linearCombination_apply, Module.Basis.equivFun_symm_apply, Module.Basis.equivFun_symm_apply]
  simp only [SetLike.val_smul, AddSubmonoidClass.coe_finsetSum, Function.comp_apply, map_sum]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  change x i • (b i : V) = Q.ι (Q.fst (x i)) • (b i : V) +
    Q.j • (Q.ι (Q.snd (x i)) • (b i : V))
  rw [smul_smul, ← add_smul, Q.decompose]

/-- A paired decomposition in complementary subspaces is unique at zero. -/
theorem eq_zero_of_add_jAction_eq_zero (hW : IsCompl W (Q.jImage W)) (x y : W)
    (h : (x : V) + Q.jAction (y : V) = 0) : x = 0 ∧ y = 0 := by
  have hy : Q.jAction (y : V) ∈ Q.jImage W := (Q.mem_jImage_iff W _).mpr ⟨y, y.property, rfl⟩
  have hxy : (x : V) = -Q.jAction (y : V) := eq_neg_of_add_eq_zero_left h
  have hx : (x : V) = 0 :=
    Submodule.disjoint_def.mp hW.disjoint _ x.property (hxy.symm ▸ (Q.jImage W).neg_mem hy)
  have hy0 : (y : V) = 0 := by
    apply (Q.jAction_bijective (V := V)).1
    rw [map_zero]
    simpa only [hx, zero_add] using h
  exact ⟨Subtype.ext hx, Subtype.ext hy0⟩

/-- With a complementary semilinear image, a quadratic-field basis of the
  subspace is a quaternion basis of the original space. -/
theorem exists_quaternionicBasis (hW : IsCompl W (Q.jImage W)) (b : Module.Basis I E W) :
    ∃ bD : Module.Basis I D V, ∀ i, bD i = (b i : V) := by
  classical
  let f := Fintype.linearCombination D (fun i => (b i : V))
  have hfinj : Function.Injective f := by
    apply (injective_iff_map_eq_zero f).mpr
    intro x hx
    have hpair := Q.eq_zero_of_add_jAction_eq_zero W hW
      (b.equivFun.symm (Q.fst ∘ x)) (b.equivFun.symm (Q.snd ∘ x))
      ((Q.quaternionicCombination_decompose W b x).symm.trans hx)
    have hf : Q.fst ∘ x = 0 := b.equivFun.symm.injective (hpair.1.trans b.equivFun.symm.map_zero.symm)
    have hs : Q.snd ∘ x = 0 := b.equivFun.symm.injective (hpair.2.trans b.equivFun.symm.map_zero.symm)
    funext i
    have hfi : Q.fst (x i) = 0 := congrFun hf i
    have hsi : Q.snd (x i) = 0 := congrFun hs i
    rw [← Q.decompose (x i), hfi, hsi, Pi.zero_apply, map_zero, mul_zero, add_zero]
  have hfsurj : Function.Surjective f := by
    intro z
    obtain ⟨u, hu, v, hv, rfl⟩ := Q.exists_add_jAction_of_isCompl W hW z
    let x := fun i => Q.ι (b.equivFun ⟨u, hu⟩ i) + Q.j * Q.ι (b.equivFun ⟨v, hv⟩ i)
    refine ⟨x, ?_⟩
    have hf : Q.fst ∘ x = b.equivFun ⟨u, hu⟩ := funext fun _ => Q.fst_mk _ _
    have hs : Q.snd ∘ x = b.equivFun ⟨v, hv⟩ := funext fun _ => Q.snd_mk _ _
    change Fintype.linearCombination D (fun i => (b i : V)) x = _
    rw [quaternionicCombination_decompose, hf, hs, b.equivFun.symm_apply_apply, b.equivFun.symm_apply_apply]
  let e := LinearEquiv.ofBijective f ⟨hfinj, hfsurj⟩
  refine ⟨Module.Basis.ofEquivFun e.symm, ?_⟩
  intro i
  rw [Module.Basis.coe_ofEquivFun]
  change Fintype.linearCombination D (fun i => (b i : V)) (Pi.single i 1) = _
  rw [Fintype.linearCombination_apply_single, one_smul]

/-- An embedded quadratic-field basis extends over the division algebra when its
  subspace is complementary to the image under the second generator. -/
def QuaternionicComplementBasisStatement : Prop :=
  ∀ (F D : Type u) [Field F] [DivisionRing D] [Algebra F D] (Q : QuatData F D)
    (V : Type v) [AddCommGroup V] [Module D V] (I : Type w) [Fintype I],
    letI : Module (field Q.c) V := Module.compHom V Q.ι.toRingHom
    ∀ (W : Submodule (field Q.c) V), IsCompl W (Q.jImage W) →
    ∀ b : Module.Basis I (field Q.c) W, ∃ bD : Module.Basis I D V, ∀ i, bD i = (b i : V)

theorem quaternionicComplementBasis : QuaternionicComplementBasisStatement.{u,v,w} := by
  intro F D _ _ _ Q V _ _ I _ W hW b
  exact Q.exists_quaternionicBasis W hW b

end Langlands.GroupScheme.KneserThree.QuatData
