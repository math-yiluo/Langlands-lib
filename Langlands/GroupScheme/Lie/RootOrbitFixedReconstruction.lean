import Langlands.GroupScheme.Lie.RootOrbitReconstruction
import Langlands.GroupScheme.Lie.GaloisFixedDescent

/-! # Invariant root tuples and actual fixed ambient Lie vectors -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u v w

namespace Langlands.LinearAlgebra

open Langlands.GroupScheme

variable {K V I J Γ : Type*} [Field K] [AddCommGroup V] [Module K V]
    [Fintype I] [DecidableEq J] [Group Γ] [MulAction Γ I] [DistribMulAction Γ V]
    (q : J → Submodule K V) (hq : DirectSum.IsInternal q)
    (f : I → J) (hf : Function.Injective f)
    (htransport : ∀ (σ : Γ) (i : I) {x : V}, x ∈ q (f i) →
      σ • x ∈ q (f (σ • i)))

include hq hf htransport in
/-- In a finite family of distinct actual weight components permuted by an
additive action, a sum is fixed exactly when its components form an invariant tuple. -/
theorem finiteWeightSum_fixed_iff (x : Π i : I, q (f i)) :
    (∀ (σ : Γ) i, σ • (x i : V) = (x (σ • i) : V)) ↔
      ∀ σ : Γ, σ • (∑ i : I, (x i : V)) = ∑ i : I, (x i : V) := by
  constructor
  · intro hx σ
    calc
      σ • (∑ i : I, (x i : V)) = ∑ i : I, σ • (x i : V) := Finset.smul_sum
      _ = ∑ i : I, (x (σ • i) : V) := Finset.sum_congr rfl (fun i _ => hx σ i)
      _ = ∑ i : I, (x i : V) := Equiv.sum_comp (MulAction.toPerm σ) (fun i => (x i : V))
  · intro hx σ i
    let y : Π i : I, q (f i) := fun j =>
      ⟨σ • (x (σ⁻¹ • j) : V), by
        have h := htransport σ (σ⁻¹ • j) (x (σ⁻¹ • j)).property
        simpa only [smul_inv_smul] using h⟩
    have hsum : ∑ j : I, (y j : V) = ∑ j : I, (x j : V) := by
      calc
        ∑ j : I, (y j : V) = ∑ j : I, σ • (x j : V) := by
          apply (Fintype.sum_equiv (MulAction.toPerm σ)
            (fun j => σ • (x j : V)) (fun j => (y j : V)) ?_).symm
          intro j
          change σ • (x j : V) = σ • (x (σ⁻¹ • σ • j) : V)
          rw [inv_smul_smul]
        _ = σ • (∑ j : I, (x j : V)) := Finset.smul_sum.symm
        _ = ∑ j : I, (x j : V) := hx σ
    have hyx : y = x := (finiteWeightSumEquiv q hq f hf).injective (Subtype.ext hsum)
    have hi := congrArg (fun z => (z (σ • i) : V)) hyx
    change σ • (x (σ⁻¹ • σ • i) : V) = (x (σ • i) : V) at hi
    have hval : (x (σ⁻¹ • σ • i) : V) = (x i : V) :=
      congrArg (fun j => (x j : V)) (inv_smul_smul σ i)
    exact (congrArg (fun z : V => σ • z) hval).symm.trans hi

end Langlands.LinearAlgebra

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable (k L : Type u) [Field k] [Field L] [Algebra k L]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (j : T.toGrp ⟶ G)

local notation "G_L" => CategoryTheory.Functor.obj
  (GroupScheme.baseChange (algebraBaseMap k L)) G
local notation "T_L" => CategoryTheory.Functor.obj
  (CommGroupScheme.baseChange (algebraBaseMap k L)) T
local notation "j_L" => CategoryTheory.Functor.map
  (GroupScheme.baseChange (algebraBaseMap k L)) j

local instance : IsAffineHom (G_L).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k L))
  infer_instance

attribute [local instance] rootsGaloisAction Lie.baseChangeGaloisAction

/-- The literal Galois-fixed vectors in one actual ambient Lie root-orbit span. -/
def rootOrbitFixedSpan
    (β : roots (T := (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T)
      ((GroupScheme.baseChange (algebraBaseMap k L)).map j)) :
    AddSubgroup (rootOrbitWeightSpan k L j β) :=
  (Lie.baseChangeFixedLie k L G).comap
    (rootOrbitWeightSpan k L j β).subtype.toAddMonoidHom

variable [FiniteDimensional k L] [LocallyOfFiniteType G.X.hom]

local instance orbitFintype
    (β : roots (T := (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T)
      ((GroupScheme.baseChange (algebraBaseMap k L)).map j)) :
    Fintype (MulAction.orbit (L ≃ₐ[k] L) β) :=
  (Finite.finite_mulAction_orbit (M := L ≃ₐ[k] L) β).fintype

local instance : LocallyOfFiniteType (G_L).X.hom := by
  change LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k L))
  infer_instance

/-- The actual root-orbit sum is the finite sum of its literal ambient vectors. -/
theorem rootOrbitSumEquiv_val
    (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T).toGrp)
    (β : roots (T := (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T)
      ((GroupScheme.baseChange (algebraBaseMap k L)).map j))
    (x : Π γ : MulAction.orbit (L ≃ₐ[k] L) β,
      weightSpace (T := T_L) j_L γ.val.val) :
    (rootOrbitSumEquiv k L j hT β x).val = ∑ γ, (x γ : Additive (lieKernel G_L L)) := rfl

/-- Fixedness of the actual sum detects precisely the invariant root tuple. -/
theorem rootOrbitSumEquiv_mem_fixed_iff
    (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T).toGrp)
    (β : roots (T := (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T)
      ((GroupScheme.baseChange (algebraBaseMap k L)).map j))
    (x : Π γ : MulAction.orbit (L ≃ₐ[k] L) β,
      weightSpace (T := T_L) j_L γ.val.val) :
    rootOrbitSumEquiv k L j hT β x ∈ rootOrbitFixedSpan k L j β ↔
      x ∈ rootOrbitInvariantSections k L j β := by
  classical
  change (∀ σ : L ≃ₐ[k] L, σ • (rootOrbitSumEquiv k L j hT β x).val =
      (rootOrbitSumEquiv k L j hT β x).val) ↔
    ∀ (σ : L ≃ₐ[k] L) γ, σ • (x γ : Additive (lieKernel G_L L)) =
      (x (σ • γ) : Additive (lieKernel G_L L))
  rw [rootOrbitSumEquiv_val]
  apply (Langlands.LinearAlgebra.finiteWeightSum_fixed_iff
    (weightSpace (T := T_L) j_L)
    (isInternal_weightSpace_of_isSplitTorus L G_L T_L hT j_L)
    (fun γ : MulAction.orbit (L ≃ₐ[k] L) β => γ.val.val)
    (by intro γ δ h; exact Subtype.ext (Subtype.ext h)) ?_ x).symm
  intro σ γ y hy
  have hy' : y ∈ RelativeRoot.actionWeightSpace
      ((AutomorphicAction.conjugation j).baseChange (algebraBaseMap k L)) γ.val.val := by
    rw [AutomorphicAction.baseChange_conjugation, RelativeRoot.actionWeightSpace_conjugation]
    exact hy
  have h := RelativeRoot.galois_mem_actionWeightSpace k L
    (AutomorphicAction.conjugation j) σ γ.val.val hy'
  rw [AutomorphicAction.baseChange_conjugation, RelativeRoot.actionWeightSpace_conjugation] at h
  exact h

/-- Actual invariant Lie-root tuples reconstruct exactly the Galois-fixed
vectors in their literal ambient orbit span. -/
def rootOrbitInvariantSumEquiv
    (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T).toGrp)
    (β : roots (T := (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T)
      ((GroupScheme.baseChange (algebraBaseMap k L)).map j)) :
    rootOrbitInvariantSections k L j β ≃+ rootOrbitFixedSpan k L j β where
  toFun x := ⟨rootOrbitSumEquiv k L j hT β x.val,
    (rootOrbitSumEquiv_mem_fixed_iff k L j hT β x.val).mpr x.property⟩
  invFun x := ⟨(rootOrbitSumEquiv k L j hT β).symm x.val, by
    apply (rootOrbitSumEquiv_mem_fixed_iff k L j hT β _).mp
    rw [LinearEquiv.apply_symm_apply]
    exact x.property⟩
  left_inv x := Subtype.ext ((rootOrbitSumEquiv k L j hT β).symm_apply_apply x.val)
  right_inv x := Subtype.ext ((rootOrbitSumEquiv k L j hT β).apply_symm_apply x.val)
  map_add' x y := Subtype.ext ((rootOrbitSumEquiv k L j hT β).map_add x.val y.val)

variable [IsGalois k L]

/-- A finite separable orbit field parametrizes actual Galois-fixed ambient
root-orbit vectors, using the constructed coherent actual root-line coordinates. -/
def rootOrbitFieldFixedSpanEquiv
    (hG : IsConnectedReductive G) (hj : IsMaximalTorus j)
    (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k L)).obj T).toGrp)
    (β : roots (T := (CommGroupScheme.baseChange (algebraBaseMap k L)).obj T)
      ((GroupScheme.baseChange (algebraBaseMap k L)).map j)) :
    rootOrbitField k L j β ≃+ rootOrbitFixedSpan k L j β :=
  (rootOrbitFieldSectionEquiv k L j hG hj hT β).trans
    (rootOrbitInvariantSumEquiv k L j hT β)

end Langlands.GroupScheme
