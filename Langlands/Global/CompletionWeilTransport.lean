import Langlands.Global.Arithmetic.HenniartGlobalizationStatement

/-!
# Weil equivalence of isomorphic p-adic fields

The actual local Weil map along a p-adic algebra isomorphism is a topological
group isomorphism. In particular the completion transport used in Henniart's
globalization statement induces an equivalence on continuous exact virtual
representations.
-/

noncomputable section

universe u v uK uW

namespace Langlands.Weil.Local

variable {p : ℕ} [Fact p.Prime]
  (F : PadicField.{u} p) (E : PadicField.{v} p)
  (f : F.Carrier ≃ₐ[Padic p] E.Carrier)

/-- A p-adic algebra isomorphism has extension degree one. -/
@[simp] theorem extensionDegree_algEquiv :
    extensionDegree F E f.toAlgHom = 1 := by
  have h := finrank_mul_extensionDegree F E f.toAlgHom
  rw [← f.toLinearEquiv.finrank_eq] at h
  exact Nat.eq_of_mul_eq_mul_left (Module.finrank_pos (R := Padic p) (M := F.Carrier))
    (h.trans (mul_one _).symm)

/-- The actual local Weil map of a p-adic algebra isomorphism is bijective. -/
theorem extensionWeilMap_algEquiv_bijective :
    Function.Bijective (extensionWeilMap F E f.toAlgHom) := by
  refine ⟨extensionWeilMap_injective F E f.toAlgHom, ?_⟩
  apply MonoidHom.range_eq_top.mp
  apply Subgroup.index_eq_one.mp
  rw [extensionWeilMap_range_index, extensionDegree_algEquiv]

/-- The actual local Weil map of an algebra isomorphism as a topological
group isomorphism. Its inverse inverts this same map, including its chosen
algebraic-closure embedding. -/
def extensionWeilEquivOfAlgEquiv : localWeilGroup E ≃ₜ* localWeilGroup F where
  toMulEquiv := MulEquiv.ofBijective (extensionWeilMap F E f.toAlgHom)
    (extensionWeilMap_algEquiv_bijective F E f)
  continuous_toFun := (extensionWeilMap F E f.toAlgHom).continuous
  continuous_invFun := by
    rw [(extensionWeilMap_isEmbedding F E f.toAlgHom).isInducing.continuous_iff]
    let e := MulEquiv.ofBijective (extensionWeilMap F E f.toAlgHom)
      (extensionWeilMap_algEquiv_bijective F E f)
    convert continuous_id (X := localWeilGroup F) using 1
    funext x
    exact e.apply_symm_apply x

@[simp] theorem extensionWeilEquivOfAlgEquiv_apply (w : localWeilGroup E) :
    extensionWeilEquivOfAlgEquiv F E f w = extensionWeilMap F E f.toAlgHom w := rfl

@[simp] theorem extensionWeilEquivOfAlgEquiv_toContinuousMonoidHom :
    (extensionWeilEquivOfAlgEquiv F E f : localWeilGroup E →ₜ* localWeilGroup F) =
      extensionWeilMap F E f.toAlgHom := rfl

end Langlands.Weil.Local

namespace Langlands.Global

open NumberField Langlands.Weil.Local Langlands.Global.CompletionPadic
open Langlands.VirtualRepresentation

variable {F : Type u} [Field F] [NumberField F] (v : FinitePlace F)
  {p : ℕ} [Fact p.Prime] (h : residuePrime v = p) (K : PadicField.{uK} p)
  (f : letI := (padicFieldAt v h).algebra
    K.Carrier ≃ₐ[Padic p] (padicFieldAt v h).Carrier)

/-- The exact completion transport of the globalization target, equipped with
its continuous inverse. -/
def completionWeilTransportEquiv :
    localWeilGroup K ≃ₜ* localWeilGroup (padicField v) :=
  letI := (padicFieldAt v h).algebra
  (extensionWeilEquivOfAlgEquiv (padicFieldAt v h) K f.symm).trans
    (padicFieldAtWeilEquiv v h)

@[simp] theorem completionWeilTransportEquiv_toContinuousMonoidHom :
    (completionWeilTransportEquiv v h K f :
      localWeilGroup K →ₜ* localWeilGroup (padicField v)) =
      completionWeilTransport v h K f := rfl

/-- Restriction along the target's completion transport is an equivalence of
the continuous exact Grothendieck groups in every carrier universe. -/
def completionWeilExactEquiv :
    ExactGrothendieckGroup
      (fun A : FiniteRepresentation.{0, u, uW} ℂ (localWeilGroup (padicField v)) =>
        A.IsContinuous) ≃ₗ[ℤ]
      ExactGrothendieckGroup
        (fun A : FiniteRepresentation.{0, uK, uW} ℂ (localWeilGroup K) =>
          A.IsContinuous) :=
  ExactGrothendieckGroup.continuousRestrictEquivalence
    (completionWeilTransportEquiv v h K f)

@[simp] theorem completionWeilExactEquiv_toLinearMap :
    (completionWeilExactEquiv.{u, uK, uW} v h K f).toLinearMap =
      ExactGrothendieckGroup.continuousRestrict (completionWeilTransport v h K f) := rfl

end Langlands.Global
