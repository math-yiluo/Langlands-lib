import Langlands.Geometry.Building.IwahoriWeylStatement
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Quotient algebra for the actual Iwahori–Weyl group

These lemmas isolate the group-theoretic steps of KP 7.8.1(1) and 7.8.2.
Normality and the geometric action comparison remain explicit intermediate inputs.
-/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme

namespace Langlands.Geometry.Building

namespace IwahoriWeylAlgebra

variable {A : Type u} {B : Type v} {C : Type w} [Group A] [Group B] [Group C]

/-- Two surjective homomorphisms with the same kernel identify their codomains
through their values on every common representative. -/
def sameKernelEquiv (f : A →* B) (g : A →* C)
    (hf : Function.Surjective f) (hg : Function.Surjective g) (hker : f.ker = g.ker) :
    B ≃* C :=
  (QuotientGroup.quotientKerEquivOfSurjective f hf).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective g hg))

theorem sameKernelEquiv_apply (f : A →* B) (g : A →* C)
    (hf : Function.Surjective f) (hg : Function.Surjective g) (hker : f.ker = g.ker)
    (a : A) : sameKernelEquiv f g hf hg hker (f a) = g a := by
  let e := QuotientGroup.quotientKerEquivOfSurjective f hf
  have he : e (QuotientGroup.mk a) = f a := rfl
  change ((QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivOfSurjective g hg)) (e.symm (f a)) = g a
  rw [← he, e.symm_apply_apply]
  rfl

/-- A complement of the kernel maps bijectively to the codomain of a surjection. -/
theorem bijective_restriction_of_complement (f : A →* B) (hf : Function.Surjective f)
    (H K : Subgroup A) (hker : f.ker = H) (hcomp : H.IsComplement' K) :
    Function.Bijective (f.comp K.subtype) := by
  constructor
  · intro x y hxy
    have hH : (x : A)⁻¹ * y ∈ H := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_inv]
      change ((f.comp K.subtype) x)⁻¹ * (f.comp K.subtype) y = 1
      rw [hxy, inv_mul_cancel]
    have h1 := Subgroup.disjoint_def.1 hcomp.disjoint hH
      (K.mul_mem (K.inv_mem x.property) y.property)
    exact Subtype.ext (inv_mul_eq_one.1 h1)
  · intro b
    obtain ⟨a, rfl⟩ := hf b
    obtain ⟨⟨h, k⟩, hhk⟩ := hcomp.2 a
    refine ⟨k, ?_⟩
    change f k = f a
    have hh : f h = 1 := MonoidHom.mem_ker.1 (hker.symm ▸ h.property)
    change (h : A) * (k : A) = a at hhk
    rw [← hhk, map_mul, hh, one_mul]

/-- Conversely, a subgroup that maps bijectively under a homomorphism is a complement
of its kernel. -/
theorem complement_of_bijective_restriction (f : A →* B) (H K : Subgroup A)
    (hker : f.ker = H) (hbij : Function.Bijective (f.comp K.subtype)) :
    H.IsComplement' K := by
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
  · apply Subgroup.disjoint_def.2
    intro x hxH hxK
    have hx : f x = 1 := MonoidHom.mem_ker.1 (hker.symm ▸ hxH)
    have heq : (⟨x, hxK⟩ : K) = 1 := hbij.1 (by simpa using hx)
    exact congrArg Subtype.val heq
  · apply Set.eq_univ_iff_forall.2
    intro a
    obtain ⟨k, hk⟩ := hbij.2 (f a)
    refine ⟨a * (k : A)⁻¹, ?_, k, k.property, inv_mul_cancel_right a k⟩
    change a * (k : A)⁻¹ ∈ H
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv]
    change f a * ((f.comp K.subtype) k)⁻¹ = 1
    rw [hk, mul_inv_cancel]

end IwahoriWeylAlgebra

namespace ParahoricBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (P : ParahoricBuildingData G)

section NormalizerNormal

variable [P.normalizerZero.Normal]

theorem affinePartMk_surjective : Function.Surjective P.affinePartMk :=
  MonoidHom.subgroupMap_surjective _ _

theorem affinePartMk_eq_one_iff (n : P.normalizerZeroComponent) :
    P.affinePartMk n = 1 ↔ (n : normalizerPoints P.i) ∈ P.normalizerZero := by
  rw [Subtype.ext_iff]
  exact QuotientGroup.eq_one_iff _

/-- Once the actual restricted normalizer action has the stated range and kernel,
its comparison with the affine part is prescribed on every representative. -/
theorem exists_affinePart_equiv_of_action
    (hmem : ∀ n : P.normalizerZeroComponent,
      P.apartment.normalizerAffineEquiv n ∈ AffineRootSystem.affineWeylGroup P.affineRoots)
    (hker : ∀ n : P.normalizerZeroComponent,
      P.apartment.normalizerAffineEquiv n = 1 ↔
        (n : normalizerPoints P.i) ∈ P.normalizerZero)
    (hsurj : ∀ w : AffineRootSystem.affineWeylGroup P.affineRoots,
      ∃ n : P.normalizerZeroComponent,
        P.apartment.normalizerAffineEquiv n = (w : P.Apartment ≃ᵃ[ℝ] P.Apartment)) :
    ∃ e : P.affinePart ≃* AffineRootSystem.affineWeylGroup P.affineRoots,
      ∀ n : P.normalizerZeroComponent,
        (e (P.affinePartMk n) : P.Apartment ≃ᵃ[ℝ] P.Apartment) =
          P.apartment.normalizerAffineEquiv (n : normalizerPoints P.i) := by
  let a : P.normalizerZeroComponent →*
      AffineRootSystem.affineWeylGroup P.affineRoots :=
    (P.apartment.normalizerAffineEquiv.comp P.normalizerZeroComponent.subtype).codRestrict
      _ hmem
  have ha : Function.Surjective a := by
    intro w
    obtain ⟨n, hn⟩ := hsurj w
    exact ⟨n, Subtype.ext hn⟩
  have hk : P.affinePartMk.ker = a.ker := by
    ext n
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, P.affinePartMk_eq_one_iff]
    apply (hker n).symm.trans
    constructor
    · intro hn
      exact Subtype.ext hn
    · intro hn
      exact congrArg Subtype.val hn
  refine ⟨IwahoriWeylAlgebra.sameKernelEquiv P.affinePartMk a
    P.affinePartMk_surjective ha hk, fun n => ?_⟩
  exact congrArg Subtype.val (IwahoriWeylAlgebra.sameKernelEquiv_apply
    P.affinePartMk a P.affinePartMk_surjective ha hk n)

variable [P.zeroSubgroup.Normal]

theorem toComponents_ker_eq_affinePart : P.toComponents.ker = P.affinePart := by
  unfold toComponents
  rw [QuotientGroup.ker_lift]
  apply congrArg (Subgroup.map (QuotientGroup.mk' P.normalizerZero))
  ext n
  change QuotientGroup.mk (n : rationalPoints G) = (1 : rationalPoints G ⧸
    P.zeroSubgroup) ↔ (n : rationalPoints G) ∈ P.zeroSubgroup
  exact QuotientGroup.eq_one_iff _

theorem affinePart_normal : P.affinePart.Normal := by
  rw [← P.toComponents_ker_eq_affinePart]
  infer_instance

/-- Surjectivity on components is equivalent to the full normalizer meeting every
`G(F)^0` coset. -/
theorem toComponents_surjective_iff :
    Function.Surjective P.toComponents ↔
      ∀ g : rationalPoints G, ∃ n : normalizerPoints P.i,
        QuotientGroup.mk (n : rationalPoints G) =
          (QuotientGroup.mk g : rationalPoints G ⧸ P.zeroSubgroup) := by
  constructor
  · intro h g
    obtain ⟨q, hq⟩ := h (QuotientGroup.mk g)
    obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨n, hq⟩
  · intro h q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨n, hn⟩ := h g
    exact ⟨QuotientGroup.mk n, hn⟩

theorem chamberStabilizer_toComponents_bijective
    (hsurj : Function.Surjective P.toComponents) (C : Set P.Apartment)
    (hcomp : P.affinePart.IsComplement' (P.chamberStabilizer C)) :
    Function.Bijective (P.toComponents.comp (P.chamberStabilizer C).subtype) :=
  IwahoriWeylAlgebra.bijective_restriction_of_complement P.toComponents hsurj
    P.affinePart (P.chamberStabilizer C) P.toComponents_ker_eq_affinePart hcomp

theorem chamberStabilizer_isComplement_of_bijective (C : Set P.Apartment)
    (hbij : Function.Bijective (P.toComponents.comp (P.chamberStabilizer C).subtype)) :
    P.affinePart.IsComplement' (P.chamberStabilizer C) :=
  IwahoriWeylAlgebra.complement_of_bijective_restriction P.toComponents P.affinePart
    (P.chamberStabilizer C) P.toComponents_ker_eq_affinePart hbij

end NormalizerNormal

end ParahoricBuildingData

end Langlands.Geometry.Building
