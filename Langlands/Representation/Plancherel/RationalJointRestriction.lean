import Langlands.Representation.Plancherel.RationalRestrictionSurjectivity
import Langlands.Topology.ComplexCharacterExtension

/-! # Joint restriction of actual unramified characters -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.Plancherel

universe u

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable {G H K : GroupScheme (Spec (CommRingCat.of F))}

/-- Rational spanning by the two character restrictions detects the actual valuation image. -/
theorem rationalValuationImageMap_prod_injective_of_nsmul
    (f : H ⟶ G) (g : H ⟶ K)
    (hspan : ∀ chi : GroupScheme.rationalCharacters H,
      ∃ n : ℕ, 0 < n ∧ ∃ (psi : GroupScheme.rationalCharacters G)
        (eta : GroupScheme.rationalCharacters K),
        n • chi = GroupScheme.characterRestrict f psi + GroupScheme.characterRestrict g eta) :
    Function.Injective ((rationalValuationImageMap f).prod (rationalValuationImageMap g)) := by
  intro a b hab
  have hf : rationalValuationImageMap f a = rationalValuationImageMap f b :=
    congrArg Prod.fst hab
  have hg : rationalValuationImageMap g a = rationalValuationImageMap g b :=
    congrArg Prod.snd hab
  have hker : (GroupScheme.characterRestrict f).range ⊔
      (GroupScheme.characterRestrict g).range ≤ (a.val.toAdd - b.val.toAdd).ker := by
    refine sup_le ?_ ?_
    · rintro _ ⟨chi, rfl⟩
      have hc := congrArg (fun x : rationalDiscreteValuationImage G => x.val.toAdd chi) hf
      change (a.val.toAdd - b.val.toAdd) (GroupScheme.characterRestrict f chi) = 0
      exact sub_eq_zero.mpr (by simpa only [rationalValuationImageMap_apply] using hc)
    · rintro _ ⟨chi, rfl⟩
      have hc := congrArg (fun x : rationalDiscreteValuationImage K => x.val.toAdd chi) hg
      change (a.val.toAdd - b.val.toAdd) (GroupScheme.characterRestrict g chi) = 0
      exact sub_eq_zero.mpr (by simpa only [rationalValuationImageMap_apply] using hc)
  apply Subtype.ext
  apply Multiplicative.toAdd.injective
  apply AddMonoidHom.ext
  intro chi
  obtain ⟨n, hn, psi, eta, heq⟩ := hspan chi
  have hmem : n • chi ∈ (GroupScheme.characterRestrict f).range ⊔
      (GroupScheme.characterRestrict g).range := by
    rw [heq]
    exact AddSubgroup.add_mem_sup ⟨psi, rfl⟩ ⟨eta, rfl⟩
  have hc := hker hmem
  change a.val.toAdd (n • chi) - b.val.toAdd (n • chi) = 0 at hc
  simp only [map_nsmul, sub_eq_zero] at hc
  exact nsmul_right_injective (M := ℤ) hn.ne' hc

/-- A finite-index sum of character restriction ranges detects the actual valuation image. -/
theorem rationalValuationImageMap_prod_injective_of_finiteIndex
    (f : H ⟶ G) (g : H ⟶ K)
    (hindex : ((GroupScheme.characterRestrict f).range ⊔
      (GroupScheme.characterRestrict g).range).FiniteIndex) :
    Function.Injective ((rationalValuationImageMap f).prod (rationalValuationImageMap g)) := by
  let := hindex
  apply rationalValuationImageMap_prod_injective_of_nsmul f g
  intro chi
  obtain ⟨n, hn, _, hmem⟩ := AddSubgroup.exists_nsmul_mem_of_index_ne_zero
    (H := (GroupScheme.characterRestrict f).range ⊔ (GroupScheme.characterRestrict g).range)
    AddSubgroup.FiniteIndex.index_ne_zero chi
  obtain ⟨_, ⟨psi, rfl⟩, _, ⟨eta, rfl⟩, heq⟩ := AddSubgroup.mem_sup.mp hmem
  exact ⟨n, hn, psi, eta, heq.symm⟩

section CanonicalTopology

variable [IsAffine G.X.left] [IsAffine H.X.left] [IsAffine K.X.left]

local instance : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
local instance : TopologicalSpace (GroupScheme.rationalPoints H) := rationalPointTopology F H.X
local instance : TopologicalSpace (GroupScheme.rationalPoints K) := rationalPointTopology F K.X

/-- Multiply the two restrictions to the common source. -/
def rationalUnramifiedCharacterProductRestrict (f : H ⟶ G) (g : H ⟶ K) :
    (unramifiedCharacters (fun chi => (rationalNormCharacters G chi).toMul) ×
      unramifiedCharacters (fun chi => (rationalNormCharacters K chi).toMul)) →*
    unramifiedCharacters (fun chi => (rationalNormCharacters H chi).toMul) :=
  ((rationalUnramifiedCharacterRestrict f).toMonoidHom.comp (MonoidHom.fst _ _)) *
    ((rationalUnramifiedCharacterRestrict g).toMonoidHom.comp (MonoidHom.snd _ _))

@[simp]
theorem rationalUnramifiedCharacterProductRestrict_apply (f : H ⟶ G) (g : H ⟶ K)
    (psi : unramifiedCharacters (fun chi => (rationalNormCharacters G chi).toMul))
    (eta : unramifiedCharacters (fun chi => (rationalNormCharacters K chi).toMul)) :
    rationalUnramifiedCharacterProductRestrict f g (psi, eta) =
      rationalUnramifiedCharacterRestrict f psi * rationalUnramifiedCharacterRestrict g eta := rfl

variable [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType K.X.hom]

/-- Extend a character from the joint valuation image and split it on the two factors. -/
theorem rationalUnramifiedCharacterProductRestrict_surjective_of_injective
    (f : H ⟶ G) (g : H ⟶ K)
    (hfg : Function.Injective
      ((rationalValuationImageMap f).prod (rationalValuationImageMap g))) :
    Function.Surjective (rationalUnramifiedCharacterProductRestrict f g) := by
  intro phi
  let eta := rationalImageUnramifiedDescend H phi
  obtain ⟨theta, htheta⟩ := Langlands.Topology.exists_complex_character_extension
    ((rationalValuationImageMap f).prod (rationalValuationImageMap g)) hfg eta.toMonoidHom
  let psi : rationalImageCharacters G :=
    ⟨theta.comp (MonoidHom.inl _ _), continuous_of_discreteTopology⟩
  let chi : rationalImageCharacters K :=
    ⟨theta.comp (MonoidHom.inr _ _), continuous_of_discreteTopology⟩
  refine ⟨(rationalCanonicalImageUnramifiedContinuousEquiv G psi,
    rationalCanonicalImageUnramifiedContinuousEquiv K chi), ?_⟩
  apply Subtype.ext
  apply ContinuousMonoidHom.ext
  intro h
  change psi (rationalValuationImageProjection G (GroupScheme.rationalPoints.map f h)) *
    chi (rationalValuationImageProjection K (GroupScheme.rationalPoints.map g h)) = phi.val h
  rw [← rationalValuationImageMap_projection f h, ← rationalValuationImageMap_projection g h]
  change theta (rationalValuationImageMap f (rationalValuationImageProjection H h), 1) *
    theta (1, rationalValuationImageMap g (rationalValuationImageProjection H h)) = phi.val h
  rw [← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
  have he := DFunLike.congr_fun htheta (rationalValuationImageProjection H h)
  change theta (rationalValuationImageMap f (rationalValuationImageProjection H h),
    rationalValuationImageMap g (rationalValuationImageProjection H h)) =
      eta (rationalValuationImageProjection H h) at he
  exact he.trans (rationalImageUnramifiedDescend_projection H phi h)

/-- Rational spanning by the two actual character restrictions gives joint surjectivity. -/
theorem rationalUnramifiedCharacterProductRestrict_surjective_of_nsmul
    (f : H ⟶ G) (g : H ⟶ K)
    (hspan : ∀ chi : GroupScheme.rationalCharacters H,
      ∃ n : ℕ, 0 < n ∧ ∃ (psi : GroupScheme.rationalCharacters G)
        (eta : GroupScheme.rationalCharacters K),
        n • chi = GroupScheme.characterRestrict f psi + GroupScheme.characterRestrict g eta) :
    Function.Surjective (rationalUnramifiedCharacterProductRestrict f g) :=
  rationalUnramifiedCharacterProductRestrict_surjective_of_injective f g
    (rationalValuationImageMap_prod_injective_of_nsmul f g hspan)

/-- A finite-index sum of actual algebraic-character ranges suffices for joint surjectivity. -/
theorem rationalUnramifiedCharacterProductRestrict_surjective_of_finiteIndex
    (f : H ⟶ G) (g : H ⟶ K)
    (hindex : ((GroupScheme.characterRestrict f).range ⊔
      (GroupScheme.characterRestrict g).range).FiniteIndex) :
    Function.Surjective (rationalUnramifiedCharacterProductRestrict f g) :=
  rationalUnramifiedCharacterProductRestrict_surjective_of_injective f g
    (rationalValuationImageMap_prod_injective_of_finiteIndex f g hindex)

end CanonicalTopology

end Langlands.Plancherel
