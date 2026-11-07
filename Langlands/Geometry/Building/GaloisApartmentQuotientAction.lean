import Langlands.Geometry.Building.ApartmentGaloisAction
import Langlands.GroupScheme.Rational.NormalizerGaloisAction
import Langlands.GroupScheme.IntegralModel.UnramifiedBuildingSemilinearAction

/-! # Actual coefficient action on the same root-valuation quotient -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} (i : T.toGrp ⟶ G)

local notation "b" => algebraBaseMap k K
local notation "T_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T
local notation "G_K" => baseChanged k K G
local notation "i_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) i

variable [Mono (CategoryTheory.Functor.map
  (GroupScheme.baseChange (algebraBaseMap k K)) i).hom.hom.left]

/-- Moving coefficient transport across the existing Weyl action introduces the
inverse coefficient automorphism on the character. -/
theorem galoisCharacter_weylAction (σ : K ≃ₐ[k] K)
    (n : normalizerPoints (T := T_K) i_K) (a : characterLattice T_K) :
    characterLattice.galoisRepresentation k K T σ⁻¹
        (weylAction (T := T_K) i_K (normalizerGaloisAction k K i σ n) a) =
      weylAction (T := T_K) i_K n (characterLattice.galoisRepresentation k K T σ⁻¹ a) := by
  have h := weylAction_normalizerGaloisAction k K i σ n
    (characterLattice.galoisRepresentation k K T σ⁻¹ a)
  have h' := congrArg (characterLattice.galoisRepresentation k K T σ⁻¹) h
  simpa only [Representation.inv_self_apply, Representation.self_inv_apply] using h'

namespace RootFunctionFamily

/-- The actual coefficient family action intertwines the existing normalizer
action with the actual coefficient conjugate normalizer point. -/
theorem galoisAction_smul (σ : K ≃ₐ[k] K)
    (n : normalizerPoints (T := T_K) i_K) (φ : RootFunctionFamily T_K G_K) :
    galoisAction k K T G σ (n • φ) =
      normalizerGaloisAction k K i σ n • galoisAction k K T G σ φ := by
  apply RootFunctionFamily.ext
  intro a g
  rw [galoisAction_apply, smul_apply, smul_apply, galoisAction_apply,
    ← map_inv (normalizerGaloisAction k K i σ) n, galoisCharacter_weylAction]
  congr 1
  change n.val⁻¹ * rationalConjugate k K G σ⁻¹ g * n.val =
    rationalConjugate k K G σ⁻¹
      ((rationalConjugate k K G σ n.val)⁻¹ * g * rationalConjugate k K G σ n.val)
  simp only [map_mul, map_inv, ← rationalConjugate_mul, inv_mul_cancel, rationalConjugate_one]

end RootFunctionFamily

namespace KPApartmentData

variable [IsAffineHom G.X.hom]

private instance extendedAffine : IsAffineHom (G_K).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
  infer_instance

variable {ω : Kˣ → ℝ}
  (D : KPApartmentData
    (S := CategoryTheory.Functor.obj (CommGroupScheme.baseChange (algebraBaseMap k K)) T)
    (CategoryTheory.Functor.map (GroupScheme.baseChange (algebraBaseMap k K)) i) ω)
  (hD : GaloisStable k K i D)

/-- The same apartment action intertwines the original normalizer action. -/
theorem galoisAction_normalizer_smul (σ : K ≃ₐ[k] K)
    (n : normalizerPoints (T := T_K) i_K) (x : D.Apartment) :
    galoisAction k K i D hD σ (n • x) =
      normalizerGaloisAction k K i σ n • galoisAction k K i D hD σ x := by
  apply Apartment.ext
  exact RootFunctionFamily.galoisAction_smul k K i σ n x.val

/-- Exact root-filtration transport carries each generator of the sharp fixer
into the sharp fixer at the transported point. -/
theorem rationalConjugate_mem_sharpFixer (σ : K ≃ₐ[k] K)
    (x : D.Apartment) (g : rationalPoints G_K) (hg : g ∈ D.sharpFixer {x}) :
    rationalConjugate k K G σ g ∈ D.sharpFixer {galoisAction k K i D hD σ x} := by
  have h : D.sharpFixer {x} ≤
      (D.sharpFixer {galoisAction k K i D hD σ x}).comap
        (rationalConjugate k K G σ).toMonoidHom := by
    refine iSup_le fun a => ?_
    intro p hp
    change rationalConjugate k K G σ p ∈ D.sharpFixer {galoisAction k K i D hD σ x}
    apply D.rootFixer_le_sharpFixer (galoisRootAction k K i σ a)
      {galoisAction k K i D hD σ x}
    rw [D.rootFixer_singleton] at hp ⊢
    exact (rationalConjugate_mem_filtration_iff k K i D hD σ x a.val 0 p).2 hp
  exact h hg

/-- Actual coefficient transport supplies all semilinear relation data for the
same original quotient, from only the stability of the supplied valuation class. -/
def galoisQuotientActionData :
    ApartmentQuotient.SemilinearActionData D.sharpFixerFamily (rationalConjugateAction k K G) where
  apartment := galoisAction k K i D hD
  normalizer_mem := fun σ n => rationalConjugate_mem_normalizerPoints k K i σ n.property
  normalizer_smul := galoisAction_normalizer_smul k K i D hD
  subgroup_mem := rationalConjugate_mem_sharpFixer k K i D hD

/-- Actual coefficient permutations of the existing reduced-building quotient. -/
def galoisQuotientAction : (K ≃ₐ[k] K) →* Equiv.Perm D.ReducedBuilding :=
  (galoisQuotientActionData k K i D hD).action

@[simp] theorem galoisQuotientAction_apartmentMap (σ : K ≃ₐ[k] K) (x : D.Apartment) :
    galoisQuotientAction k K i D hD σ (D.apartmentMap x) =
      D.apartmentMap (galoisAction k K i D hD σ x) :=
  (galoisQuotientActionData k K i D hD).action_apartment σ x

/-- Semilinearity for the original rational-point action on this same quotient. -/
theorem galoisQuotientAction_smul (σ : K ≃ₐ[k] K) (g : rationalPoints G_K)
    (z : D.ReducedBuilding) :
    galoisQuotientAction k K i D hD σ (g • z) =
      rationalConjugate k K G σ g • galoisQuotientAction k K i D hD σ z :=
  (galoisQuotientActionData k K i D hD).action_smul σ g z

/-- Fixation under the existing full rational-point action is reflected and
preserved by the actual coefficient action. -/
theorem galoisQuotientAction_smul_eq_iff (σ : K ≃ₐ[k] K) (g : rationalPoints G_K)
    (z : D.ReducedBuilding) :
    rationalConjugate k K G σ g • galoisQuotientAction k K i D hD σ z =
        galoisQuotientAction k K i D hD σ z ↔ g • z = z :=
  (galoisQuotientActionData k K i D hD).action_smul_eq_iff σ g z

end KPApartmentData

end Langlands.Geometry.Building
