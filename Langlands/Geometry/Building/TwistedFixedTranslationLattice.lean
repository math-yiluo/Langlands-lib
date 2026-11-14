import Langlands.Geometry.Building.UnramifiedTwistedFixedTranslationStatement
import Langlands.GroupScheme.Absolute.InfiniteGaloisCocharacterDescent
import Langlands.Geometry.Building.RootDatumValuationGaloisAction
import Langlands.GroupScheme.Rational.SplitTorusFactorization
import Langlands.GroupScheme.Rational.SubgroupConjugacyDescent
import Langlands.GroupScheme.CocharacterTransportNaturality
import Langlands.GroupScheme.Rational.RadicalGaloisInnerTransport

/-! # Twisted-fixed cocharacters of a torus conjugate to a split extension -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.Geometry.Building.TwistedFixedTranslation

variable (k K : Type u) [Field k] [Field K] [Algebra k K]

/-- Abstract form: coefficient transport of a cocharacter followed by an inner
automorphism, for a point whose transport is given through an equation. -/
theorem transportCocharacter_comp_innerIso_of_eq {B S : Scheme.{u}} (b : S ⟶ B) (a : S ⟶ S)
    (ha : a ≫ b = b) (H : GroupScheme B)
    (χ : (Gm S).toGrp ⟶ (GroupScheme.baseChange b).obj H)
    (n m : Over.mk (𝟙 S) ⟶ ((GroupScheme.baseChange b).obj H).X)
    (hm : m = baseChangeBasePoint a ((GroupScheme.baseChange b).obj H) n ≫
      (descentBaseChangeIso b a ha H).hom.hom.hom) :
    transportCocharacter b a ha H (χ ≫ (((GroupScheme.baseChange b).obj H).innerIso n).hom) =
      transportCocharacter b a ha H χ ≫ (((GroupScheme.baseChange b).obj H).innerIso m).hom := by
  have h := descent_comp_innerIso_of_eq b a ha χ n m hm
  simp only [transportCocharacter, Category.assoc] at h ⊢
  rw [h]

/-- Coefficient transport of a cocharacter followed by an inner automorphism is the
transported cocharacter followed by the inner automorphism of the conjugate point. -/
theorem transportCocharacter_comp_innerIso (G : GroupScheme (Spec (CommRingCat.of k)))
    (σ : K ≃ₐ[k] K)
    (χ : (Gm (Spec (CommRingCat.of K))).toGrp ⟶
      (GroupScheme.baseChange (algebraBaseMap k K)).obj G)
    (g : rationalPoints ((GroupScheme.baseChange (algebraBaseMap k K)).obj G)) :
    transportCocharacter (algebraBaseMap k K) (galoisBaseMap k K σ)
        (galoisBaseMap_over k K σ) G
        (χ ≫ (((GroupScheme.baseChange (algebraBaseMap k K)).obj G).innerIso g).hom) =
      transportCocharacter (algebraBaseMap k K) (galoisBaseMap k K σ)
          (galoisBaseMap_over k K σ) G χ ≫
        (((GroupScheme.baseChange (algebraBaseMap k K)).obj G).innerIso
          (rationalConjugate k K G σ g)).hom :=
  transportCocharacter_comp_innerIso_of_eq (algebraBaseMap k K) (galoisBaseMap k K σ)
    (galoisBaseMap_over k K σ) G χ g _ (rationalConjugate_eq_baseChange_descent k K σ g)

section Twisted

variable {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} (iT : T.toGrp ⟶ G)

local notation "b" => algebraBaseMap k K
local notation "T_K" => CategoryTheory.Functor.obj (CommGroupScheme.baseChange b) T
local notation "G_K" => CategoryTheory.Functor.obj (GroupScheme.baseChange b) G
local notation "i_K" => CategoryTheory.Functor.map (GroupScheme.baseChange b) iT

/-- A twisted-fixed cocharacter of `T_K`, conjugated by `h`, is a coefficient-invariant
cocharacter of `G_K`. -/
theorem isInvariant_conj_of_twisted_fixed (h : rationalPoints G_K)
    (n : (K ≃ₐ[k] K) → normalizerPoints (T := T_K) i_K)
    (hn : ∀ σ, (n σ : rationalPoints G_K) = h⁻¹ * rationalConjugate k K G σ h)
    (ν : cocharacterLattice T_K)
    (hν : ∀ σ, cocharacterLattice.galoisRepresentation k K T σ ν ≫
      (normalizingAut (T := T_K) i_K (n σ)).hom = ν) :
    GaloisCocharacterDescent.IsInvariant k K G
      (CommGroupScheme.groupHom ν ≫ i_K ≫ (innerIso G_K h).hom) := by
  intro σ
  have hσ : rationalConjugate k K G σ h = h * (n σ : rationalPoints G_K) := by
    rw [hn σ, mul_inv_cancel_left]
  have e1 := transportCocharacter_comp_innerIso k K G σ (CommGroupScheme.groupHom ν ≫ i_K) h
  have e2 := transportCocharacter_naturality b (galoisBaseMap k K σ) (galoisBaseMap_over k K σ)
    iT (CommGroupScheme.groupHom ν)
  have e3 : (innerIso G_K (rationalConjugate k K G σ h)).hom =
      (innerIso G_K (n σ : rationalPoints G_K)).hom ≫ (innerIso G_K h).hom :=
    (congrArg (fun p => (innerIso G_K p).hom) hσ).trans (innerIso_mul_hom _ _ _)
  have e4 : i_K ≫ (innerIso G_K (n σ : rationalPoints G_K)).hom =
      CommGroupScheme.groupHom (normalizingAut (T := T_K) i_K (n σ)).hom ≫ i_K :=
    isNormalizingPoint_normalizingAut (T := T_K) i_K (n σ)
  have e5 : CommGroupScheme.groupHom (cocharacterLattice.galoisRepresentation k K T σ ν) =
      transportCocharacter b (galoisBaseMap k K σ) (galoisBaseMap_over k K σ) T.toGrp
        (CommGroupScheme.groupHom ν) := rfl
  have e6 : CommGroupScheme.groupHom (cocharacterLattice.galoisRepresentation k K T σ ν ≫
      (normalizingAut (T := T_K) i_K (n σ)).hom) =
      CommGroupScheme.groupHom (cocharacterLattice.galoisRepresentation k K T σ ν) ≫
        CommGroupScheme.groupHom (normalizingAut (T := T_K) i_K (n σ)).hom := rfl
  rw [Category.assoc] at e1
  rw [e1, e2, e3, ← e5]
  conv_rhs => rw [← hν σ, e6]
  simp only [Category.assoc]
  rw [reassoc_of% e4]

end Twisted

end Langlands.Geometry.Building.TwistedFixedTranslation
