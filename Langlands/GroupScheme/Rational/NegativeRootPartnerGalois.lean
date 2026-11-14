import Langlands.GroupScheme.Rational.NegativeRootPartner
import Langlands.GroupScheme.Rational.RootMapGaloisRationalPoints

/-! # Galois transport of negative root partners -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
set_option autoImplicit false

namespace SplitPinning

section Galois

open GaloisPointComparison

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (i : T.toGrp ⟶ G)

local instance negativeRootPartnerGaloisIsAffineHom :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap k K)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom (algebraBaseMap k K))
  infer_instance

variable (p : Langlands.GroupScheme.SplitPinning
    ((GroupScheme.baseChange (algebraBaseMap k K)).obj G))
    (eT : p.torus ≅ ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))
    (hT : p.inclusion = CommGroupScheme.groupHom eT.hom ≫
      (GroupScheme.baseChange (algebraBaseMap k K)).map i)

namespace NormalizedRootParametrization

variable {a c : p.base.support}
    (x : p.NormalizedRootParametrization a) (y : p.NormalizedRootParametrization c)

include hT in
/-- If coefficient conjugation by `σ` carries the root of `a` to that of `c` and the
values of `x` to those of `y`, then it carries the negative partner of `x` to that of
`y`: `σ(y_a(d)) = y_c(σ d)`. -/
theorem negPoint_rationalConjugate (σ : K ≃ₐ[k] K)
    (hroot : characterLattice.congr eT (p.rootDatum.root c) =
      characterLattice.galoisRepresentation k K T σ
        (characterLattice.congr eT (p.rootDatum.root a)))
    (hval : ∀ e : K, rationalConjugate k K G σ (x.toRootParametrization.rationalPoint e) =
      y.toRootParametrization.rationalPoint (σ e))
    (d : K) :
    rationalConjugate k K G σ (x.negPoint d) = y.negPoint (σ d) := by
  by_cases hd : d = 0
  · rw [hd, x.negPoint_zero, map_one, map_zero, y.negPoint_zero]
  · set e : Kˣ := Units.mk0 (-d⁻¹) (by simpa using hd)
    have hde : -((e : K))⁻¹ = d := by simp [e]
    have hx := x.isOppositeFactorPair_rationalPoint e
    rw [hde] at hx
    have hq := (hx.changeTorus eT hT).rationalConjugate k K i σ
    rw [← hroot, hval] at hq
    have hq' := (RelativeRoot.isOppositeFactorPair_changeTorus_iff eT hT).mp hq
    set f : Kˣ := Units.mk0 (σ (e : K)) (by simp)
    have hf : (f : K) = σ (e : K) := rfl
    rw [← hf] at hq'
    have h := y.eq_negPoint_of_isOppositeFactorPair f hq'
    have hσd : -((f : K))⁻¹ = σ d := by
      rw [hf, ← hde, map_neg, map_inv₀]
    rw [hσd] at h
    exact congrArg Prod.fst h

end NormalizedRootParametrization

/-- The negative partners of a family of normalized simple-root parametrizations. -/
def negPointFamily (x : p.NormalizedSimpleRootParametrizations) (a : p.base.support) (d : K) :
    rationalPoints ((GroupScheme.baseChange (algebraBaseMap k K)).obj G) :=
  (x a).negPoint d

include hT in
/-- For Galois-compatible normalized simple-root maps, the negative partners are Galois
compatible as well: `σ(y_a(d)) = y_{ρ σ a}(σ d)`. -/
theorem RootMapsGaloisCompatible.negPointFamily_rationalConjugate
    {x : p.NormalizedSimpleRootParametrizations}
    {ρ : (K ≃ₐ[k] K) →* Equiv.Perm p.base.support}
    (hx : RootMapsGaloisCompatible k K p x ρ)
    (hroot : ∀ (σ : K ≃ₐ[k] K) (a : p.base.support),
      characterLattice.congr eT (p.rootDatum.root (ρ σ a)) =
        characterLattice.galoisRepresentation k K T σ
          (characterLattice.congr eT (p.rootDatum.root a)))
    (σ : K ≃ₐ[k] K) (a : p.base.support) (d : K) :
    rationalConjugate k K G σ (negPointFamily k K p x a d) =
      negPointFamily k K p x (ρ σ a) (σ d) :=
  NormalizedRootParametrization.negPoint_rationalConjugate k K i p eT hT (x a) (x (ρ σ a)) σ
    (hroot σ a) (RootMapsGaloisCompatible.rationalPoint k K hx σ a) d

end Galois

end SplitPinning

end Langlands.GroupScheme
