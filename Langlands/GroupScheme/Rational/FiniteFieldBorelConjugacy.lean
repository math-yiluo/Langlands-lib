import Langlands.GroupScheme.IdentityComponentRationalGalois
import Langlands.GroupScheme.Rational.FrobeniusStableBorel
import Langlands.GroupScheme.Absolute.FrobeniusBorelDescent
import Langlands.GroupScheme.Absolute.BorelConjugacyProof
import Langlands.GroupScheme.Absolute.BorelNormalizerProof
import Langlands.GroupScheme.Rational.RadicalGaloisInnerTransport
import Langlands.GroupScheme.Rational.TorusTransporterOrbit
import Langlands.GroupScheme.FiniteFieldTorsorPoint.PointDescent

/-! # Rational conjugacy of geometric Borel subgroups over finite fields -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.GroupScheme.GaloisPointComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.FiniteFieldBorelPair

section Points

variable (k K : Type u) [Field k] [Fintype k]
  [Field K] [Algebra k K] [Algebra.IsAlgebraic k K]
  (G : GroupScheme (Spec (CommRingCat.of k)))

/-- A Frobenius-fixed geometric point of an affine group has an original-field
point whose pullback is exactly the prescribed point. -/
theorem exists_rationalPoint_of_frobenius_fixed [IsAffine G.X.left]
    (p : rationalPoints (baseChanged k K G))
    (hp : rationalConjugate k K G
      (FiniteField.frobeniusAlgEquivOfAlgebraic k K) p = p) :
    ∃ q : rationalPoints G, baseChangeBasePoint (baseMap k K) G q = p := by
  let x := baseChangeCoeffEquiv k K G p
  let c := GaloisPoint.coordinates k G K x
  have hfix : GaloisPoint.conjugate k K G
      (FiniteField.frobeniusAlgEquivOfAlgebraic k K) x = x := by
    simpa only [baseChangeCoeffEquiv_rationalConjugate] using
      congrArg (baseChangeCoeffEquiv k K G) hp
  have hm : ∀ a, ∃ t : k, algebraMap k K t = c a := by
    intro a
    apply FiniteFieldTorsorPoint.mem_range_algebraMap_of_pow_card_eq (k := k)
    have h := congrArg (fun y => GaloisPoint.coordinates k G K y a) hfix
    rw [GaloisPoint.coordinates_conjugate] at h
    exact h
  choose d hd using hm
  let d' : AffineCoordinateRing k G.X →ₐ[k] k :=
    { toFun := d
      map_one' := (algebraMap k K).injective (by simp only [hd, map_one])
      map_mul' := fun a b => (algebraMap k K).injective (by simp only [map_mul, hd])
      map_zero' := (algebraMap k K).injective (by simp only [hd, map_zero])
      map_add' := fun a b => (algebraMap k K).injective (by simp only [map_add, hd])
      commutes' := fun r => (algebraMap k K).injective (by
        rw [hd, c.commutes]
        simp) }
  let q := (rationalCoeffEquiv k G).symm ((GaloisPoint.coordinates k G k).symm d')
  refine ⟨q, ?_⟩
  rw [← rationalExtend_eq_baseChangeBasePoint]
  apply (baseChangeCoeffEquiv k K G).injective
  rw [baseChangeCoeffEquiv_rationalExtend]
  apply (GaloisPoint.coordinates k G K).injective
  ext a
  rw [GaloisPoint.coordinates_extend]
  change algebraMap k K
    (GaloisPoint.coordinates k G k
      ((rationalCoeffEquiv k G) ((rationalCoeffEquiv k G).symm
        ((GaloisPoint.coordinates k G k).symm d'))) a) = c a
  rw [MulEquiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact hd a

end Points

section Transport

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  {H G : GroupScheme (Spec (CommRingCat.of k))}

/-- Galois transport of a conjugated ground-field subgroup is conjugation by
the transported point. -/
theorem galoisTransport_conjugate_range (i : H ⟶ G) (σ : K ≃ₐ[k] K)
    (g : rationalPoints (baseChanged k K G)) :
    SubgroupFunctor.galoisTransport k K G σ
        (SubgroupFunctor.range
          ((GroupScheme.baseChange (baseMap k K)).map i ≫
            ((baseChanged k K G).innerIso g).hom)) =
      SubgroupFunctor.range
        ((GroupScheme.baseChange (baseMap k K)).map i ≫
          ((baseChanged k K G).innerIso (rationalConjugate k K G σ g)).hom) := by
  change SubgroupFunctor.descentTransport _ _ _ _ _ = _
  rw [SubgroupFunctor.descentTransport_range]
  change SubgroupFunctor.range (radicalGaloisHom _ σ) = _
  rw [radicalGaloisHom_comp_innerIso]
  change SubgroupFunctor.range
    (((GroupScheme.baseChange (galoisBaseMap k K σ)).map
      ((GroupScheme.baseChange (baseMap k K)).map i) ≫
        (descentBaseChangeIso (baseMap k K) (galoisBaseMap k K σ)
          (galoisBaseMap_over k K σ) G).hom) ≫ _) = _
  rw [descentBaseChangeIso_naturality, Category.assoc, SubgroupFunctor.range_iso_comp]

/-- Ground-field subgroup ranges are Galois invariant. -/
theorem galoisTransport_range (i : H ⟶ G) (σ : K ≃ₐ[k] K) :
    SubgroupFunctor.galoisTransport k K G σ
        (SubgroupFunctor.range ((GroupScheme.baseChange (baseMap k K)).map i)) =
      SubgroupFunctor.range ((GroupScheme.baseChange (baseMap k K)).map i) := by
  change SubgroupFunctor.descentTransport _ _ _ _ _ = _
  rw [SubgroupFunctor.descentTransport_range, descentBaseChangeIso_naturality,
    SubgroupFunctor.range_iso_comp]

end Transport

end Langlands.GroupScheme.FiniteFieldBorelPair
