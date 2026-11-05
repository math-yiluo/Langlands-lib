import Langlands.GroupScheme.IntegralModel
import Langlands.GroupScheme.GaloisPointNorm
import Langlands.GroupScheme.AffinePointAutomorphisms
import Langlands.GroupScheme.CocharacterTransport
import Langlands.GroupScheme.Rational.Characters
import Langlands.AlgebraicGeometry.PointTopology.RationalPoints
import Langlands.GroupScheme.MultiplicativePointTopology
import Mathlib.RingTheory.Norm.Transitivity

/-! # Rational-point comparisons for finite-Galois group-scheme norms -/

noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GaloisPointComparison

open GaloisPoint
open Langlands.AlgebraicGeometry.PointTopology

variable (k L : Type u) [Field k] [Field L] [Algebra k L]

/-- The actual morphism of base schemes induced by the field inclusion. -/
abbrev baseMap := Spec.map (CommRingCat.ofHom (algebraMap k L))

/-- The actual base change of the existing group scheme. -/
abbrev baseChanged (G : GroupScheme (Spec (CommRingCat.of k))) :=
  (GroupScheme.baseChange (baseMap k L)).obj G

variable (G : GroupScheme (Spec (CommRingCat.of k)))

/-- The identity-test and base-coefficient conventions agree multiplicatively. -/
def rationalCoeffEquiv : rationalPoints G ≃* G.affinePoints (CommAlgCat.of k k) :=
  (G.points.mapIso (ringTestSelfIso k).op).groupIsoToMulEquiv

@[simp] theorem rationalCoeffEquiv_left (x : rationalPoints G) :
    (rationalCoeffEquiv k G x).left = x.left := by
  change 𝟙 _ ≫ x.left = x.left
  simp

/-- This multiplicative comparison has exactly the existing rationalPointEquiv as carrier map. -/
theorem rationalCoeffEquiv_eq (x : rationalPoints G) :
    rationalCoeffEquiv k G x = rationalPointEquiv k G.X x := by
  apply Over.OverMorphism.ext
  rw [rationalCoeffEquiv_left, rationalPointEquiv_left]

/-- Rational points of the actual base change are the existing L-coefficient points. -/
def baseChangeCoeffEquiv : rationalPoints (baseChanged k L G) ≃*
    G.affinePoints (CommAlgCat.of k L) :=
  baseChangeBasePointsEquiv (baseMap k L) G

/-- The comparison uses the projection of the actual scheme pullback. -/
@[simp] theorem baseChangeCoeffEquiv_left (x : rationalPoints (baseChanged k L G)) :
    (baseChangeCoeffEquiv k L G x).left =
      x.left ≫ CategoryTheory.Limits.pullback.fst G.X.hom (baseMap k L) :=
  baseChangeBasePointsEquiv_left (baseMap k L) G x

section Naturality

variable {G} {H : GroupScheme (Spec (CommRingCat.of k))}

/-- The rational/coefficient comparison commutes with actual group-scheme maps. -/
theorem rationalCoeffEquiv_map (f : G ⟶ H) (x : rationalPoints G) :
    rationalCoeffEquiv k H (rationalPoints.map f x) =
      G.affinePointsTarget f (CommAlgCat.of k k) (rationalCoeffEquiv k G x) := by
  rw [rationalPoints.map_apply, affinePointsTarget_apply]
  apply Over.OverMorphism.ext
  simp only [rationalCoeffEquiv_left, Over.comp_left]


/-- The pullback comparison commutes with the actual base-changed morphism. -/
theorem baseChangeCoeffEquiv_map (f : G ⟶ H) (x : rationalPoints (baseChanged k L G)) :
    baseChangeCoeffEquiv k L H
        (rationalPoints.map ((GroupScheme.baseChange (baseMap k L)).map f) x) =
      G.affinePointsTarget f (CommAlgCat.of k L) (baseChangeCoeffEquiv k L G x) := by
  exact baseChangeBasePointsEquiv_comp (baseMap k L) f x

end Naturality

/-- Extension on the Library's existing rational-point carriers. -/
def rationalExtend : rationalPoints G →* rationalPoints (baseChanged k L G) :=
  (baseChangeCoeffEquiv k L G).symm.toMonoidHom.comp
    ((extend k L G).comp (rationalCoeffEquiv k G).toMonoidHom)

@[simp] theorem baseChangeCoeffEquiv_rationalExtend (x : rationalPoints G) :
    baseChangeCoeffEquiv k L G (rationalExtend k L G x) =
      extend k L G (rationalCoeffEquiv k G x) := by
  simp [rationalExtend]

/-- Extension is pullback of the original section along the actual base map. -/
theorem rationalExtend_fst (x : rationalPoints G) :
    (rationalExtend k L G x).left ≫
        CategoryTheory.Limits.pullback.fst G.X.hom (baseMap k L) =
      baseMap k L ≫ x.left := by
  have h := congrArg (fun p => p.left) (baseChangeCoeffEquiv_rationalExtend k L G x)
  rw [baseChangeCoeffEquiv_left] at h
  change _ = baseMap k L ≫ (rationalCoeffEquiv k G x).left at h
  rwa [rationalCoeffEquiv_left] at h

/-- The Galois automorphism on rational points of the actual base change. -/
def rationalConjugate (σ : L ≃ₐ[k] L) : MulAut (rationalPoints (baseChanged k L G)) :=
  ((baseChangeCoeffEquiv k L G).trans (G.affinePointAut σ)).trans
    (baseChangeCoeffEquiv k L G).symm

@[simp] theorem baseChangeCoeffEquiv_rationalConjugate (σ : L ≃ₐ[k] L)
    (x : rationalPoints (baseChanged k L G)) :
    baseChangeCoeffEquiv k L G (rationalConjugate k L G σ x) =
      conjugate k L G σ (baseChangeCoeffEquiv k L G x) := by
  simp only [rationalConjugate, MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
  rfl

@[simp] theorem rationalConjugate_one (x : rationalPoints (baseChanged k L G)) :
    rationalConjugate k L G 1 x = x := by
  apply (baseChangeCoeffEquiv k L G).injective
  simp

theorem rationalConjugate_mul (σ τ : L ≃ₐ[k] L)
    (x : rationalPoints (baseChanged k L G)) :
    rationalConjugate k L G (σ * τ) x =
      rationalConjugate k L G σ (rationalConjugate k L G τ x) := by
  apply (baseChangeCoeffEquiv k L G).injective
  simp only [baseChangeCoeffEquiv_rationalConjugate, conjugate_mul]

variable [FiniteDimensional k L] [IsGalois k L]
variable (T : CommGroupScheme (Spec (CommRingCat.of k))) [IsAffine T.X.left]

/-- The descended norm on rationalPoints of the actual commutative base change. -/
def rationalNorm :
    rationalPoints ((CommGroupScheme.baseChange (baseMap k L)).obj T).toGrp →*
      rationalPoints T.toGrp :=
  (rationalCoeffEquiv k T.toGrp).symm.toMonoidHom.comp
    ((GaloisPoint.norm k L T).comp (baseChangeCoeffEquiv k L T.toGrp).toMonoidHom)

/-- The rational norm is the constructed coefficient norm under the explicit comparisons. -/
@[simp] theorem rationalCoeffEquiv_rationalNorm
    (x : rationalPoints ((CommGroupScheme.baseChange (baseMap k L)).obj T).toGrp) :
    rationalCoeffEquiv k T.toGrp (rationalNorm k L T x) =
      GaloisPoint.norm k L T (baseChangeCoeffEquiv k L T.toGrp x) := by
  exact (rationalCoeffEquiv k T.toGrp).apply_symm_apply
    (GaloisPoint.norm k L T (baseChangeCoeffEquiv k L T.toGrp x))

@[simp] theorem rationalNorm_extend (x : rationalPoints T.toGrp) :
    rationalNorm k L T (rationalExtend k L T.toGrp x) = x ^ Module.finrank k L := by
  apply (rationalCoeffEquiv k T.toGrp).injective
  simp

/-- The rational norm extends to the product of all rational-point Galois conjugates. -/
theorem rationalExtend_norm
    (x : rationalPoints ((CommGroupScheme.baseChange (baseMap k L)).obj T).toGrp) :
    rationalExtend k L T.toGrp (rationalNorm k L T x) =
      ∏ σ : L ≃ₐ[k] L, rationalConjugate k L T.toGrp σ x := by
  apply (baseChangeCoeffEquiv k L T.toGrp).injective
  simp only [baseChangeCoeffEquiv_rationalExtend, rationalCoeffEquiv_rationalNorm,
    GaloisPoint.extend_norm, map_prod, baseChangeCoeffEquiv_rationalConjugate]

end Langlands.GroupScheme.GaloisPointComparison

namespace Langlands.GroupScheme.GaloisPoint

variable (k L : Type u) [Field k] [Field L] [Algebra k L]

/-- The coefficient inclusion for Gm is the usual map on field units. -/
theorem gm_units_extend
    (x : affinePoints (Gm (Spec (CommRingCat.of k))).toGrp (CommAlgCat.of k k)) :
    Gm.affineUnitsEquiv (CommRingCat.of k) (CommAlgCat.of k L)
        (extend k L (Gm (Spec (CommRingCat.of k))).toGrp x) =
      Units.map (algebraMap k L).toMonoidHom
        (Gm.affineUnitsEquiv (CommRingCat.of k) (CommAlgCat.of k k) x) :=
  Gm.affineUnitsEquiv_naturality (CommRingCat.of k)
    (CommAlgCat.ofHom (Algebra.ofId k L)) x

/-- Galois conjugation for Gm is the usual action on field units. -/
theorem gm_units_conjugate (σ : L ≃ₐ[k] L)
    (x : affinePoints (Gm (Spec (CommRingCat.of k))).toGrp (CommAlgCat.of k L)) :
    Gm.affineUnitsEquiv (CommRingCat.of k) (CommAlgCat.of k L)
        (conjugate k L (Gm (Spec (CommRingCat.of k))).toGrp σ x) =
      Units.map σ.toMonoidHom
        (Gm.affineUnitsEquiv (CommRingCat.of k) (CommAlgCat.of k L) x) :=
  Gm.affineUnitsEquiv_naturality (CommRingCat.of k) (CommAlgCat.ofHom σ.toAlgHom) x

/-- At the base field, the rational/coefficient comparison preserves the existing Gm unit. -/
theorem gm_units_rationalCoeffEquiv
    (x : rationalPoints (Gm (Spec (CommRingCat.of k))).toGrp) :
    Gm.affineUnitsEquiv (CommRingCat.of k) (CommAlgCat.of k k)
        (GaloisPointComparison.rationalCoeffEquiv k (Gm (Spec (CommRingCat.of k))).toGrp x) =
      Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of k))) x := by
  apply Units.ext
  change (Scheme.ΓSpecIso (CommRingCat.of k)).hom
      (Gm.pointsEquiv _ _ (GaloisPointComparison.rationalCoeffEquiv k
        (Gm (Spec (CommRingCat.of k))).toGrp x)).val =
    (Scheme.ΓSpecIso (CommRingCat.of k)).hom (Gm.pointsEquiv _ _ x).val
  rw [Gm.pointsEquiv_val, Gm.pointsEquiv_val, GaloisPointComparison.rationalCoeffEquiv_left]
  rfl

/-- The Gm comparison for the actual base change preserves its existing global-units equivalence. -/
theorem gm_units_baseChangeCoeffEquiv
    (x : rationalPoints (GaloisPointComparison.baseChanged k L
      (Gm (Spec (CommRingCat.of k))).toGrp)) :
    Gm.affineUnitsEquiv (CommRingCat.of k) (CommAlgCat.of k L)
        (GaloisPointComparison.baseChangeCoeffEquiv k L
          (Gm (Spec (CommRingCat.of k))).toGrp x) =
      Units.map (Scheme.ΓSpecIso (CommRingCat.of L)).hom.hom.toMonoidHom
        (Gm.baseChangeUnitsEquiv (GaloisPointComparison.baseMap k L)
          (Over.mk (𝟙 (Spec (CommRingCat.of L)))) x) := by
  apply Units.ext
  change (Scheme.ΓSpecIso (CommRingCat.of L)).hom
      (Gm.pointsEquiv _ _ (GaloisPointComparison.baseChangeCoeffEquiv k L
        (Gm (Spec (CommRingCat.of k))).toGrp x)).val =
    (Scheme.ΓSpecIso (CommRingCat.of L)).hom
      (Gm.pointsEquiv _ _ (baseChangePointsEquiv (GaloisPointComparison.baseMap k L)
        (Gm (Spec (CommRingCat.of k))).toGrp _ x)).val
  rw [Gm.pointsEquiv_val, Gm.pointsEquiv_val,
    GaloisPointComparison.baseChangeCoeffEquiv_left, baseChangePointsEquiv_left]
  rfl

variable [FiniteDimensional k L] [IsGalois k L]

private instance gm_isAffine : IsAffine (Gm (Spec (CommRingCat.of k))).X.left := by
  change IsAffine (CategoryTheory.Limits.pullback
    (Spec.map (CommRingCat.ofHom (LaurentPolynomial.C (R := ULift.{u} ℤ))))
    (Gm.toSpecZ (Spec (CommRingCat.of k))))
  infer_instance

/-- Under the existing units equivalences, the descended point norm is the field norm on units. -/
theorem gm_units_norm
    (x : affinePoints (Gm (Spec (CommRingCat.of k))).toGrp (CommAlgCat.of k L)) :
    Gm.affineUnitsEquiv (CommRingCat.of k) (CommAlgCat.of k k)
        (norm k L (Gm (Spec (CommRingCat.of k))) x) =
      Units.map (Algebra.norm k)
        (Gm.affineUnitsEquiv (CommRingCat.of k) (CommAlgCat.of k L) x) := by
  apply Units.ext
  apply (algebraMap k L).injective
  change algebraMap k L _ = algebraMap k L (Algebra.norm k _)
  rw [Algebra.norm_eq_prod_automorphisms]
  have h := congrArg
    (fun p => (Gm.affineUnitsEquiv (CommRingCat.of k) (CommAlgCat.of k L) p : L))
    (extend_norm k L (Gm (Spec (CommRingCat.of k))) x)
  calc
    _ = (Gm.affineUnitsEquiv (CommRingCat.of k) (CommAlgCat.of k L)
        (extend k L (Gm (Spec (CommRingCat.of k))).toGrp
          (norm k L (Gm (Spec (CommRingCat.of k))) x)) : L) :=
      (congrArg (fun u : Lˣ => (u : L))
        (gm_units_extend k L (norm k L (Gm (Spec (CommRingCat.of k))) x))).symm
    _ = ∏ σ : L ≃ₐ[k] L,
        (Gm.affineUnitsEquiv (CommRingCat.of k) (CommAlgCat.of k L)
          (conjugate k L (Gm (Spec (CommRingCat.of k))).toGrp σ x) : L) := by
      exact h.trans (by rw [map_prod, Units.coe_prod])
    _ = _ := Finset.prod_congr rfl (fun σ _ =>
      congrArg (fun u : Lˣ => (u : L)) (gm_units_conjugate k L σ x))

/-- The norm on the existing rational-point carriers is the usual finite-extension unit norm. -/
theorem gm_rational_units_norm
    (x : rationalPoints ((CommGroupScheme.baseChange (GaloisPointComparison.baseMap k L)).obj
      (Gm (Spec (CommRingCat.of k)))).toGrp) :
    Gm.affinePointsEquiv (𝟙 (Spec (CommRingCat.of k)))
        (GaloisPointComparison.rationalNorm k L (Gm (Spec (CommRingCat.of k))) x) =
      Units.map (Algebra.norm k)
        (Units.map (Scheme.ΓSpecIso (CommRingCat.of L)).hom.hom.toMonoidHom
          (Gm.baseChangeUnitsEquiv (GaloisPointComparison.baseMap k L)
            (Over.mk (𝟙 (Spec (CommRingCat.of L)))) x)) := by
  rw [← gm_units_rationalCoeffEquiv k,
    GaloisPointComparison.rationalCoeffEquiv_rationalNorm, gm_units_norm,
    gm_units_baseChangeCoeffEquiv]

end Langlands.GroupScheme.GaloisPoint
