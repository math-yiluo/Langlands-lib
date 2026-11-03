import Langlands.GroupScheme.AutomorphicAction.BaseChange
import Langlands.GroupScheme.Rational.VectorLinearAction
import Langlands.GroupScheme.Lie.BaseChange

/-! # Actual vector coordinates under field extension -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]
    {H V : GroupScheme (Spec (CommRingCat.of k))} {d : ℕ}
    (e : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ V.X) ≃* Multiplicative (Fin d → Γ(T.left, ⊤)))
    (K : Type u) [Field K] [Algebra k K]

/-- Pull back the supplied vector coordinates along a field extension. -/
def vectorBaseChangeCoordinates (T : Over (Spec (CommRingCat.of K))) :
    (T ⟶ ((GroupScheme.baseChange (algebraBaseMap k K)).obj V).X) ≃*
      Multiplicative (Fin d → Γ(T.left, ⊤)) :=
  (baseChangePointsEquiv (algebraBaseMap k K) V T).trans
    (e ((Over.map (algebraBaseMap k K)).obj T))

variable {e K}

/-- Natural vector coordinates remain natural after field extension. -/
theorem IsNaturalVectorCoordinates.baseChange (he : IsNaturalVectorCoordinates e) :
    IsNaturalVectorCoordinates (vectorBaseChangeCoordinates e K) := by
  intro T W f v
  simp only [vectorBaseChangeCoordinates, MulEquiv.trans_apply,
    baseChangePointsEquiv_naturality]
  exact he _ _ ((Over.map (algebraBaseMap k K)).map f)
    (baseChangePointsEquiv (algebraBaseMap k K) V T v)

/-- Scalar-linearity of the actual action persists under field extension. -/
theorem IsLinearVectorCoordinates.baseChange {a : AutomorphicAction H V}
    (he : IsLinearVectorCoordinates a e) :
    IsLinearVectorCoordinates (a.baseChange (algebraBaseMap k K))
      (vectorBaseChangeCoordinates e K) := by
  refine ⟨he.1.baseChange, ?_⟩
  intro T h c v
  simpa only [vectorBaseChangeCoordinates, MulEquiv.trans_apply,
    MulEquiv.symm_trans_apply,
    AutomorphicAction.baseChangePointsEquiv_act, MulEquiv.apply_symm_apply] using
    he.2 ((Over.map (algebraBaseMap k K)).obj T)
      (baseChangePointsEquiv (algebraBaseMap k K) H T h) c
      (baseChangePointsEquiv (algebraBaseMap k K) V T v)

/-- Restriction of the acting group preserves the same scalar-linear coordinates. -/
theorem IsLinearVectorCoordinates.restrict {a : AutomorphicAction H V}
    (he : IsLinearVectorCoordinates a e) {J : GroupScheme (Spec (CommRingCat.of k))}
    (f : J ⟶ H) : IsLinearVectorCoordinates (a.restrict f) e := by
  refine ⟨he.1, ?_⟩
  intro T h c v
  simpa only [AutomorphicAction.restrict_act] using he.2 T (h ≫ f.hom.hom) c v

/-- On affine tests the transported coordinates are the original coordinates
under the actual affine base-change comparison. -/
theorem vectorAffineCoordinates_baseChange
    (he : IsNaturalVectorCoordinates e)
    {A : Type u} [CommRing A] [Algebra k A] [Algebra K A] [IsScalarTower k K A]
    (v : Lie.AffinePoints ((GroupScheme.baseChange (algebraBaseMap k K)).obj V) A) :
    vectorAffineCoordinates (vectorBaseChangeCoordinates e K) A v =
      vectorAffineCoordinates e A (Lie.affineBaseChangeEquiv k K V A v) := by
  apply Multiplicative.toAdd.injective
  funext j
  change (Scheme.ΓSpecIso (CommRingCat.of A)).hom
      ((e _ (baseChangePointsEquiv (algebraBaseMap k K) V _ v)).toAdd j) =
    (Scheme.ΓSpecIso (CommRingCat.of A)).hom
      ((e _ ((Lie.affineBaseTestIso k K A).inv ≫
        baseChangePointsEquiv (algebraBaseMap k K) V _ v)).toAdd j)
  rw [he _ _ (Lie.affineBaseTestIso k K A).inv]
  rfl

end Langlands.GroupScheme.RelativeRoot
