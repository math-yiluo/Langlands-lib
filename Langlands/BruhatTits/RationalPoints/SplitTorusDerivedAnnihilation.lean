import Langlands.GroupScheme.Rational.WeylTorusNorm
import Langlands.GroupScheme.Rational.ReductiveWeylFaithfulness
import Langlands.GroupScheme.Rational.ParabolicPointConjugation
import Langlands.BruhatTits.RationalPoints.CentralDerivedTorsion

/-! # Annihilation of actual derived points in a split torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme
open scoped CategoryTheory.MonObj BigOperators

namespace Langlands.BruhatTits.RationalPoints

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ G) (f : rationalPoints G →* Multiplicative ℝ)
    (x : rationalPoints T.toGrp)

/-- Evaluate an actual torus endomorphism at a fixed rational point and apply
the ambient real homomorphism. -/
def torusEndRealEvaluation : (T ⟶ T) →+ ℝ :=
  (f.comp (rationalPoints.map i)).toAdditiveLeft.comp (evalPoint x)

@[simp] theorem torusEndRealEvaluation_apply (a : T ⟶ T) :
    torusEndRealEvaluation i f x a =
      (f (rationalPoints.map (CommGroupScheme.groupHom a ≫ i) x)).toAdd := rfl

@[simp] theorem torusEndRealEvaluation_id :
    torusEndRealEvaluation i f x (𝟙 T) =
      (f (rationalPoints.map i x)).toAdd := by
  rfl

/-- A normalizer translate of the whole torus point has the original real
value, by ambient conjugation. -/
theorem torusEndRealEvaluation_normalizingAut (n : normalizerPoints i) :
    torusEndRealEvaluation i f x (normalizingAut i n).hom =
      torusEndRealEvaluation i f x (𝟙 T) := by
  change (f ((x ≫ (CommGroupScheme.groupHom (normalizingAut i n).hom).hom.hom) ≫
    i.hom.hom)).toAdd = (f (x ≫ i.hom.hom)).toAdd
  rw [comp_normalizingAut_hom, constantPoint_rationalPoint]
  simp

variable [Mono i.hom.hom.left]

/-- Each actual Weyl translate has the original real value. -/
theorem torusEndRealEvaluation_relativeWeyl (w : relativeWeylGroup i) :
    torusEndRealEvaluation i f x (relativeWeylTorusAction i w).hom =
      torusEndRealEvaluation i f x (𝟙 T) := by
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective w
  exact torusEndRealEvaluation_normalizingAut i f x n

variable [Fintype (relativeWeylGroup i)]

/-- The integral norm of the whole torus point multiplies its real value by
the finite Weyl group order. -/
theorem torusEndRealEvaluation_relativeWeylTorusNorm :
    torusEndRealEvaluation i f x (relativeWeylTorusNorm i) =
      (Fintype.card (relativeWeylGroup i) : ℝ) *
        (f (rationalPoints.map i x)).toAdd := by
  rw [relativeWeylTorusNorm, map_sum]
  simp only [torusEndRealEvaluation_relativeWeyl, torusEndRealEvaluation_id]
  simp [nsmul_eq_mul]

/-- Under actual root-reflection existence, every point of a split torus
whose ambient image lies in the algebraic derived subgroup is annihilated.
Only the original whole point is required to belong to the derived subgroup. -/
theorem map_eq_one_of_splitTorus_mem_derived (hG : IsConnectedReductive G)
    (hT : IsSplitTorus T.toGrp)
    (href : haveI := hG.isAffineHom
      ∀ α ∈ relativeRoots i, ∃ w, IsRelativeReflection i α w)
    (hx : rationalPoints.map i x ∈
      (derivedSubgroup G).carrier (Over.mk (𝟙 _))) :
    f (rationalPoints.map i x) = 1 := by
  let := hG.isAffineHom
  let := hG.smooth
  let := hG.connectedSpace
  have hc := relativeWeylTorusNorm_isCentral i hT href
  have hd := relativeWeylTorusNorm_eval_mem i (derivedSubgroup_isNormal G) x hx
  have hn : f (rationalPoints.map
      (CommGroupScheme.groupHom (relativeWeylTorusNorm i) ≫ i) x) = 1 :=
    centralDerivedPoints_le_ker hG f ⟨hc _ x, hd⟩
  have he : torusEndRealEvaluation i f x (relativeWeylTorusNorm i) = 0 := by
    rw [torusEndRealEvaluation_apply, hn, toAdd_one]
  rw [torusEndRealEvaluation_relativeWeylTorusNorm] at he
  apply toAdd_eq_zero.mp
  exact (mul_eq_zero.mp he).resolve_left (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

omit [Mono i.hom.hom.left] [Fintype (relativeWeylGroup i)] in
/-- For a maximal split torus, reductivity supplies the finite actual Weyl
quotient. Actual root-reflection existence is still an explicit premise. -/
theorem map_eq_one_of_maximalSplitTorus_mem_derived (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i)
    (href : haveI := hG.isAffineHom
      haveI := hi.isSplitSubtorus.mono
      ∀ α ∈ relativeRoots i, ∃ w, IsRelativeReflection i α w)
    (hx : rationalPoints.map i x ∈
      (derivedSubgroup G).carrier (Over.mk (𝟙 _))) :
    f (rationalPoints.map i x) = 1 := by
  let := hG.isAffineHom
  let := hi.isSplitSubtorus.mono
  let := hG.finite_relativeWeylGroup i hi
  let : Fintype (relativeWeylGroup i) := Fintype.ofFinite _
  exact map_eq_one_of_splitTorus_mem_derived i f x hG hi.isSplitSubtorus.1 href hx

end Langlands.BruhatTits.RationalPoints
