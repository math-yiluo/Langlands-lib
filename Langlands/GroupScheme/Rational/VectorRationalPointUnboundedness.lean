import Langlands.GroupScheme.Rational.VectorGroupCoordinates
import Langlands.BruhatTits.RationalPoints.BoundedSetOperations

/-! # Unbounded rational points in natural vector coordinates -/

noncomputable section
universe u

open CategoryTheory AlgebraicGeometry ValuativeRel
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k]
    {V : GroupScheme (Spec (CommRingCat.of k))} {d : ℕ}
    (e : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ V.X) ≃* Multiplicative (Fin d → Γ(T.left, ⊤)))

/-- A natural vector coordinate as an actual global regular function. -/
def globalVectorCoordinate (i : Fin d) : AffineCoordinateRing k V.X :=
  (e V.X (𝟙 V.X)).toAdd i

/-- Evaluation of the global coordinate is the coordinate of the actual rational point. -/
theorem rationalPointAlgebraHom_globalVectorCoordinate [IsAffine V.X.left]
    (he : IsNaturalVectorCoordinates e) (p : rationalPoints V) (i : Fin d) :
    rationalPointAlgebraHom k V.X p (globalVectorCoordinate e i) =
      (Scheme.ΓSpecIso (CommRingCat.of k)).hom ((e _ p).toAdd i) := by
  rw [rationalPointAlgebraHom_apply_appTop]
  have hn := congrFun (he V.X (Over.mk (𝟙 _)) p (𝟙 V.X)) i
  simpa only [Category.comp_id, globalVectorCoordinate] using
    (congrArg (Scheme.ΓSpecIso (CommRingCat.of k)).hom hn).symm

/-- A positive-dimensional vector group has unbounded rational points whenever
some field element is valuatively larger than one. -/
theorem not_isAlgebraicallyBounded_univ_of_naturalVectorCoordinates
    [ValuativeRel k] [IsAffine V.X.left]
    (he : IsNaturalVectorCoordinates e) (hd : 0 < d)
    (hlarge : ∃ t : k, (1 : k) <ᵥ t) :
    ¬ IsAlgebraicallyBounded k V.X (Set.univ : Set (rationalPoints V)) := by
  classical
  intro hB
  let i : Fin d := ⟨0, hd⟩
  obtain ⟨b, hb, hbound⟩ := hB (globalVectorCoordinate e i)
  obtain ⟨t, ht⟩ := hlarge
  let T : Over (Spec (CommRingCat.of k)) := Over.mk (𝟙 _)
  let c : Γ(T.left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of k)).inv (b * t)
  let p : rationalPoints V := (e T).symm (Multiplicative.ofAdd (Pi.single i c))
  have hp := hbound p (Set.mem_univ p)
  rw [rationalPointAlgebraHom_globalVectorCoordinate e he] at hp
  change (Scheme.ΓSpecIso (CommRingCat.of k)).hom
    (((e T) ((e T).symm (Multiplicative.ofAdd (Pi.single i c)))).toAdd i) ≤ᵥ b at hp
  rw [MulEquiv.apply_symm_apply, toAdd_ofAdd, Pi.single_eq_same,
    show (Scheme.ΓSpecIso (CommRingCat.of k)).hom c = b * t from
      (Scheme.ΓSpecIso (CommRingCat.of k)).inv_hom_id_apply (b * t)] at hp
  have hlt := mul_vlt_mul_left (zero_vlt_iff.mpr hb) ht
  rw [one_mul, mul_comm t b] at hlt
  exact hlt hp

end Langlands.GroupScheme.RelativeRoot
