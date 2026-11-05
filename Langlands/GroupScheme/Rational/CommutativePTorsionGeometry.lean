import Langlands.GroupScheme.Rational.CommutativePTorsionVectorProof
import Langlands.GroupScheme.Rational.UnipotentPointsExponent
import Langlands.GroupScheme.Rational.VectorGroupUnipotent
import Langlands.GroupScheme.Unipotent.FieldReflectionProof
import Langlands.GroupScheme.GeometricConnectedness
import Langlands.AbelianScheme.KernelBaseChange

/-! # Geometric vector coordinates and unipotence of commutative p-torsion groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- An exponent valid on every scheme test remains valid after any base change. -/
theorem HasUniformPowerExponent.baseChange {S T : Scheme.{u}}
    {G : GroupScheme S} {q : ℕ} (hG : HasUniformPowerExponent G q) (b : T ⟶ S) :
    HasUniformPowerExponent ((GroupScheme.baseChange b).obj G) q := by
  intro X x
  apply (baseChangePointsEquiv b G X).injective
  rw [map_pow, map_one]
  exact hG _ _

/-- An actual group-scheme isomorphism transports an exponent on all tests. -/
theorem HasUniformPowerExponent.of_iso {S : Scheme.{u}} {G H : GroupScheme S}
    {q : ℕ} (hH : HasUniformPowerExponent H q) (e : G ≅ H) :
    HasUniformPowerExponent G q := by
  intro T x
  apply (cancel_mono e.hom.hom.hom).1
  rw [MonObj.pow_comp, MonObj.one_comp]
  exact hH _ _

namespace CommutativePTorsion

variable {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (G : CommGroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (hG : HasUniformPowerExponent G.toGrp p)

include p hG in
/-- The algebraic-closure base change has natural vector coordinates on every test. -/
theorem isVectorGroup_algebraicClosure :
    RelativeRoot.IsVectorGroup
      ((GroupScheme.baseChange (algebraBaseMap k (AlgebraicClosure k))).obj G.toGrp) := by
  let b := algebraBaseMap k (AlgebraicClosure k)
  let H := (CommGroupScheme.baseChange b).obj G
  have hsm : Smooth H.X.hom := by
    change Smooth (CategoryTheory.Limits.pullback.snd G.X.hom b)
    infer_instance
  have haff : IsAffineHom H.X.hom := by
    change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
    infer_instance
  have hconn : ConnectedSpace H.X.left :=
    Langlands.GroupScheme.connectedSpace_baseChange_of_smooth_affine G.toGrp b
  exact RelativeRoot.smoothCommutativePTorsionVector (AlgebraicClosure k) p H
    hsm haff hconn (hG.baseChange b)

/-- A finite dimension for the geometric vector group, including dimension zero. -/
def geometricVectorDimension : ℕ :=
  Classical.choose (isVectorGroup_algebraicClosure p G hG)

/-- The chosen dimension carries natural additive coordinates on all relative tests. -/
theorem geometricVectorDimension_spec :
    RelativeRoot.IsVectorGroupOfDimension
      ((GroupScheme.baseChange (algebraBaseMap k (AlgebraicClosure k))).obj G.toGrp)
      (geometricVectorDimension p G hG) :=
  Classical.choose_spec (isVectorGroup_algebraicClosure p G hG)

/-- An actual geometric group-scheme isomorphism to the standard vector group. -/
def geometricVectorIso :
    (GroupScheme.baseChange (algebraBaseMap k (AlgebraicClosure k))).obj G.toGrp ≅
      VectorGroup.groupScheme (CommRingCat.of (AlgebraicClosure k))
        (geometricVectorDimension p G hG) :=
  (geometricVectorDimension_spec p G hG).iso

include p hG in
/-- A smooth connected commutative affine group killed by `p` is unipotent over
its original field, in the existing coefficient-representation sense. -/
theorem isUnipotent : IsUnipotent G.toGrp := by
  have h :=
    (isVectorGroup_algebraicClosure p G hG).isUnipotent
  exact h.of_baseChange

end CommutativePTorsion
end Langlands.GroupScheme
