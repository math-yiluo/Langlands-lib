import Langlands.GroupScheme.Rational.VectorGroupCoordinates
import Langlands.GroupScheme.Rational.VectorCoordinateLieSupport
import Langlands.GroupScheme.Rational.TorusUnipotenceProof

/-! # Coefficient-representation unipotence of actual vector groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]
    {V : GroupScheme (Spec (CommRingCat.of k))}
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {b : AutomorphicAction S.toGrp V} {n : ℕ}
    {χ : characterLattice S}
    {e : ∀ T : Over (Spec (CommRingCat.of k)),
      (T ⟶ V.X) ≃* Multiplicative (Fin n → Γ(T.left, ⊤))}

/-- Single-weight coordinates give homogeneous coordinates with constant label. -/
def IsWeightVectorCoordinates.homogeneousCoordinatesOfWeight
    (he : IsWeightVectorCoordinates b χ e) : HomogeneousVectorCoordinates b where
  dimension := n
  coordinates := e
  weight := fun _ => χ
  naturality := he.1
  action := fun T s x i => congrFun (he.2 T s x) i

variable [IsAffineHom V.X.hom]

/-- Every actual Lie vector has the supplied single weight. -/
theorem IsWeightVectorCoordinates.actionWeightSpace_eq_top
    (he : IsWeightVectorCoordinates b χ e) : actionWeightSpace b χ = ⊤ := by
  let q := he.homogeneousCoordinatesOfWeight
  apply top_unique
  intro X _
  rw [← q.lieBasis.sum_repr X]
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _ (q.lieBasis_mem_weightSpace i)

/-- A nonzero single weight for a split torus excludes zero Lie weight. -/
theorem IsWeightVectorCoordinates.actionWeightSpace_zero_eq_bot
    (he : IsWeightVectorCoordinates b χ e)
    (hS : IsSplitTorus S.toGrp) (hχ : χ ≠ 0) : actionWeightSpace b 0 = ⊥ := by
  have hd :=
    (he.homogeneousCoordinatesOfWeight.independent_weightSpaces hS).pairwiseDisjoint hχ
  change Disjoint (actionWeightSpace b χ) (actionWeightSpace b 0) at hd
  rw [he.actionWeightSpace_eq_top] at hd
  exact top_disjoint.mp hd

end Langlands.GroupScheme.RelativeRoot

namespace Langlands.GroupScheme

/-- The standard vector group is unipotent in the actual all-coefficient
representation sense, in every dimension and characteristic. -/
theorem VectorGroup.isUnipotent (k : Type u) [Field k] (n : ℕ) :
    IsUnipotent (VectorGroup.groupScheme (CommRingCat.of k) n) := by
  let h : RelativeRoot.IsVectorGroupOfDimension
      (VectorGroup.groupScheme (CommRingCat.of k) n) n :=
    ⟨VectorGroup.coordinates (CommRingCat.of k) n,
      VectorGroup.isNaturalVectorCoordinates⟩
  let : IsAffineHom (VectorGroup.groupScheme (CommRingCat.of k) n).X.hom :=
    h.isAffineHom
  let χ : characterLattice (Gm (Spec (CommRingCat.of k))) := 𝟙 _
  have hχ : χ ≠ 0 := by
    intro hz
    have hi := congrArg (gmEndEquiv k) hz
    simp [χ] at hi
  have hw := VectorGroup.isWeightVectorCoordinates_weightAction (n := n) χ
  exact RelativeRoot.torusActionUnipotence k _ h.smooth h.isAffineHom
    h.connectedSpace _ isSplitTorus_gm (VectorGroup.weightAction χ)
    (hw.actionWeightSpace_zero_eq_bot isSplitTorus_gm hχ)

namespace RelativeRoot

variable {k : Type u} [Field k]
    {V : GroupScheme (Spec (CommRingCat.of k))} {n : ℕ}

/-- Natural vector coordinates imply coefficient-representation unipotence. -/
theorem IsVectorGroupOfDimension.isUnipotent
    (h : IsVectorGroupOfDimension V n) : IsUnipotent V :=
  IsUnipotent.of_iso h.iso (VectorGroup.isUnipotent k n)

/-- Every finite-dimensional vector group is unipotent. -/
theorem IsVectorGroup.isUnipotent (h : IsVectorGroup V) : IsUnipotent V := by
  obtain ⟨n, hn⟩ := h
  exact hn.isUnipotent

end RelativeRoot
end Langlands.GroupScheme
