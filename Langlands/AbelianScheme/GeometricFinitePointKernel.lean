import Langlands.AbelianScheme.Basic
import Langlands.AbelianScheme.AlgClosedIsogenyPoints
import Langlands.AbelianScheme.FieldFiniteKernelIsogenyProof
import Langlands.GroupScheme.SchemeActionFiniteTarget

/-! # Finite actual geometric point kernels characterize isogenies -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme

variable {k : Type u} [Field k]
    (A : AbelianScheme (Spec (CommRingCat.of k))) (f : End A)

/-- The kernel of the actual homomorphism on points valued in the base field. -/
abbrev geometricPointKernel :=
  (GroupScheme.pointsHom (groupHom f.asHom) (Over.mk (𝟙 _))).ker

/-- Over an algebraically closed field, finite actual point kernel implies
finite scheme kernel and hence the isogeny property. -/
theorem isogeny_of_finite_geometricPointKernel [IsAlgClosed k]
    [Finite (geometricPointKernel A f)] : GroupScheme.IsIsogeny (groupHom f.asHom) := by
  let K := GroupScheme.kernel (groupHom f.asHom)
  have : LocallyOfFiniteType K.X.hom := by
    rw [← Over.w (GroupScheme.kernelι (groupHom f.asHom)).hom.hom]
    infer_instance
  have : IsProper K.X.hom := by
    rw [← Over.w (GroupScheme.kernelι (groupHom f.asHom)).hom.hom]
    infer_instance
  have : Finite (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ K.X) :=
    Finite.of_equiv (geometricPointKernel A f)
      (GroupScheme.kernelPointsEquiv (groupHom f.asHom) (Over.mk (𝟙 _))).toEquiv.symm
  have : DiscreteTopology K.X.left :=
    GroupScheme.discreteTopology_of_finite_rationalPoints K.X
  have : LocallyQuasiFinite K.X.hom := by
    apply (locallyQuasiFinite_iff_isDiscrete_preimage_singleton (f := K.X.hom)).mpr
    intro y
    exact isDiscrete_iff_discreteTopology.mpr inferInstance
  have : IsFinite K.X.hom := IsFinite.of_isProper_of_locallyQuasiFinite _
  exact GroupScheme.fieldFiniteKernelIsogeny k A.toGrp (groupHom f.asHom)
    inferInstance inferInstance inferInstance inferInstance

/-- For actual abelian endomorphisms, the isogeny property is equivalent to
finiteness of the actual geometric point kernel. -/
theorem isogeny_iff_finite_geometricPointKernel [IsAlgClosed k] :
    GroupScheme.IsIsogeny (groupHom f.asHom) ↔ Finite (geometricPointKernel A f) := by
  constructor
  · intro hf
    exact hf.finite_ker_pointsHom (𝟙 _)
  · intro hf
    let := hf
    exact isogeny_of_finite_geometricPointKernel A f

/-- In particular the Nat.card convention gives zero for every nonisogeny. -/
theorem natCard_geometricPointKernel_eq_zero_of_not_isogeny [IsAlgClosed k]
    (hf : ¬ GroupScheme.IsIsogeny (groupHom f.asHom)) :
    Nat.card (geometricPointKernel A f) = 0 := by
  have : Infinite (geometricPointKernel A f) := by
    rw [← not_finite_iff_infinite]
    exact fun h => hf ((isogeny_iff_finite_geometricPointKernel A f).mpr h)
  exact Nat.card_eq_zero_of_infinite

end Langlands.AbelianScheme
