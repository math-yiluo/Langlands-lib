import Langlands.GroupScheme.MatrixRepresentation.StableProjection
import Langlands.GroupScheme.MatrixRepresentation.NormalIntertwiners
import Langlands.GroupScheme.MatrixRepresentation.ComponentIntertwiners
import Langlands.GroupScheme.MatrixRepresentation.DenseRationalStability
import Langlands.GroupScheme.Rational.SubquotientSpectralIntegrality
import Langlands.GroupScheme.Reductive.CharZeroSemisimplicity.TangentStability
import Langlands.GroupScheme.ComponentPointQuotient
import Langlands.Representation.FiniteQuotientProjection

/-! # Actual component-quotient averaging -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme.MatrixRepresentation

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- A subgroup intertwiner gives an intertwiner for rational points in the
identity component, for any supplied open identity-component inclusion. -/
def componentRationalIntertwiner
    (ρ : MatrixRepresentation G n) (σ : MatrixRepresentation G m)
    (i : H ⟶ G) [IsOpenImmersion i.hom.hom.left]
    (hi : Set.range i.hom.hom.left = IdentityComponent.identitySet G)
    (C : Matrix m n k) (hC : Intertwines (ρ.restrict i) (σ.restrict i) C) :
    Representation.IntertwiningMap
      (ρ.rationalAction.comp (IdentityComponent.rationalIdentityKernel G).subtype)
      (σ.rationalAction.comp (IdentityComponent.rationalIdentityKernel G).subtype) where
  toLinearMap := C.mulVecLin
  isIntertwining' g := by
    apply LinearMap.ext
    intro v
    obtain ⟨y, hy⟩ := (IdentityComponent.mem_rationalIdentityKernel_iff_lift G i hi g.val).mp
      g.property
    have h := hC.rationalMatrix y
    rw [rationalMatrix_restrict, rationalMatrix_restrict, hy] at h
    change C *ᵥ ((ρ.rationalMatrix g.val : Matrix n n k) *ᵥ v) =
      (σ.rationalMatrix g.val : Matrix m m k) *ᵥ (C *ᵥ v)
    rw [Matrix.mulVec_mulVec, h, ← Matrix.mulVec_mulVec]

variable (ρ : MatrixRepresentation G n) (σ : MatrixRepresentation G m)
  [Fintype ((rationalPoints G ⧸ IdentityComponent.rationalIdentityKernel G))]
  [Invertible (Fintype.card ((rationalPoints G ⧸ IdentityComponent.rationalIdentityKernel G)) : k)]

/-- The normalized matrix sum over the actual rational-point component quotient. -/
def componentMatrixAverage (C : Matrix m n k) : Matrix m n k :=
  ⅟(Fintype.card ((rationalPoints G ⧸ IdentityComponent.rationalIdentityKernel G)) : k) •
    ∑ q : (rationalPoints G ⧸ IdentityComponent.rationalIdentityKernel G),
      (σ.rationalMatrix q.out : Matrix m m k) * C *
        (ρ.rationalMatrix q.out⁻¹ : Matrix n n k)

/-- The actual matrix sum agrees with ordinary finite-quotient intertwiner
averaging on every coordinate vector. -/
theorem componentMatrixAverage_mulVec
    (i : H ⟶ G) [IsOpenImmersion i.hom.hom.left]
    (hi : Set.range i.hom.hom.left = IdentityComponent.identitySet G)
    (C : Matrix m n k) (hC : Intertwines (ρ.restrict i) (σ.restrict i) C) (v : n → k) :
    componentMatrixAverage ρ σ C *ᵥ v =
      Langlands.FiniteQuotientAveraging.intertwinerAverage ρ.rationalAction σ.rationalAction
        (IdentityComponent.rationalIdentityKernel G)
        (componentRationalIntertwiner ρ σ i hi C hC) v := by
  rw [Langlands.FiniteQuotientAveraging.intertwinerAverage_apply ρ.rationalAction
    σ.rationalAction (IdentityComponent.rationalIdentityKernel G)
    (componentRationalIntertwiner ρ σ i hi C hC) Quotient.out
    (fun q => Quotient.out_eq q)]
  simp only [componentMatrixAverage, Matrix.smul_mulVec, Matrix.sum_mulVec,
    ← Matrix.mulVec_mulVec]
  rfl

/-- The normalized component average of an actual identity-component
intertwiner is an actual ambient intertwiner. -/
theorem intertwines_componentMatrixAverage
    [IsAlgClosed k] [LocallyOfFiniteType G.X.hom]
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    (i : H ⟶ G) [IsOpenImmersion i.hom.hom.left]
    (hi : Set.range i.hom.hom.left = IdentityComponent.identitySet G)
    (hN : (SubgroupFunctor.range i).IsNormal)
    (C : Matrix m n k) (hC : Intertwines (ρ.restrict i) (σ.restrict i) C) :
    Intertwines ρ σ (componentMatrixAverage ρ σ C) := by
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  apply intertwines_of_identityComponent_and_rationalMatrix i hi ρ σ _
  · apply Intertwines.smul
    apply intertwines_sum
    intro q _
    exact hC.normalConjugate ρ σ i hN q.out
  · intro g
    apply Matrix.ext_of_mulVec_single
    intro j
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rw [componentMatrixAverage_mulVec ρ σ i hi C hC,
      componentMatrixAverage_mulVec ρ σ i hi C hC]
    exact (Langlands.FiniteQuotientAveraging.intertwinerAverage ρ.rationalAction
      σ.rationalAction (IdentityComponent.rationalIdentityKernel G)
      (componentRationalIntertwiner ρ σ i hi C hC)).isIntertwining _ _ g (Pi.single j 1)

omit σ in
/-- A projection onto an ambient stable subspace, equivariant under the actual
identity component, averages to an actual ambient equivariant projection. -/
theorem exists_equivariantProjection_of_componentProjection
    [IsAlgClosed k] [LocallyOfFiniteType G.X.hom]
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    (i : H ⟶ G) [IsOpenImmersion i.hom.hom.left]
    (hi : Set.range i.hom.hom.left = IdentityComponent.identitySet G)
    (hN : (SubgroupFunctor.range i).IsNormal)
    (V : Submodule k (n → k)) (hV : ρ.IsStableSubspace V)
    (P : Module.End k (n → k)) (hP : (ρ.restrict i).IsEquivariantProjection V P) :
    ∃ Q : Module.End k (n → k), ρ.IsEquivariantProjection V Q := by
  let p := componentRationalIntertwiner ρ ρ i hi (LinearMap.toMatrix' P) hP.1
  let av := Langlands.FiniteQuotientAveraging.intertwinerAverage ρ.rationalAction
    ρ.rationalAction (IdentityComponent.rationalIdentityKernel G) p
  have hp : p.toLinearMap = P := by
    apply LinearMap.ext
    intro v
    exact LinearMap.toMatrix'_mulVec P v
  let U : Subrepresentation ρ.rationalAction :=
    { toSubmodule := V
      apply_mem_toSubmodule g _ hv := hV.rationalMatrix_mulVec_mem g hv }
  have havProj : LinearMap.IsProj V av.toLinearMap := by
    have hproj : LinearMap.IsProj U.toSubmodule p.toLinearMap := by
      rw [hp]
      exact hP.2
    exact Langlands.FiniteQuotientAveraging.intertwinerAverage_isProj ρ.rationalAction
      (IdentityComponent.rationalIdentityKernel G) U p hproj
  have havMat : LinearMap.toMatrix' av.toLinearMap =
      componentMatrixAverage ρ ρ (LinearMap.toMatrix' P) := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_toMatrix']
    apply LinearMap.ext
    intro v
    exact (componentMatrixAverage_mulVec ρ ρ i hi (LinearMap.toMatrix' P) hP.1 v).symm
  refine ⟨av.toLinearMap, ?_, havProj⟩
  rw [havMat]
  exact intertwines_componentMatrixAverage ρ ρ i hi hN (LinearMap.toMatrix' P) hP.1

end Langlands.GroupScheme.MatrixRepresentation
