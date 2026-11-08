import Langlands.Automorphic.OperatorSubquotientCompactDifferentiation
import Langlands.Automorphic.OperatorSubquotientTensorHorizontal
import Langlands.Automorphic.HorizontalDifferentialFinite

/-!
# The horizontal differential on actual automorphic operator quotients

The reduced Lie action of an actual operator quotient is the restriction of its
induced complex Lie action. Its horizontal insertion identity is derived from
full compact equivariance by the quotient compact differentiation, so the
generic Lie algebra cochain differential preserves the quotient horizontal
full-compact-equivariant cochains.
-/

noncomputable section

universe uF

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Langlands.Automorphic

open Langlands.Global
open ArchimedeanGL

variable {F : Type uF} [Field F] [NumberField F] {n : ℕ}

local instance quotientHorizontalDiffRationalGroup :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance quotientHorizontalDiffContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance quotientHorizontalDiffSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance quotientHorizontalDiffFormGroup :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance quotientHorizontalDiffStableGroup :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance quotientHorizontalDiffRealizationGroup (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

namespace OperatorSubquotient

variable (Q : OperatorSubquotient F n)

attribute [local instance 100] LieRing.ofAssociativeRing

/-! ## The reduced Lie action -/

/-- Restrict the quotient's induced complex Lie action to the actual reduced algebra. -/
def reducedLieAction : ReducedComplexLieAlgebra F n →ₗ⁅ℂ⁆ Module.End ℂ Q.Space :=
  Q.complexLieAction.comp (reducedComplexInclusion F n)

theorem reducedLieAction_apply (X : ReducedComplexLieAlgebra F n) (f : Q.Space) :
    Q.reducedLieAction X f = Q.complexLieAction (reducedComplexInclusion F n X) f := rfl

instance quotientReducedLieRingModule :
    LieRingModule (ReducedComplexLieAlgebra F n) Q.Space :=
  LieRingModule.compLieHom Q.Space (reducedComplexInclusion F n)

instance quotientReducedLieModule : LieModule ℂ (ReducedComplexLieAlgebra F n) Q.Space :=
  LieModule.compLieHom Q.Space (reducedComplexInclusion F n)

@[simp] theorem reduced_lie_eq (X : ReducedComplexLieAlgebra F n) (f : Q.Space) :
    ⁅X, f⁆ = Q.reducedLieAction X f := rfl

/-- On a projected representative the reduced quotient operator is the projected
numerator operator. -/
theorem reducedLieAction_projection (X : ReducedComplexLieAlgebra F n) (f : Q.upper.Space) :
    Q.reducedLieAction X (Q.projection f) = Q.projection (Q.upper.reducedLieAction X f) := rfl

/-- The canonical projection is a map of reduced Lie modules. -/
def projectionReducedLieHom :
    Q.upper.Space →ₗ⁅ℂ, ReducedComplexLieAlgebra F n⁆ Q.Space where
  toLinearMap := Q.projection.toLinearMap
  map_lie' := rfl

theorem projectionReducedLieHom_apply (f : Q.upper.Space) :
    Q.projectionReducedLieHom f = Q.projection f := rfl

/-- Restriction through the compact image agrees with the quotient compact Lie action. -/
theorem reducedLieAction_compact (Y : CompactComplexLieAlgebra F n) :
    Q.reducedLieAction (compactToReducedComplex F n Y) = Q.compactLieAction Y :=
  congrArg Q.complexLieAction (reducedComplexInclusion_compact F n Y)

/-- The reduced quotient action commutes with actual finite adelic translation. -/
theorem finiteRepresentation_reducedLieAction (d : FiniteAdelicGL F n)
    (X : ReducedComplexLieAlgebra F n) (f : Q.Space) :
    Q.finiteRepresentation d (Q.reducedLieAction X f) =
      Q.reducedLieAction X (Q.finiteRepresentation d f) :=
  Q.finiteRepresentation_complexLieAction d (reducedComplexInclusion F n X) f

/-- Full compact covariance of the reduced quotient action. -/
theorem compactRepresentation_reducedLieAction (k : standardInfiniteCompact F n)
    (X : ReducedComplexLieAlgebra F n) (f : Q.Space) :
    Q.compactRepresentation k (Q.reducedLieAction X f) =
      Q.reducedLieAction (reducedCompactRepresentation F n k X)
        (Q.compactRepresentation k f) :=
  (Q.compactRepresentation_complexLieAction k (reducedComplexInclusion F n X) f).trans
    (congrArg (fun Z : ComplexLieAlgebra F n => Q.complexLieAction Z (Q.compactRepresentation k f))
      (reducedComplexInclusion_conjugation F n k.val X).symm)

/-! ## The horizontal differential -/

section Differential

variable [NeZero n]

/-- Derive the horizontal insertion identity from quotient full compact equivariance. -/
theorem horizontalCochain_infinitesimal (q : ℕ)
    (f : (ReducedComplexLieAlgebra F n) [⋀^Fin q]→ₗ[ℂ] Q.Space)
    (hf : f ∈ horizontalEquivariantSubmodule F n Q.compactRepresentation q)
    (Y : ReducedComplexLieAlgebra F n) (hY : Y ∈ compactInReducedSubmodule F n)
    (X : Fin q → ReducedComplexLieAlgebra F n) :
    ⁅Y, f X⁆ = ∑ i, f (Function.update X i ⁅Y, X i⁆) := by
  rcases hY with ⟨Z, hZ⟩
  subst hZ
  exact (LinearMap.congr_fun (Q.reducedLieAction_compact Z) (f X)).trans
    (Q.reducedCochain_compact_complex q f hf.2 Z X)

/-- The actual coefficient differential restricted to the quotient horizontal space. -/
def horizontalDifferential (q : ℕ) :
    horizontalEquivariantSubmodule F n Q.compactRepresentation q →ₗ[ℂ]
      horizontalEquivariantSubmodule F n Q.compactRepresentation (q + 1) :=
  Langlands.Cohomology.Lie.horizontalEquivariantDifferential
    (compactInReducedSubmodule F n) (reducedCompactRepresentation F n)
    Q.compactRepresentation
    (fun k X Y => (reducedComplexLieConjugation F n k.val).map_lie X Y)
    Q.compactRepresentation_reducedLieAction q (Q.horizontalCochain_infinitesimal q)

@[simp]
theorem horizontalDifferential_val (q : ℕ)
    (f : horizontalEquivariantSubmodule F n Q.compactRepresentation q) :
    (Q.horizontalDifferential q f).val =
      Langlands.Cohomology.Lie.differential q f.val := rfl

theorem horizontalDifferential_apply (q : ℕ)
    (f : horizontalEquivariantSubmodule F n Q.compactRepresentation q)
    (X : Fin (q + 1) → ReducedComplexLieAlgebra F n) :
    (Q.horizontalDifferential q f).val X =
      Langlands.Cohomology.Lie.differential q f.val X := rfl

end Differential

/-! ## Finite adelic translation -/

/-- Actual quotient finite translation, viewed as a full-compact coefficient intertwiner. -/
def finiteCompactIntertwiner (d : FiniteAdelicGL F n) :
    Q.compactRepresentation.IntertwiningMap Q.compactRepresentation where
  toLinearMap := Q.finiteRepresentation d
  isIntertwining' k := LinearMap.ext (Q.finiteRepresentation_compactRepresentation d k)

/-- The same finite translation is a map of the quotient reduced Lie module. -/
def finiteReducedLieHom (d : FiniteAdelicGL F n) :
    Q.Space →ₗ⁅ℂ, ReducedComplexLieAlgebra F n⁆ Q.Space where
  toLinearMap := Q.finiteRepresentation d
  map_lie' := Q.finiteRepresentation_reducedLieAction d _ _

/-- Finite adelic translation on quotient horizontal full-compact-equivariant cochains. -/
def horizontalFiniteRepresentation (q : ℕ) :
    Representation ℂ (FiniteAdelicGL F n)
      (horizontalEquivariantSubmodule F n Q.compactRepresentation q) where
  toFun d := horizontalMapCoefficients F n q (Q.finiteCompactIntertwiner d)
  map_one' := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    apply AlternatingMap.ext
    intro X
    exact LinearMap.congr_fun (map_one Q.finiteRepresentation) (f.val X)
  map_mul' d e := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    apply AlternatingMap.ext
    intro X
    exact LinearMap.congr_fun (map_mul Q.finiteRepresentation d e) (f.val X)

@[simp]
theorem horizontalFiniteRepresentation_apply (q : ℕ) (d : FiniteAdelicGL F n)
    (f : horizontalEquivariantSubmodule F n Q.compactRepresentation q)
    (X : Fin q → ReducedComplexLieAlgebra F n) :
    (Q.horizontalFiniteRepresentation q d f).val X =
      Q.finiteRepresentation d (f.val X) := rfl

section Differential

variable [NeZero n]

/-- The quotient horizontal differential commutes with every finite translation. -/
theorem horizontalDifferential_finite (q : ℕ) (d : FiniteAdelicGL F n)
    (f : horizontalEquivariantSubmodule F n Q.compactRepresentation q) :
    Q.horizontalDifferential q (Q.horizontalFiniteRepresentation q d f) =
      Q.horizontalFiniteRepresentation (q + 1) d (Q.horizontalDifferential q f) := by
  apply Subtype.ext
  exact (Langlands.Cohomology.Lie.map_differential
    (Q.finiteReducedLieHom d) q f.val).symm

/-- The quotient horizontal differential is a finite adelic intertwiner. -/
def horizontalDifferentialIntertwiner (q : ℕ) :
    (Q.horizontalFiniteRepresentation q).IntertwiningMap
      (Q.horizontalFiniteRepresentation (q + 1)) where
  toLinearMap := Q.horizontalDifferential q
  isIntertwining' d := LinearMap.ext (Q.horizontalDifferential_finite q d)

@[simp]
theorem horizontalDifferentialIntertwiner_toLinearMap (q : ℕ) :
    (Q.horizontalDifferentialIntertwiner q).toLinearMap = Q.horizontalDifferential q := rfl

end Differential

/-! ## The canonical projection from the numerator -/

/-- The canonical projection induces a finite intertwiner of horizontal cochains. -/
def horizontalProjection (q : ℕ) :
    (Q.upper.horizontalFiniteRepresentation q).IntertwiningMap
      (Q.horizontalFiniteRepresentation q) where
  toLinearMap := horizontalMapCoefficients F n q Q.compactProjection
  isIntertwining' d := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    apply AlternatingMap.ext
    intro X
    exact (Q.finiteRepresentation_projection d (f.val X)).symm

@[simp]
theorem horizontalProjection_apply (q : ℕ)
    (f : horizontalEquivariantSubmodule F n Q.upper.compactRepresentation q)
    (X : Fin q → ReducedComplexLieAlgebra F n) :
    (Q.horizontalProjection q f).val X = Q.projection (f.val X) := rfl

/-- A projected cochain vanishes exactly when all its values lie in the denominator. -/
theorem horizontalProjection_eq_zero_iff (q : ℕ)
    (f : horizontalEquivariantSubmodule F n Q.upper.compactRepresentation q) :
    Q.horizontalProjection q f = 0 ↔ ∀ X, f.val X ∈ Q.lower := by
  constructor
  · intro h X
    have hX := congrArg (fun g : horizontalEquivariantSubmodule F n Q.compactRepresentation q =>
      g.val X) h
    exact (Q.projection_eq_zero_iff (f.val X)).mp hX
  · intro h
    apply Subtype.ext
    apply AlternatingMap.ext
    intro X
    exact (Q.projection_eq_zero_iff (f.val X)).mpr (h X)

/-- Projection commutes with the numerator and quotient horizontal differentials. -/
theorem horizontalProjection_differential [NeZero n] (q : ℕ)
    (f : horizontalEquivariantSubmodule F n Q.upper.compactRepresentation q) :
    Q.horizontalProjection (q + 1) (Q.upper.horizontalDifferential q f) =
      Q.horizontalDifferential q (Q.horizontalProjection q f) := by
  apply Subtype.ext
  exact Langlands.Cohomology.Lie.map_differential Q.projectionReducedLieHom q f.val

/-- The projection square is an equality of finite adelic intertwiners. -/
theorem horizontalProjection_differential_comp [NeZero n] (q : ℕ) :
    (Q.horizontalProjection (q + 1)).comp (Q.upper.horizontalDifferentialIntertwiner q) =
      (Q.horizontalDifferentialIntertwiner q).comp (Q.horizontalProjection q) := by
  apply Representation.IntertwiningMap.ext
  exact LinearMap.ext (Q.horizontalProjection_differential q)

/-! ## Whole-operator quotient intertwiners and equivalences -/

variable {Q} {T U : OperatorSubquotient F n}

/-- A whole-operator quotient intertwiner is a map of reduced Lie modules. -/
def reducedLieRestrictionMap (L : Q.representation.IntertwiningMap T.representation) :
    Q.Space →ₗ⁅ℂ, ReducedComplexLieAlgebra F n⁆ T.Space where
  toLinearMap := L.toLinearMap
  map_lie' := fun {X} {f} => LinearMap.congr_fun
    (L.isIntertwining'
      (differentialOperator F n (envelopingGenerator F n (reducedComplexInclusion F n X)))) f

theorem reducedLieRestrictionMap_apply
    (L : Q.representation.IntertwiningMap T.representation) (f : Q.Space) :
    reducedLieRestrictionMap L f = L f := rfl

/-- A whole-operator quotient intertwiner transports the horizontal finite action. -/
def horizontalMap (L : Q.representation.IntertwiningMap T.representation) (q : ℕ) :
    (Q.horizontalFiniteRepresentation q).IntertwiningMap
      (T.horizontalFiniteRepresentation q) where
  toLinearMap := horizontalMapCoefficients F n q (compactRestrictionMap L)
  isIntertwining' d := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    apply AlternatingMap.ext
    intro X
    exact LinearMap.congr_fun (L.isIntertwining' (finiteOperator F n d)) (f.val X)

@[simp]
theorem horizontalMap_apply (L : Q.representation.IntertwiningMap T.representation) (q : ℕ)
    (f : horizontalEquivariantSubmodule F n Q.compactRepresentation q)
    (X : Fin q → ReducedComplexLieAlgebra F n) :
    (horizontalMap L q f).val X = L (f.val X) := rfl

theorem horizontalMap_id (q : ℕ) :
    horizontalMap (Representation.IntertwiningMap.id Q.representation) q =
      Representation.IntertwiningMap.id (Q.horizontalFiniteRepresentation q) := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  apply AlternatingMap.ext
  intro X
  rfl

theorem horizontalMap_comp (L : Q.representation.IntertwiningMap T.representation)
    (M : T.representation.IntertwiningMap U.representation) (q : ℕ) :
    horizontalMap (M.comp L) q = (horizontalMap M q).comp (horizontalMap L q) := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  apply AlternatingMap.ext
  intro X
  rfl

/-- Transport by a quotient intertwiner commutes with the horizontal differentials. -/
theorem horizontalMap_differential [NeZero n]
    (L : Q.representation.IntertwiningMap T.representation) (q : ℕ)
    (f : horizontalEquivariantSubmodule F n Q.compactRepresentation q) :
    horizontalMap L (q + 1) (Q.horizontalDifferential q f) =
      T.horizontalDifferential q (horizontalMap L q f) := by
  apply Subtype.ext
  exact Langlands.Cohomology.Lie.map_differential (reducedLieRestrictionMap L) q f.val

/-- The naturality square is an equality of finite adelic intertwiners. -/
theorem horizontalMap_differential_comp [NeZero n]
    (L : Q.representation.IntertwiningMap T.representation) (q : ℕ) :
    (horizontalMap L (q + 1)).comp (Q.horizontalDifferentialIntertwiner q) =
      (T.horizontalDifferentialIntertwiner q).comp (horizontalMap L q) := by
  apply Representation.IntertwiningMap.ext
  exact LinearMap.ext (horizontalMap_differential L q)

namespace Equivalence

/-- A quotient equivalence retains the actual reduced Lie module. -/
def reducedLieRestriction (e : Q.Equivalence T) :
    Q.Space ≃ₗ⁅ℂ, ReducedComplexLieAlgebra F n⁆ T.Space :=
  { e.toLinearEquiv with
    map_lie' := (reducedLieRestrictionMap e.toIntertwiningMap).map_lie' }

@[simp] theorem reducedLieRestriction_apply (e : Q.Equivalence T) (f : Q.Space) :
    e.reducedLieRestriction f = e f := rfl

/-- Quotient equivalences transport horizontal spaces and their finite actions. -/
def horizontalEquiv (e : Q.Equivalence T) (q : ℕ) :
    (Q.horizontalFiniteRepresentation q).Equiv (T.horizontalFiniteRepresentation q) :=
  Representation.Equiv.mk
    (horizontalCoefficientEquiv F n q e.compactRestriction)
    (horizontalMap e.toIntertwiningMap q).isIntertwining'

@[simp]
theorem horizontalEquiv_apply (e : Q.Equivalence T) (q : ℕ)
    (f : horizontalEquivariantSubmodule F n Q.compactRepresentation q)
    (X : Fin q → ReducedComplexLieAlgebra F n) :
    (e.horizontalEquiv q f).val X = e (f.val X) := rfl

theorem horizontalEquiv_toLinearMap (e : Q.Equivalence T) (q : ℕ) :
    (e.horizontalEquiv q).toLinearEquiv.toLinearMap =
      (horizontalMap e.toIntertwiningMap q).toLinearMap := rfl

/-- The equivalence transports the same differential in every degree. -/
theorem horizontalEquiv_differential [NeZero n] (e : Q.Equivalence T) (q : ℕ)
    (f : horizontalEquivariantSubmodule F n Q.compactRepresentation q) :
    e.horizontalEquiv (q + 1) (Q.horizontalDifferential q f) =
      T.horizontalDifferential q (e.horizontalEquiv q f) :=
  horizontalMap_differential e.toIntertwiningMap q f

end Equivalence

end OperatorSubquotient
end Langlands.Automorphic
