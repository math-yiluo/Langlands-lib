import Langlands.Representation.Plancherel.RationalNormKernelTopology
import Langlands.Representation.CompactCoefficient.Classes
import Langlands.Representation.Filtration.SubquotientAlgebraProof
import Langlands.CategoryTheory.RenardCategoryDecomposition

/-!
# The actual norm-kernel factors of Renard VI.3.4

A compact-class factor consists of actual coproducts of irreducible compact
representatives of that class. The remaining factor excludes every nonzero
compact actual subquotient. No identification with an irreducible-subquotient
block and no category-decomposition theorem are assumed or proved.
-/

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe uF uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
variable (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

local instance rationalNormKernelCategoryPointTopology :
    TopologicalSpace (GroupScheme.rationalPoints G) :=
  rationalPointTopology F G.X

/-- The source's `M(0G)_τ`: actual coproducts of irreducible compact-coefficient
representatives of the specified existing class. Multiplicities may be infinite,
and the empty multiplicity type is permitted. -/
def rationalNormKernelClassSumProperty
    (c : CompactCoefficientClass.{uF, uV} (Plancherel.rationalCommonNormKernel G)) :
    ObjectProperty
      (SmoothRep.{0, uF, uV} ℂ (Plancherel.rationalCommonNormKernel G)) :=
  fun A => ∃ (I : Type uV)
    (D : I → IrreducibleCompactCoefficientRep.{uF, uV}
      (Plancherel.rationalCommonNormKernel G))
    (j : ∀ i, (D i).obj ⟶ A),
    (∀ i, CompactCoefficientClass.ofRep (D i) = c) ∧
      Nonempty (IsColimit (Cofan.mk A j))

/-- The actual full compact-class category of VI.3.4. -/
abbrev RationalNormKernelClassSumCategory
    (c : CompactCoefficientClass.{uF, uV} (Plancherel.rationalCommonNormKernel G)) :=
  (rationalNormKernelClassSumProperty G c).FullSubcategory

/-- The source's `M(0G)_nc`: no nonzero actual subquotient has compact
coefficients against its entire smooth dual. No irreducibility test is imposed
on the subquotient. -/
def rationalNormKernelNoCompactSubquotientProperty :
    ObjectProperty
      (SmoothRep.{0, uF, uV} ℂ (Plancherel.rationalCommonNormKernel G)) :=
  fun A => ∀ D : SmoothRep.{0, uF, uV} ℂ (Plancherel.rationalCommonNormKernel G),
    Nontrivial D → SmoothRep.IsSubquotient D A →
      ¬ HasCompactSmoothDualCoefficients D.representation

/-- The actual full remaining category of VI.3.4. -/
abbrev RationalNormKernelNoncompactCategory :=
  (rationalNormKernelNoCompactSubquotientProperty.{uF, uV} G).FullSubcategory

/-- The compact-class factors and the remaining factor, with `none` indexing
the latter. This reuses the existing compact irreducible class quotient. -/
def rationalNormKernelProductProperties :
    Option (CompactCoefficientClass.{uF, uV} (Plancherel.rationalCommonNormKernel G)) →
      ObjectProperty
        (SmoothRep.{0, uF, uV} ℂ (Plancherel.rationalCommonNormKernel G))
  | none => rationalNormKernelNoCompactSubquotientProperty G
  | some c => rationalNormKernelClassSumProperty G c

omit [LocallyOfFiniteType G.X.hom] in
@[simp]
theorem rationalNormKernelProductProperties_none :
    rationalNormKernelProductProperties.{uF, uV} G none =
      rationalNormKernelNoCompactSubquotientProperty G := rfl

omit [LocallyOfFiniteType G.X.hom] in
@[simp]
theorem rationalNormKernelProductProperties_some
    (c : CompactCoefficientClass.{uF, uV} (Plancherel.rationalCommonNormKernel G)) :
    rationalNormKernelProductProperties G (some c) =
      rationalNormKernelClassSumProperty G c := rfl

/-- The category-decomposition assertion of VI.3.4, using actual coproduct
components and off-diagonal zero morphisms. This definition proves no
decomposition and assumes no KF or projector property. -/
def IsRationalNormKernelCategoryDecomposition : Prop :=
  Renard.IsCategoryDecomposition (rationalNormKernelProductProperties.{uF, uV} G)

variable {G}
  {A B : SmoothRep.{0, uF, uV} ℂ (Plancherel.rationalCommonNormKernel G)}

omit [LocallyOfFiniteType G.X.hom] in
/-- Transport a source class-sum presentation along an ambient isomorphism. -/
theorem rationalNormKernelClassSumProperty_of_iso
    {c : CompactCoefficientClass.{uF, uV} (Plancherel.rationalCommonNormKernel G)}
    (hA : rationalNormKernelClassSumProperty G c A) (e : A ≅ B) :
    rationalNormKernelClassSumProperty G c B := by
  obtain ⟨I, D, j, hD, ⟨hj⟩⟩ := hA
  refine ⟨I, D, fun i => j i ≫ e.hom, hD, ⟨?_⟩⟩
  exact IsColimit.ofIsoColimit hj (Cofan.ext e)

omit [LocallyOfFiniteType G.X.hom] in
/-- The remaining factor is closed under actual subquotients. -/
theorem rationalNormKernelNoCompactSubquotientProperty_of_isSubquotient
    (hA : rationalNormKernelNoCompactSubquotientProperty G A)
    (hBA : SmoothRep.IsSubquotient B A) :
    rationalNormKernelNoCompactSubquotientProperty G B :=
  fun D hD hDB => hA D hD (smoothSubquotientTransitivity ℂ _ A B D hDB hBA)

omit [LocallyOfFiniteType G.X.hom] in
/-- The remaining factor is invariant under ambient isomorphism. -/
theorem rationalNormKernelNoCompactSubquotientProperty_of_iso
    (hA : rationalNormKernelNoCompactSubquotientProperty G A) (e : B ≅ A) :
    rationalNormKernelNoCompactSubquotientProperty G B :=
  fun D hD hDB => hA D hD (hDB.of_iso_right e)

end Langlands.CuspidalSupport
