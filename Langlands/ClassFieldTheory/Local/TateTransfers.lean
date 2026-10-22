import Langlands.ClassFieldTheory.Local.Corestriction
import Langlands.Cohomology.Tate.Reindex

/-! # Restriction and corestriction on local Tate cohomology -/

noncomputable section

open CategoryTheory

namespace Langlands.ClassFieldTheory.Local

universe u v w

variable (K : Type v) (L : Type w) (M : Type u)
  [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]

/-- The actual unit coefficient modules agree under the subgroup identification. -/
def relativeSubgroupUnitsIso :
    Rep.res (relativeGaloisSubgroupEquiv K L M).symm.toMonoidHom
      (unitsRepresentation L M) ≅
        Rep.res (relativeGaloisSubgroup K L M).subtype (unitsRepresentation K M) :=
  Rep.mkIso (Representation.Equiv.mk
    (LinearEquiv.refl IntegerScalars.{u} (Additive Mˣ)) (fun σ => by
      apply LinearMap.ext
      intro x
      apply Units.ext
      exact congrArg (fun τ : Gal(M/K) => τ (↑(show Mˣ from x) : M))
        (congrArg Subtype.val
          ((relativeGaloisSubgroupEquiv K L M).apply_symm_apply σ))))

/-- Trivial integral coefficients agree under the same group identification. -/
def integralSubgroupCoefficientsIso :
    Rep.res (relativeGaloisSubgroupEquiv K L M).symm.toMonoidHom
      (Rep.trivial IntegerScalars.{u} Gal(M/L) IntegerScalars.{u}) ≅
        Rep.res (relativeGaloisSubgroup K L M).subtype
          (Rep.trivial IntegerScalars.{u} Gal(M/K) IntegerScalars.{u}) :=
  Rep.mkIso (Representation.Equiv.mk
    (LinearEquiv.refl IntegerScalars.{u} IntegerScalars.{u}) (fun _ => rfl))

variable [FiniteDimensional K M] [FiniteDimensional L M]

/-- Reindex actual relative Tate cohomology by the image of scalar restriction. -/
def relativeSubgroupTateIso (n : ℤ) :
    relativeTateCohomology L M n ≅
      letI := Fintype.ofFinite (relativeGaloisSubgroup K L M)
      tateCohomology
        (Rep.res (relativeGaloisSubgroup K L M).subtype (unitsRepresentation K M)) n := by
  letI := Fintype.ofFinite Gal(M/L)
  letI := Fintype.ofFinite (relativeGaloisSubgroup K L M)
  exact Langlands.Tate.reindexIso (relativeGaloisSubgroupEquiv K L M)
    (relativeSubgroupUnitsIso K L M) n

/-- The same actual Tate reindexing for the trivial integral coefficient module. -/
def integralSubgroupTateIso (n : ℤ) :
    integralTateCohomology L M n ≅
      letI := Fintype.ofFinite (relativeGaloisSubgroup K L M)
      tateCohomology
        (Rep.res (relativeGaloisSubgroup K L M).subtype
          (Rep.trivial IntegerScalars.{u} Gal(M/K) IntegerScalars.{u})) n := by
  letI := Fintype.ofFinite Gal(M/L)
  letI := Fintype.ofFinite (relativeGaloisSubgroup K L M)
  exact Langlands.Tate.reindexIso (relativeGaloisSubgroupEquiv K L M)
    (integralSubgroupCoefficientsIso K L M) n

/-- Unit-valued Tate restriction in every integer degree. -/
def relativeTateRestriction (n : ℤ) :
    relativeTateCohomology K M n →ₗ[IntegerScalars.{u}] relativeTateCohomology L M n := by
  letI := Fintype.ofFinite Gal(M/K)
  letI := Fintype.ofFinite (relativeGaloisSubgroup K L M)
  letI := Fintype.ofFinite (Gal(M/K) ⧸ relativeGaloisSubgroup K L M)
  exact (relativeSubgroupTateIso K L M n).symm.toLinearEquiv.toLinearMap.comp
    (Langlands.Tate.restriction (relativeGaloisSubgroup K L M)
      (unitsRepresentation K M) n)

/-- Unit-valued Tate corestriction in every integer degree. -/
def relativeTateCorestriction (n : ℤ) :
    relativeTateCohomology L M n →ₗ[IntegerScalars.{u}] relativeTateCohomology K M n := by
  letI := Fintype.ofFinite Gal(M/K)
  letI := Fintype.ofFinite (relativeGaloisSubgroup K L M)
  letI := Fintype.ofFinite (Gal(M/K) ⧸ relativeGaloisSubgroup K L M)
  exact (Langlands.Tate.corestriction (relativeGaloisSubgroup K L M)
    (unitsRepresentation K M) n).comp
      (relativeSubgroupTateIso K L M n).toLinearEquiv.toLinearMap

/-- Tate restriction on the actual trivial integral coefficient module. -/
def integralTateRestriction (n : ℤ) :
    integralTateCohomology K M n →ₗ[IntegerScalars.{u}] integralTateCohomology L M n := by
  letI := Fintype.ofFinite Gal(M/K)
  letI := Fintype.ofFinite (relativeGaloisSubgroup K L M)
  letI := Fintype.ofFinite (Gal(M/K) ⧸ relativeGaloisSubgroup K L M)
  exact (integralSubgroupTateIso K L M n).symm.toLinearEquiv.toLinearMap.comp
    (Langlands.Tate.restriction (relativeGaloisSubgroup K L M)
      (Rep.trivial IntegerScalars.{u} Gal(M/K) IntegerScalars.{u}) n)

/-- Tate corestriction on the actual trivial integral coefficient module. -/
def integralTateCorestriction (n : ℤ) :
    integralTateCohomology L M n →ₗ[IntegerScalars.{u}] integralTateCohomology K M n := by
  letI := Fintype.ofFinite Gal(M/K)
  letI := Fintype.ofFinite (relativeGaloisSubgroup K L M)
  letI := Fintype.ofFinite (Gal(M/K) ⧸ relativeGaloisSubgroup K L M)
  exact (Langlands.Tate.corestriction (relativeGaloisSubgroup K L M)
    (Rep.trivial IntegerScalars.{u} Gal(M/K) IntegerScalars.{u}) n).comp
      (integralSubgroupTateIso K L M n).toLinearEquiv.toLinearMap

/-- The new reindexing agrees with the existing ordinary comparison in
positive degrees. -/
theorem relativeSubgroupTateIso_positive (n : ℕ) [NeZero n] :
    letI := Fintype.ofFinite Gal(M/L)
    letI := Fintype.ofFinite (relativeGaloisSubgroup K L M)
    (relativeSubgroupTateIso K L M n).hom =
      ((TateCohomology.isoGroupCohomology n).app (unitsRepresentation L M)).hom ≫
        (relativeSubgroupCohomologyIso K L M n).hom ≫
          ((TateCohomology.isoGroupCohomology n).app
            (Rep.res (relativeGaloisSubgroup K L M).subtype
              (unitsRepresentation K M))).inv := by
  let := Fintype.ofFinite Gal(M/L)
  let := Fintype.ofFinite (relativeGaloisSubgroup K L M)
  exact Langlands.Tate.reindex_groupCohomology (relativeGaloisSubgroupEquiv K L M)
    (relativeSubgroupUnitsIso K L M).hom n

/-- Positive-degree Tate corestriction recovers the published ordinary map
under the actual Tate-to-ordinary comparisons. -/
theorem relativeTateCorestriction_positive (n : ℕ) [NeZero n]
    (x : relativeTateCohomology L M n) :
    letI := Fintype.ofFinite Gal(M/K)
    letI := Fintype.ofFinite Gal(M/L)
    ((TateCohomology.isoGroupCohomology n).app (unitsRepresentation K M)).hom.hom
      (relativeTateCorestriction K L M n x) =
        relativeCorestriction K L M n
          (((TateCohomology.isoGroupCohomology n).app
            (unitsRepresentation L M)).hom.hom x) := by
  let := Fintype.ofFinite Gal(M/K)
  let := Fintype.ofFinite Gal(M/L)
  let := Fintype.ofFinite (relativeGaloisSubgroup K L M)
  let := Fintype.ofFinite (Gal(M/K) ⧸ relativeGaloisSubgroup K L M)
  have h := relativeSubgroupTateIso_positive K L M n
  have hx := congrArg (fun f => f.hom x) h
  exact congrArg (fun y =>
      ((TateCohomology.isoGroupCohomology n).app (unitsRepresentation K M)).hom.hom
        (Langlands.Tate.corestriction (relativeGaloisSubgroup K L M)
          (unitsRepresentation K M) n y)) hx

end Langlands.ClassFieldTheory.Local
