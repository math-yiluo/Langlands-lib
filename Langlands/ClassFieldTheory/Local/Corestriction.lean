import Langlands.ClassFieldTheory.Local.Invariants
import Langlands.Cohomology.Tate.TransferDefinitions

/-! # Positive-degree relative Galois corestriction -/

noncomputable section

open CategoryTheory

namespace Langlands.ClassFieldTheory.Local

universe u v w

section Tower

variable (K : Type v) (L : Type w) (M : Type u)
  [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]

/-- The actual subgroup of `Gal(M/K)` consisting of the automorphisms over `L`. -/
def relativeGaloisSubgroup : Subgroup Gal(M/K) :=
  (AlgEquiv.restrictScalarsHom K : Gal(M/L) →* Gal(M/K)).range

/-- Restriction of scalars identifies `Gal(M/L)` with its actual image. -/
def relativeGaloisSubgroupEquiv : Gal(M/L) ≃* relativeGaloisSubgroup K L M :=
  MonoidHom.ofInjective (AlgEquiv.restrictScalarsHom_injective K)

@[simp]
theorem relativeGaloisSubgroupEquiv_apply (σ : Gal(M/L)) :
    (relativeGaloisSubgroupEquiv K L M σ : Gal(M/K)) = σ.restrictScalars K := rfl

/-- Cohomology reindexing uses the same unit group and the identity coefficient
map; the group isomorphism is constructed from restriction of scalars. -/
def relativeSubgroupCohomologyIso (n : ℕ) :
    relativeCohomology L M n ≅
      groupCohomology
        (Rep.res (relativeGaloisSubgroup K L M).subtype (unitsRepresentation K M)) n :=
  groupCohomology.mapIso (relativeGaloisSubgroupEquiv K L M)
    (LinearEquiv.refl IntegerScalars.{u} (Additive Mˣ)) (fun _ => rfl) n

variable [FiniteDimensional K M]

/-- Actual relative corestriction in a positive ordinary cohomological degree,
transported from the constructed Tate corestriction. -/
def relativeCorestriction (n : ℕ) [NeZero n] :
    relativeCohomology L M n →ₗ[IntegerScalars.{u}] relativeCohomology K M n := by
  letI := Fintype.ofFinite Gal(M/K)
  letI := Fintype.ofFinite (relativeGaloisSubgroup K L M)
  letI := Fintype.ofFinite (Gal(M/K) ⧸ relativeGaloisSubgroup K L M)
  let A := unitsRepresentation K M
  let B := Rep.res (relativeGaloisSubgroup K L M).subtype A
  exact ((TateCohomology.isoGroupCohomology n).app A).toLinearEquiv.toLinearMap.comp
    ((Langlands.Tate.corestriction (relativeGaloisSubgroup K L M) A n).comp
      (((TateCohomology.isoGroupCohomology n).app B).symm.toLinearEquiv.toLinearMap.comp
        (relativeSubgroupCohomologyIso K L M n).toLinearEquiv.toLinearMap))

/-- The ordinary map is exactly subgroup reindexing followed by the two
positive-degree comparison maps and the constructed Tate corestriction. -/
theorem relativeCorestriction_eq (n : ℕ) [NeZero n] :
    letI := Fintype.ofFinite Gal(M/K)
    letI := Fintype.ofFinite (relativeGaloisSubgroup K L M)
    letI := Fintype.ofFinite (Gal(M/K) ⧸ relativeGaloisSubgroup K L M)
    let A := unitsRepresentation K M
    let B := Rep.res (relativeGaloisSubgroup K L M).subtype A
    relativeCorestriction K L M n =
      ((TateCohomology.isoGroupCohomology n).app A).toLinearEquiv.toLinearMap.comp
        ((Langlands.Tate.corestriction (relativeGaloisSubgroup K L M) A n).comp
          (((TateCohomology.isoGroupCohomology n).app B).symm.toLinearEquiv.toLinearMap.comp
            (relativeSubgroupCohomologyIso K L M n).toLinearEquiv.toLinearMap)) := rfl

end Tower

namespace InvariantFamily

/-- Finite relative degree-two corestriction preserves the value of the invariant
on the same raw invariant family. This predicate asserts no existence. -/
def RelativeCorestriction {p : ℕ} [Fact p.Prime] (I : InvariantFamily.{u,v} p) :
    Prop :=
  ∀ (F E : PadicField.{u} p) (M : Type v) [Field M]
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    [Algebra F.Carrier M] [Algebra E.Carrier M]
    [IsScalarTower F.Carrier E.Carrier M]
    [FiniteDimensional F.Carrier E.Carrier]
    [FiniteDimensional F.Carrier M] [FiniteDimensional E.Carrier M]
    [IsGalois F.Carrier M] [IsGalois E.Carrier M],
    ∀ c : relativeCohomology E.Carrier M 2,
      I.relative F M (relativeCorestriction F.Carrier E.Carrier M 2 c) =
        I.relative E M c

end InvariantFamily

end Langlands.ClassFieldTheory.Local
