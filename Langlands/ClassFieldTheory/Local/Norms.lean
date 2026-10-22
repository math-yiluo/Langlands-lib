import Langlands.LocalField.Definitions
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.Topology.Algebra.Group.Units
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Instances.Matrix

/-!
# Finite-extension norms and actual norm quotients

The algebraic constructions work for finite field extensions in independent
universes. The continuous constructions specialize them to the supplied
topologies of actual finite extensions of `Padic p`. Norm transitivity
discharges the well-definedness of the two tower quotient maps.
-/

noncomputable section

namespace Langlands.LocalClassField

universe u v w

/-- The determinant norm on multiplicative groups of a finite field extension. -/
def normUnits (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] : Lˣ →* Kˣ :=
  Units.map (Algebra.norm K)

/-- The actual norm image, without any assertion that it is open or of finite index. -/
def normSubgroup (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] : Subgroup Kˣ :=
  (normUnits K L).range

/-- The norm as a homomorphism onto its actual image. -/
def normToImage (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] : Lˣ →* normSubgroup K L :=
  (normUnits K L).rangeRestrict

/-- The actual norm quotient, with its quotient topology whenever `Kˣ` has a topology. -/
abbrev NormQuotient (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] :=
  Kˣ ⧸ normSubgroup K L

/-- Canonical projection to the norm quotient. -/
def normQuotientProjection (K : Type u) (L : Type v) [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] : Kˣ →* NormQuotient K L :=
  QuotientGroup.mk' _

section Tower

variable (K : Type u) (L : Type v) (M : Type w)
  [Field K] [Field L] [Field M]
  [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
  [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M]

/-- In a finite tower, the larger extension's norm subgroup is contained
in the intermediate extension's norm subgroup. This certificate is used
to construct the quotient projection below. -/
private theorem tower_normSubgroup_le : normSubgroup K M ≤ normSubgroup K L := by
  rintro _ ⟨x, rfl⟩
  refine ⟨normUnits L M x, ?_⟩
  apply Units.ext
  exact Algebra.norm_norm (R := K) (S := L) (a := (x : M))

/-- Projection `Kˣ/N_{M/K}(Mˣ) → Kˣ/N_{L/K}(Lˣ)` in a finite tower. -/
def normQuotientTowerProjection : NormQuotient K M →* NormQuotient K L :=
  QuotientGroup.map _ _ (MonoidHom.id _) (tower_normSubgroup_le K L M)

/-- The norm `N_{L/K}` induces `Lˣ/N_{M/L}(Mˣ) → Kˣ/N_{M/K}(Mˣ)`.
The containment needed to descend is a consequence of the actual norm tower law. -/
def normQuotientTowerNorm : NormQuotient L M →* NormQuotient K M :=
  QuotientGroup.map _ _ (normUnits K L) (by
    rintro _ ⟨x, rfl⟩
    refine ⟨x, ?_⟩
    apply Units.ext
    exact (Algebra.norm_norm (R := K) (S := L) (a := (x : M))).symm)

end Tower

section Local

variable {p : ℕ} [Fact p.Prime]
  {F : PadicField.{u} p} {E : PadicField.{v} p}
  (T : F.TopologicalData) (S : E.TopologicalData)
  [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]

/-- The inclusion of actual local multiplicative groups is continuous.
Continuity comes from linearity over `Padic p` and the supplied module topologies. -/
def localInclusion :
    letI := T.topology
    letI := S.topology
    F.Carrierˣ →ₜ* E.Carrierˣ := by
  letI := T.topology
  letI := S.topology
  letI := T.valuativeRel
  letI := S.valuativeRel
  letI := T.localField
  letI := S.localField
  letI := T.moduleTopology
  letI := S.moduleTopology
  let f := IsScalarTower.toAlgHom (Padic p) F.Carrier E.Carrier
  exact
    { Units.map f.toMonoidHom with
      continuous_toFun :=
        (IsModuleTopology.continuous_of_linearMap f.toLinearMap).units_map _ }

/-- The actual finite-extension norm is continuous for the supplied local-field
topologies. Its certificate uses a matrix of multiplication and continuity
of determinant; no norm-topology comparison theorem is assumed. -/
def localNorm :
    letI := T.topology
    letI := S.topology
    E.Carrierˣ →ₜ* F.Carrierˣ := by
  letI := T.topology
  letI := S.topology
  letI := T.valuativeRel
  letI := S.valuativeRel
  letI := T.localField
  letI := S.localField
  letI := T.moduleTopology
  letI := S.moduleTopology
  letI : FiniteDimensional F.Carrier E.Carrier :=
    FiniteDimensional.right (Padic p) F.Carrier E.Carrier
  let b := Module.finBasis F.Carrier E.Carrier
  let f := (Algebra.leftMulMatrix b).toLinearMap.restrictScalars (Padic p)
  have hf : Continuous f := IsModuleTopology.continuous_of_linearMap f
  have hn : Continuous (Algebra.norm F.Carrier : E.Carrier → F.Carrier) := by
    convert hf.matrix_det using 1
    ext x
    exact Algebra.norm_eq_matrix_det b x
  exact
    { normUnits F.Carrier E.Carrier with
      continuous_toFun := hn.units_map _ }

/-- The actual local norm subgroup, with finite dimensionality inherited from `Q_p`. -/
abbrev localNormSubgroup : Subgroup F.Carrierˣ :=
  letI : FiniteDimensional F.Carrier E.Carrier :=
    FiniteDimensional.right (Padic p) F.Carrier E.Carrier
  normSubgroup F.Carrier E.Carrier

/-- Actual local norm quotient; its topology is the quotient of `T.multiplicativeTopology`. -/
abbrev LocalNormQuotient :=
  F.Carrierˣ ⧸ localNormSubgroup (F := F) (E := E)

/-- Continuous canonical projection to the local norm quotient. -/
def localNormQuotientProjection :
    letI := T.topology
    F.Carrierˣ →ₜ* LocalNormQuotient (F := F) (E := E) :=
  letI := T.topology
  { QuotientGroup.mk' _ with
    continuous_toFun := QuotientGroup.continuous_mk }

variable (D : PadicField.{w} p)
  [Algebra F.Carrier D.Carrier] [Algebra E.Carrier D.Carrier]
  [IsScalarTower (Padic p) F.Carrier D.Carrier]
  [IsScalarTower (Padic p) E.Carrier D.Carrier]
  [IsScalarTower F.Carrier E.Carrier D.Carrier]

/-- Continuous projection between the two actual local norm quotients.
Only the lower field's topology is involved. -/
def localNormQuotientTowerProjection :
    letI := T.topology
    LocalNormQuotient (F := F) (E := D) →ₜ*
      LocalNormQuotient (F := F) (E := E) := by
  letI := T.topology
  letI : FiniteDimensional F.Carrier E.Carrier :=
    FiniteDimensional.right (Padic p) F.Carrier E.Carrier
  letI : FiniteDimensional F.Carrier D.Carrier :=
    FiniteDimensional.right (Padic p) F.Carrier D.Carrier
  letI : FiniteDimensional E.Carrier D.Carrier :=
    FiniteDimensional.right (Padic p) E.Carrier D.Carrier
  exact
    { normQuotientTowerProjection F.Carrier E.Carrier D.Carrier with
      continuous_toFun := (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
        QuotientGroup.continuous_mk }

/-- The continuous field norm induces a continuous map between the actual
norm quotients in a local-field tower. -/
def localNormQuotientTowerNorm :
    letI := T.topology
    letI := S.topology
    LocalNormQuotient (F := E) (E := D) →ₜ*
      LocalNormQuotient (F := F) (E := D) := by
  letI := T.topology
  letI := S.topology
  letI : FiniteDimensional F.Carrier E.Carrier :=
    FiniteDimensional.right (Padic p) F.Carrier E.Carrier
  letI : FiniteDimensional F.Carrier D.Carrier :=
    FiniteDimensional.right (Padic p) F.Carrier D.Carrier
  letI : FiniteDimensional E.Carrier D.Carrier :=
    FiniteDimensional.right (Padic p) E.Carrier D.Carrier
  exact
    { normQuotientTowerNorm F.Carrier E.Carrier D.Carrier with
      continuous_toFun := (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
        (QuotientGroup.continuous_mk.comp (localNorm T S).continuous) }

end Local

end Langlands.LocalClassField
