import Langlands.GroupScheme.CentralSimpleBinaryWeilGeneration
import Langlands.Algebra.LocalDivisionSK1Statement
import Langlands.LocalField.FiniteExtension

/-! # Local arithmetic reduction for actual restricted binary norm-one images -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.CentralSimpleUnits.BinaryRoot.WeilRoot

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (E D : Type u) [Field E] [Algebra F E] [FiniteDimensional F E]
  [DivisionRing D] [Algebra E D] [FiniteDimensional E D] [Algebra.IsCentral E D]

include F in
/-- Local SK1 over the ground field's finite extensions supplies the actual
coefficient norm-kernel equality, without a supplied topology on the extension. -/
theorem coefficientNorm_ker_of_localSK1
    (hSK : Langlands.CentralDivision.LocalSK1Statement.{u}) :
    (Langlands.BinaryElementary.Reduced.coefficientNorm E D).ker = commutator Dˣ := by
  let := Langlands.LocalField.FiniteExtension.normedField F E
  let := Langlands.LocalField.FiniteExtension.valuativeRel F E
  let := Langlands.LocalField.FiniteExtension.isLocalField F E
  exact hSK E D

/-- The exact local arithmetic theorem implies full generation by the two
actual restricted binary elementary images. -/
theorem rationalElementarySubgroup_eq_top_of_localSK1
    (hSK : Langlands.CentralDivision.LocalSK1Statement.{u})
    {d : ℕ} (bD : Module.Basis (Fin d) E D) :
    rationalElementarySubgroup F E D bD = ⊤ :=
  (rationalElementarySubgroup_eq_top_iff F E bD).mpr
    (coefficientNorm_ker_of_localSK1 F E D hSK)

variable {G : GroupScheme (Spec (CommRingCat.of F))}

/-- Local SK1 implies that every actual restricted binary rational image lies
in the target's actual parabolic elementary subgroup. -/
theorem rationalPoints_range_le_parabolicElementarySubgroup_of_localSK1
    (hSK : Langlands.CentralDivision.LocalSK1Statement.{u})
    (hG : IsConnectedReductive G) (f : groupScheme F E D ⟶ G) :
    (rationalPoints.map f).range ≤ parabolicElementarySubgroup G :=
  rationalPoints_range_le_parabolicElementarySubgroup F E hG f
    (coefficientNorm_ker_of_localSK1 F E D hSK)

/-- The original full rational point map, restricted to the actual target
elementary subgroup using the explicit local SK1 premise. -/
def rationalPointsToParabolicElementarySubgroup_of_localSK1
    (hSK : Langlands.CentralDivision.LocalSK1Statement.{u})
    (hG : IsConnectedReductive G) (f : groupScheme F E D ⟶ G) :
    rationalPoints (groupScheme F E D) →* parabolicElementarySubgroup G :=
  (rationalPoints.map f).codRestrict (parabolicElementarySubgroup G) fun x =>
    rationalPoints_range_le_parabolicElementarySubgroup_of_localSK1
      F E D hSK hG f ⟨x, rfl⟩

@[simp]
theorem rationalPointsToParabolicElementarySubgroup_of_localSK1_apply_coe
    (hSK : Langlands.CentralDivision.LocalSK1Statement.{u})
    (hG : IsConnectedReductive G) (f : groupScheme F E D ⟶ G)
    (x : rationalPoints (groupScheme F E D)) :
    (rationalPointsToParabolicElementarySubgroup_of_localSK1 F E D hSK hG f x :
      rationalPoints G) = rationalPoints.map f x := rfl

/-- The local arithmetic reduction respects any specified actual model of the
restricted binary source and keeps its original rational point map. -/
theorem rationalPoints_range_le_parabolicElementarySubgroup_of_localSK1_of_iso
    (hSK : Langlands.CentralDivision.LocalSK1Statement.{u})
    {A : GroupScheme (Spec (CommRingCat.of F))}
    (hG : IsConnectedReductive G) (e : A ≅ groupScheme F E D) (a : A ⟶ G) :
    (rationalPoints.map a).range ≤ parabolicElementarySubgroup G :=
  rationalPoints_range_le_parabolicElementarySubgroup_of_iso F E hG e a
    (coefficientNorm_ker_of_localSK1 F E D hSK)

/-- An actual connected reductive group identified with a restricted binary
norm-one group satisfies full parabolic elementary generation under local SK1. -/
theorem parabolicElementarySubgroup_eq_top_of_localSK1_of_iso
    (hSK : Langlands.CentralDivision.LocalSK1Statement.{u})
    (hG : IsConnectedReductive G) (e : G ≅ groupScheme F E D) :
    parabolicElementarySubgroup G = ⊤ := by
  have h := rationalPoints_range_le_parabolicElementarySubgroup_of_localSK1_of_iso
    F E D hSK hG e (𝟙 G)
  apply top_unique
  intro x _
  exact h ⟨x, Category.comp_id x⟩

end Langlands.GroupScheme.CentralSimpleUnits.BinaryRoot.WeilRoot
