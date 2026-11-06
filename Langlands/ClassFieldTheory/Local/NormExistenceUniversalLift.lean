import Langlands.ClassFieldTheory.Local.NormExistenceAbelianReduction
import Langlands.ClassFieldTheory.Local.NormExistenceClosedSupport
import Langlands.ClassFieldTheory.Local.UniversalNormDivisibility
import Mathlib.FieldTheory.Normal.Closure

/-! # Lifting universal norms through finite local extensions -/

noncomputable section

namespace Langlands.ClassFieldTheory.Local

universe u v w

open Langlands.LocalClassField

/-- Universal norm lifting and the closed, downward directed family of
actual finite abelian norm subgroups, in every local field of universe `u`. -/
def UniversalNormLiftAndNormFamily : Prop :=
  UniversalNormLifting.{u} ∧
    ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (T : F.TopologicalData),
      DirectedOn (· ≥ ·) (finiteAbelianNormFamily F.Carrier) ∧
        (letI := T.topology
          ∀ N ∈ finiteAbelianNormFamily F.Carrier, IsClosed (N : Set F.Carrierˣ))

/-- Changing a finite extension by a base-algebra equivalence preserves its
actual determinant-norm subgroup. -/
theorem normSubgroup_eq_of_algEquiv
    (K : Type u) (L : Type v) (M : Type w)
    [Field K] [Field L] [Field M] [Algebra K L] [Algebra K M]
    [FiniteDimensional K L] [FiniteDimensional K M]
    (e : L ≃ₐ[K] M) : normSubgroup K L = normSubgroup K M := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    refine ⟨Units.map e.toRingEquiv.toMonoidHom x, ?_⟩
    apply Units.ext
    exact Algebra.norm_eq_of_algEquiv e (x : L)
  · rintro _ ⟨x, rfl⟩
    refine ⟨Units.map e.symm.toRingEquiv.toMonoidHom x, ?_⟩
    apply Units.ext
    exact Algebra.norm_eq_of_algEquiv e.symm (x : M)

/-- A universal norm is a norm from every finite abelian extension, even when
that extension is not already embedded in the chosen closure. -/
theorem universalNormSubgroup_le_normSubgroup_of_abelian
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L] :
    universalNormSubgroup K ≤ normSubgroup K L := by
  let f : L →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
  let e : L ≃ₐ[K] f.fieldRange := AlgEquiv.ofInjectiveField f
  let : FiniteDimensional K f.fieldRange := f.toLinearMap.finiteDimensional_range
  let : IsAbelianGalois K f.fieldRange := IsAbelianGalois.of_algHom e.symm.toAlgHom
  intro a ha
  rw [normSubgroup_eq_of_algEquiv K L f.fieldRange e]
  exact ha f.fieldRange

variable {p : ℕ} [Fact p.Prime]

/-- Maximal abelian reduction extends universal norm membership to finite
Galois extensions. -/
theorem universalNormSubgroup_le_normSubgroup_of_galois
    (F : PadicField.{u} p) (L : Type u) [Field L] [Algebra F.Carrier L]
    [FiniteDimensional F.Carrier L] [IsGalois F.Carrier L] :
    universalNormSubgroup F.Carrier ≤ normSubgroup F.Carrier L := by
  rw [normSubgroup_maximalAbelianNormSubfield F L]
  exact universalNormSubgroup_le_normSubgroup_of_abelian F.Carrier _

/-- Taking a finite normal closure shows that a universal norm is a norm from
any finite extension of the local field. -/
theorem universalNormSubgroup_le_normSubgroup
    (F : PadicField.{u} p) (L : Type u) [Field L] [Algebra F.Carrier L]
    [FiniteDimensional F.Carrier L] :
    universalNormSubgroup F.Carrier ≤ normSubgroup F.Carrier L := by
  let : CharZero F.Carrier := Algebra.charZero_of_charZero (Padic p) F.Carrier
  let : Algebra.IsAlgebraic F.Carrier (AlgebraicClosure L) :=
    Algebra.IsAlgebraic.trans F.Carrier L (AlgebraicClosure L)
  let M := IntermediateField.normalClosure F.Carrier L (AlgebraicClosure L)
  let : IsGalois F.Carrier M := { }
  let : FiniteDimensional L M := FiniteDimensional.right F.Carrier L M
  exact (universalNormSubgroup_le_normSubgroup_of_galois F M).trans
    (normSubgroup_le_of_tower F.Carrier M L)

/-- In a finite tower, mapping the upper relative norm group by the middle
norm gives the absolute upper norm group. -/
theorem normSubgroup_map_normUnits
    (K L M : Type u) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M] [Algebra L M] [IsScalarTower K L M]
    [FiniteDimensional K L] [FiniteDimensional L M] [FiniteDimensional K M] :
    (normSubgroup L M).map (normUnits K L) = normSubgroup K M := by
  ext a
  constructor
  · rintro ⟨b, ⟨c, rfl⟩, rfl⟩
    refine ⟨c, ?_⟩
    apply Units.ext
    exact (Algebra.norm_norm (R := K) (S := L) (a := (c : M))).symm
  · rintro ⟨c, rfl⟩
    refine ⟨normUnits L M c, ⟨c, rfl⟩, ?_⟩
    apply Units.ext
    exact Algebra.norm_norm (R := K) (S := L) (a := (c : M))

/-- Enlarging a finite intermediate extension makes its norm subgroup smaller. -/
theorem normSubgroup_antitone_intermediateField
    (K : Type u) [Field K]
    (L M : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K L] [FiniteDimensional K M] (h : L ≤ M) :
    normSubgroup K M ≤ normSubgroup K L := by
  let : Algebra L M := (IntermediateField.inclusion h).toAlgebra
  let : IsScalarTower K L M := IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional L M := FiniteDimensional.right K L M
  exact normSubgroup_le_of_tower K M L

/-- Composita make the actual finite abelian norm family downward directed. -/
theorem finiteAbelianNormFamily_directed (K : Type u) [Field K] :
    DirectedOn (· ≥ ·) (finiteAbelianNormFamily K) := by
  rintro N ⟨L, hL, rfl⟩ M ⟨R, hR, rfl⟩
  let := hL
  let := hR
  let D : FiniteIntermediateExtension K := ⟨L.field ⊔ R.field, inferInstance⟩
  refine ⟨normSubgroup K D.field, ⟨D, inferInstance, rfl⟩, ?_, ?_⟩
  · exact normSubgroup_antitone_intermediateField K L.field D.field le_sup_left
  · exact normSubgroup_antitone_intermediateField K R.field D.field le_sup_right

/-- Every member of the actual finite abelian norm family is closed. -/
theorem isClosed_finiteAbelianNormFamily
    (F : PadicField.{u} p) (T : F.TopologicalData) :
    letI := T.topology
    ∀ N ∈ finiteAbelianNormFamily F.Carrier, IsClosed (N : Set F.Carrierˣ) := by
  rintro N ⟨D, _, rfl⟩
  let D' : PadicField.{u} p := D.asPadicField
  let : Algebra (Padic p) D'.Carrier := D'.algebra
  let : IsScalarTower (Padic p) F.Carrier D'.Carrier :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact isClosed_normSubgroup F D' T D'.canonicalTopologicalData

/-- A universal norm below has a norm preimage which is a universal norm
above, for every actual finite local extension. -/
theorem universalNorm_lift (F E : PadicField.{u} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier] :
    letI : FiniteDimensional F.Carrier E.Carrier :=
      FiniteDimensional.right (Padic p) F.Carrier E.Carrier
    ∀ a : F.Carrierˣ, a ∈ universalNormSubgroup F.Carrier →
      ∃ b : E.Carrierˣ, b ∈ universalNormSubgroup E.Carrier ∧
        normUnits F.Carrier E.Carrier b = a := by
  let : FiniteDimensional F.Carrier E.Carrier :=
    FiniteDimensional.right (Padic p) F.Carrier E.Carrier
  intro a ha
  let T := F.canonicalTopologicalData
  let S := E.canonicalTopologicalData
  let := T.topology
  let := S.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := S.valuativeRel
  let := S.localField
  let := S.fieldT2
  let f : E.Carrierˣ →ₜ* F.Carrierˣ := localNorm T S
  have hpre : ∀ N ∈ finiteAbelianNormFamily E.Carrier,
      a ∈ N.map f.toMonoidHom := by
    rintro N ⟨D, _, rfl⟩
    let hAlg : Algebra F.Carrier D.field :=
      ((algebraMap E.Carrier D.field).comp
        (algebraMap F.Carrier E.Carrier)).toAlgebra
    let : Module F.Carrier D.field := @Algebra.toModule _ _ _ _ hAlg
    let hTower : IsScalarTower F.Carrier E.Carrier D.field :=
      IsScalarTower.of_algebraMap_eq' rfl
    let hFin : FiniteDimensional F.Carrier D.field :=
      FiniteDimensional.trans F.Carrier E.Carrier D.field
    change a ∈ (normSubgroup E.Carrier D.field).map
      (normUnits F.Carrier E.Carrier)
    have hmap := @normSubgroup_map_normUnits F.Carrier E.Carrier D.field
      inferInstance inferInstance inferInstance inferInstance hAlg inferInstance
      hTower inferInstance inferInstance hFin
    rw [hmap]
    exact universalNormSubgroup_le_normSubgroup F D.field ha
  obtain ⟨b, hb, hbN⟩ := exists_universal_preimage_of_compact_fiber f
    (finiteAbelianNormFamily E.Carrier) (finiteAbelianNormFamily_nonempty E.Carrier)
    (finiteAbelianNormFamily_directed E.Carrier) (isClosed_finiteAbelianNormFamily E S)
    a (isCompact_localNorm_fiber F E T S a) hpre
  exact ⟨b, (mem_universalNormSubgroup_iff E.Carrier b).mpr hbN, hb⟩

/-- The global lifting assertion has no extra arithmetic premise. -/
theorem universalNormLifting : UniversalNormLifting.{u} := by
  intro p hp F E hA hTower
  exact universalNorm_lift F E

/-- The actual finite-extension norm family satisfies both the algebraic
and topological inputs needed for universal-norm divisibility. -/
theorem universalNormLiftAndNormFamily : UniversalNormLiftAndNormFamily.{u} := by
  refine ⟨universalNormLifting, ?_⟩
  intro p hp F T
  exact ⟨finiteAbelianNormFamily_directed F.Carrier, isClosed_finiteAbelianNormFamily F T⟩

end Langlands.ClassFieldTheory.Local
