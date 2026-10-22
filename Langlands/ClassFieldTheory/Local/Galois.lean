import Langlands.LocalField.Definitions
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.Nonarchimedean.TotallyDisconnected

/-!
# Actual Galois groups and continuous topological abelianization

The quotient is by the *closed* commutator subgroup. Finite abelian extensions
are actual finite Galois intermediate fields of the existing algebraic closure.
No reciprocity map is supplied or chosen.
-/

noncomputable section

namespace Langlands.LocalClassField

universe u v w

section TopologicalAbelianization

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The existing topological abelianization has its actual quotient topology
and is Hausdorff because the subgroup being divided out is closed. -/
theorem abelianizationHausdorff : T2Space (TopologicalAbelianization G) := by
  let : IsClosed ((commutator G).topologicalClosure : Set G) :=
    Subgroup.isClosed_topologicalClosure _
  infer_instance

/-- The canonical continuous projection to the closed-commutator quotient. -/
def abelianizationProjection : G →ₜ* TopologicalAbelianization G where
  toMonoidHom := QuotientGroup.mk' _
  continuous_toFun := QuotientGroup.continuous_mk

variable {G} {A : Type v} [Group A] [IsMulCommutative A] [TopologicalSpace A]
  [T1Space A]

private theorem closedCommutator_le_kernel (f : G →ₜ* A) :
    (commutator G).topologicalClosure ≤ f.toMonoidHom.ker :=
  Subgroup.topologicalClosure_minimal _
    (Abelianization.commutator_subset_ker f.toMonoidHom)
    (isClosed_singleton.preimage f.continuous)

/-- Descend a continuous homomorphism into a T1 abelian group.
The closed-kernel argument is part of the construction. -/
def abelianizationLift (f : G →ₜ* A) : TopologicalAbelianization G →ₜ* A where
  toMonoidHom := QuotientGroup.lift _ f.toMonoidHom (closedCommutator_le_kernel f)
  continuous_toFun :=
    (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr f.continuous

/-- The universal property as an actual equivalence of continuous homomorphism
sets. It asserts no reciprocity or choice of an Artin homomorphism. -/
def abelianizationLiftEquiv :
    (G →ₜ* A) ≃ (TopologicalAbelianization G →ₜ* A) where
  toFun := abelianizationLift
  invFun f := f.comp (abelianizationProjection G)
  left_inv f := by ext; rfl
  right_inv f := by
    ext x
    refine QuotientGroup.induction_on x ?_
    intro g
    rfl

variable {H : Type v} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- The map on closed-commutator quotients induced by a continuous homomorphism. -/
def abelianizationMap (f : G →ₜ* H) :
    TopologicalAbelianization G →ₜ* TopologicalAbelianization H := by
  letI := abelianizationHausdorff H
  exact abelianizationLift ((abelianizationProjection H).comp f)

/-- The quotient of a nonarchimedean topological group remains nonarchimedean.
Its open subgroups are constructed as images under the open quotient map. -/
theorem quotientNonarchimedean {G : Type u} [Group G] [TopologicalSpace G]
    [NonarchimedeanGroup G] (N : Subgroup G) [N.Normal] :
    NonarchimedeanGroup (G ⧸ N) where
  is_nonarchimedean U hU := by
    have hpre : QuotientGroup.mk ⁻¹' U ∈ nhds (1 : G) := by
      have h := (QuotientGroup.continuous_mk (N := N)).continuousAt.preimage_mem_nhds hU
      simpa using h
    obtain ⟨V, hV⟩ := NonarchimedeanGroup.is_nonarchimedean _ hpre
    refine ⟨{ V.toSubgroup.map (QuotientGroup.mk' N) with
      isOpen' := QuotientGroup.isOpenMap_coe _ V.isOpen }, ?_⟩
    rintro _ ⟨g, hg, rfl⟩
    exact hV hg

end TopologicalAbelianization

section Galois

variable (K : Type u) [Field K]

/-- Actual finite abelian extensions in the chosen algebraic closure.
The predicate refers to the actual automorphism group's multiplication. -/
def FiniteAbelianExtension :=
  {L : FiniteGaloisIntermediateField K (AlgebraicClosure K) //
    IsMulCommutative Gal(L/K)}

namespace FiniteAbelianExtension

variable {K} (L : FiniteAbelianExtension K)

/-- The already-existing finite Galois intermediate field. -/
abbrev field : FiniteGaloisIntermediateField K (AlgebraicClosure K) := L.1

/-- The actual automorphism group, with the inherited Krull topology. -/
abbrev galoisGroup := Gal(L.field/K)

instance : IsMulCommutative L.galoisGroup := L.2

/-- The same actual automorphism group packaged as a finite group. -/
def finiteGroup : FiniteGrp := L.field.finGaloisGroup

/-- The actual open subgroup fixing this finite extension pointwise. -/
def fixingOpenSubgroup : OpenSubgroup (Field.absoluteGaloisGroup K) :=
  ⟨L.field.toIntermediateField.fixingSubgroup,
    L.field.toIntermediateField.fixingSubgroup_isOpen⟩

/-- Restriction from the actual absolute Galois group to the finite abelian
extension. Its target has its Krull topology, which is already discrete. -/
def restriction : Field.absoluteGaloisGroup K →ₜ* L.galoisGroup where
  toMonoidHom := AlgEquiv.restrictNormalHom (F := K)
    (K₁ := AlgebraicClosure K) L.field
  continuous_toFun := InfiniteGalois.restrictNormalHom_continuous
    L.field.toIntermediateField

/-- Restriction descended to the absolute Galois topological abelianization. -/
def abelianRestriction :
    Field.absoluteGaloisGroupAbelianization K →ₜ* L.galoisGroup :=
  abelianizationLift L.restriction

/-- Finite-level transition by restriction along an actual inclusion of
intermediate fields. The smaller field is normal over K. -/
def restrictionOfLE (M : FiniteAbelianExtension K) (h : L.field ≤ M.field) :
    M.galoisGroup →ₜ* L.galoisGroup := by
  letI : Algebra L.field M.field :=
    (Subsemiring.inclusion h).toAlgebra
  letI : IsScalarTower K L.field M.field :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact
    { AlgEquiv.restrictNormalHom (F := K) (K₁ := M.field) L.field with
      continuous_toFun := continuous_of_discreteTopology }

/-- A finite abelian extension is in particular an actual finite extension
of the same p-adic base field. No new field operations are introduced. -/
def asPadicField {p : ℕ} [Fact p.Prime] [Algebra (Padic p) K]
    [FiniteDimensional (Padic p) K] : PadicField.{u} p := by
  letI := FiniteDimensional.trans (Padic p) K L.field
  exact PadicField.ofField L.field

end FiniteAbelianExtension

/-- The canonical continuous projection for the actual absolute Galois group. -/
def absoluteAbelianizationProjection :
    Field.absoluteGaloisGroup K →ₜ* Field.absoluteGaloisGroupAbelianization K :=
  abelianizationProjection _

/-- The actual Krull open-subgroup basis makes the absolute Galois group
nonarchimedean. No local-field residue theorem is used. -/
theorem absoluteGaloisNonarchimedean :
    NonarchimedeanGroup (Field.absoluteGaloisGroup K) where
  is_nonarchimedean U hU := by
    obtain ⟨L, hL, hLU⟩ :=
      (krullTopology_mem_nhds_one_iff K (AlgebraicClosure K) U).mp hU
    let := hL
    exact ⟨⟨L.fixingSubgroup, L.fixingSubgroup_isOpen⟩, hLU⟩

/-- The topological abelianization of the absolute Galois group is genuinely
profinite. The field is perfect so that the chosen algebraic closure is Galois. -/
def absoluteAbelianizationProfinite [PerfectField K] : ProfiniteGrp := by
  letI : IsGalois K (AlgebraicClosure K) := ⟨⟩
  letI := absoluteGaloisNonarchimedean K
  letI := abelianizationHausdorff (Field.absoluteGaloisGroup K)
  letI := quotientNonarchimedean (commutator (Field.absoluteGaloisGroup K)).topologicalClosure
  letI : CompactSpace (Field.absoluteGaloisGroup K) :=
    inferInstanceAs (CompactSpace Gal(AlgebraicClosure K/K))
  exact ProfiniteGrp.of (Field.absoluteGaloisGroupAbelianization K)

variable {K} {E : Type v} [Field E] [Algebra K E]
  [Algebra (AlgebraicClosure K) (AlgebraicClosure E)]
  [IsScalarTower K (AlgebraicClosure K) (AlgebraicClosure E)]

/-- Extension functoriality on actual abelianized absolute Galois groups,
using an explicitly compatible embedding of the algebraic closures.
The direction is from the extension E to the base K. -/
def absoluteAbelianizationMap :
    Field.absoluteGaloisGroupAbelianization E →ₜ*
      Field.absoluteGaloisGroupAbelianization K :=
  abelianizationMap (Field.absoluteGaloisGroup.mapOfAlgebra K E)

end Galois

section Local

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

/-- The actual finite abelian intermediate extensions of a p-adic field. -/
abbrev LocalFiniteAbelianExtension := FiniteAbelianExtension F.Carrier

/-- The genuine compact profinite absolute-Galois abelianization of F.
This is not an identification with the noncompact group Fˣ. -/
def localAbelianGaloisGroup : ProfiniteGrp := by
  letI := Algebra.charZero_of_charZero (Padic p) F.Carrier
  exact absoluteAbelianizationProfinite F.Carrier

/-- The canonical quotient map of the actual local absolute Galois group. -/
def localAbelianGaloisProjection :
    Field.absoluteGaloisGroup F.Carrier →ₜ*
      Field.absoluteGaloisGroupAbelianization F.Carrier :=
  absoluteAbelianizationProjection F.Carrier

end Local

end Langlands.LocalClassField
