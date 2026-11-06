import Langlands.ClassFieldTheory.Local.ProfiniteReciprocityStatement
import Langlands.ClassFieldTheory.Local.NormStatement
import Langlands.ClassFieldTheory.Local.NormCorrespondenceStatement
import Langlands.LocalField.Normalization.Proof

/-!
# Norm-kernel bridges for the profinite reciprocity completion

These constructions retain the arithmetic existence and separation statements
as explicit premises. They do not prove either arithmetic input.
-/

noncomputable section

namespace Langlands.LocalClassField

universe u

namespace FiniteAbelianExtension

/-- Package an actual finite abelian intermediate field without changing its
carrier, algebra structure, or norm. -/
def ofIntermediateField {K : Type u} [Field K]
    (E : IntermediateField K (AlgebraicClosure K))
    [FiniteDimensional K E] [IsAbelianGalois K E] :
    FiniteAbelianExtension K :=
  ⟨⟨E⟩, inferInstance⟩

end FiniteAbelianExtension

section FiniteQuotient

variable {K : Type u} [Field K] [TopologicalSpace K]

/-- The certified finite norm-residue equivalence has the given finite Artin
map as its value on quotient representatives. -/
theorem finiteNormResidueEquiv_apply_mk (L : FiniteAbelianExtension K)
    (a : Kˣ →ₜ* L.galoisGroup) (h : FiniteNormResidueRelation L a) (x : Kˣ) :
    finiteNormResidueEquiv L a h (QuotientGroup.mk x) = a x := by
  rfl

/-- When a finite quotient kernel is an actual norm group, the quotient map
descends from the absolute-Galois abelianization. -/
def finiteReciprocityQuotientDescent (L : FiniteAbelianExtension K)
    (r : Kˣ →ₜ* Field.absoluteGaloisGroupAbelianization K)
    (h : FiniteNormResidueRelation L (finiteFamilyOfHom r L))
    (N : ContinuousProfinite.OpenFiniteQuotient Kˣ)
    (hN : normSubgroup K L.field = N.1.toSubgroup) :
    Field.absoluteGaloisGroupAbelianization K →ₜ* N.Quotient := by
  let q : NormQuotient K L.field →ₜ* N.Quotient :=
    { toMonoidHom := QuotientGroup.map _ _ (MonoidHom.id _) (by
        intro x hx
        exact hN ▸ hx)
      continuous_toFun :=
        (QuotientGroup.isQuotientMap_mk _).continuous_iff.mpr
          QuotientGroup.continuous_mk }
  exact q.comp
    ((finiteNormResidueEquiv L (finiteFamilyOfHom r L) h).symm :
      L.galoisGroup →ₜ* NormQuotient K L.field) |>.comp L.abelianRestriction

theorem finiteReciprocityQuotientDescent_apply (L : FiniteAbelianExtension K)
    (r : Kˣ →ₜ* Field.absoluteGaloisGroupAbelianization K)
    (h : FiniteNormResidueRelation L (finiteFamilyOfHom r L))
    (N : ContinuousProfinite.OpenFiniteQuotient Kˣ)
    (hN : normSubgroup K L.field = N.1.toSubgroup) (x : Kˣ) :
    finiteReciprocityQuotientDescent L r h N hN (r x) = N.projection x := by
  change
    QuotientGroup.map (normSubgroup K L.field) N.1.toSubgroup
      (MonoidHom.id _) (fun y hy => hN ▸ hy)
      ((finiteNormResidueEquiv L (finiteFamilyOfHom r L) h).symm
        (finiteFamilyOfHom r L x)) = N.projection x
  rw [← finiteNormResidueEquiv_apply_mk L (finiteFamilyOfHom r L) h x,
    ContinuousMulEquiv.symm_apply_apply]
  rfl

end FiniteQuotient

section Local

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)
    (T : F.TopologicalData)

/-- The arithmetic norm existence assertion applies to each compatible
supplied topology because both topologies equal the module topology. -/
theorem normSubgroupExistence_for_topology (h : NormSubgroupExistence.{u}) :
    letI := T.topology
    ∀ H : Subgroup F.Carrierˣ, IsOpen (H : Set F.Carrierˣ) → H.FiniteIndex →
      ∃! E : IntermediateField F.Carrier (AlgebraicClosure F.Carrier),
        FiniteDimensional F.Carrier E ∧ IsAbelianGalois F.Carrier E ∧
          (Units.map (Algebra.norm F.Carrier (S := E))).range = H := by
  have hT : T.topology = F.canonicalTopologicalData.topology :=
    T.topology_eq_canonicalModule.trans
      F.canonicalTopologicalData.topology_eq_canonicalModule.symm
  rw [hT]
  exact h p F

/-- Arithmetic norm existence supplies descent for every actual open finite
quotient of the original multiplicative topology. -/
theorem finiteQuotientDescent_of_normSubgroupExistence
    (h : NormSubgroupExistence.{u}) :
    letI := T.topology
    ∀ (r : F.Carrierˣ →ₜ* Field.absoluteGaloisGroupAbelianization F.Carrier),
      ProfiniteNormResidueRelation r →
        ∀ N : ContinuousProfinite.OpenFiniteQuotient F.Carrierˣ,
          ∃ q : Field.absoluteGaloisGroupAbelianization F.Carrier →ₜ* N.Quotient,
            q.comp r = N.projection := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro r hr N
  obtain ⟨E, ⟨hfd, hAb, hEq⟩, _⟩ :=
    normSubgroupExistence_for_topology F T h N.1.toSubgroup N.2 inferInstance
  let := hfd
  let := hAb
  let L := FiniteAbelianExtension.ofIntermediateField E
  have hN : normSubgroup F.Carrier L.field = N.1.toSubgroup := hEq
  refine ⟨finiteReciprocityQuotientDescent L r (hr.2.1 L) N hN, ?_⟩
  ext x
  exact finiteReciprocityQuotientDescent_apply L r (hr.2.1 L) N hN x

/-- Exact finite norm kernels and arithmetic norm separation imply
injectivity of the given reciprocity candidate. -/
theorem injective_of_normSubgroupsSeparatePoints
    (h : NormSubgroupsSeparatePoints.{u}) :
    letI := T.topology
    ∀ (r : F.Carrierˣ →ₜ* Field.absoluteGaloisGroupAbelianization F.Carrier),
      ProfiniteNormResidueRelation r → Function.Injective r := by
  let := T.topology
  intro r hr
  apply (injective_iff_map_eq_one r).mpr
  intro a ha
  by_contra hne
  obtain ⟨E, hfd, hAb, hNot⟩ := h p F a hne
  let := hfd
  let := hAb
  let L := FiniteAbelianExtension.ofIntermediateField E
  apply hNot
  change a ∈ normSubgroup F.Carrier L.field
  rw [← (hr.2.1 L).1]
  change L.abelianRestriction (r a) = 1
  rw [ha, map_one]

end Local

end Langlands.LocalClassField
