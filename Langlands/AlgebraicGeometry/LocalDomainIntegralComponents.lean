import Langlands.AlgebraicGeometry.GenericPointAvoidance
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.Topology.NoetherianSpace

/-! # Integral open components of schemes whose stalks are domains -/

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace Langlands.AlgebraicGeometry

/-- If the stalk at a point is a domain, there is only one irreducible
component through that point. -/
theorem irreducibleComponent_eq_of_stalk_isDomain
    {X : Scheme.{u}} (x : X) [IsDomain (X.presheaf.stalk x)]
    (C D : irreducibleComponents X) (hxC : x ∈ C.val) (hxD : x ∈ D.val) :
    C = D := by
  let ηC := genericPoints.ofComponent C
  let ηD := genericPoints.ofComponent D
  have hCx : ηC.val ⤳ x := (genericPoints.isGenericPoint_ofComponent C).specializes hxC
  have hDx : ηD.val ⤳ x := (genericPoints.isGenericPoint_ofComponent D).specializes hxD
  obtain ⟨c, hc⟩ : ηC.val ∈ Set.range (X.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]
    exact hCx
  obtain ⟨d, hd⟩ : ηD.val ∈ Set.range (X.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]
    exact hDx
  let η := genericPoint (Spec (X.presheaf.stalk x))
  have hηC : X.fromSpecStalk x η = ηC.val :=
    (GenericPointAvoidance.mem_genericPoints_iff.mp ηC.property) _
      (hc ▸ (genericPoint_specializes c).map (X.fromSpecStalk x).continuous)
  have hηD : X.fromSpecStalk x η = ηD.val :=
    (GenericPointAvoidance.mem_genericPoints_iff.mp ηD.property) _
      (hd ▸ (genericPoint_specializes d).map (X.fromSpecStalk x).continuous)
  apply Subtype.ext
  rw [← (genericPoints.isGenericPoint_ofComponent C).def,
    ← (genericPoints.isGenericPoint_ofComponent D).def]
  exact congrArg (fun a : X ↦ closure ({a} : Set X)) (hηC.symm.trans hηD)

/-- In a scheme with domain stalks, irreducible components are pairwise
disjoint. -/
theorem irreducibleComponents_disjoint_of_stalk_isDomain
    {X : Scheme.{u}} (hX : ∀ x : X, IsDomain (X.presheaf.stalk x))
    {C D : irreducibleComponents X} (hCD : C ≠ D) : Disjoint C.val D.val := by
  apply Set.disjoint_left.mpr
  intro x hxC hxD
  have := hX x
  exact hCD (irreducibleComponent_eq_of_stalk_isDomain x C D hxC hxD)

/-- A noetherian scheme with domain stalks has open irreducible components. -/
theorem isOpen_irreducibleComponent_of_stalk_isDomain
    {X : Scheme.{u}} [NoetherianSpace X]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x))
    (C : irreducibleComponents X) : IsOpen C.val := by
  classical
  let S : Set (Set X) := {D | D ∈ irreducibleComponents X ∧ D ≠ C.val}
  have hclosed : IsClosed (⋃₀ S) :=
    (NoetherianSpace.finite_irreducibleComponents.subset fun _ hD ↦ hD.1).isClosed_sUnion
      fun D hD ↦ isClosed_of_mem_irreducibleComponents D hD.1
  have hcompl : C.val = (⋃₀ S)ᶜ := by
    ext x
    constructor
    · intro hxC ⟨D, hD, hxD⟩
      exact Set.disjoint_left.mp
        (irreducibleComponents_disjoint_of_stalk_isDomain hX
          (show C ≠ (⟨D, hD.1⟩ : irreducibleComponents X) from
            fun h ↦ hD.2 (congrArg Subtype.val h).symm)) hxC hxD
    · intro hx
      by_contra hxC
      have hne : irreducibleComponent x ≠ C.val := by
        intro h
        exact hxC (h ▸ mem_irreducibleComponent)
      exact hx ⟨irreducibleComponent x,
        ⟨irreducibleComponent_mem_irreducibleComponents x, hne⟩,
        mem_irreducibleComponent⟩
  rw [hcompl]
  exact hclosed.isOpen_compl

/-- The actual open irreducible-component subscheme of a noetherian scheme
with domain stalks. -/
def integralComponentOpen
    (X : Scheme.{u}) [NoetherianSpace X]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x))
    (C : irreducibleComponents X) : X.Opens :=
  ⟨C.val, isOpen_irreducibleComponent_of_stalk_isDomain hX C⟩

theorem isIntegral_integralComponentOpen
    (X : Scheme.{u}) [NoetherianSpace X]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x))
    (C : irreducibleComponents X) :
    IsIntegral (integralComponentOpen X hX C).toScheme := by
  have (x : X) : _root_.IsReduced (X.presheaf.stalk x) := by
    have := hX x
    infer_instance
  have : IsReduced X := isReduced_of_isReduced_stalk X
  have : IrreducibleSpace (integralComponentOpen X hX C).toScheme :=
    Subtype.irreducibleSpace C.property.1
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- Assemble affine neighbourhoods in the disjoint integral open components.
The component family is finite, and the empty scheme is included. -/
def affineNeighbourhoodOfIntegralComponentOpens
    (X : Scheme.{u}) [NoetherianSpace X]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x)) (E : Set X)
    (V : ∀ C : irreducibleComponents X,
      {U : (integralComponentOpen X hX C).toScheme.Opens //
        IsAffineOpen U ∧ (integralComponentOpen X hX C).ι ⁻¹' E ⊆ U}) :
    {U : X.Opens // IsAffineOpen U ∧ E ⊆ U} := by
  letI : Finite (irreducibleComponents X) :=
    NoetherianSpace.finite_irreducibleComponents.to_subtype
  let W (C : irreducibleComponents X) : X.Opens :=
    (integralComponentOpen X hX C).ι ''ᵁ (V C).val
  have hW (C) : IsAffineOpen (W C) :=
    (V C).property.1.image_of_isOpenImmersion _
  have hdisj : Pairwise (fun C D ↦ Disjoint (W C) (W D)) := by
    intro C D hCD
    apply disjoint_iff_inf_le.mpr
    rintro x ⟨⟨c, _, rfl⟩, hd⟩
    obtain ⟨d, _, hd⟩ := hd
    change d.val = c.val at hd
    have hxD : c.val ∈ D.val := hd ▸ d.2
    exact Set.disjoint_left.mp
      (irreducibleComponents_disjoint_of_stalk_isDomain hX hCD) c.2 hxD
  refine ⟨⨆ C, W C, IsAffineOpen.iSup_of_disjoint hW hdisj, ?_⟩
  intro x hx
  let C : irreducibleComponents X :=
    ⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩
  apply Opens.mem_iSup.mpr
  refine ⟨C, ⟨⟨x, mem_irreducibleComponent⟩, ?_, rfl⟩⟩
  exact (V C).property.2 hx

end Langlands.AlgebraicGeometry
