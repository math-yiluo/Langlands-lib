import Langlands.Geometry.Analytic.StrictTestDomain.OpenSubgroupTransport
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Topology.Algebra.Algebra

/-! # Actual open-subgroup invariants of rational quotient sections -/

noncomputable section

universe u v

namespace Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ρ : RationalSpectralAction G P}

namespace OpenSubgroupTransport

/-- The actual forward operator on the object's rational quotient sections. -/
def sectionOperator (X : ρ.OpenSubgroupTransport) (k : X.subgroup) :
    BoundedAlgHom K X.domain.obj.algebra X.domain.obj.algebra :=
  (ρ.sectionAction X.domain.obj
    (ρ.invariantStabilizerInclusion X.subgroup X.domain k)).hom

/-- The K-subalgebra of actual quotient sections fixed by every element of the
object's chosen open subgroup. -/
def invariantSubalgebra (X : ρ.OpenSubgroupTransport) :
    Subalgebra K X.domain.obj.algebra :=
  ⨅ k : X.subgroup, AlgHom.equalizer (X.sectionOperator k).toAlgHom
    (AlgHom.id K X.domain.obj.algebra)

@[simp]
theorem mem_invariantSubalgebra (X : ρ.OpenSubgroupTransport)
    (b : X.domain.obj.algebra) :
    b ∈ X.invariantSubalgebra ↔ ∀ k : X.subgroup, X.sectionOperator k b = b := by
  simp only [invariantSubalgebra, Algebra.mem_iInf, AlgHom.mem_equalizer,
    AlgHom.id_apply]

/-- Each operator is bounded, so the fixed subalgebra is closed in the actual
quotient norm topology. No continuity in the group parameter is needed. -/
theorem isClosed_invariantSubalgebra (X : ρ.OpenSubgroupTransport) :
    IsClosed (X.invariantSubalgebra : Set X.domain.obj.algebra) := by
  have heq : (X.invariantSubalgebra : Set X.domain.obj.algebra) =
      ⋂ k : X.subgroup, {b | X.sectionOperator k b = b} := by
    ext b
    change b ∈ X.invariantSubalgebra ↔ _
    simp only [mem_invariantSubalgebra, Set.mem_iInter, Set.mem_ofPred_eq]
  rw [heq]
  exact isClosed_iInter (fun k => isClosed_eq (X.sectionOperator k).continuous continuous_id)

/-- Fixed sections form a complete normed subalgebra of the quotient. This does
not assert that this subalgebra has a finite affinoid presentation. -/
instance (X : ρ.OpenSubgroupTransport) : CompleteSpace X.invariantSubalgebra :=
  X.isClosed_invariantSubalgebra.completeSpace_coe

/-- The actual bounded inclusion of fixed sections into all quotient sections. -/
def invariantInclusion (X : ρ.OpenSubgroupTransport) :
    BoundedAlgHom K X.invariantSubalgebra X.domain.obj.algebra where
  toAlgHom := X.invariantSubalgebra.val
  bounded := ⟨1, zero_lt_one, fun b => le_of_eq (one_mul ‖b.val‖).symm⟩

@[simp]
theorem invariantInclusion_apply (X : ρ.OpenSubgroupTransport)
    (b : X.invariantSubalgebra) :
    X.invariantInclusion b = (b : X.domain.obj.algebra) := rfl

namespace Hom

variable {X Y Z : ρ.OpenSubgroupTransport}

/-- Conjugation compatibility of the published quotient pullback implies
preservation of fixed sections. -/
theorem restriction_mem_invariantSubalgebra (f : X ⟶ Y)
    {b : Y.domain.obj.algebra} (hb : b ∈ Y.invariantSubalgebra) :
    f.restriction b ∈ X.invariantSubalgebra := by
  rw [mem_invariantSubalgebra] at hb ⊢
  intro k
  have ht := congrArg
    (fun q : BoundedAlgHom K Y.domain.obj.algebra X.domain.obj.algebra => q b)
    (f.sectionAction_restriction k)
  change f.restriction (Y.sectionOperator (f.groupHom k) b) =
    X.sectionOperator k (f.restriction b) at ht
  exact ht.symm.trans (congrArg f.restriction (hb (f.groupHom k)))

/-- The actual bounded quotient pullback, restricted to the fixed subalgebras.
The same positive norm bound works after both subtype restrictions. -/
def invariantRestriction (f : X ⟶ Y) :
    BoundedAlgHom K Y.invariantSubalgebra X.invariantSubalgebra where
  toAlgHom :=
    (f.restriction.toAlgHom.comp Y.invariantSubalgebra.val).codRestrict
      X.invariantSubalgebra (fun b => f.restriction_mem_invariantSubalgebra b.property)
  bounded := by
    obtain ⟨C, hC, hb⟩ := f.restriction.bounded
    exact ⟨C, hC, fun b => hb b⟩

@[simp]
theorem invariantRestriction_apply (f : X ⟶ Y) (b : Y.invariantSubalgebra) :
    (f.invariantRestriction b : X.domain.obj.algebra) =
      f.restriction (b : Y.domain.obj.algebra) := rfl

/-- The bounded inclusions commute with the actual quotient restrictions. -/
theorem invariantRestriction_inclusion (f : X ⟶ Y) :
    X.invariantInclusion.comp f.invariantRestriction =
      f.restriction.comp Y.invariantInclusion :=
  BoundedAlgHom.ext fun _ => rfl

@[simp]
theorem invariantRestriction_id (X : ρ.OpenSubgroupTransport) :
    (𝟙 X : X ⟶ X).invariantRestriction =
      BoundedAlgHom.id K X.invariantSubalgebra := by
  apply BoundedAlgHom.ext
  intro b
  apply Subtype.ext
  change (𝟙 X : X ⟶ X).restriction (b : X.domain.obj.algebra) = b
  rw [restriction_id]
  rfl

@[simp]
theorem invariantRestriction_comp (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).invariantRestriction =
      f.invariantRestriction.comp g.invariantRestriction := by
  apply BoundedAlgHom.ext
  intro b
  apply Subtype.ext
  change (f ≫ g).restriction (b : Z.domain.obj.algebra) =
    f.restriction (g.restriction (b : Z.domain.obj.algebra))
  rw [restriction_comp]
  rfl

end Hom

/-- Actual open-subgroup-fixed quotient sections and their constructed bounded
pullbacks, with norms forgotten to commutative K-algebras. -/
def invariantAlgebraPresheaf :
    (ρ.OpenSubgroupTransport)ᵒᵖ ⥤ CommAlgCat K where
  obj X := CommAlgCat.of K X.unop.invariantSubalgebra
  map f := CommAlgCat.ofHom f.unop.invariantRestriction.toAlgHom
  map_id X := by
    apply CommAlgCat.hom_ext
    exact congrArg BoundedAlgHom.toAlgHom (Hom.invariantRestriction_id X.unop)
  map_comp f g := by
    apply CommAlgCat.hom_ext
    exact congrArg BoundedAlgHom.toAlgHom (Hom.invariantRestriction_comp g.unop f.unop)

/-- The actual fixed-section inclusions form a natural transformation into the
published full quotient-algebra presheaf. -/
def invariantAlgebraInclusion :
    invariantAlgebraPresheaf (ρ := ρ) ⟶ algebraPresheaf where
  app X := CommAlgCat.ofHom X.unop.invariantInclusion.toAlgHom
  naturality _ _ f := by
    apply CommAlgCat.hom_ext
    exact congrArg BoundedAlgHom.toAlgHom f.unop.invariantRestriction_inclusion

/-- Every component inclusion is injective. -/
theorem invariantAlgebraInclusion_injective (X : (ρ.OpenSubgroupTransport)ᵒᵖ) :
    Function.Injective ((invariantAlgebraInclusion (ρ := ρ)).app X) := by
  intro b c h
  exact Subtype.ext h

/-- Subgroup restriction sends a fixed section to the same actual quotient
element, now fixed by the smaller subgroup. -/
@[simp]
theorem subgroupRestriction_invariantRestriction_apply
    {U V : OpenSubgroup G} (h : V ≤ U) (d : ρ.InvariantRationalDomain U)
    (b : ((inclusion U).obj d).invariantSubalgebra) :
    ((subgroupRestriction h d).invariantRestriction b).val = b.val := by
  change (subgroupRestriction h d).restriction b.val = _
  rw [subgroupRestriction_restriction]
  rfl

end OpenSubgroupTransport

end Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction
