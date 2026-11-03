import Langlands.GroupScheme.Adjoint.Quotient
import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.GroupScheme.Rational.RelativeCentralDirections
import Mathlib.LinearAlgebra.Isomorphisms

/-! # Actual maximal split tori in an adjoint quotient -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
variable {G A : GroupScheme (Spec (CommRingCat.of k))}
variable {T T_ad : CommGroupScheme (Spec (CommRingCat.of k))}

/-- An actual maximal split torus in the adjoint group, with its fppf map from
the supplied maximal split torus of the source. Finiteness of this map is not required. -/
structure IsAdjointSplitTorusImage (q : G ⟶ A) (i : T.toGrp ⟶ G)
    (j : T_ad.toGrp ⟶ A) (p : T ⟶ T_ad) : Prop where
  isAdjointQuotient : IsAdjointQuotient q
  sourceMaximal : IsMaximalSplitTorus i
  targetMaximal : IsMaximalSplitTorus j
  comp_eq : CommGroupScheme.groupHom p ≫ j = i ≫ q
  flat : Flat (CommGroupScheme.groupHom p).hom.hom.left
  surjective : Surjective (CommGroupScheme.groupHom p).hom.hom.left
  locallyOfFinitePresentation :
    LocallyOfFinitePresentation (CommGroupScheme.groupHom p).hom.hom.left

namespace IsAdjointSplitTorusImage

variable {q : G ⟶ A} {i : T.toGrp ⟶ G} {j : T_ad.toGrp ⟶ A} {p : T ⟶ T_ad}
variable (h : IsAdjointSplitTorusImage q i j p)
include h

/-- The map between the actual split tori is an fppf covering map. -/
theorem fppf :
    Flat (CommGroupScheme.groupHom p).hom.hom.left ∧
      LocallyOfFinitePresentation (CommGroupScheme.groupHom p).hom.hom.left ∧
      Surjective (CommGroupScheme.groupHom p).hom.hom.left :=
  ⟨h.flat, h.locallyOfFinitePresentation, h.surjective⟩

/-- On every test scheme, the kernel of the torus map is exactly the preimage
of the full centre of the source group. -/
theorem comp_eq_one_iff_mem_center
    (U : Over (Spec (CommRingCat.of k))) (x : U ⟶ T.toGrp.X) :
    x ≫ (CommGroupScheme.groupHom p).hom.hom = 1 ↔
      x ≫ i.hom.hom ∈ (center G).carrier U := by
  rw [h.isAdjointQuotient.mem_center_iff_comp_eq_one]
  have hsquare := congrArg (fun f : T.toGrp ⟶ A => f.hom.hom) h.comp_eq
  change (CommGroupScheme.groupHom p).hom.hom ≫ j.hom.hom =
    i.hom.hom ≫ q.hom.hom at hsquare
  let : IsClosedImmersion j.hom.hom.left := h.targetMaximal.1.2
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  constructor
  · intro hx
    rw [Category.assoc, ← hsquare, ← Category.assoc, hx, MonObj.one_comp]
  · intro hx
    apply (cancel_mono j.hom.hom).mp
    rw [Category.assoc, hsquare, ← Category.assoc, hx, MonObj.one_comp]

/-- The actual kernel inclusion has precisely the all-test range prescribed by
the intersection of the torus with the source centre. -/
theorem mem_range_kernel_iff
    (U : Over (Spec (CommRingCat.of k))) (x : U ⟶ T.toGrp.X) :
    x ∈ (SubgroupFunctor.range (kernelι (CommGroupScheme.groupHom p))).carrier U ↔
      x ≫ i.hom.hom ∈ (center G).carrier U :=
  (Langlands.GroupScheme.mem_range_kernelι_iff _ x).trans (h.comp_eq_one_iff_mem_center U x)

/-- Actual integral cocharacters satisfy the original quotient square after
composition into the source and adjoint groups. -/
theorem cocharacter_comp_eq (ν : cocharacterLattice T) :
    CommGroupScheme.groupHom (ν ≫ p) ≫ j =
      CommGroupScheme.groupHom ν ≫ i ≫ q := by
  change (CommGroupScheme.groupHom ν ≫ CommGroupScheme.groupHom p) ≫ j = _
  rw [Category.assoc, h.comp_eq]

end IsAdjointSplitTorusImage

/-- The additional real cocharacter comparison needed for the adjoint apartment
direction. Surjectivity is explicit input, with no integral lifting hypothesis. -/
structure IsAdjointSplitTorusComparison (q : G ⟶ A) (i : T.toGrp ⟶ G)
    (j : T_ad.toGrp ⟶ A) (p : T ⟶ T_ad) : Prop
    extends IsAdjointSplitTorusImage q i j p where
  realSurjective : Function.Surjective (RealTorusSpace.cocharacterMapReal p)

namespace IsAdjointSplitTorusComparison

variable {q : G ⟶ A} {i : T.toGrp ⟶ G} {j : T_ad.toGrp ⟶ A} {p : T ⟶ T_ad}
variable (h : IsAdjointSplitTorusComparison q i j p)

include h

/-- The real cocharacter space of the actual adjoint torus is the quotient by
the full real kernel of the actual torus map. -/
def realQuotientEquiv :
    (RealTorusSpace.V T ⧸ (RealTorusSpace.cocharacterMapReal p).ker) ≃ₗ[ℝ]
      RealTorusSpace.V T_ad :=
  (RealTorusSpace.cocharacterMapReal p).quotKerEquivOfSurjective h.realSurjective

/-- The real quotient equivalence is induced by the actual torus homomorphism. -/
theorem realQuotientEquiv_mk (v : RealTorusSpace.V T) :
    h.realQuotientEquiv (Submodule.Quotient.mk v) =
      RealTorusSpace.cocharacterMapReal p v :=
  LinearMap.quotKerEquivOfSurjective_apply_mk _ _ _

/-- Every real adjoint cocharacter vector lifts to a real vector of the original
torus, without a claim about integral or primitive lifts. -/
theorem exists_real_lift (v : RealTorusSpace.V T_ad) :
    ∃ w : RealTorusSpace.V T, RealTorusSpace.cocharacterMapReal p w = v :=
  h.realSurjective v

end IsAdjointSplitTorusComparison

end Langlands.GroupScheme
