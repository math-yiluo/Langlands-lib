import Langlands.GroupScheme.Rational.SplitTorus
import Langlands.GroupScheme.Torus.Lattice

/-! # Vanishing actual cocharacters implies split rank zero -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

/-- A commutative group scheme over a field with no nonzero actual
cocharacters has no nontrivial closed split subtorus. -/
theorem isAnisotropic_of_cocharacter_eq_zero
    (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (hT : ∀ ν : cocharacterLattice T, ν = 0) :
    IsAnisotropic T.toGrp := by
  apply isAnisotropic_iff.mpr
  intro I _ i hi
  let : IsClosedImmersion i.hom.hom.left := hi
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  let j : splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I ⟶ T :=
    Additive.ofMul i
  have hj : CommGroupScheme.groupHom j = i := by rfl
  refine ⟨fun a => ?_⟩
  have hs : splitTorus.single (Spec (CommRingCat.of k)) I a = 0 := by
    apply CommGroupScheme.hom_ext_points
    intro U x
    apply (cancel_mono i.hom.hom).mp
    have h := congrArg
      (fun f : cocharacterLattice T => x ≫ (CommGroupScheme.groupHom f).hom.hom)
      (hT (splitTorus.single (Spec (CommRingCat.of k)) I a ≫ j))
    simpa only [comp_groupHom_comp, comp_groupHom_zero, MonObj.one_comp, hj] using h
  have hid : (𝟙 (Gm (Spec (CommRingCat.of k)))) = 0 := by
    have h := congrArg
      (fun f : cocharacterLattice
          (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I) =>
        f ≫ splitTorus.proj (Spec (CommRingCat.of k)) I a) hs
    simpa [splitTorus.single_comp_proj] using h
  have h := congrArg (gmEndEquiv k) hid
  simp at h

end Langlands.GroupScheme
