import Langlands.GroupScheme.Reductive.AffinePinnedRootVectors
import Langlands.GroupScheme.Lie.ElementCentralizer

/-! # Coefficient-test naturality of actual simple pinning points -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme.AffinePinnedModel

/-- The dual-number coefficient morphism attached to an actual morphism
between coefficient spectra, independent of any original model ring. -/
def dualCoefficientMap {A B : Type u} [CommRing A] [CommRing B]
    (b : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A)) :
    Spec (CommRingCat.of (DualNumber B)) ⟶ Spec (CommRingCat.of (DualNumber A)) :=
  Spec.map (CommRingCat.ofHom
    (GeneralLinear.DualNumber.coefficientMap (Spec.preimage b).hom))

/-- The dual coefficient map lies over the original coefficient-spectrum map. -/
theorem dualCoefficientMap_base {A B : Type u} [CommRing A] [CommRing B]
    (b : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A)) :
    dualCoefficientMap b ≫ algebraBaseMap A (DualNumber A) =
      algebraBaseMap B (DualNumber B) ≫ b := by
  conv_rhs => rw [← Spec.map_preimage b]
  simp only [dualCoefficientMap, algebraBaseMap, ← Spec.map_comp]
  congr 1
  ext x
  · rfl
  · exact map_zero (Spec.preimage b).hom

variable (M : AffinePinnedModel.{u}) {T : Scheme.{u}} (f : T ⟶ M.base)
    (A B : Type u) [CommRing A] [CommRing B]
    [Algebra M.ring A] [Algebra M.ring B]
    (a : Spec (CommRingCat.of A) ⟶ T)
    (b : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A))
    (ha : algebraBaseMap M.ring A = a ≫ f)
    (hb : algebraBaseMap M.ring B = (b ≫ a) ≫ f)

/-- The original model's actual pinning point is natural under every
coefficient-spectrum refinement compatible with its base map. -/
theorem rootVectorPoint_coefficient (s : M.basis.support) :
    dualCoefficientMap b ≫ M.rootVectorPoint f A a ha s =
      M.rootVectorPoint f B (b ≫ a) hb s := by
  let b₀ : (algSpec (CommRingCat.of M.ring)).obj (op (CommAlgCat.of M.ring B)) ⟶
      (algSpec (CommRingCat.of M.ring)).obj (op (CommAlgCat.of M.ring A)) :=
    Over.homMk b (by
      change b ≫ algebraBaseMap M.ring A = algebraBaseMap M.ring B
      rw [ha]
      simpa only [Category.assoc] using hb.symm)
  let φ : A →ₐ[M.ring] B :=
    (algSpec.fullyFaithful.preimage b₀).unop.hom
  have hφmap : (algSpec (CommRingCat.of M.ring)).map (CommAlgCat.ofHom φ).op = b₀ :=
    algSpec.fullyFaithful.map_preimage b₀
  have hφspec : Spec.map (CommRingCat.ofHom φ.toRingHom) = b :=
    congrArg (fun z => z.left) hφmap
  have hφ : φ.toRingHom = (Spec.preimage b).hom :=
    congrArg (fun z => z.hom) (Spec.map_injective
      (hφspec.trans (Spec.map_preimage b).symm))
  have hvector : lieKernelMap M.group φ (M.rootVectorAt A s) = M.rootVectorAt B s := by
    change lieKernelMap M.group φ
      (lieKernelMap M.group (Algebra.ofId M.ring A) (M.pinning s 1).val.toMul) = _
    rw [← lieKernelMap_comp]
    have hcomp : φ.comp (Algebra.ofId M.ring A) = Algebra.ofId M.ring B :=
      Subsingleton.elim _ _
    rw [hcomp]
    rfl
  have hleft := congrArg (fun z : lieKernel M.group B => z.val.left) hvector
  change Spec.map (CommRingCat.ofHom
      (GeneralLinear.DualNumber.coefficientMap φ.toRingHom)) ≫
        (M.rootVectorAt A s).val.left = (M.rootVectorAt B s).val.left at hleft
  rw [hφ] at hleft
  apply pullback.hom_ext
  · rw [Category.assoc, rootVectorPoint_fst, rootVectorPoint_fst]
    exact hleft
  · change (dualCoefficientMap b ≫ M.rootVectorPoint f A a ha s) ≫
        (M.groupOver f).X.hom =
      M.rootVectorPoint f B (b ≫ a) hb s ≫ (M.groupOver f).X.hom
    rw [Category.assoc, rootVectorPoint_snd, rootVectorPoint_snd,
      ← Category.assoc, dualCoefficientMap_base, Category.assoc]

end Langlands.GroupScheme.AffinePinnedModel
