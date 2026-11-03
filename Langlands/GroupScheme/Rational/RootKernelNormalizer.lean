import Langlands.GroupScheme.Rational.RootSubgroup
import Langlands.GroupScheme.Rational.TorusNormalizer

/-! # Kernel centralization and the normalizing torus automorphism -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {B : Scheme.{u}} {T : CommGroupScheme B} {G : GroupScheme B}

/-- The torus endomorphism whose pullback on a character is identity minus
the Weyl action of the normalizing point. -/
def normalizerDifference (i : T.toGrp ⟶ G) (n : normalizerPoints i) : T ⟶ T :=
  𝟙 T - (normalizingAut i n).inv

variable {i : T.toGrp ⟶ G} [Mono i.hom.hom.left]

/-- A normalizing point centralizes the full character kernel exactly when
its torus automorphism fixes the actual kernel inclusion. -/
theorem IsNormalizingPoint.mem_kernelCentralizer_iff
    {n : Over.mk (𝟙 B) ⟶ G.X} {σ : T ≅ T}
    (hn : IsNormalizingPoint i n σ) (a : characterLattice T) :
    n ∈ (RelativeRoot.kernelCentralizer i a).carrier (Over.mk (𝟙 B)) ↔
      RelativeRoot.characterKernelι a ≫ CommGroupScheme.groupHom σ.hom =
        RelativeRoot.characterKernelι a := by
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  constructor
  · intro hc
    apply hom_ext_points
    intro V c
    apply (cancel_mono i.hom.hom).mp
    have hcomm := (RelativeRoot.mem_kernelCentralizer i a).mp hc V
      (Over.homMk V.hom (by simp)) c
    rw [comp_eq_constantPoint] at hcomm
    have hconj := hn.conj_comp V (c ≫ (RelativeRoot.characterKernelι a).hom.hom)
    simp only [Grp.comp_hom_hom, Category.assoc] at hcomm hconj
    rw [hcomm.eq, mul_inv_cancel_right] at hconj
    simpa only [Grp.comp_hom_hom, Category.assoc] using hconj.symm
  · intro hfix
    rw [RelativeRoot.mem_kernelCentralizer]
    intro V b c
    rw [comp_eq_constantPoint, Grp.comp_hom_hom]
    have hconj := hn.conj_comp V (c ≫ (RelativeRoot.characterKernelι a).hom.hom)
    have he := congrArg (fun f => c ≫ f.hom.hom ≫ i.hom.hom) hfix
    simp only [Grp.comp_hom_hom, Category.assoc] at he
    simp only [Category.assoc] at hconj
    rw [he] at hconj
    exact (mul_inv_eq_iff_eq_mul.mp hconj : _)

/-- Both directions of the normalizing automorphism fix the full kernel. -/
theorem IsNormalizingPoint.characterKernel_comp_inv
    {n : Over.mk (𝟙 B) ⟶ G.X} {σ : T ≅ T}
    (hn : IsNormalizingPoint i n σ) (a : characterLattice T)
    (hc : n ∈ (RelativeRoot.kernelCentralizer i a).carrier (Over.mk (𝟙 B))) :
    RelativeRoot.characterKernelι a ≫ CommGroupScheme.groupHom σ.inv =
      RelativeRoot.characterKernelι a :=
  (hn.inv.mem_kernelCentralizer_iff a).mp
    ((RelativeRoot.kernelCentralizer i a).carrier _ |>.inv_mem hc)

/-- On every test scheme, the difference between identity and the inverse
normalizing automorphism kills every point of the actual character kernel. -/
theorem IsNormalizingPoint.characterKernel_comp_difference
    {n : Over.mk (𝟙 B) ⟶ G.X} {σ : T ≅ T}
    (hn : IsNormalizingPoint i n σ) (a : characterLattice T)
    (hc : n ∈ (RelativeRoot.kernelCentralizer i a).carrier (Over.mk (𝟙 B))) :
    RelativeRoot.characterKernelι a ≫ CommGroupScheme.groupHom (𝟙 T - σ.inv) = 1 := by
  apply hom_ext_points
  intro V c
  have he := congrArg (fun f => c ≫ f.hom.hom) (hn.characterKernel_comp_inv a hc)
  simp only [Grp.comp_hom_hom] at he
  change (c ≫ (RelativeRoot.characterKernelι a).hom.hom) ≫
      (CommGroupScheme.groupHom (𝟙 T - σ.inv)).hom.hom = _
  have hsub := congrArg Additive.toMul
    ((evalPoint (c ≫ (RelativeRoot.characterKernelι a).hom.hom)).map_sub (𝟙 T) σ.inv)
  change (c ≫ (RelativeRoot.characterKernelι a).hom.hom) ≫
      (CommGroupScheme.groupHom (𝟙 T - σ.inv)).hom.hom =
      (c ≫ (RelativeRoot.characterKernelι a).hom.hom) *
      ((c ≫ (RelativeRoot.characterKernelι a).hom.hom) ≫
        (CommGroupScheme.groupHom σ.inv).hom.hom)⁻¹ at hsub
  rw [hsub, Category.assoc, he, mul_inv_cancel]
  simp

/-- A normalizing point centralizing the full kernel has a difference
endomorphism which is trivial on that same kernel. -/
theorem normalizerDifference_kills_characterKernel (n : normalizerPoints i)
    (a : characterLattice T)
    (hc : n.val ∈ (RelativeRoot.kernelCentralizer i a).carrier (Over.mk (𝟙 B))) :
    RelativeRoot.characterKernelι a ≫ CommGroupScheme.groupHom (normalizerDifference i n) = 0 :=
  (isNormalizingPoint_normalizingAut i n).characterKernel_comp_difference a hc

end Langlands.GroupScheme
