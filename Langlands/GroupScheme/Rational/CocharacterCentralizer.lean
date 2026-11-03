import Langlands.GroupScheme.Rational.RootSubgroup
import Langlands.GroupScheme.Rational.StandardLeviRootTransport

/-! # Cocharacter centralizers and character kernels -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace RelativeRoot

/-- The canonical lift of a cocharacter point to the actual character kernel. -/
def cocharacterKernelPoint
    {B : Scheme.{u}} {T : CommGroupScheme B}
    (a : characterLattice T) (zeta : cocharacterLattice T)
    (hzero : zeta ≫ a = 0) {U : Over B} (x : U ⟶ (Gm B).X) :
    U ⟶ (characterKernel a).X :=
  (kernelPointsEquiv (CommGroupScheme.groupHom a) U).symm
    ⟨x ≫ (CommGroupScheme.groupHom zeta).hom.hom, by
      change (x ≫ (CommGroupScheme.groupHom zeta).hom.hom) ≫
        (CommGroupScheme.groupHom a).hom.hom = 1
      rw [← comp_groupHom_comp, hzero, comp_groupHom_zero]⟩

/-- The lift maps to the given cocharacter point under the kernel inclusion. -/
@[simp] theorem cocharacterKernelPoint_comp_ι
    {B : Scheme.{u}} {T : CommGroupScheme B}
    (a : characterLattice T) (zeta : cocharacterLattice T)
    (hzero : zeta ≫ a = 0) {U : Over B} (x : U ⟶ (Gm B).X) :
    cocharacterKernelPoint a zeta hzero x ≫ (characterKernelι a).hom.hom =
      x ≫ (CommGroupScheme.groupHom zeta).hom.hom :=
  congrArg Subtype.val
    ((kernelPointsEquiv (CommGroupScheme.groupHom a) U).apply_symm_apply _)

/-- If a cocharacter factors through the actual character kernel, its dynamic
centralizer contains the centralizer of that kernel. -/
theorem kernelCentralizer_le_dynamicCentralizer_of_comp_eq_zero
    {B : Scheme.{u}} {T : CommGroupScheme B} {G : GroupScheme B}
    (i : T.toGrp ⟶ G) (a : characterLattice T) (zeta : cocharacterLattice T)
    (hzero : zeta ≫ a = 0) :
    kernelCentralizer i a ≤
      Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i) := by
  intro U g hg
  rw [← torusCentralizer_gm_eq_dynamicCentralizer,
    mem_torusCentralizer_iff_universal]
  have hcomm := (mem_kernelCentralizer i a).mp hg
    (U ⊗ (Gm B).X) (fst U (Gm B).X)
    (cocharacterKernelPoint a zeta hzero (snd U (Gm B).X))
  simpa only [Grp.comp_hom_hom, ← Category.assoc,
    cocharacterKernelPoint_comp_ι] using hcomm

/-- Zero integral pairing places the cocharacter in the actual character kernel. -/
theorem kernelCentralizer_le_dynamicCentralizer_of_pairing_eq_zero
    {k : Type u} [CommRing k] [IsDomain k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ G) (a : characterLattice T) (zeta : cocharacterLattice T)
    (h : latticePairing T a zeta = 0) :
    kernelCentralizer i a ≤
      Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i) := by
  apply kernelCentralizer_le_dynamicCentralizer_of_comp_eq_zero i a zeta
  apply (gmEndEquiv k).injective
  simpa only [latticePairing_apply, map_zero] using h

end RelativeRoot

/-- A normalizing base point centralizes the cocharacter exactly when its
induced torus automorphism fixes that cocharacter. -/
theorem normalizerPoint_mem_dynamicCentralizer_iff
    {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
    (n : normalizerPoints i) (zeta : cocharacterLattice T) :
    (n : Over.mk (𝟙 _) ⟶ G.X) ∈
        (Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i)).carrier
          (Over.mk (𝟙 _)) ↔
      cocharacterAut (normalizingAut i n) zeta = zeta := by
  rw [← torusCentralizer_gm_eq_dynamicCentralizer,
    mem_torusCentralizer_base_iff, ← groupHom_cocharacterAut_comp]
  constructor
  · intro h
    apply CommGroupScheme.hom_ext_points
    intro U x
    have : Mono i.hom.hom := Over.mono_of_mono_left _
    apply (cancel_mono i.hom.hom).mp
    have heq := congrArg
      (fun f : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G => x ≫ f.hom.hom) h
    simpa only [Grp.comp_hom_hom, Category.assoc] using heq
  · intro h
    rw [h]

end Langlands.GroupScheme
