import Langlands.GroupScheme.DominantHomFaithfullyFlat
import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.GroupScheme.NormalSubgroupQuotientStatement

/-! # Smooth affine quotients from prescribed affine kernels -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace AffineHomImage

variable {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom] (f : G ⟶ H)

/-- Restricting the codomain to the actual image does not change the full kernel. -/
theorem kernel_range_projection :
    SubgroupFunctor.range (kernelι (projection f)) = SubgroupFunctor.range (kernelι f) := by
  have : Mono (inclusion f).hom.hom := Over.mono_of_mono_left _
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro x
  rw [mem_range_kernelι_iff, mem_range_kernelι_iff]
  constructor
  · intro hx
    rw [← projection_inclusion f, Grp.comp_hom_hom, ← Category.assoc, hx, MonObj.one_comp]
  · intro hx
    apply (cancel_mono (inclusion f).hom.hom).mp
    rw [Category.assoc, ← Grp.comp_hom_hom, projection_inclusion, hx, MonObj.one_comp]

/-- The actual image projection represents the fppf quotient by the full kernel. -/
theorem isFppfQuotient [Smooth G.X.hom] [LocallyOfFiniteType H.X.hom] :
    RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (kernelι f)) (projection f) := by
  obtain ⟨_, hf, hs, hl, _⟩ := projection_geometry f
  exact ⟨hf, hs, hl, kernel_range_projection f⟩

end AffineHomImage

/-- An actual homomorphism into an affine finite-type group supplies a smooth
and affine fppf quotient of a smooth affine source by its full kernel. -/
def AffineKernelQuotientStatement : Prop :=
  ∀ (k : Type u) [Field k] (G H : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom] (f : G ⟶ H),
    ∃ (Q : GroupScheme (Spec (CommRingCat.of k))) (q : G ⟶ Q),
      Smooth Q.X.hom ∧ IsAffineHom Q.X.hom ∧
        RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (kernelι f)) q

/-- The image group and its original projection prove the kernel quotient statement. -/
theorem affineKernelQuotient : AffineKernelQuotientStatement.{u} := by
  intro k _ G H _ _ _ _ f
  exact ⟨AffineHomImage.image f, AffineHomImage.projection f,
    AffineHomImage.smooth_image f, inferInstance, AffineHomImage.isFppfQuotient f⟩

/-- A prescribed all-test represented kernel yields the target quotient conclusion. -/
theorem exists_quotient_of_affine_kernel {k : Type u} [Field k]
    {G H N : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom]
    (i : N ⟶ G) (f : G ⟶ H)
    (hf : SubgroupFunctor.range (kernelι f) = SubgroupFunctor.range i) :
    ∃ (Q : GroupScheme (Spec (CommRingCat.of k))) (q : G ⟶ Q),
      Smooth Q.X.hom ∧ IsAffineHom Q.X.hom ∧
        RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q := by
  obtain ⟨Q, q, hQ, hQa, hq⟩ := affineKernelQuotient k G H f
  rw [hf] at hq
  exact ⟨Q, q, hQ, hQa, hq⟩

/-- The outstanding construction input: a normal closed subgroup is the full
kernel of a homomorphism into some affine locally finite type group. -/
def NormalSubgroupAffineKernelStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (N : GroupScheme (Spec (CommRingCat.of k))) (i : N ⟶ G),
    IsClosedSubgroup i → (SubgroupFunctor.range i).IsNormal →
      ∃ (H : GroupScheme (Spec (CommRingCat.of k))) (f : G ⟶ H),
        IsAffineHom H.X.hom ∧ LocallyOfFiniteType H.X.hom ∧
          SubgroupFunctor.range (kernelι f) = SubgroupFunctor.range i

/-- Exact reduction to the unchanged, universe-general target statement. -/
theorem normalSubgroupQuotient_of_affineKernel
    (h : NormalSubgroupAffineKernelStatement.{u}) : NormalSubgroupQuotientStatement.{u} := by
  intro k _ G _ _ N i hi hn
  obtain ⟨H, f, ha, hl, hk⟩ := h k G N i hi hn
  have := ha
  have := hl
  exact exists_quotient_of_affine_kernel i f hk

end Langlands.GroupScheme
