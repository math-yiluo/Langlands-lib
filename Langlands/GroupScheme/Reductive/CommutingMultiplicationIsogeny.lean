import Langlands.GroupScheme.Reductive.CommutingMultiplicationKernel
import Langlands.GroupScheme.ProductProperties
import Mathlib.AlgebraicGeometry.Noetherian
import Langlands.GroupScheme.Reductive.Semisimple
import Langlands.GroupScheme.CentralIsogeny.FiniteKernelQuotient

/-! # Central kernels of multiplication of commuting subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Base

variable {S : Scheme.{u}} {H K G : GroupScheme S}
variable (j : H ⟶ G) (i : K ⟶ G)
variable (hc : ∀ (T : Over S) (h : T ⟶ H.X) (x : T ⟶ K.X),
  Commute (h ≫ j.hom.hom) (x ≫ i.hom.hom))

/-- A central closed subgroup of a group with finite full centre is finite. -/
theorem isFinite_of_isClosedSubgroup_of_isCentral_of_hasFiniteCenter
    {N D : GroupScheme S} (n : N ⟶ D) (hn : IsClosedSubgroup n)
    (hc : IsCentral n) (hD : HasFiniteCenter D) : IsFinite N.X.hom := by
  obtain ⟨Z, z, hz, hZ⟩ := hD
  let f := hz.isRepresentedBy.factorHom n ((isCentral_iff_range_le_center n).mp hc)
  have hf : f ≫ z = n := hz.isRepresentedBy.factorHom_comp n _
  have : IsClosedImmersion n.hom.hom.left := hn
  have : IsClosedImmersion z.hom.hom.left := hz.1
  have hcomp : IsClosedImmersion (f.hom.hom.left ≫ z.hom.hom.left) := by
    rw [← Over.comp_left, ← Grp.comp_hom_hom, hf]
    infer_instance
  have : IsClosedImmersion f.hom.hom.left := IsClosedImmersion.of_comp f.hom.hom.left z.hom.hom.left
  have : IsFinite Z.X.hom := hZ
  rw [← Over.w f.hom.hom]
  infer_instance

end Base

section Field

variable {k : Type u} [Field k]
variable {H K G : GroupScheme (Spec (CommRingCat.of k))}

/-- Surjective multiplication of closed commuting subgroups with finite actual
kernel is a central isogeny. -/
theorem isCentralIsogeny_commutingSubgroupMultiplicationHom_of_finite_kernel
    [IsAffineHom G.X.hom] [Smooth G.X.hom]
    (j : H ⟶ G) (i : K ⟶ G) (hj : IsClosedSubgroup j) (hi : IsClosedSubgroup i)
    (hc : ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X) (x : T ⟶ K.X),
      Commute (h ≫ j.hom.hom) (x ≫ i.hom.hom))
    (hs : Surjective (subgroupMultiplication j i).left)
    (hker : IsFinite (kernel (commutingSubgroupMultiplicationHom j i hc)).X.hom) :
    IsCentralIsogeny (commutingSubgroupMultiplicationHom j i hc) := by
  let f := commutingSubgroupMultiplicationHom j i hc
  have : IsClosedImmersion j.hom.hom.left := hj
  have : IsClosedImmersion i.hom.hom.left := hi
  have : Mono j.hom.hom := Over.mono_of_mono_left _
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have : IsAffineHom H.X.hom := by
    rw [← Over.w j.hom.hom]
    infer_instance
  have : IsAffineHom K.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  have : IsAffineHom (H ⊗ K).X.hom := by
    change IsAffineHom (Limits.pullback.fst H.X.hom K.X.hom ≫ H.X.hom)
    have : IsAffineHom (Limits.pullback.fst H.X.hom K.X.hom) := by
      set_option backward.isDefEq.respectTransparency.types false in
      exact MorphismProperty.pullback_fst _ _ ‹IsAffineHom K.X.hom›
    infer_instance
  have : QuasiCompact f.hom.hom.left := by
    have : QuasiCompact (f.hom.hom.left ≫ G.X.hom) := by
      rw [Over.w f.hom.hom]
      infer_instance
    exact QuasiCompact.of_comp _ G.X.hom
  have : Flat f.hom.hom.left :=
    subgroupMultiplication_flat_of_closedSubgroups j i hj hi hc hs
  have : Surjective f.hom.hom.left := hs
  have : IsFinite (kernel f).X.hom := hker
  have : IsFinite f.hom.hom.left := isFinite_of_finite_kernel f
  have : IsLocallyNoetherian G.X.left :=
    LocallyOfFiniteType.isLocallyNoetherian G.X.hom
  have : LocallyOfFinitePresentation f.hom.hom.left := inferInstance
  exact ⟨⟨inferInstance, inferInstance, inferInstance⟩, inferInstance,
    isCentral_kernelι_commutingSubgroupMultiplicationHom j i hc⟩

/-- The actual surjective commuting multiplication, bundled with its central
isogeny property when its full kernel is finite. -/
def commutingMultiplicationWithFiniteKernel
    [IsAffineHom G.X.hom] [Smooth G.X.hom]
    (j : H ⟶ G) (i : K ⟶ G) (hj : IsClosedSubgroup j) (hi : IsClosedSubgroup i)
    (hc : ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X) (x : T ⟶ K.X),
      Commute (h ≫ j.hom.hom) (x ≫ i.hom.hom))
    (hs : Surjective (subgroupMultiplication j i).left)
    (hker : IsFinite (kernel (commutingSubgroupMultiplicationHom j i hc)).X.hom) :
    { f : H ⊗ K ⟶ G // IsCentralIsogeny f } :=
  ⟨commutingSubgroupMultiplicationHom j i hc,
    isCentralIsogeny_commutingSubgroupMultiplicationHom_of_finite_kernel
      j i hj hi hc hs hker⟩

@[simp]
theorem commutingMultiplicationWithFiniteKernel_val
    [IsAffineHom G.X.hom] [Smooth G.X.hom]
    (j : H ⟶ G) (i : K ⟶ G) (hj : IsClosedSubgroup j) (hi : IsClosedSubgroup i)
    (hc : ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X) (x : T ⟶ K.X),
      Commute (h ≫ j.hom.hom) (x ≫ i.hom.hom))
    (hs : Surjective (subgroupMultiplication j i).left)
    (hker : IsFinite (kernel (commutingSubgroupMultiplicationHom j i hc)).X.hom) :
    (commutingMultiplicationWithFiniteKernel j i hj hi hc hs hker).val =
      commutingSubgroupMultiplicationHom j i hc := rfl

end Field

end Langlands.GroupScheme
