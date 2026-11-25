import Langlands.GroupScheme.Torus.MultiplicativeTypeSubgroupInfinitesimalLiftStatement
import Langlands.GroupScheme.Torus.MultiplicativeTypeNilpotentEquivalenceProof
import Langlands.GroupScheme.Torus.MultiplicativeTypeFlatNilpotentReflectionProof
import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeGeometry
import Langlands.GroupScheme.HomScheme.InfinitesimalCohomologyReduction
import Langlands.GroupScheme.HomScheme.SquareZeroCohomology
import Langlands.GroupScheme.Cohomology.MultiplicativeTypeVanishingProof
import Langlands.GroupScheme.RepresentedSubgroup
import Langlands.AlgebraicGeometry.ImmersionNilpotentReflection

/-! # Lifting subgroups of multiplicative type through nilpotent thickenings -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

open RelativeMultiplicativeType
open Langlands.AlgebraicGeometry.ImmersionNilpotentReflection
  (isImmersion_of_nilpotent_baseChange)

/-- The Hom bijections for nilpotent reduction lift an isomorphism and its inverse. -/
private theorem liftMultiplicativeTypeIso
    (A : Type u) [CommRing A] (J : Ideal A) (hJ : IsNilpotent J)
    (H K : GroupScheme (Spec (CommRingCat.of A)))
    (hH : IsMultiplicativeType H) (hK : IsMultiplicativeType K)
    (e₀ : (GroupScheme.baseChange (Spec.algebraMap A (A ⧸ J))).obj H ≅
      (GroupScheme.baseChange (Spec.algebraMap A (A ⧸ J))).obj K) :
    ∃ e : H ≅ K,
      (GroupScheme.baseChange (Spec.algebraMap A (A ⧸ J))).map e.hom = e₀.hom := by
  let F := GroupScheme.baseChange (Spec.algebraMap A (A ⧸ J))
  have homs := (multiplicativeTypeNilpotentEquivalence A J hJ).2
  obtain ⟨f, hf⟩ := (homs H K hH hK).2 e₀.hom
  obtain ⟨g, hg⟩ := (homs K H hK hH).2 e₀.inv
  change F.map f = e₀.hom at hf
  change F.map g = e₀.inv at hg
  have hfg : f ≫ g = 𝟙 H := by
    apply (homs H H hH hH).1
    change F.map (f ≫ g) = F.map (𝟙 H)
    rw [F.map_comp, F.map_id, hf, hg, e₀.hom_inv_id]
  have hgf : g ≫ f = 𝟙 K := by
    apply (homs K K hK hK).1
    change F.map (g ≫ f) = F.map (𝟙 K)
    rw [F.map_comp, F.map_id, hg, hf, e₀.inv_hom_id]
  exact ⟨⟨f, g, hfg, hgf⟩, hf⟩

/-- Flat lifts, reflection of multiplicative type, and conjugacy of lifts for
immersive subgroups of a smooth group (SGA 3, IX, Théorème 3.6 bis). -/
theorem multiplicativeTypeSubgroupInfinitesimalLift :
    MultiplicativeTypeSubgroupInfinitesimalLiftStatement.{u} := by
  have homomorphisms : MultiplicativeTypeInfinitesimalLiftStatement.{u} :=
    HomScheme.multiplicativeTypeInfinitesimalLift_of_cohomology
      Cohomology.multiplicativeTypeLowDegreeVanishing
      HomScheme.squareZeroHomomorphismCohomology
      (fun _ _ h => h.flat)
      (fun _ _ h => h.isAffineHom)
  intro A _ J hJ G _
  let r := Spec.algebraMap A (A ⧸ J)
  let F := GroupScheme.baseChange r
  have objects := (multiplicativeTypeNilpotentEquivalence A J hJ).1
  refine ⟨?_, ?_, ?_⟩
  · intro H₀ h₀ hi₀ hMT₀
    let := hi₀
    obtain ⟨H, hMT, hflat, ⟨e₀⟩⟩ := objects H₀ hMT₀
    obtain ⟨h, hh⟩ := (homomorphisms A J hJ G H hMT).1 (e₀.hom ≫ h₀)
    have hred : IsImmersion (F.map h).hom.hom.left := by
      rw [hh]
      change IsImmersion (e₀.hom.hom.hom.left ≫ h₀.hom.hom.left)
      have : IsIso e₀.hom.hom.hom.left := by
        set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
        infer_instance
      infer_instance
    refine ⟨H, h, isImmersion_of_nilpotent_baseChange A J hJ h.hom.hom hred, hflat, ?_⟩
    rw [hh]
    exact SubgroupFunctor.range_iso_comp e₀ h₀
  · intro H _ _ hflat hMT₀
    exact multiplicativeTypeFlatNilpotentReflection A J hJ H hflat hMT₀
  · intro H K h k hi hflat hk kflat hMT₀ hrange
    have hred : IsImmersion (F.map h).hom.hom.left :=
      MorphismProperty.overPullbackMap (P := @IsImmersion) r h.hom.hom hi
    have kred : IsImmersion (F.map k).hom.hom.left :=
      MorphismProperty.overPullbackMap (P := @IsImmersion) r k.hom.hom hk
    let := hred
    let := kred
    let : Mono (F.map h).hom.hom := Over.mono_of_mono_left _
    let : Mono (F.map k).hom.hom := Over.mono_of_mono_left _
    have repH : (SubgroupFunctor.range (F.map h)).IsRepresentedBy (F.map h) :=
      ⟨inferInstance, rfl⟩
    have repK : (SubgroupFunctor.range (F.map h)).IsRepresentedBy (F.map k) :=
      ⟨inferInstance, hrange.symm⟩
    let e₀ := repH.isoOfIsRepresentedBy repK
    have he₀ : e₀.hom ≫ F.map k = F.map h :=
      repH.isoOfIsRepresentedBy_hom_comp repK
    have hMT : IsMultiplicativeType H :=
      multiplicativeTypeFlatNilpotentReflection A J hJ H hflat hMT₀
    have kMT₀ : IsMultiplicativeType (F.obj K) := hMT₀.of_iso e₀.symm
    have kMT : IsMultiplicativeType K :=
      multiplicativeTypeFlatNilpotentReflection A J hJ K kflat kMT₀
    obtain ⟨e, he⟩ := liftMultiplicativeTypeIso A J hJ H K hMT kMT e₀
    have hsame : F.map h = F.map (e.hom ≫ k) := by
      rw [F.map_comp, he, he₀]
    obtain ⟨g, hg, hconj⟩ := (homomorphisms A J hJ G H hMT).2 h (e.hom ≫ k) hsame
    refine ⟨g, hg, ?_⟩
    rw [← hconj]
    exact SubgroupFunctor.range_iso_comp e k

end Langlands.GroupScheme
