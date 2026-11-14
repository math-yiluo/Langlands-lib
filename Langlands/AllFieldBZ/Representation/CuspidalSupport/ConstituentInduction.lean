import Langlands.AllFieldBZ.Representation.Category.ConstituentDichotomy
import Langlands.Representation.CuspidalSupport.ConstituentInduction

/-!
# All-field port of `Langlands.Representation.CuspidalSupport.ConstituentInduction`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.CuspidalSupport.ConstituentInduction` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
namespace Langlands.AllFieldBZ.CuspidalSupport
open Langlands.CuspidalSupport
open CategoryTheory
open Langlands.SmoothRep
universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

private def _root_.Langlands.CuspidalSupport.rangeFactor {A B : SmoothRep.{0, uG, uV} ℂ G}
    (f : A ⟶ B) : A ⟶ image f :=
  ofHom {
    toLinearMap := (hom f).toLinearMap.rangeRestrict
    isIntertwining' g := by
      ext v
      exact Subtype.ext (Representation.IntertwiningMap.isIntertwining _ _ (hom f) g v) }

omit [IsTopologicalGroup G] in
private theorem _root_.Langlands.CuspidalSupport.rangeFactor_surjective {A B : SmoothRep.{0, uG, uV} ℂ G}
    (f : A ⟶ B) : Function.Surjective (hom (rangeFactor f)) := by
  rintro ⟨v, w, hw⟩
  exact ⟨w, Subtype.ext hw⟩

/-- The nonscalar branch of strong induction. Its recursive hypothesis is
exactly the same conclusion for smaller fixed-vector dimensions. -/
private theorem _root_.Langlands.CuspidalSupport.constituentInduction_nonScalarStep
    (H : Subgroup G) (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (hKH : K.toSubgroup ≤ H)
    (A D : SmoothRep.{0, uG, uV} ℂ G)
    (hA : Representation.IsSemisimpleRepresentation (A.representation.comp H.subtype))
    (hgen : ∀ S : Subrepresentation (A.representation.comp H.subtype),
      fixedVectors A.representation K.toSubgroup ≤ S.toSubmodule → S = ⊤)
    [Module.Finite ℂ (fixedVectors A.representation K.toSubgroup)]
    (hD : D.IsIrreducible)
    [Nontrivial (fixedVectors D.representation K.toSubgroup)]
    (h : IsSubquotient D A)
    (z : Subgroup.center G) (c : ℂ)
    (hDz : ∀ v : D, D.representation z v = c • v)
    (hAz : ¬ ∀ v : A, A.representation z v = c • v)
    (ih : ∀ B : SmoothRep.{0, uG, uV} ℂ G,
      Module.finrank ℂ (fixedVectors B.representation K.toSubgroup) <
        Module.finrank ℂ (fixedVectors A.representation K.toSubgroup) →
      Representation.IsSemisimpleRepresentation (B.representation.comp H.subtype) →
      (∀ S : Subrepresentation (B.representation.comp H.subtype),
        fixedVectors B.representation K.toSubgroup ≤ S.toSubmodule → S = ⊤) →
      Module.Finite ℂ (fixedVectors B.representation K.toSubgroup) →
      IsSubquotient D B → IsSubrepresentation D B ∧ IsQuotient D B) :
    IsSubrepresentation D A ∧ IsQuotient D A := by
  let f := centralShift A z c
  obtain ⟨hklt, hilt, hclt⟩ :=
    centralShift_fixedVectors_descent H K hK hgen h z c hDz hAz
  have hker : IsSubquotient (kernel f) A :=
    (subrepresentation_isSubrepresentation (hom f).ker).isSubquotient
  have him : IsSubquotient (image f) A :=
    (subrepresentation_isSubrepresentation (hom f).range).isSubquotient
  have hcoker : IsSubquotient (cokernel f) A :=
    (quotient_isQuotient (hom f).range).isSubquotient
  have hkfin : Module.Finite ℂ (fixedVectors (kernel f).representation K.toSubgroup) :=
    Module.Finite.of_injective (fixedVectorsMap (hom (kernelι f)) K.toSubgroup)
      (fixedVectorsMap_injective _ (subtype_injective A (hom f).ker) K.toSubgroup)
  have hifin : Module.Finite ℂ (fixedVectors (image f).representation K.toSubgroup) :=
    Module.Finite.of_injective (fixedVectorsMap (hom (imageι f)) K.toSubgroup)
      (fixedVectorsMap_injective _ (subtype_injective A (hom f).range) K.toSubgroup)
  have hcfin : Module.Finite ℂ (fixedVectors (cokernel f).representation K.toSubgroup) :=
    Module.Finite.of_surjective (fixedVectorsMap (hom (cokernelπ f)) K.toSubgroup)
      (Compact.fixedVectorSurjectivity G A (cokernel f) A.representation
        (cokernel f).representation A.isSmooth (cokernel f).isSmooth K hK
        (hom (cokernelπ f)) (mkQ_surjective A (hom f).range))
  have applyIH (B : SmoothRep.{0, uG, uV} ℂ G)
      (hBA : IsSubquotient B A)
      (hlt : Module.finrank ℂ (fixedVectors B.representation K.toSubgroup) <
        Module.finrank ℂ (fixedVectors A.representation K.toSubgroup))
      (hfin : Module.Finite ℂ (fixedVectors B.representation K.toSubgroup))
      (hDB : IsSubquotient D B) : IsSubrepresentation D B ∧ IsQuotient D B := by
    obtain ⟨hB, hgenB⟩ := semisimple_fixedVectors_generate_subquotient
      H K.toSubgroup hKH hA hgen hBA
    exact ih B hlt hB hgenB hfin hDB
  constructor
  · rcases irreducibleSubquotient_kernel_or_image hD h f with hk | hi
    · obtain ⟨j, hj⟩ := (applyIH (kernel f) hker hklt hkfin hk).1
      refine ⟨j ≫ kernelι f, ?_⟩
      exact (subtype_injective A (hom f).ker).comp hj
    · obtain ⟨j, hj⟩ := (applyIH (image f) him hilt hifin hi).1
      refine ⟨j ≫ imageι f, ?_⟩
      exact (subtype_injective A (hom f).range).comp hj
  · rcases irreducibleSubquotient_image_or_cokernel hD h f with hi | hc
    · obtain ⟨q, hq⟩ := (applyIH (image f) him hilt hifin hi).2
      refine ⟨rangeFactor f ≫ q, ?_⟩
      exact hq.comp (rangeFactor_surjective f)
    · obtain ⟨q, hq⟩ := (applyIH (cokernel f) hcoker hclt hcfin hc).2
      refine ⟨cokernelπ f ≫ q, ?_⟩
      exact hq.comp (mkQ_surjective A (hom f).range)

end Langlands.AllFieldBZ.CuspidalSupport
