import Langlands.GroupScheme.Lie.ConjugationDerivation
import Langlands.GroupScheme.Dynamic.SmoothProof

/-! # The quotient spectrum of the actual Lie-element centralizer -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Lie

variable {R : CommRingCat.{u}} (G : GroupScheme (Spec R))
  [IsAffineHom G.X.hom]

/-- The quotient coordinate algebra defined by infinitesimal conjugation. -/
abbrev elementCentralizerQuotientAlgebra (X : lieKernel G R) : CommAlgCat R :=
  CommAlgCat.of R (coordinateAlgebra G ⧸ conjugationIdeal G X)

/-- The quotient spectrum as a scheme over the original base. -/
abbrev elementCentralizerQuotient (X : lieKernel G R) : Over (Spec R) :=
  (algSpec R).obj (op (elementCentralizerQuotientAlgebra G X))

/-- The closed inclusion of the quotient spectrum into the original affine group. -/
def elementCentralizerQuotientι (X : lieKernel G R) :
    elementCentralizerQuotient G X ⟶ G.X :=
  (algSpec R).map (CommAlgCat.ofHom
    (Ideal.Quotient.mkₐ R (conjugationIdeal G X))).op ≫ (coordinateIso G).hom

@[simp] theorem pointCoordinates_elementCentralizerQuotientι (X : lieKernel G R) :
    pointCoordinates G (elementCentralizerQuotientι G X) =
      Ideal.Quotient.mkₐ R (conjugationIdeal G X) :=
  (pointCoordinates G).apply_symm_apply _

/-- The quotient inclusion is itself a point of the original all-test
Lie-element centralizer. -/
theorem elementCentralizerQuotientι_mem (X : lieKernel G R) :
    elementCentralizerQuotientι G X ∈
      (elementCentralizer G X).carrier (elementCentralizerQuotient G X) := by
  rw [mem_elementCentralizer_affine_iff_conjugationIdeal,
    pointCoordinates_elementCentralizerQuotientι]
  intro c hc
  exact Ideal.Quotient.eq_zero_iff_mem.2 hc

/-- A centralizing affine test point factors through the quotient spectrum. -/
theorem exists_comp_elementCentralizerQuotientι
    (X : lieKernel G R) {A : Type u} [CommRing A] [Algebra R A]
    (g : AffinePoints G A)
    (hg : g ∈ (elementCentralizer G X).carrier
      ((algSpec R).obj (op (CommAlgCat.of R A)))) :
    ∃ y : (algSpec R).obj (op (CommAlgCat.of R A)) ⟶
        elementCentralizerQuotient G X,
      y ≫ elementCentralizerQuotientι G X = g := by
  have hker := (mem_elementCentralizer_affine_iff_conjugationIdeal G X g).1 hg
  let f : (coordinateAlgebra G ⧸ conjugationIdeal G X) →ₐ[R] A :=
    Ideal.Quotient.liftₐ _ (pointCoordinates G g) (fun c hc => hker hc)
  refine ⟨(algSpec R).map (CommAlgCat.ofHom f).op, ?_⟩
  have hf : CommAlgCat.ofHom (Ideal.Quotient.mkₐ R (conjugationIdeal G X)) ≫
      CommAlgCat.ofHom f = CommAlgCat.ofHom (pointCoordinates G g) := by
    apply CommAlgCat.hom_ext
    exact Ideal.Quotient.liftₐ_comp _ _ _
  rw [elementCentralizerQuotientι, ← Category.assoc, ← Functor.map_comp,
    ← op_comp, hf]
  exact (pointCoordinates G).symm_apply_apply g

set_option backward.isDefEq.respectTransparency.types false in
/-- The quotient spectrum is a closed subscheme of the original group. -/
theorem isClosedImmersion_elementCentralizerQuotientι (X : lieKernel G R) :
    IsClosedImmersion (elementCentralizerQuotientι G X).left := by
  have hq : IsClosedImmersion
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (conjugationIdeal G X)))) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have he : IsIso (coordinateIso G).hom.left :=
    (Over.forget (Spec R)).map_isIso (coordinateIso G).hom
  have hc : IsClosedImmersion (coordinateIso G).hom.left := inferInstance
  change IsClosedImmersion
    (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (conjugationIdeal G X))) ≫
      (coordinateIso G).hom.left)
  exact @IsClosedImmersion.comp _ _ _ _ _ hq hc

instance mono_elementCentralizerQuotientι (X : lieKernel G R) :
    Mono (elementCentralizerQuotientι G X) := by
  have := isClosedImmersion_elementCentralizerQuotientι G X
  exact Over.mono_of_mono_left _

private theorem universalPoint_eq_coordinateIso_hom
    (H : GroupScheme (Spec R)) [IsAffineHom H.X.hom] :
    universalPoint H = (coordinateIso H).hom := by
  change (algSpec R).map (𝟙 _) ≫ _ = _
  simp

/-- Every affine representative of the actual Lie-element centralizer is
isomorphic over the base to the image-ideal quotient spectrum, compatibly
with its inclusion into the original group. -/
theorem exists_elementCentralizerQuotientIso
    (X : lieKernel G R) {C : GroupScheme (Spec R)} [IsAffineHom C.X.hom]
    (j : C ⟶ G) (hrep : (elementCentralizer G X).IsRepresentedBy j) :
    ∃ e : C.X ≅ elementCentralizerQuotient G X,
      e.hom ≫ elementCentralizerQuotientι G X = j.hom.hom := by
  let : Mono j.hom.hom := hrep.1
  have hq := elementCentralizerQuotientι_mem G X
  rw [← hrep.2, SubgroupFunctor.mem_range] at hq
  obtain ⟨i, hi⟩ := hq
  have hj : universalPoint C ≫ j.hom.hom ∈
      (elementCentralizer G X).carrier
        ((algSpec R).obj (op (coordinateAlgebra C))) := by
    rw [← hrep.2, SubgroupFunctor.mem_range]
    exact ⟨universalPoint C, rfl⟩
  obtain ⟨y, hy⟩ := exists_comp_elementCentralizerQuotientι G X
    (universalPoint C ≫ j.hom.hom) hj
  let r : C.X ⟶ elementCentralizerQuotient G X := (coordinateIso C).inv ≫ y
  have hr : r ≫ elementCentralizerQuotientι G X = j.hom.hom := by
    dsimp only [r]
    rw [Category.assoc, hy, universalPoint_eq_coordinateIso_hom,
      Iso.inv_hom_id_assoc]
  refine ⟨⟨r, i, ?_, ?_⟩, hr⟩
  · apply (cancel_mono j.hom.hom).1
    rw [Category.assoc, hi, hr, Category.id_comp]
  · apply (cancel_mono (elementCentralizerQuotientι G X)).1
    rw [Category.assoc, hr, hi, Category.id_comp]

/-- The quotient-spectrum comparison for any closed representative of the
actual centralizer; its affineness follows from the closed inclusion. -/
theorem exists_elementCentralizerQuotientIso_of_isClosedSubgroup
    (X : lieKernel G R) {C : GroupScheme (Spec R)}
    (j : C ⟶ G) (hrep : (elementCentralizer G X).IsRepresentedBy j)
    (hj : IsClosedSubgroup j) :
    ∃ e : C.X ≅ elementCentralizerQuotient G X,
      e.hom ≫ elementCentralizerQuotientι G X = j.hom.hom := by
  have : IsClosedImmersion j.hom.hom.left := hj
  have : IsAffineHom C.X.hom := by
    rw [← Over.w j.hom.hom]
    infer_instance
  exact exists_elementCentralizerQuotientIso G X j hrep

section Smoothness

variable {k : Type u} [Field k] [IsAlgClosed k]
  (H : GroupScheme (Spec (CommRingCat.of k)))
  [IsAffineHom H.X.hom] [Smooth H.X.hom]

/-- Local semisimplicity of actual conjugation on affine coordinates implies
smoothness of its quotient spectrum over an algebraically closed field. -/
theorem smooth_elementCentralizerQuotient_of_locallySemisimple
    (X : lieKernel H k)
    (hD : Langlands.Algebra.SemisimpleDerivation.LocallySemisimple
      (conjugationDerivation H X).toLinearMap) :
    Smooth (elementCentralizerQuotient H X).hom := by
  have : Algebra.Smooth (CommRingCat.of k) (coordinateAlgebra H) :=
    (DynamicSmooth.smooth_algSpec_iff _).1
      (smooth_of_over_iso (coordinateIso H) inferInstance)
  apply (DynamicSmooth.smooth_algSpec_iff
    (elementCentralizerQuotientAlgebra H X)).2
  change Algebra.Smooth k (coordinateAlgebra H ⧸ conjugationIdeal H X)
  rw [conjugationIdeal_eq_imageIdeal]
  exact Langlands.Algebra.SemisimpleDerivation.smooth_quotient_imageIdeal_of_locallySemisimple
    (conjugationDerivation H X) hD

/-- Local semisimplicity of the actual global conjugation derivation supplies
smoothness of every closed representative of the original centralizer functor. -/
theorem smooth_elementCentralizer_of_locallySemisimple
    (X : lieKernel H k)
    (hD : Langlands.Algebra.SemisimpleDerivation.LocallySemisimple
      (conjugationDerivation H X).toLinearMap)
    {C : GroupScheme (Spec (CommRingCat.of k))}
    (j : C ⟶ H) (hrep : (elementCentralizer H X).IsRepresentedBy j)
    (hj : IsClosedSubgroup j) :
    Smooth C.X.hom := by
  obtain ⟨e, _⟩ := exists_elementCentralizerQuotientIso_of_isClosedSubgroup H X j hrep hj
  exact smooth_of_over_iso e
    (smooth_elementCentralizerQuotient_of_locallySemisimple H X hD)

end Smoothness

end Langlands.GroupScheme.Lie
