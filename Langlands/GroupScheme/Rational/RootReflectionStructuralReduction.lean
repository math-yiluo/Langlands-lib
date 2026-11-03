import Langlands.GroupScheme.Rational.RootKernelOppositeNormalizer
import Langlands.GroupScheme.Rational.KernelCentralizerComponentReductiveStatement
import Langlands.GroupScheme.Rational.RootReflectionExistenceStatement
import Langlands.GroupScheme.Reductive.GroundFieldRadical

/-! # Relative-root reflections from explicit structural inputs -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

variable
    (hUnip : RelativeRoot.TorusActionUnipotenceStatement.{u})
    (hConnected : DynamicConnectedStatement.{u})
    (hTconj : SmoothMaximalSplitTorusConjugacyStatement.{u})
    (hMinConj : MinimalPseudoParabolicConjugacyStatement.{u})
    (hKernel : RelativeRoot.KernelCentralizerComponentReductiveStatement.{u})
    (hExtension : UnipotentFieldExtensionStatement.{u})

include hUnip hConnected hTconj hMinConj hKernel hExtension

/-- Six explicit structural inputs imply the exact published integral
relative-root reflection existence proposition. -/
theorem relativeRootReflectionExistence_of_structure :
    RelativeRootReflectionExistenceStatement.{u} := by
  intro k _ G hG T i hi
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
  apply exists_reflectionData_of_kernelCentralizing_representatives i hi.1.1
  intro a
  obtain ⟨C, j, hj, hjc, hs, _hLie⟩ :=
    RelativeRoot.kernelCentralizerStructure k G hG.smooth hG.isAffineHom
      T hi.1.1 i a.val a.property.1
  let : Smooth C.X.hom := hs
  let : IsClosedImmersion j.hom.hom.left := hjc
  let : IsAffineHom C.X.hom := by
    have h : IsAffineHom (j.hom.hom.left ≫ G.X.hom) := inferInstance
    simpa only [Over.w] using h
  have hC := hKernel k G hG T hi.1.1 i a.val a.property.1 C j hj hjc hs
  have hR := hC.hasTrivialUnipotentRadical_of_unipotentFieldExtension hExtension
  exact ⟨RelativeRoot.kernelCentralizerOppositeNormalizer
      hUnip hConnected hTconj hMinConj i hi a.val a.property j hj hjc hR,
    RelativeRoot.kernelCentralizerOppositeNormalizer_flip
      hUnip hConnected hTconj hMinConj i hi a.val a.property j hj hjc hR,
    RelativeRoot.kernelCentralizerOppositeNormalizer_mem
      hUnip hConnected hTconj hMinConj i hi a.val a.property j hj hjc hR⟩

variable (k : Type u) [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i)

/-- Actual reflection data chosen from the structural reduction. The six
structural inputs are retained as parameters of this construction. -/
def relativeRootReflectionDataOfStructure :
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    RelativeRootReflectionData i :=
  Classical.choose (relativeRootReflectionExistence_of_structure
    hUnip hConnected hTconj hMinConj hKernel hExtension k G hG T i hi)

/-- Each chosen rational representative centralizes the full character kernel
on every test scheme and every refinement. -/
theorem relativeRootReflectionDataOfStructure_mem :
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    ∀ a : relativeRoots i,
      ((relativeRootReflectionDataOfStructure
        hUnip hConnected hTconj hMinConj hKernel hExtension k G hG T i hi).representative
          a).val ∈
        (RelativeRoot.kernelCentralizer i a.val).carrier (Over.mk (𝟙 _)) :=
  Classical.choose_spec (relativeRootReflectionExistence_of_structure
    hUnip hConnected hTconj hMinConj hKernel hExtension k G hG T i hi)

end Langlands.GroupScheme
