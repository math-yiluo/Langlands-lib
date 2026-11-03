import Langlands.GroupScheme.Rational.RankOneOppositeParabolics
import Langlands.GroupScheme.Rational.RootKernelIdentityWeights
import Langlands.GroupScheme.Rational.WeightVectorUniqueness
import Langlands.GroupScheme.Rational.RootKernelReflection
import Langlands.GroupScheme.Dynamic.SmoothProof

/-! # Opposing-parabolic normalizers in full root-kernel centralizers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

set_option backward.isDefEq.respectTransparency false

section CanonicalParabolics

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (hUnip : TorusActionUnipotenceStatement.{u})
    (hConnected : DynamicConnectedStatement.{u})
    (hTconj : SmoothMaximalSplitTorusConjugacyStatement.{u})
    (hMinConj : MinimalPseudoParabolicConjugacyStatement.{u})
    (hR : HasTrivialUnipotentRadical G)
    (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] (hi : IsMaximalSplitTorus i)
    (a : characterLattice T) (ha : a ∈ relativeRoots i)
    (hcyclic : ∀ α ∈ relativeRoots i, ∃ n : ℤ, α = n • a)
    (ν : cocharacterLattice T) (hpos : 0 < latticePairing T a ν)

include hUnip hConnected hTconj hMinConj hR hi ha hcyclic hpos

/-- Canonical closed affine representatives remove the need to supply opposing
parabolic subgroup schemes. Connectedness remains an explicit structural input. -/
theorem exists_moving_normalizer_of_cyclic_roots :
    ∃ n : normalizerPoints i, weylAction i n a ≠ a := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let χ := CommGroupScheme.groupHom ν ≫ i
  let χ' := CommGroupScheme.groupHom (-ν) ≫ i
  let P := Dynamic.Affine.parabolicScheme χ
  let Q := Dynamic.Affine.parabolicScheme χ'
  let j := Dynamic.Affine.parabolicHom χ
  let l := Dynamic.Affine.parabolicHom χ'
  have hj := Dynamic.Affine.isRepresentedBy_parabolicHom χ
  have hl := Dynamic.Affine.isRepresentedBy_parabolicHom χ'
  let : Smooth P.X.hom := (dynamicSmooth k G χ P j).1 hj
  let : Smooth Q.X.hom := (dynamicSmooth k G χ' Q l).1 hl
  let : ConnectedSpace P.X.left :=
    ((hConnected k G χ P j).2 inferInstance).1 hj
  let : ConnectedSpace Q.X.left :=
    ((hConnected k G χ' Q l).2 inferInstance).1 hl
  refine ⟨(rankOneOppositeParabolicNormalizer hUnip hTconj hMinConj hR
    T i hi a ha hcyclic ν hpos j l
      (Dynamic.Affine.isClosedSubgroup_parabolicHom χ)
      (Dynamic.Affine.isClosedSubgroup_parabolicHom χ') hj hl).1, ?_⟩
  exact rankOneOppositeParabolicNormalizer_moves_root hUnip hTconj hMinConj hR
    T i hi a ha hcyclic ν hpos j l
      (Dynamic.Affine.isClosedSubgroup_parabolicHom χ)
      (Dynamic.Affine.isClosedSubgroup_parabolicHom χ') hj hl

end CanonicalParabolics

section KernelCentralizer

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G C : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    [Smooth C.X.hom] [IsAffineHom C.X.hom]
    (hUnip : TorusActionUnipotenceStatement.{u})
    (hConnected : DynamicConnectedStatement.{u})
    (hTconj : SmoothMaximalSplitTorusConjugacyStatement.{u})
    (hMinConj : MinimalPseudoParabolicConjugacyStatement.{u})
    (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] (hi : IsMaximalSplitTorus i)
    (a : characterLattice T) (ha : a ∈ relativeRoots i)
    (j : C ⟶ G) (hj : (kernelCentralizer i a).IsRepresentedBy j)
    (hjc : IsClosedSubgroup j)
    (hR : HasTrivialUnipotentRadical (identityComponent C))

include hUnip hConnected hTconj hMinConj hi ha hjc hR in
omit [Mono i.hom.hom.left] in
/-- The integral component-root comparison supplies an actual component
normalizer which moves the original root. -/
theorem exists_moving_kernelCentralizerIdentityNormalizer :
    letI : Mono (kernelCentralizerIdentityTorus i hi.1.1 a j hj).hom.hom.left :=
      (hi.kernelCentralizerIdentityTorus a j hj hjc).isSplitSubtorus.mono
    ∃ n : normalizerPoints (kernelCentralizerIdentityTorus i hi.1.1 a j hj),
      weylAction (kernelCentralizerIdentityTorus i hi.1.1 a j hj) n a ≠ a := by
  let i₀ := kernelCentralizerIdentityTorus i hi.1.1 a j hj
  have hi₀ : IsMaximalSplitTorus i₀ := hi.kernelCentralizerIdentityTorus a j hj hjc
  let : Mono i₀.hom.hom.left := hi₀.isSplitSubtorus.mono
  have ha₀ : a ∈ relativeRoots i₀ :=
    mem_relativeRoots_kernelCentralizerIdentityTorus i hi.1.1 a j hj ha
  have hcyclic : ∀ α ∈ relativeRoots i₀, ∃ n : ℤ, α = n • a := by
    intro α hα
    rw [relativeRoots_kernelCentralizerIdentityTorus i hi.1.1 a j hj] at hα
    obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp hα.2
    exact ⟨n, hn.symm⟩
  obtain ⟨D, hD, ν, hν⟩ := hi.1.1.exists_pairing_eq_pos ha.1
  have hpos : 0 < latticePairing T a ν := by omega
  exact exists_moving_normalizer_of_cyclic_roots
    hUnip hConnected hTconj hMinConj hR T i₀ hi₀ a ha₀ hcyclic ν hpos

/-- An actual component normalizer which moves the original root. Its existence
uses the complete integral component-root comparison, not root classification. -/
def kernelCentralizerIdentityOppositeNormalizer :
    normalizerPoints (kernelCentralizerIdentityTorus i hi.1.1 a j hj) :=
  Classical.choose (exists_moving_kernelCentralizerIdentityNormalizer
    hUnip hConnected hTconj hMinConj i hi a ha j hj hjc hR)

include hUnip hConnected hTconj hMinConj hi ha hjc hR in
omit [Mono i.hom.hom.left] in
/-- The chosen component normalizer moves the original character under its
actual whole-lattice Weyl action. -/
theorem kernelCentralizerIdentityOppositeNormalizer_moves_root :
    letI : Mono (kernelCentralizerIdentityTorus i hi.1.1 a j hj).hom.hom.left :=
      (hi.kernelCentralizerIdentityTorus a j hj hjc).isSplitSubtorus.mono
    weylAction (kernelCentralizerIdentityTorus i hi.1.1 a j hj)
      (kernelCentralizerIdentityOppositeNormalizer
        hUnip hConnected hTconj hMinConj i hi a ha j hj hjc hR) a ≠ a := by
  exact Classical.choose_spec (exists_moving_kernelCentralizerIdentityNormalizer
    hUnip hConnected hTconj hMinConj i hi a ha j hj hjc hR)

/-- Include the opposing-parabolic component normalizer into the original
group. It normalizes the original torus and centralizes its full root kernel. -/
def kernelCentralizerOppositeNormalizer : normalizerPoints i :=
  kernelCentralizerIdentityNormalizerMap i hi.1.1 a j hj
    (kernelCentralizerIdentityOppositeNormalizer
      hUnip hConnected hTconj hMinConj i hi a ha j hj hjc hR)

include hUnip hConnected hTconj hMinConj hi ha hjc hR

omit [Mono i.hom.hom.left] in
/-- All-test centralization is preserved by the actual component inclusion. -/
theorem kernelCentralizerOppositeNormalizer_mem :
    (kernelCentralizerOppositeNormalizer
      hUnip hConnected hTconj hMinConj i hi a ha j hj hjc hR).val ∈
        (kernelCentralizer i a).carrier (Over.mk (𝟙 _)) :=
  kernelCentralizerIdentityNormalizerMap_mem i hi.1.1 a j hj _

/-- The transported rational normalizer still moves the original root. -/
theorem kernelCentralizerOppositeNormalizer_moves_root :
    weylAction i (kernelCentralizerOppositeNormalizer
      hUnip hConnected hTconj hMinConj i hi a ha j hj hjc hR) a ≠ a := by
  let : Mono (kernelCentralizerIdentityTorus i hi.1.1 a j hj).hom.hom.left :=
    (hi.kernelCentralizerIdentityTorus a j hj hjc).isSplitSubtorus.mono
  rw [kernelCentralizerOppositeNormalizer,
    weylAction_kernelCentralizerIdentityNormalizerMap]
  exact kernelCentralizerIdentityOppositeNormalizer_moves_root
    hUnip hConnected hTconj hMinConj i hi a ha j hj hjc hR

/-- Full-kernel centralization makes every character difference an integral
multiple of the original root; movement therefore forces its negative sign. -/
theorem kernelCentralizerOppositeNormalizer_flip :
    weylAction i (kernelCentralizerOppositeNormalizer
      hUnip hConnected hTconj hMinConj i hi a ha j hj hjc hR) a = -a := by
  have := hi.1.1.isPerfPair_latticePairing
  have := Module.IsReflexive.of_isPerfPair (p := latticePairing T)
  exact IntegralRootLine.apply_eq_neg_of_ne a ha.1 _
    (exists_integral_difference_of_mem_kernelCentralizer i hi.1.1 a ha.1 _
      (kernelCentralizerOppositeNormalizer_mem
        hUnip hConnected hTconj hMinConj i hi a ha j hj hjc hR))
    (kernelCentralizerOppositeNormalizer_moves_root
      hUnip hConnected hTconj hMinConj i hi a ha j hj hjc hR)

/-- The constructed rational representative has a unique actual integral
coroot giving its reflection formula on the entire character lattice. -/
theorem kernelCentralizerOppositeNormalizer_existsUnique_coroot :
    ∃! ν : cocharacterLattice T,
      latticePairing T a ν = 2 ∧
        ∀ χ : characterLattice T,
          weylAction i (kernelCentralizerOppositeNormalizer
            hUnip hConnected hTconj hMinConj i hi a ha j hj hjc hR) χ =
              χ - latticePairing T χ ν • a :=
  hi.1.1.existsUnique_coroot_of_mem_kernelCentralizer i a ha.1 _
    (kernelCentralizerOppositeNormalizer_flip
      hUnip hConnected hTconj hMinConj i hi a ha j hj hjc hR)
    (kernelCentralizerOppositeNormalizer_mem
      hUnip hConnected hTconj hMinConj i hi a ha j hj hjc hR)

end KernelCentralizer

end Langlands.GroupScheme.RelativeRoot
