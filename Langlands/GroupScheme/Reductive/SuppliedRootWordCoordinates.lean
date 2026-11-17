import Langlands.GroupScheme.Rational.HighestWeightWordEndpoint
import Langlands.GroupScheme.Rational.RootSubgroupConjugation
import Langlands.GroupScheme.Dynamic.AffineRepresentability

/-! # Full root word maps from supplied simple root parametrizations -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace VectorGroup

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
    (α : characterLattice T)
    (x : groupScheme (CommRingCat.of k) 1 ⟶ G)
    (hx : (RelativeRoot.subgroup i α).IsRepresentedBy x)
    {g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X}
    {σ : T ≅ T}

include hx

/-- Normalizer conjugation transports a full root parametrization, with no
root-dimension or rank-one existence input. -/
theorem isRepresentedBy_conjugateMap (hg : IsNormalizingPoint i g σ) :
    (RelativeRoot.subgroup i (characterAut σ α)).IsRepresentedBy
      (conjugateMap x g) := by
  let n : normalizerPoints i := ⟨g, ⟨σ, hg⟩⟩
  have ha : weylAction i n α = characterAut σ α :=
    weylAction_eq i (n := n) (σ := σ) hg α
  have hr :
      (RelativeRoot.subgroup i α).comap (G.innerIso g).inv =
        RelativeRoot.subgroup i (weylAction i n α) := by
    apply SubgroupFunctor.ext
    intro Z
    apply Subgroup.ext
    intro z
    rw [SubgroupFunctor.mem_comap, ← G.innerIso_inv_hom g, comp_innerIso_hom]
    have h := RelativeRoot.normalizer_conj_mem_iff i (weylAction i n α) n⁻¹ z
    have hi : weylAction i n⁻¹ (weylAction i n α) = α := by
      rw [map_inv]
      exact (weylAction i n).symm_apply_apply α
    rw [hi] at h
    exact h
  rw [← ha, ← hr]
  exact hx.comp_iso (G.innerIso g)

end VectorGroup

namespace SplitPinning

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G)
    (s : p.SimpleReflectionRepresentatives)
    (xm : p.base.support → (VectorGroup.groupScheme (CommRingCat.of k) 1 ⟶ G))
    (hxm : ∀ (i : p.base.support), (RelativeRoot.subgroup p.inclusion
      (-p.rootDatum.root i)).IsRepresentedBy (xm i))

include hxm

/-- Every factor of a reflection word remains a parametrization of the full
successive root functor, by transport of the supplied simple parametrizations. -/
theorem reflectionWordLoweringMaps_represents_of_fullSimpleMaps
    (l : List p.base.support) :
    List.Forall₂
      (fun x j => (RelativeRoot.subgroup p.inclusion
        (-p.rootDatum.root j)).IsRepresentedBy x)
      (p.reflectionWordLoweringMaps s xm l)
      (Langlands.PositiveRootWord.wordRoots p.rootDatum p.base l) := by
  let : Mono p.inclusion.hom.hom.left := p.isMaximalTorus.2.1.mono
  induction l with
  | nil => exact List.Forall₂.nil
  | cons i l ih =>
    refine List.Forall₂.cons ?_ ih
    have h := VectorGroup.isRepresentedBy_conjugateMap p.inclusion
      (-p.rootDatum.root i) (xm i) (hxm i) (p.reflectionWordPoint_normalizes s l)
    rw [p.characterAut_reflectionWordTorusAut s l, map_neg] at h
    convert h using 1
    exact congrArg (fun a => RelativeRoot.subgroup p.inclusion (-a))
      (RootPairing.Equiv.root_indexEquiv_eq_smul
      p.rootDatum (i : p.rootIndex)
      (Langlands.PositiveRootWord.wordAut p.rootDatum p.base l))

end SplitPinning

end Langlands.GroupScheme
