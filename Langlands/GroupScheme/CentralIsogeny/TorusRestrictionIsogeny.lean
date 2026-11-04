import Langlands.GroupScheme.CentralIsogeny.TorusRestriction
import Langlands.GroupScheme.Rational.SplitTorusFppfImage
import Langlands.GroupScheme.Rational.CentralSurjectionMaximalSplitTorusImageStatement
import Langlands.GroupScheme.Torus.MaximalSplitComparison
import Langlands.GroupScheme.Rational.SplitTorusIsogenyCocharacterProof
import Langlands.GroupScheme.Rational.SplitTorusSurjection

/-! # Torus restrictions of central isogenies from maximality of split images -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G G' : GroupScheme (Spec (CommRingCat.of k))}
  {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
  {i : T.toGrp ⟶ G} {i' : T'.toGrp ⟶ G'} {φ : G ⟶ G'}

/-- Maximality of split-torus images under central fppf surjections makes the supplied
restriction of a central isogeny an isogeny. -/
theorem IsCentralIsogeny.isIsogeny_torusRestriction_of_maximalImage
    (himage : CentralSurjectionMaximalSplitTorusImageStatement.{u})
    (hφ : IsCentralIsogeny φ) (hG : IsConnectedReductive G) (hG' : IsConnectedReductive G')
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    (hi : IsMaximalTorus i) (hi' : IsMaximalTorus i') (t : T ⟶ T')
    (ht : i ≫ φ = CommGroupScheme.groupHom t ≫ i') :
    IsIsogeny (CommGroupScheme.groupHom t) := by
  have := hT'.isAffineHom
  let E := hT.fppfImage (CommGroupScheme.groupHom t)
  let j : E.torus.toGrp ⟶ G' := E.inclusion ≫ i'
  have hj : IsSplitSubtorus j := by
    refine ⟨E.isSplitSubtorus.1, ?_⟩
    have : IsClosedImmersion E.inclusion.hom.hom.left := E.isSplitSubtorus.2
    have : IsClosedImmersion i'.hom.hom.left := hi'.2.1
    change IsClosedImmersion (E.inclusion.hom.hom.left ≫ i'.hom.hom.left)
    infer_instance
  have hfactor : CommGroupScheme.groupHom E.projection ≫ j = i ≫ φ := by
    dsimp only [j]
    rw [← Category.assoc, E.factorization, ht]
  have hmax : IsMaximalSplitTorus j :=
    himage k G G' φ hG hG' hφ.flat hφ.surjective hφ.locallyOfFinitePresentation
      hφ.isCentral_kernelι T E.torus i j E.projection (hi.isMaximalSplitTorus hT) hj
      E.flat E.surjective E.locallyOfFinitePresentation hfactor
  have hinc : IsIso E.inclusion :=
    hmax.2 T' i' ⟨hT', hi'.2.1⟩ E.inclusion rfl
  have : IsIso E.inclusion.hom.hom.left :=
    (Over.forget _).map_isIso ((Grp.forget _).map E.inclusion)
  have : Flat (CommGroupScheme.groupHom E.projection).hom.hom.left := E.flat
  have : Surjective (CommGroupScheme.groupHom E.projection).hom.hom.left := E.surjective
  have htScheme : (CommGroupScheme.groupHom t).hom.hom.left =
      (CommGroupScheme.groupHom E.projection).hom.hom.left ≫ E.inclusion.hom.hom.left :=
    (congrArg (fun f => f.hom.hom.left) E.factorization).symm
  refine ⟨?_, ?_, ?_⟩
  · have := hφ.isFinite
    exact isFinite_torusRestriction hi.2.1 hi'.2.1 φ t ht
  · rw [htScheme]
    infer_instance
  · rw [htScheme]
    infer_instance

/-- The supplied restriction is injective on actual integral characters once the maximal-image
input is available. -/
theorem IsCentralIsogeny.characterPullback_injective_of_maximalImage
    (himage : CentralSurjectionMaximalSplitTorusImageStatement.{u})
    (hφ : IsCentralIsogeny φ) (hG : IsConnectedReductive G) (hG' : IsConnectedReductive G')
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    (hi : IsMaximalTorus i) (hi' : IsMaximalTorus i') (t : T ⟶ T')
    (ht : i ≫ φ = CommGroupScheme.groupHom t ≫ i') :
    Function.Injective (fun χ : characterLattice T' => t ≫ χ) := by
  have h := hφ.isIsogeny_torusRestriction_of_maximalImage himage hG hG' hT hT' hi hi' t ht
  have : Flat (CommGroupScheme.groupHom t).hom.hom.left := h.2.1
  have : Surjective (CommGroupScheme.groupHom t).hom.hom.left := h.2.2
  have : Epi (CommGroupScheme.groupHom t).hom.hom.left :=
    Flat.epi_of_flat_of_surjective _
  exact RealTorusSpace.characterRestrict_injective_of_epi t

/-- Data for an actual reverse torus homomorphism whose composites are multiplication by a
nonzero integer. -/
structure TorusRestrictionQuasiInverse (t : T ⟶ T') where
  scalar : ℤ
  scalar_ne_zero : scalar ≠ 0
  reverse : T' ⟶ T
  source_composite : t ≫ reverse = scalar • 𝟙 T
  target_composite : reverse ≫ t = scalar • 𝟙 T'

/-- The integer quasiinverse of the restriction, constructed using the maximal-image
geometric input and the published split-torus isogeny comparison. -/
def IsCentralIsogeny.torusRestrictionQuasiInverseOfMaximalImage
    (himage : CentralSurjectionMaximalSplitTorusImageStatement.{u})
    (hφ : IsCentralIsogeny φ) (hG : IsConnectedReductive G) (hG' : IsConnectedReductive G')
    (hT : IsSplitTorus T.toGrp) (hT' : IsSplitTorus T'.toGrp)
    (hi : IsMaximalTorus i) (hi' : IsMaximalTorus i') (t : T ⟶ T')
    (ht : i ≫ φ = CommGroupScheme.groupHom t ≫ i') :
    TorusRestrictionQuasiInverse t :=
  Classical.choice (by
    obtain ⟨n, hn, g, hg, hg'⟩ := hT.exists_isogeny_quasiInverse hT' t
      (hφ.isIsogeny_torusRestriction_of_maximalImage himage hG hG' hT hT' hi hi' t ht)
    exact ⟨⟨n, hn, g, hg, hg'⟩⟩)

end Langlands.GroupScheme
