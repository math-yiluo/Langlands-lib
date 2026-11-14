import Langlands.GroupScheme.CentralIsogeny.IndexTwoKernel
import Langlands.GroupScheme.CentralIsogeny.GaloisStableKernelDescent
import Langlands.GroupScheme.Torus.CharacterAnnihilatorGalois
import Langlands.GroupScheme.CocharacterTransportNaturality
import Langlands.GroupScheme.Rational.ParabolicLeviIntersectionReduction
import Langlands.GroupScheme.Rational.UnipotentRadicalGalois

/-! # Full central kernels from Galois-stable torus character images -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

section KernelComparison

variable {K : Type u} [Field K]
    {G Q : GroupScheme (Spec (CommRingCat.of K))}
    {T T' : CommGroupScheme (Spec (CommRingCat.of K))}
    {p : G ⟶ Q} {i : T.toGrp ⟶ G} {i' : T'.toGrp ⟶ Q} {t : T ⟶ T'}

/-- The full kernel of a central isogeny is the image in the source group of
    the character annihilator of its split target-torus pullback image. -/
theorem range_kernel_eq_torus_characterAnnihilator
    (hp : IsCentralIsogeny p) (hG : IsConnectedReductive G)
    (hi : IsMaximalTorus i) (hi' : IsClosedSubgroup i')
    (hT' : IsSplitTorus T'.toGrp)
    (ht : i ≫ p = CommGroupScheme.groupHom t ≫ i') :
    SubgroupFunctor.range (kernelι p) =
      (characterLattice.annihilatorSubgroupFunctor T
        (characterLattice.comapHom (CommGroupScheme.groupHom t)).toIntLinearMap.range).map i := by
  calc
    SubgroupFunctor.range (kernelι p) =
        SubgroupFunctor.range
          ((IndexTwoKernel.kernelComparisonIso hp hG hi hi' ht).hom ≫ kernelι p) :=
      (SubgroupFunctor.range_iso_comp _ _).symm
    _ = SubgroupFunctor.range (kernelι (CommGroupScheme.groupHom t) ≫ i) := by
      rw [IndexTwoKernel.kernelComparisonIso_hom_kernelι]
    _ = _ := by
      rw [RepresentedParabolicLeviIntersection.range_comp_eq_map,
        characterLattice.range_kernel_eq_annihilator _ hT']

end KernelComparison

namespace SubgroupFunctor

/-- Canonical descent transport commutes with the image of a represented
    subgroup under a homomorphism defined over the original base. -/
theorem descentTransport_range_comp_baseChange
    {B S : Scheme.{u}} (b : S ⟶ B) (a : S ⟶ S) (ha : a ≫ b = b)
    {T G : GroupScheme B} (i : T ⟶ G) {H : GroupScheme S}
    (j : H ⟶ (GroupScheme.baseChange b).obj T) :
    descentTransport b a ha G (range (j ≫ (GroupScheme.baseChange b).map i)) =
      (descentTransport b a ha T (range j)).map ((GroupScheme.baseChange b).map i) := by
  rw [descentTransport_range, Functor.map_comp, Category.assoc,
    descentBaseChangeIso_naturality, ← Category.assoc,
    RepresentedParabolicLeviIntersection.range_comp_eq_map,
    ← descentTransport_range]

end SubgroupFunctor

section GaloisKernel

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {Q : GroupScheme (Spec (CommRingCat.of K))}
    {T' : CommGroupScheme (Spec (CommRingCat.of K))}
    {p : (GroupScheme.baseChange (algebraBaseMap k K)).obj G ⟶ Q}
    {i : T.toGrp ⟶ G} {i' : T'.toGrp ⟶ Q}
    {t : (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T ⟶ T'}

/-- Stability of the actual integral torus character image implies Galois
    invariance of the full ambient kernel, including infinitesimal structure. -/
theorem range_galoisTranslate_kernel_eq_of_torus_characterImage
    (hp : IsCentralIsogeny p)
    (hG : IsConnectedReductive ((GroupScheme.baseChange (algebraBaseMap k K)).obj G))
    (hi : IsMaximalTorus (T := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
      ((GroupScheme.baseChange (algebraBaseMap k K)).map i))
    (hi' : IsClosedSubgroup i') (hT' : IsSplitTorus T'.toGrp)
    (ht : (GroupScheme.baseChange (algebraBaseMap k K)).map i ≫ p =
      CommGroupScheme.groupHom t ≫ i')
    (σ : K ≃ₐ[k] K)
    (hL : (characterLattice.comapHom (CommGroupScheme.groupHom t)).toIntLinearMap.range.map
        (characterLattice.galoisRepresentation k K T σ) =
      (characterLattice.comapHom (CommGroupScheme.groupHom t)).toIntLinearMap.range) :
    SubgroupFunctor.range (radicalGaloisHom (kernelι p) σ) =
      SubgroupFunctor.range (kernelι p) := by
  have hker : SubgroupFunctor.range (kernelι p) =
      SubgroupFunctor.range
        (kernelι (CommGroupScheme.groupHom t) ≫
          (GroupScheme.baseChange (algebraBaseMap k K)).map i) := by
    rw [range_kernel_eq_torus_characterAnnihilator hp hG hi hi' hT' ht,
      RepresentedParabolicLeviIntersection.range_comp_eq_map,
      characterLattice.range_kernel_eq_annihilator _ hT']
  change SubgroupFunctor.range
      ((GroupScheme.baseChange (galoisBaseMap k K σ)).map (kernelι p) ≫
        (descentBaseChangeIso (algebraBaseMap k K) (galoisBaseMap k K σ)
          (galoisBaseMap_over k K σ) G).hom) = _
  rw [← SubgroupFunctor.descentTransport_range, hker,
    SubgroupFunctor.descentTransport_range_comp_baseChange,
    RepresentedParabolicLeviIntersection.range_comp_eq_map,
    characterLattice.range_kernel_eq_annihilator _ hT',
    characterLattice.descentTransport_annihilatorSubgroupFunctor_eq _ _ σ hL]

namespace Descent

/-- Descend a supplied affine central-isogeny target when its maximal-torus
    character image is Galois stable, retaining the exact recovery equation. -/
def centralIsogenyRecoveryOfStableTorusCharacterImage
    [IsGalois k K] [IsAffineHom G.X.hom] [IsAffine Q.X.left]
    (hp : IsCentralIsogeny p)
    (hG : IsConnectedReductive ((GroupScheme.baseChange (algebraBaseMap k K)).obj G))
    (hi : IsMaximalTorus (T := (CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
      ((GroupScheme.baseChange (algebraBaseMap k K)).map i))
    (hi' : IsClosedSubgroup i') (hT' : IsSplitTorus T'.toGrp)
    (ht : (GroupScheme.baseChange (algebraBaseMap k K)).map i ≫ p =
      CommGroupScheme.groupHom t ≫ i')
    (hL : ∀ σ : K ≃ₐ[k] K,
      (characterLattice.comapHom (CommGroupScheme.groupHom t)).toIntLinearMap.range.map
          (characterLattice.galoisRepresentation k K T σ) =
        (characterLattice.comapHom (CommGroupScheme.groupHom t)).toIntLinearMap.range) :
    CentralIsogenyRecovery (algebraBaseMap k K) p :=
  centralIsogenyRecoveryOfGaloisInvariantKernel p hp fun σ =>
    range_galoisTranslate_kernel_eq_of_torus_characterImage hp hG hi hi' hT' ht σ (hL σ)

end Descent

end GaloisKernel

end Langlands.GroupScheme
