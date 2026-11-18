import Langlands.GroupScheme.SimplyConnected.GeometricCentralSection
import Langlands.GroupScheme.Reductive.MultiplicativeKernelReduction
import Langlands.GroupScheme.Torus.MultiplicativeTypeFiniteGaloisSplittingProof

/-! # Sections of central multiplicative-type extensions over arbitrary fields -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G H : GroupScheme (Spec (CommRingCat.of k))}
  [LocallyOfFiniteType H.X.hom] [IsAffineHom H.X.hom]
  (hG : IsSimplyConnected G) (q : H ⟶ G) [Flat q.hom.hom.left]
  (hq : IsCentral (kernelι q)) (hK : IsMultiplicativeType (kernel q))

include hG hq hK

/-- A central multiplicative-type extension of a simply connected semisimple
group splits over every field, without smoothness or connectedness of its source. -/
theorem IsSimplyConnected.exists_section_of_central_multiplicative :
    ∃ s : G ⟶ H, s ≫ q = 𝟙 G := by
  let b := toAlgebraicClosure k
  let B := baseChange b
  have hGK : IsSimplyConnected (B.obj G) :=
    isSimplyConnectedFieldExtension k (AlgebraicClosure k) G hG
  let : Smooth (B.obj G).X.hom := hGK.isSemisimple.isConnectedReductive.smooth
  let : IsAffineHom (B.obj G).X.hom := hGK.isSemisimple.isConnectedReductive.isAffineHom
  let : ConnectedSpace (B.obj G).X.left := hGK.isSemisimple.isConnectedReductive.connectedSpace
  let : IsAffineHom (B.obj H).X.hom :=
    MorphismProperty.pullback_snd H.X.hom b inferInstance
  let : LocallyOfFiniteType (B.obj H).X.hom :=
    MorphismProperty.pullback_snd H.X.hom b inferInstance
  let : Flat (B.map q).hom.hom.left :=
    MorphismProperty.overPullbackMap (P := @Flat) b q.hom.hom inferInstance
  have hKK : IsMultiplicativeType (kernel (B.map q)) :=
    IsMultiplicativeType.of_iso (kernelBaseChangeIso b q).symm
      (MultiplicativeTypeSplitting.isMultiplicativeType_baseChange_of_isAlgebraic
        k (AlgebraicClosure k) (kernel q) hK)
  let D := ReducedSubgroup.identityCore (B.obj H)
  let i := ReducedSubgroup.identityCoreι (B.obj H)
  have hD : IsConnectedReductive D :=
    IsConnectedReductive.identityCore_of_multiplicativeTypeKernel
      (B.map q) hKK hGK.isSemisimple.isConnectedReductive
  let : IsClosedImmersion i.hom.hom.left :=
    ReducedSubgroup.isClosedImmersion_identityCoreι (B.obj H)
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  let : Surjective (i ≫ B.map q).hom.hom.left :=
    (ReducedSubgroup.identityCore_comp_flat_surjective (B.map q)).2
  exact hG.exists_section_of_geometric_reductive_lift q hq D i hD

/-- The chosen section of a central extension with multiplicative-type full kernel. -/
def IsSimplyConnected.centralMultiplicativeSection : G ⟶ H :=
  (hG.exists_section_of_central_multiplicative q hq hK).choose

/-- The constructed homomorphism is a section of the original extension. -/
@[reassoc]
theorem IsSimplyConnected.centralMultiplicativeSection_comp :
    hG.centralMultiplicativeSection q hq hK ≫ q = 𝟙 G :=
  (hG.exists_section_of_central_multiplicative q hq hK).choose_spec

end Langlands.GroupScheme
