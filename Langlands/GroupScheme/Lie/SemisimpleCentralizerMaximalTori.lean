import Langlands.GroupScheme.Lie.SemisimpleCentralizerTori
import Langlands.GroupScheme.Lie.SemisimpleCentralizerSmooth
import Langlands.GroupScheme.Lie.ElementCentralizerTangent
import Langlands.GroupScheme.Chevalley.ActualRepresentationExtension
import Langlands.GroupScheme.Cartan.StructureStatement
import Langlands.GroupScheme.Cartan.SemisimpleCentralizers

/-! # Semisimple centralizer tangent factors and maximal tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
    {G C : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    [Smooth C.X.hom] [IsAffineHom C.X.hom]

namespace Lie

section Factor

variable (hstructure : NilpotentCentralTorusStatement.{u})
    (hvan : UnipotentSemisimpleStatement.{u})
    (hcartan : CartanStructureStatement.{u})
    {X : lieKernel G k} (hX : IsSemisimpleElement G X)
    (j : C ⟶ G) (hrep : (elementCentralizer G X).IsRepresentedBy j)
    (hj : IsClosedSubgroup j)
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ identityComponent C) (hi : IsMaximalTorus i)

/-- A semisimple vector has a prescribed maximal-torus preimage in its
centralizer, under the three displayed structural statements. -/
def semisimpleCentralizerTorusFactor : lieKernel T.toGrp k :=
  elementCentralizerIdentityTorusFactor hstructure hvan X j hrep hj
    (mem_elementCentralizerLie_self X)
    (fun D d hd => (hcartan k (identityComponent C) D d hd).2)
    (fun D d hd Y hY => isSemisimpleElement_of_closed_subgroup d hd
      (by rwa [hY])) i hi

@[simp]
theorem targetMap_semisimpleCentralizerTorusFactor :
    targetMap (i ≫ identityComponentι C ≫ j) k
      (semisimpleCentralizerTorusFactor hstructure hvan hcartan hX j hrep hj i hi) = X := by
  unfold semisimpleCentralizerTorusFactor
  exact targetMap_elementCentralizerIdentityTorusFactor _ _ _ _ _ _ _ _ _ _ _

end Factor

end Lie

/-- Semisimple centralizer inclusions preserve maximal tori. Self-membership
and reflection of semisimplicity are supplied by the actual affine theory. -/
theorem preservesMaximalTori_identityComponent_elementCentralizer_of_semisimple
    (hstructure : NilpotentCentralTorusStatement.{u})
    (hvan : UnipotentSemisimpleStatement.{u})
    (hcartan : CartanStructureStatement.{u})
    {X : lieKernel G k} (hX : Lie.IsSemisimpleElement G X)
    (j : C ⟶ G) (hrep : (Lie.elementCentralizer G X).IsRepresentedBy j)
    (hj : IsClosedSubgroup j) :
    PreservesMaximalTori (identityComponentι C ≫ j) := by
  intro T i hi
  apply hi.comp_identityComponent_elementCentralizer j hj hrep
  exact ⟨Lie.semisimpleCentralizerTorusFactor hstructure hvan hcartan hX j hrep hj i hi,
    Lie.targetMap_semisimpleCentralizerTorusFactor hstructure hvan hcartan hX j hrep hj i hi⟩

/-- The semisimple-centralizer induction step now requires only tangent
spanning and the three remaining structural statements. -/
theorem isGeneratedByCartanSubgroups_of_semisimpleCentralizerSpanning
    [Smooth G.X.hom] [ConnectedSpace G.X.left]
    (hstructure : NilpotentCentralTorusStatement.{u})
    (hvan : UnipotentSemisimpleStatement.{u})
    (hcartan : CartanStructureStatement.{u})
    (hspan : (⨆ (X : lieKernel G k) (_ : Lie.IsSemisimpleElement G X)
      (_ : Lie.elementCentralizerLie G X ≠ ⊤), Lie.elementCentralizerLie G X) = ⊤)
    (hind : ∀ (H : GroupScheme (Spec (CommRingCat.of k)))
      [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left],
      Lie.dimension H < Lie.dimension G → IsGeneratedByCartanSubgroups H) :
    IsGeneratedByCartanSubgroups G := by
  apply isGeneratedByCartanSubgroups_of_semisimpleCentralizers
    Lie.semisimpleCentralizerSmooth hspan hind
  intro X hX C _ _ j hrep hj
  exact preservesMaximalTori_identityComponent_elementCentralizer_of_semisimple
    hstructure hvan hcartan hX j hrep hj

end Langlands.GroupScheme
