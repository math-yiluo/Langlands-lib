import Langlands.GroupScheme.Absolute.SplitParabolicCocharacterProof
import Langlands.GroupScheme.Absolute.ParabolicMaximalTorusProof
import Langlands.GroupScheme.Absolute.ParabolicFieldExtensionProof
import Langlands.GroupScheme.Absolute.SplitParabolicCocharacterAbsoluteReduction
import Langlands.GroupScheme.Absolute.BorelConjugacyProof
import Langlands.GroupScheme.Absolute.BorelOvergroupCocharacterProof
import Langlands.GroupScheme.Absolute.FixedTorusGaloisDescent
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof
import Langlands.GroupScheme.Torus.MaximalBaseChangeProof
import Langlands.GroupScheme.Reductive.FieldExtensionProof

/-! # Parabolic subgroups are dynamic over their own field -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

/-- Every parabolic subgroup of a connected reductive group over a field is the
dynamic parabolic of a cocharacter defined over that field. The cocharacter
factors through a maximal torus contained in the parabolic. -/
theorem exists_cocharacter_range_eq_parabolic_of_isParabolicSubgroup
    (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (P : GroupScheme (Spec (CommRingCat.of k)))
    (i : P ⟶ G) (hi : IsParabolicSubgroup i) :
    ∃ χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G,
      SubgroupFunctor.range i = Dynamic.parabolic χ := by
  have : Smooth G.X.hom := hG.smooth
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : ConnectedSpace G.X.left := hG.connectedSpace
  have : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  obtain ⟨T, j, f, hj, hf⟩ := parabolicMaximalTorus k G hG P i hi
  have : IsClosedImmersion j.hom.hom.left := hj.2.1
  have : IsAffineHom T.X.hom := by
    rw [← Over.w j.hom.hom]
    infer_instance
  obtain ⟨K, _, _, hfin, hgal, hsplit⟩ := torusFiniteGaloisSplitting k T.toGrp hj.1
  let : Fintype (K ≃ₐ[k] K) := Fintype.ofFinite _
  let b := algebraBaseMap k K
  let F := GroupScheme.baseChange b
  let TK := (CommGroupScheme.baseChange b).obj T
  have hTK : IsSplitTorus TK.toGrp := hsplit
  obtain ⟨mu, hmu⟩ :=
    (exists_range_eq_parabolic_iff_finiteGaloisBaseChange k K T j i hTK).mpr (by
      have hGK : IsConnectedReductive (F.obj G) :=
        connectedReductiveFieldExtensionStatement k K G hG
      have hjK : IsMaximalTorus (T := TK) (F.map j) :=
        (maximalTorusBaseChange k K G T j hj.1 hj.2.1).mp hj
      have hiK : IsParabolicSubgroup (F.map i) :=
        parabolicFieldExtensionStatement k K G hG P i hi
      exact splitParabolicCocharacterStatement K (F.obj G) hGK TK (F.map j) hTK hjK
        (F.obj P) (F.map i) (F.map f) hiK
        ((F.map_comp f i).symm.trans (congrArg F.map hf)))
  exact ⟨CommGroupScheme.groupHom mu ≫ j, hmu⟩

end Langlands.GroupScheme
