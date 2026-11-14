import Langlands.GroupScheme.RelativeLevi.BorelConjugacyStatement
import Langlands.GroupScheme.RelativeLevi.ParabolicEtaleConjugacyStatement
import Langlands.GroupScheme.Reductive.BaseChange
import Langlands.GroupScheme.Rational.GeometricBorelMinimalParabolic
import Langlands.GroupScheme.Rational.MinimalParabolicConjugacyProof

/-! # Relative Borel conjugacy from relative parabolic conjugacy -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Relative Borel subgroups of a reductive group have conjugate residue fibres
over the residue field itself. -/
theorem IsRelativeBorelSubgroup.residueFiber_conjugate
    {S : Scheme.{u}} {G B B' : GroupScheme S} {i : B ⟶ G} {i' : B' ⟶ G}
    (hi : IsRelativeBorelSubgroup i) (hi' : IsRelativeBorelSubgroup i')
    (hG : IsReductive G) (s : S) :
    ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of (S.residueField s)))) ⟶
        ((GroupScheme.baseChange (S.fromSpecResidueField s)).obj G).X,
      SubgroupFunctor.range (RelativeLevi.residueFiberHom i s ≫
          (((GroupScheme.baseChange (S.fromSpecResidueField s)).obj G).innerIso g).hom) =
        SubgroupFunctor.range (RelativeLevi.residueFiberHom i' s) := by
  obtain ⟨g, e, he⟩ := minimalParabolicConjugacy (S.residueField s) _
    (hG.isConnectedReductive_residueFiber s) _ _
    (RelativeLevi.residueFiberHom i s) (RelativeLevi.residueFiberHom i' s)
    (hi.residueFiber s).isMinimalParabolicSubgroup
    (hi'.residueFiber s).isMinimalParabolicSubgroup
  refine ⟨g, ?_⟩
  exact (congrArg SubgroupFunctor.range he).trans (SubgroupFunctor.range_iso_comp e _)

/-- Choose an étale cover with conjugating sections for two relative Borel
subgroups, given relative parabolic conjugacy. -/
def relativeBorelEtaleConjugacyData
    (hparabolic : RelativeParabolicEtaleLocalConjugacyStatement.{u})
    {S : Scheme.{u}} {G B B' : GroupScheme S} {i : B ⟶ G} {i' : B' ⟶ G}
    (hG : IsReductive G) (hi : IsRelativeBorelSubgroup i)
    (hi' : IsRelativeBorelSubgroup i') :
    Σ 𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S,
      (j : 𝒰.I₀) →
        {g : Over.mk (𝟙 (𝒰.X j)) ⟶ ((GroupScheme.baseChange (𝒰.f j)).obj G).X //
          SubgroupFunctor.range ((GroupScheme.baseChange (𝒰.f j)).map i ≫
              (((GroupScheme.baseChange (𝒰.f j)).obj G).innerIso g).hom) =
            SubgroupFunctor.range ((GroupScheme.baseChange (𝒰.f j)).map i')} := by
  have hlocal := fun s : S => hparabolic S G B B' i i' s hG
    hi.isRelativeParabolicSubgroup hi'.isRelativeParabolicSubgroup
    (hi.residueFiber_conjugate hi' hG s)
  choose U f hf hcover g hg using hlocal
  let 𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S :=
    Scheme.Cover.mkOfCovers S U f (fun s => ⟨s, hcover s⟩) hf
  exact ⟨𝒰, fun s => ⟨g s, hg s⟩⟩

/-- Conrad's relative Borel conjugacy follows from the residue-field version of
relative parabolic conjugacy, using rational conjugacy of minimal parabolics. -/
theorem relativeBorelEtaleLocalConjugacy_of_parabolic
    (hparabolic : RelativeParabolicEtaleLocalConjugacyStatement.{u}) :
    RelativeBorelEtaleLocalConjugacyStatement.{u} := by
  intro S G B B' i i' hG hi hi'
  let d := relativeBorelEtaleConjugacyData hparabolic hG hi hi'
  exact ⟨d.1, fun j => ⟨(d.2 j).1, (d.2 j).2⟩⟩

end Langlands.GroupScheme
