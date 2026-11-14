import Langlands.GroupScheme.Dynamic.BaseRepresentabilityProof
import Langlands.GroupScheme.Dynamic.BaseSmoothConnectedProof
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.GroupScheme.Reductive.AlgebraicallyClosedPseudoReductive
import Langlands.GroupScheme.Rational.GenericParabolicCocharacterConjugacy

/-! # Reductive quotients of represented dynamic parabolics over an arbitrary base -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace Dynamic

/-- A closed representative of a cocharacter centralizer in a reductive group over
an arbitrary scheme is reductive. -/
theorem isReductive_centralizer {S : Scheme.{u}} {G Z : GroupScheme S}
    (hG : IsReductive G) (χ : (Gm S).toGrp ⟶ G) (j : Z ⟶ G)
    (hj : IsClosedSubgroup j) (hZ : (centralizer χ).IsRepresentedBy j) :
    IsReductive Z := by
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  refine ⟨((dynamicBaseSmoothConnected S G χ Z j).2.2 hZ).1, hj.isAffineHom, ?_⟩
  intro s
  have hZs := hZ.baseChange (geometricPoint S s)
  rw [← centralizer_baseChange] at hZs
  exact (dynamicCentralizerReductive _ _
    (hG.geometricFiber s).isConnectedReductive_of_isAlgClosed
    (baseChangeCocharacter (geometricPoint S s) χ) _ _
    (hj.baseChange (geometricPoint S s)) hZs).isPseudoReductive

/-- The limit map is the fppf quotient by any supplied representative of the
contracting subgroup inside the parabolic representative. -/
theorem isFppfQuotient_limitGroupHom_range
    {S : Scheme.{u}} {G P Z U : GroupScheme S} [IsSeparated G.X.hom]
    {χ : (Gm S).toGrp ⟶ G} {iP : P ⟶ G} {iZ : Z ⟶ G} (r : U ⟶ P)
    (hP : (parabolic χ).IsRepresentedBy iP)
    (hZ : (centralizer χ).IsRepresentedBy iZ)
    (hU : (unipotent χ).IsRepresentedBy (r ≫ iP)) [Smooth U.X.hom] :
    RelativeRoot.IsFppfQuotient (SubgroupFunctor.range r) (limitGroupHom hP hZ) := by
  let e := unipotentIsoKernel (hP := hP) (hZ := hZ) hU
  have he : e.hom ≫ kernelι (limitGroupHom hP hZ) = r := by
    apply hP.hom_ext
    exact unipotentIsoKernel_hom_comp hU
  have hr : SubgroupFunctor.range r =
      SubgroupFunctor.range (kernelι (limitGroupHom hP hZ)) := by
    rw [← he, SubgroupFunctor.range_iso_comp]
  rw [hr]
  exact isFppfQuotient_limitGroupHom hP hZ hU

end Dynamic

/-- A represented dynamic parabolic modulo its represented contracting subgroup
has a reductive represented fppf quotient over every base scheme. -/
def DynamicReductiveQuotientStatement : Prop :=
  ∀ (S : Scheme.{u}) (G P U : GroupScheme S) (χ : (Gm S).toGrp ⟶ G)
    (iP : P ⟶ G) (r : U ⟶ P),
    IsReductive G → (Dynamic.parabolic χ).IsRepresentedBy iP →
      (Dynamic.unipotent χ).IsRepresentedBy (r ≫ iP) →
      ∃ (Z : GroupScheme S) (q : P ⟶ Z),
        IsReductive Z ∧ RelativeRoot.IsFppfQuotient (SubgroupFunctor.range r) q

/-- Dynamic representability supplies the centralizer, geometric fibre reductivity
supplies its reductivity, and the smooth limit map is the desired quotient. -/
theorem dynamicReductiveQuotient : DynamicReductiveQuotientStatement.{u} := by
  intro S G P U χ iP r hG hP hU
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  obtain ⟨Z, iZ, hiZ, -, hZ⟩ := (dynamicBaseRepresentability S G χ).2.2
  let : Smooth U.X.hom :=
    ((dynamicBaseSmoothConnected S G χ U (r ≫ iP)).1 hU).1
  exact ⟨Z, Dynamic.limitGroupHom hP hZ,
    Dynamic.isReductive_centralizer hG χ iZ hiZ hZ,
    Dynamic.isFppfQuotient_limitGroupHom_range r hP hZ hU⟩

end Langlands.GroupScheme
