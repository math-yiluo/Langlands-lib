import Langlands.GroupScheme.Rational.SemistandardSpectralIndex
import Langlands.GroupScheme.Rational.ParabolicCocharacterConjugacy
import Langlands.GroupScheme.Rational.ParabolicLeviRealization
import Langlands.GroupScheme.Rational.SmoothMaximalSplitTorusConjugacyProof

/-! # Every semistandard parabolic has an intrinsic spectral index -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- An actual parabolic containing a maximal split torus is dynamic for a
cocharacter of that very torus, with equality on all test schemes. -/
theorem IsParabolicFunctor.exists_fixedTorusCocharacter
    {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G)
    {T : CommGroupScheme (Spec (CommRingCat.of k))} {i : T.toGrp ⟶ G}
    (hi : IsMaximalSplitTorus i) {F : SubgroupFunctor G}
    (hF : IsParabolicFunctor F) (hTF : SubgroupFunctor.range i ≤ F) :
    ∃ ζ : cocharacterLattice T,
      Dynamic.parabolic (CommGroupScheme.groupHom ζ ≫ i) = F := by
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  let : ConnectedSpace G.X.left := hG.connectedSpace
  obtain ⟨P, j, hj, hFj⟩ := hF
  have hjc : IsClosedSubgroup j := hj.isClosedSubgroup
  let : IsClosedImmersion j.hom.hom.left := hjc
  have hrep : F.IsRepresentedBy j := ⟨Over.mono_of_mono_left _, hFj⟩
  obtain ⟨χ, hχ⟩ := (parabolicDynamic k G hG P j hjc).1 hj
  have hP : (Dynamic.parabolic χ).IsRepresentedBy j := ⟨Over.mono_of_mono_left _, hχ⟩
  let : Smooth P.X.hom := hj.smooth
  let : IsAffineHom P.X.hom := hjc.isAffineHom
  let : ConnectedSpace P.X.left :=
    ((dynamicConnected k G χ P j).2 inferInstance).1 hP
  let iP : T.toGrp ⟶ P := hrep.factorHom i hTF
  have hiPj : iP ≫ j = i := hrep.factorHom_comp i hTF
  have hiP : IsMaximalSplitTorus iP :=
    IsMaximalSplitTorus.of_comp hjc (hiPj ▸ hi)
  let χP := hP.factorHom χ (Dynamic.range_le_parabolic χ)
  have hχPj : χP ≫ j = χ := hP.factorHom_comp _ _
  obtain ⟨g, ζ, hg⟩ := exists_innerIso_comp_eq_cocharacter
    smoothMaximalSplitTorusConjugacy hiP χP
  have hconj : χ ≫ (G.innerIso (g ≫ j.hom.hom)).hom =
      CommGroupScheme.groupHom ζ ≫ i := by
    rw [← hχPj, Category.assoc, comp_innerIso_hom_comp, ← Category.assoc, hg,
      Category.assoc, hiPj]
  have hgP : g ≫ j.hom.hom ∈ (Dynamic.parabolic χ).carrier _ := by
    rw [← hP.2]
    exact SubgroupFunctor.mem_range.mpr ⟨g, rfl⟩
  refine ⟨ζ, ?_⟩
  rw [← hconj, DynamicLeviConjugacy.parabolic_comp_innerIso_eq χ hgP]
  exact hχ.symm.trans hFj

/-- Surjectivity onto actual parabolics containing the fixed maximal split torus. -/
theorem semistandardSpectralCoverage : SemistandardSpectralCoverageStatement.{u} := by
  intro k _ G hG T i hi P
  obtain ⟨ζ, hζ⟩ := P.property.1.exists_fixedTorusCocharacter hG hi P.property.2
  refine ⟨SemistandardSpectralIndex.ofCocharacter hG ζ, ?_⟩
  exact Subtype.ext hζ

end Langlands.GroupScheme
