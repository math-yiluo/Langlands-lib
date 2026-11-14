import Langlands.GroupScheme.RelativeLevi.BorelTransport
import Langlands.GroupScheme.RelativeLevi.BorelSchemeStatement
import Langlands.GroupScheme.Rational.FiniteFieldQuasiSplit
import Langlands.CommutativeAlgebra.HenselianSections

/-! # Henselian lifting of Borel subgroups from a smooth parameter scheme -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

/-- A geometric Borel of a connected reductive field group is a relative Borel
over the spectrum of that field. -/
theorem IsGeometricBorelSubgroup.isRelativeBorelSubgroup
    {k : Type u} [Field k] {B G : GroupScheme (Spec (CommRingCat.of k))}
    {i : B ⟶ G} (hi : IsGeometricBorelSubgroup i) (hG : IsConnectedReductive G) :
    IsRelativeBorelSubgroup i := by
  let : IsClosedImmersion i.hom.hom.left := hi.1.isClosedSubgroup
  let : IsAffineHom G.X.hom := hG.isAffineHom
  have hB : IsAffineHom B.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  have hf : ∀ s : Spec (CommRingCat.of k),
      IsGeometricBorelSubgroup (RelativeLevi.residueFiberHom i s) :=
    fun s => hi.baseChange hG ((Spec (CommRingCat.of k)).fromSpecResidueField s)
  exact ⟨⟨hi.1.smooth, hB, Over.mono_of_mono_left _,
    fun s => (hf s).isParabolicSubgroup⟩, hf⟩

/-- Smooth Borel representability lifts existence of a geometric Borel in the
closed fibre to existence of a relative Borel over a Henselian local ring. -/
theorem exists_relativeBorel_of_borelScheme
    (hBor : RelativeBorelSchemeStatement.{u})
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    (G : GroupScheme (Spec (CommRingCat.of R))) (hG : IsReductive G)
    (B₀ : GroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField R))))
    (i₀ : B₀ ⟶
      (GroupScheme.baseChange (Spec.algebraMap R (IsLocalRing.ResidueField R))).obj G)
    (hi₀ : IsGeometricBorelSubgroup i₀) :
    ∃ (B : GroupScheme (Spec (CommRingCat.of R))) (i : B ⟶ G),
      IsRelativeBorelSubgroup i := by
  let f₀ := Spec.algebraMap R (IsLocalRing.ResidueField R)
  obtain ⟨M, B, j, hj, hUniversal, hSmooth, -⟩ :=
    hBor (Spec (CommRingCat.of R)) G hG
  obtain ⟨a, -, -⟩ := hUniversal (Over.mk f₀) B₀ i₀
    (hi₀.isRelativeBorelSubgroup (hG.isConnectedReductive_baseChange f₀))
  let : Smooth M.hom := hSmooth
  obtain ⟨σ, hσ, -⟩ :=
    Langlands.CommutativeAlgebra.HenselianSections.exists_section_of_smooth_of_surjective
      (show Function.Surjective (algebraMap R (IsLocalRing.ResidueField R)) from
        IsLocalRing.residue_surjective)
      M.hom a.left (Over.w a)
  exact ⟨(GroupScheme.baseChange σ).obj B,
    (GroupScheme.baseChange σ).map j ≫ (sectionPullbackIso M.hom σ hσ G).hom,
    (hj.baseChange (hG.baseChange M.hom) σ).comp_iso
      (sectionPullbackIso M.hom σ hσ G)⟩

/-- A selected actual relative Borel obtained by Henselian lifting from the
smooth universal family. Borel representability remains an explicit input. -/
def henselianBorelLift
    (hBor : RelativeBorelSchemeStatement.{u})
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    (G : GroupScheme (Spec (CommRingCat.of R))) (hG : IsReductive G)
    (B₀ : GroupScheme (Spec (CommRingCat.of (IsLocalRing.ResidueField R))))
    (i₀ : B₀ ⟶
      (GroupScheme.baseChange (Spec.algebraMap R (IsLocalRing.ResidueField R))).obj G)
    (hi₀ : IsGeometricBorelSubgroup i₀) :
    Σ B : GroupScheme (Spec (CommRingCat.of R)), {i : B ⟶ G // IsRelativeBorelSubgroup i} :=
  let h := exists_relativeBorel_of_borelScheme hBor R G hG B₀ i₀ hi₀
  ⟨Classical.choose h, Classical.choose (Classical.choose_spec h),
    Classical.choose_spec (Classical.choose_spec h)⟩

/-- Conditional quasi-splitness over a Henselian local ring with finite residue
field: the only additional input is the published Borel-scheme proposition. -/
theorem henselianFiniteResidueQuasiSplit_of_borelScheme
    (hBor : RelativeBorelSchemeStatement.{u})
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    [Finite (IsLocalRing.ResidueField R)]
    (G : GroupScheme (Spec (CommRingCat.of R))) (hG : IsReductive G) :
    IsRelativeQuasiSplit G := by
  let f₀ := Spec.algebraMap R (IsLocalRing.ResidueField R)
  obtain ⟨B₀, i₀, hi₀⟩ :=
    (finiteFieldQuasiSplit (IsLocalRing.ResidueField R)
      ((GroupScheme.baseChange f₀).obj G)
      (hG.isConnectedReductive_baseChange f₀)).exists_isGeometricBorelSubgroup
  exact ⟨hG, exists_relativeBorel_of_borelScheme hBor R G hG B₀ i₀ hi₀⟩

end Langlands.GroupScheme
