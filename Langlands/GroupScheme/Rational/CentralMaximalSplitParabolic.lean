import Langlands.GroupScheme.Rational.MaximalSplitTorusConjugacyProof
import Langlands.GroupScheme.Rational.QuasiSplitAdaptedSplitTorus
import Langlands.GroupScheme.Rational.CentralTorusFixedness
import Langlands.GroupScheme.Rational.CentralCocharacterReduction
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof

/-! # No proper rational parabolics with a central maximal split torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {F : Type u} [Field F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {s : S.toGrp ⟶ G}

/-- A central maximal split torus forces every other maximal split torus to be central,
by the proved rational conjugacy theorem and fixedness of central maps under inner maps. -/
theorem IsMaximalSplitTorus.isCentral_of_central_maximalSplitTorus
    (hs : IsMaximalSplitTorus s) (hc : IsCentral s) (hG : IsConnectedReductive G)
    {A : CommGroupScheme (Spec (CommRingCat.of F))} {a : A.toGrp ⟶ G}
    (ha : IsMaximalSplitTorus a) : IsCentral a := by
  obtain ⟨g, e, he⟩ := (maximalSplitTorusConjugacy F G hG).1 S A s a hs ha
  rw [hc.comp_innerIso_hom g] at he
  have hae : e.inv ≫ s = a := by
    rw [he, Iso.inv_hom_id_assoc]
  exact hae ▸ hc.comp e.inv

/-- Every actual ground-field cocharacter is central if one maximal split torus is central. -/
theorem IsMaximalSplitTorus.isCentral_cocharacter
    (hs : IsMaximalSplitTorus s) (hc : IsCentral s) (hG : IsConnectedReductive G)
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) : IsCentral χ := by
  have : Smooth G.X.hom := hG.smooth
  have : IsAffineHom G.X.hom := hG.isAffineHom
  obtain ⟨A, a, ha, ν, hν, -⟩ := exists_maximalSplitTorus_through_cocharacter χ
  rw [← hν]
  exact (hs.isCentral_of_central_maximalSplitTorus hc hG ha).comp ν

/-- With a central maximal split torus, every actual rational parabolic inclusion into a
connected reductive group is an isomorphism. No restriction on the field is needed. -/
theorem IsMaximalSplitTorus.isIso_parabolic_of_isCentral
    (hs : IsMaximalSplitTorus s) (hc : IsCentral s) (hG : IsConnectedReductive G)
    {P : GroupScheme (Spec (CommRingCat.of F))} {p : P ⟶ G}
    (hp : IsParabolicSubgroup p) : IsIso p :=
  isIso_parabolic_of_central_cocharacters parabolicDynamic hG
    (fun χ => (isCentral_iff_dynamicCentralizer_eq_top χ).mp
      (hs.isCentral_cocharacter hc hG χ)) hp

/-- The canonical identification of an actual rational parabolic with the ambient group
under the central-maximal-split-torus hypothesis. Its map is the original inclusion. -/
def IsMaximalSplitTorus.parabolicIsoOfIsCentral
    (hs : IsMaximalSplitTorus s) (hc : IsCentral s) (hG : IsConnectedReductive G)
    {P : GroupScheme (Spec (CommRingCat.of F))} {p : P ⟶ G}
    (hp : IsParabolicSubgroup p) : P ≅ G :=
  haveI := hs.isIso_parabolic_of_isCentral hc hG hp
  asIso p

@[simp] theorem IsMaximalSplitTorus.parabolicIsoOfIsCentral_hom
    (hs : IsMaximalSplitTorus s) (hc : IsCentral s) (hG : IsConnectedReductive G)
    {P : GroupScheme (Spec (CommRingCat.of F))} {p : P ⟶ G}
    (hp : IsParabolicSubgroup p) :
    (hs.parabolicIsoOfIsCentral hc hG hp).hom = p := rfl

/-- The assertion is about the whole subgroup functor on all test schemes. -/
theorem IsMaximalSplitTorus.range_parabolic_eq_top_of_isCentral
    (hs : IsMaximalSplitTorus s) (hc : IsCentral s) (hG : IsConnectedReductive G)
    {P : GroupScheme (Spec (CommRingCat.of F))} {p : P ⟶ G}
    (hp : IsParabolicSubgroup p) : SubgroupFunctor.range p = ⊤ := by
  have : IsIso p := hs.isIso_parabolic_of_isCentral hc hG hp
  calc
    SubgroupFunctor.range p =
        SubgroupFunctor.range ((asIso p).hom ≫ 𝟙 G) := by simp
    _ = SubgroupFunctor.range (𝟙 G) := SubgroupFunctor.range_iso_comp (asIso p) (𝟙 G)
    _ = ⊤ := (SubgroupFunctor.top_isRepresentedBy_id G).2

end Langlands.GroupScheme
