import Langlands.GroupScheme.Rational.ParabolicFunctor
import Langlands.GroupScheme.Rational.ParabolicSplitTorusConjugacyReduction
import Langlands.GroupScheme.Rational.PseudoParabolicAmbientTransport
import Langlands.GroupScheme.Reductive.UnipotentRadicalExistenceProof
import Langlands.GroupScheme.Dynamic.ConnectedProof

/-! # The intrinsic unipotent-radical family of rational parabolics -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.GroupScheme

variable {F : Type u} [Field F]
  {G : GroupScheme (Spec (CommRingCat.of F))}

/-- Every proper rational parabolic subgroup functor, with properness on all tests. -/
abbrev ProperRationalParabolic (G : GroupScheme (Spec (CommRingCat.of F))) :=
  {P : ParabolicFunctor G // P.val ≠ ⊤}

/-- The actual ambient image of the represented ground-field radical of a parabolic.
Both equalities are equalities of subgroup functors on every test scheme. -/
def IsRationalParabolicRadical (P U : SubgroupFunctor G) : Prop :=
  ∃ (P₀ U₀ : GroupScheme (Spec (CommRingCat.of F))) (p : P₀ ⟶ G) (r : U₀ ⟶ P₀),
    IsParabolicSubgroup p ∧ SubgroupFunctor.range p = P ∧ IsUnipotentRadical r ∧
      SubgroupFunctor.range (r ≫ p) = U

/-- The ambient radical image is unchanged by either closed subgroup presentation. -/
theorem parabolicRadical_range_eq
    {P P' U U' : GroupScheme (Spec (CommRingCat.of F))}
    {p : P ⟶ G} {p' : P' ⟶ G} {r : U ⟶ P} {r' : U' ⟶ P'}
    (hp : IsClosedSubgroup p) (hp' : IsClosedSubgroup p')
    (hP : SubgroupFunctor.range p = SubgroupFunctor.range p')
    (hr : IsUnipotentRadical r) (hr' : IsUnipotentRadical r') :
    SubgroupFunctor.range (r ≫ p) = SubgroupFunctor.range (r' ≫ p') := by
  let : IsClosedImmersion p.hom.hom.left := hp
  let : IsClosedImmersion p'.hom.hom.left := hp'
  let hrep : (SubgroupFunctor.range p).IsRepresentedBy p :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  let hrep' : (SubgroupFunctor.range p).IsRepresentedBy p' :=
    ⟨Over.mono_of_mono_left _, hP.symm⟩
  let e := hrep.isoOfIsRepresentedBy hrep'
  have he : e.hom ≫ p' = p := hrep.isoOfIsRepresentedBy_hom_comp hrep'
  have hrad := (hr.comp_iso e).range_eq hr'
  have heq := le_antisymm (SubgroupFunctor.range_comp_mono hrad.le p')
    (SubgroupFunctor.range_comp_mono hrad.ge p')
  simpa only [Category.assoc, he] using heq

/-- A parabolic subgroup functor has at most one ambient radical image. -/
theorem IsRationalParabolicRadical.unique {P U V : SubgroupFunctor G}
    (hU : IsRationalParabolicRadical P U) (hV : IsRationalParabolicRadical P V) : U = V := by
  obtain ⟨P₀, U₀, p, r, hp, hP, hr, rfl⟩ := hU
  obtain ⟨P₁, U₁, p', r', hp', hP', hr', rfl⟩ := hV
  exact parabolicRadical_range_eq hp.isClosedSubgroup hp'.isClosedSubgroup
    (hP.trans hP'.symm) hr hr'

/-- The radical image is an actual subgroup functor of the specified parabolic. -/
theorem IsRationalParabolicRadical.le {P U : SubgroupFunctor G}
    (hU : IsRationalParabolicRadical P U) : U ≤ P := by
  obtain ⟨P₀, U₀, p, r, _, hP, _, rfl⟩ := hU
  rw [← hP]
  exact SubgroupFunctor.range_le_of_factor r rfl

/-- Parabolic connectedness remains the explicit structural input to existence.
The represented radical itself comes from the public existence theorem. -/
theorem exists_rationalParabolicRadical
    (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive G)
    (P : ParabolicFunctor G) : ∃ U, IsRationalParabolicRadical P.val U := by
  obtain ⟨P₀, p, hp, hP⟩ := P.property
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsClosedImmersion p.hom.hom.left := hp.isClosedSubgroup
  let : IsAffineHom P₀.X.hom := by
    rw [← Over.w p.hom.hom]
    infer_instance
  let : Smooth P₀.X.hom := hp.smooth
  let : ConnectedSpace P₀.X.left :=
    hp.connectedSpace_of_parabolicDynamic hPD dynamicConnected hG
  obtain ⟨U₀, r, hr⟩ := unipotentRadicalExistence F P₀
  exact ⟨SubgroupFunctor.range (r ≫ p), P₀, U₀, p, r, hp, hP, hr, rfl⟩

/-- A choice of the unique actual ambient image; no source presentation is retained. -/
def rationalParabolicRadical
    (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive G)
    (P : ParabolicFunctor G) : SubgroupFunctor G :=
  Classical.choose (exists_rationalParabolicRadical hPD hG P)

theorem rationalParabolicRadical_spec
    (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive G)
    (P : ParabolicFunctor G) :
    IsRationalParabolicRadical P.val (rationalParabolicRadical hPD hG P) :=
  Classical.choose_spec (exists_rationalParabolicRadical hPD hG P)

/-- This canonical image equals that of every actual represented radical. -/
theorem rationalParabolicRadical_eq
    (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive G)
    (P : ParabolicFunctor G) {P₀ U₀ : GroupScheme (Spec (CommRingCat.of F))}
    {p : P₀ ⟶ G} {r : U₀ ⟶ P₀} (hp : IsParabolicSubgroup p)
    (hP : SubgroupFunctor.range p = P.val) (hr : IsUnipotentRadical r) :
    rationalParabolicRadical hPD hG P = SubgroupFunctor.range (r ≫ p) :=
  (rationalParabolicRadical_spec hPD hG P).unique ⟨P₀, U₀, p, r, hp, hP, hr, rfl⟩

/-- The whole family uses every proper rational parabolic, including nonstandard ones. -/
def properRationalParabolicRadicals
    (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive G)
    (P : ProperRationalParabolic G) : SubgroupFunctor G :=
  rationalParabolicRadical hPD hG P.val

/-- Every actual proper rational parabolic occurs in this indexing. -/
theorem properRationalParabolicRadicals_eq
    (hPD : ParabolicDynamicStatement.{u}) (hG : IsConnectedReductive G)
    {P₀ U₀ : GroupScheme (Spec (CommRingCat.of F))}
    {p : P₀ ⟶ G} {r : U₀ ⟶ P₀} (hp : IsParabolicSubgroup p)
    (hproper : SubgroupFunctor.range p ≠ ⊤) (hr : IsUnipotentRadical r) :
    properRationalParabolicRadicals hPD hG
      ⟨⟨SubgroupFunctor.range p, ⟨P₀, p, hp, rfl⟩⟩, hproper⟩ =
        SubgroupFunctor.range (r ≫ p) :=
  rationalParabolicRadical_eq hPD hG _ hp rfl hr

end Langlands.Automorphic.GroupSchemeFunctions
