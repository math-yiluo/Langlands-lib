import Langlands.AlgebraicGeometry.FiniteFlatSubschemeParameter
import Langlands.GroupScheme.Descent.Data
import Langlands.GroupScheme.FiniteSubschemeStabilizerDescent
import Langlands.GroupScheme.IdentityJetSeparatedLocalBases
import Langlands.GroupScheme.IdentityJetStabilizer
import Langlands.GroupScheme.SubgroupBaseChange

/-! # The universal closed stabilizer of a finite identity-jet subscheme -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.FiniteFlatSubschemeParameter

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.IdentityJet

variable {S : Scheme.{u}} (G : GroupScheme S) (n : ℕ) (T : Over S)

/-- A closed subscheme of the ambient identity jet, viewed over the test scheme. -/
def subschemeOver (I : ((Over.pullback T.hom).obj (overScheme G n)).left.IdealSheafData) :
    Over T.left :=
  Over.mk (I.subschemeι ≫ ((Over.pullback T.hom).obj (overScheme G n)).hom)

/-- The inclusion of a closed subscheme of the jet into the group over the test. -/
def subschemeToGroup (I : ((Over.pullback T.hom).obj (overScheme G n)).left.IdealSheafData) :
    subschemeOver G n T I ⟶ ((baseChange T.hom).obj G).X :=
  Over.homMk I.subschemeι rfl ≫ (Over.pullback T.hom).map (overInclusion G n)

/-- The inclusion is closed after every base change. -/
theorem subschemeToGroup_isClosedImmersion
    (I : ((Over.pullback T.hom).obj (overScheme G n)).left.IdealSheafData) :
    IsClosedImmersion (subschemeToGroup G n T I).left := by
  have h : IsClosedImmersion (overInclusion G n).left :=
    inferInstanceAs (IsClosedImmersion (ideal G n).subschemeι)
  have : IsClosedImmersion ((Over.pullback T.hom).map (overInclusion G n)).left :=
    MorphismProperty.of_isPullback
      (RelativeIdentityComponent.overPullback_isPullback T.hom (overInclusion G n)).flip h
  change IsClosedImmersion (I.subschemeι ≫ ((Over.pullback T.hom).map (overInclusion G n)).left)
  infer_instance

@[reassoc (attr := simp)]
theorem subschemeToGroup_fst
    (I : ((Over.pullback T.hom).obj (overScheme G n)).left.IdealSheafData) :
    (subschemeToGroup G n T I).left ≫ pullback.fst G.X.hom T.hom =
      I.subschemeι ≫ pullback.fst (overScheme G n).hom T.hom ≫ (overInclusion G n).left := by
  change (I.subschemeι ≫ ((Over.pullback T.hom).map (overInclusion G n)).left) ≫
      pullback.fst G.X.hom T.hom = _
  rw [Category.assoc,
    (RelativeIdentityComponent.overPullback_isPullback T.hom (overInclusion G n)).w]
  rfl

/-- The actual specialization of a jet subscheme is a pullback over the test point, and its
stabilizer is computed by the specialized jet. The comparison of ambient groups identifies the
iterated pullback with the direct pullback over the test. -/
theorem subschemeStabilizer_eval {T : Over S} (D : Parameter (overScheme G n))
    (g : T ⟶ D.base) :
    (conjugationStabilizer (subschemeToGroup G n D.base D.ideal)).baseChange g.left =
      conjugationStabilizer (subschemeToGroup G n T (D.eval (overScheme G n) g) ≫
        (Descent.pullbackComparison D.base.hom g.left T.hom (Over.w g) G).inv.hom.hom) := by
  let A := overScheme G n
  let a := testMap A g
  let I := D.eval A g
  let k : I.subscheme ⟶ D.ideal.subscheme :=
    (D.ideal.comapIso a).hom ≫ pullback.snd a D.ideal.subschemeι
  have he : I.subschemeι ≫ a = k ≫ D.ideal.subschemeι := by
    dsimp only [k]
    rw [Category.assoc, ← pullback.condition, ← Category.assoc,
      Scheme.IdealSheafData.comapIso_hom_fst]
    rfl
  have hp : IsPullback I.subschemeι k a D.ideal.subschemeι := by
    apply isPullback_of_isClosedImmersion _ _ _ _ he
    rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι]
    rfl
  refine conjugationStabilizerBaseChange g.left _ _ k
    (hp.flip.paste_vert (testMap_isPullback A g)) ?_
  apply pullback.hom_ext
  · simp only [Over.comp_left, Category.assoc, Descent.pullbackComparison_inv_fst,
      subschemeToGroup_fst]
    rw [← Category.assoc k, ← he, Category.assoc I.subschemeι, testMap_fst_assoc]
  · let z := subschemeToGroup G n T I ≫
          (Descent.pullbackComparison D.base.hom g.left T.hom (Over.w g) G).inv.hom.hom
    have hw : z.left ≫ pullback.snd ((baseChange D.base.hom).obj G).X.hom g.left =
        (subschemeOver G n T I).hom := Over.w z
    change z.left ≫ pullback.fst ((baseChange D.base.hom).obj G).X.hom g.left ≫
        ((baseChange D.base.hom).obj G).X.hom =
      k ≫ (subschemeToGroup G n D.base D.ideal).left ≫ ((baseChange D.base.hom).obj G).X.hom
    rw [pullback.condition, ← Category.assoc, hw, Over.w (subschemeToGroup G n D.base D.ideal)]
    exact (hp.flip.paste_vert (testMap_isPullback A g)).w.symm

/-- For each order, the closed flat subschemes of the ambient identity jet have a universal
family, and the all-test stabilizer of that family is represented by a closed group scheme. -/
def IdentityJetStabilizerParameterStatement : Prop :=
  ∀ (R : CommRingCat.{u}) (G : GroupScheme (Spec R))
    [IsSeparated G.X.hom] [Smooth G.X.hom] (n : ℕ),
    ∃ D : Parameter (overScheme G n),
      (conjugationStabilizer (subschemeToGroup G n D.base D.ideal)).IsClosedRepresentable

/-- The finite flat subscheme parameter and closed stabilizer descent applied to the actual jet. -/
theorem identityJetStabilizerParameter : IdentityJetStabilizerParameterStatement.{u} := by
  intro R G _ _ n
  have hfin := finite_projection G n
  have hflat := flat_projection G n
  have hfp := locallyOfFinitePresentation_projection G n
  obtain ⟨D⟩ := finiteFlatSubschemeParameter R (overScheme G n) hfin hflat hfp
  let : IsFinite (overScheme G n).hom := hfin
  have : IsFinite (subschemeOver G n D.base D.ideal).hom := D.isFinite (overScheme G n)
  have : Flat (subschemeOver G n D.base D.ideal).hom := D.flat
  have : LocallyOfFinitePresentation (subschemeOver G n D.base D.ideal).hom := D.finitelyPresented
  exact ⟨D, finiteSubschemeStabilizerDescent _ _ _ _ (subschemeToGroup_isClosedImmersion G n _ _)⟩

end Langlands.GroupScheme.IdentityJet
