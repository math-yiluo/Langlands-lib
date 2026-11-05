import Langlands.GroupScheme.Rational.SplitTorusHomBaseChange

/-! # Descending a homomorphism together with a split torus target -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace Langlands.GroupScheme

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- Actual ground-field target and homomorphism recovering an extension-field
map to a split torus. No quotient or kernel properties are included. -/
structure SplitTorusHomDescentData
    (G : GroupScheme (Spec (CommRingCat.of k)))
    (D : GroupScheme (Spec (CommRingCat.of K)))
    (g : (GroupScheme.baseChange (algebraBaseMap k K)).obj G ⟶ D) where
  target : GroupScheme (Spec (CommRingCat.of k))
  isSplitTorus : IsSplitTorus target
  hom : G ⟶ target
  recovery : (GroupScheme.baseChange (algebraBaseMap k K)).obj target ≅ D
  baseChange_hom :
    (GroupScheme.baseChange (algebraBaseMap k K)).map hom ≫ recovery.hom = g

variable {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsReduced G.X.left] [IsAffineHom G.X.hom]

/-- A homomorphism from a pointed split-torus dominated reduced affine group
to any supplied split torus over an extension field descends together with an
actual split ground-field target and a target recovery isomorphism. -/
def HasPointedSplitTorusDomination.descendSplitTorusHom
    (hG : HasPointedSplitTorusDomination G)
    {D : GroupScheme (Spec (CommRingCat.of K))} (hD : IsSplitTorus D)
    (g : (GroupScheme.baseChange (algebraBaseMap k K)).obj G ⟶ D) :
    SplitTorusHomDescentData G D g :=
  Classical.choice <| by
    obtain ⟨I, hI, ⟨e⟩⟩ := hD
    let T := splitTorus (Spec (CommRingCat.of k)) I
    have hT : IsSplitTorus T := isSplitTorus_splitTorus I
    let c : (GroupScheme.baseChange (algebraBaseMap k K)).obj T ≅ D :=
      splitTorus.baseChangeIso (algebraBaseMap k K) I ≪≫ e.symm
    let f := (hG.splitTorusHomEquiv (K := K) hT).symm (g ≫ c.inv)
    have hf : (GroupScheme.baseChange (algebraBaseMap k K)).map f =
        g ≫ c.inv :=
      hG.baseChange_splitTorusHomEquiv_symm hT (g ≫ c.inv)
    refine ⟨{
      target := T
      isSplitTorus := hT
      hom := f
      recovery := c
      baseChange_hom := ?_
    }⟩
    rw [hf, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end Langlands.GroupScheme
