import Langlands.GroupScheme.Absolute.CommonTorusFromNormalizerDoubleCoset
import Langlands.GroupScheme.Absolute.BorelMaximalTorusReduction
import Langlands.GroupScheme.Absolute.BruhatCoveringStatement
import Langlands.GroupScheme.Absolute.TwoBorelCommonMaximalTorusStatement

/-! # Common maximal tori from independent absolute Bruhat inputs -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Choose actual common-torus maps from independent Borel conjugacy and
absolute geometric Bruhat covering. Both structural inputs remain hypotheses. -/
def commonMaximalTorusOfBorelBruhatInputs
    (hconj : BorelConjugacyStatement.{u})
    (hcover : AbsoluteBruhatCoveringStatement.{u})
    (k : Type u) [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G)
    (B B' : GroupScheme (Spec (CommRingCat.of k))) (i : B ⟶ G) (i' : B' ⟶ G)
    (hi : IsBorelSubgroup i) (hi' : IsBorelSubgroup i') :
    Σ T : CommGroupScheme (Spec (CommRingCat.of k)), Σ t : T.toGrp ⟶ G,
      Σ f : T.toGrp ⟶ B,
        {f' : T.toGrp ⟶ B' // IsMaximalTorus t ∧ f ≫ i = t ∧ f' ≫ i' = t} := by
  apply Classical.choice
  let := hG.smooth
  let := hG.isAffineHom
  let := hG.connectedSpace
  obtain ⟨T, j, hij⟩ := borelMaximalTorusStatement_of_borelConjugacy hconj k G B i hi
  obtain ⟨g, φ, hgφ⟩ := (hconj k G).2 B B' i i' hi hi'
  obtain ⟨b₁, b₂, n, hg⟩ := hcover k G hG B T i j hij g
  obtain ⟨f, hf⟩ := hij.2.2
  exact ⟨⟨T, commonTorusOfNormalizerDoubleCoset i i' j f hij.2.1 hf g φ hgφ
    b₁ b₂ n hg⟩⟩

/-- The common-torus statement follows from the two independent absolute
geometric inputs, with the published target and all universes unchanged. -/
theorem twoBorelCommonMaximalTorusStatement_of_borel_bruhat_inputs
    (hconj : BorelConjugacyStatement.{u})
    (hcover : AbsoluteBruhatCoveringStatement.{u}) :
    TwoBorelCommonMaximalTorusStatement.{u} := by
  intro k _ _ G hG B B' i i' hi hi'
  obtain ⟨T, t, f, f', ht⟩ :=
    commonMaximalTorusOfBorelBruhatInputs hconj hcover k G hG B B' i i' hi hi'
  exact ⟨T, t, f, f', ht⟩

end Langlands.GroupScheme
