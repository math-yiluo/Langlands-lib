import Langlands.GroupScheme.AlgebraicFundamentalGroupConjugators
import Langlands.GroupScheme.Reductive.FieldExtensionProof
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof
import Langlands.GroupScheme.Torus.MaximalBaseChangeProof
import Langlands.GroupScheme.Torus.MaximalSplitComparison
import Langlands.GroupScheme.Torus.SplitLatticeBaseChange
import Langlands.GroupScheme.Rational.SmoothMaximalSplitTorusConjugacyProof
import Mathlib.FieldTheory.IsSepClosed

/-! # Geometric conjugators between presentations exist over a separable closure -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AlgebraicFundamentalGroup

variable {k E : Type u} [Field k] [Field E] [Algebra k E]

/-- A torus over `k` splits over every separable closure of `k`. -/
theorem isSplitTorus_baseChange_of_isSepClosure [IsSepClosure k E]
    (T : CommGroupScheme (Spec (CommRingCat.of k))) (hT : IsTorus T.toGrp) :
    IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k E)).obj T).toGrp := by
  have : IsSepClosed E := IsSepClosure.sep_closed k
  obtain ⟨K, _, _, _, _, hsplitK⟩ := torusFiniteGaloisSplitting k T.toGrp hT
  let φ : K →ₐ[k] E := IsSepClosed.lift
  let c : Spec (CommRingCat.of E) ⟶ Spec (CommRingCat.of K) :=
    Spec.map (CommRingCat.ofHom φ.toRingHom)
  have hc : c ≫ Spec.map (CommRingCat.ofHom (algebraMap k K)) = algebraBaseMap k E := by
    simp only [c, algebraBaseMap, ← Spec.map_comp]
    congr 1
    ext x
    exact φ.commutes x
  rw [← hc]
  exact IsSplitTorus.of_iso
    (GroupScheme.baseChangeCompIso (Spec.map (CommRingCat.ofHom (algebraMap k K))) c T.toGrp)
    (hsplitK.baseChange c)

namespace Choice

variable {G : GroupScheme (Spec (CommRingCat.of k))}

/-- Over a separable closure, the base change of a chosen maximal torus is a maximal
split torus of the base-changed group. -/
theorem isMaximalSplitTorus_baseChange [IsSepClosure k E] (hG : IsConnectedReductive G)
    (a : Choice k G) :
    IsMaximalSplitTorus (T := (CommGroupScheme.baseChange (algebraBaseMap k E)).obj a.torus)
      ((GroupScheme.baseChange (algebraBaseMap k E)).map a.inclusion) := by
  have : Smooth G.X.hom := hG.smooth
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have h := (maximalTorusBaseChange k E G a.torus a.inclusion a.isMaximal.1
    a.isMaximal.2.1).mp a.isMaximal
  exact h.isMaximalSplitTorus (isSplitTorus_baseChange_of_isSepClosure a.torus a.isMaximal.1)

variable (E)

/-- Any two presentations are related by an actual geometric conjugation over a
separable closure. -/
theorem exists_isConjugationComparison [IsSepClosure k E] (hG : IsConnectedReductive G)
    (a b : Choice k G) :
    ∃ (g : rationalPoints ((GroupScheme.baseChange (algebraBaseMap k E)).obj G))
      (e : (CommGroupScheme.baseChange (algebraBaseMap k E)).obj a.torus ≅
        (CommGroupScheme.baseChange (algebraBaseMap k E)).obj b.torus),
      a.IsConjugationComparison E b g e := by
  have hGE := connectedReductiveFieldExtensionStatement k E G hG
  have := hGE.smooth
  have := hGE.isAffineHom
  have := hGE.connectedSpace
  obtain ⟨g, e, he⟩ := smoothMaximalSplitTorusConjugacy E _ _ _ _ _
    (isMaximalSplitTorus_baseChange hG a) (isMaximalSplitTorus_baseChange hG b)
  exact ⟨g, CommGroupScheme.isoOfGroupIso e, he⟩

end Choice

end Langlands.GroupScheme.AlgebraicFundamentalGroup
