import Langlands.GroupScheme.Torus.Split
import Langlands.AbelianScheme.Tate.BaseChangeCoherence
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Descent of a split torus along a base map with a section -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S S' : Scheme.{u}}

/-- Pulling a group scheme back along a map and then along its section recovers the
original group scheme. -/
def baseChangeSectionIso (b : S' ⟶ S) (a : S ⟶ S') (ha : a ≫ b = 𝟙 S)
    (G : GroupScheme S) :
    (GroupScheme.baseChange a).obj ((GroupScheme.baseChange b).obj G) ≅ G :=
  (baseChangeCompIso b a G).symm ≪≫
    eqToIso (congrArg (fun c => (GroupScheme.baseChange c).obj G) ha) ≪≫
    baseChangeIdIso G

namespace splitTorus

/-- An actual split-torus isomorphism descends by pullback along a section of the
original base map. -/
def isoOfBaseChangeSection (b : S' ⟶ S) (a : S ⟶ S') (ha : a ≫ b = 𝟙 S)
    (G : GroupScheme S) (I : Type u) [Finite I]
    (e : (GroupScheme.baseChange b).obj G ≅ splitTorus S' I) :
    G ≅ splitTorus S I :=
  (baseChangeSectionIso b a ha G).symm ≪≫
    (GroupScheme.baseChange a).mapIso e ≪≫ splitTorus.baseChangeIso a I

end splitTorus

/-- Splitness descends along a base map admitting a section. -/
theorem IsSplitTorus.of_baseChange_of_section (b : S' ⟶ S) (a : S ⟶ S')
    (ha : a ≫ b = 𝟙 S) {G : GroupScheme S}
    (hG : IsSplitTorus ((GroupScheme.baseChange b).obj G)) : IsSplitTorus G := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hG
  exact ⟨I, hI, ⟨splitTorus.isoOfBaseChangeSection b a ha G I e⟩⟩

/-- A base map with a section preserves and reflects splitness of tori. -/
theorem isSplitTorus_baseChange_iff_of_section (b : S' ⟶ S) (a : S ⟶ S')
    (ha : a ≫ b = 𝟙 S) (G : GroupScheme S) :
    IsSplitTorus ((GroupScheme.baseChange b).obj G) ↔ IsSplitTorus G :=
  ⟨IsSplitTorus.of_baseChange_of_section b a ha, fun hG => hG.baseChange b⟩

/-- A split torus descends along an isomorphism of base schemes. -/
theorem IsSplitTorus.of_baseChange_of_isIso (b : S' ⟶ S) [IsIso b]
    {G : GroupScheme S} (hG : IsSplitTorus ((GroupScheme.baseChange b).obj G)) :
    IsSplitTorus G :=
  hG.of_baseChange_of_section b (inv b) (IsIso.inv_hom_id b)

section AlgebraicallyClosed

variable {k K : Type u} [Field k] [IsAlgClosed k] [Field K] [Algebra k K]
  [Algebra.IsAlgebraic k K]

/-- Over an algebraically closed base field, splitness descends from every algebraic
field extension. -/
theorem IsSplitTorus.of_baseChange_of_isAlgebraic
    {G : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsSplitTorus ((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G)) : IsSplitTorus G := by
  have : IsIso (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
    isIso_SpecMap_iff.mpr IsAlgClosed.algebraMap_bijective_of_isIntegral
  exact hG.of_baseChange_of_isIso _

/-- Algebraic field extension preserves and reflects splitness over an algebraically
closed base field. -/
theorem isSplitTorus_baseChange_iff_of_isAlgebraic
    (G : GroupScheme (Spec (CommRingCat.of k))) :
    IsSplitTorus ((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G) ↔ IsSplitTorus G :=
  ⟨IsSplitTorus.of_baseChange_of_isAlgebraic, fun hG => hG.baseChange _⟩

end AlgebraicallyClosed

end Langlands.GroupScheme
