import Langlands.GroupScheme.Torus.ExistenceProof
import Langlands.GroupScheme.Rational.SplitTorus

/-! # The actual rank-zero maximal split torus of an anisotropic group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.TorusExistence

variable {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsSeparated G.X.hom]

/-- The identity-section inclusion of the trivial torus is maximal split
in an anisotropic separated group over a field. -/
theorem isMaximalSplitTorus_trivialTorusHom (ha : IsAnisotropic G) :
    IsMaximalSplitTorus (trivialTorusHom G) := by
  refine ⟨⟨isSplitTorus_splitTorus _, isClosedSubgroup_trivialTorusHom G⟩, ?_⟩
  intro T i hi f _
  let :=ha.subsingleton_hom_of_isSplitSubtorus hi T.toGrp
  let :=splitTorus.subsingleton_hom_of_isEmpty (S := Spec (CommRingCat.of k))
    PEmpty.{u + 1} (trivialTorus k).toGrp
  let g : T.toGrp ⟶ (trivialTorus k).toGrp := default ≫ splitTorusEmptyIso.inv
  exact ⟨g, Subsingleton.elim _ _, Subsingleton.elim _ _⟩

/-- The maximal split torus data with exactly the rank-zero torus as domain
and the existing trivial-torus homomorphism as inclusion. -/
def anisotropicMaximalSplitTorus (ha : IsAnisotropic G) :
    Σ T : CommGroupScheme (Spec (CommRingCat.of k)), {i : T.toGrp ⟶ G // IsMaximalSplitTorus i} :=
  ⟨trivialTorus k, trivialTorusHom G, isMaximalSplitTorus_trivialTorusHom G ha⟩

@[simp] theorem anisotropicMaximalSplitTorus_torus (ha : IsAnisotropic G) :
    (anisotropicMaximalSplitTorus G ha).1 = trivialTorus k := rfl

@[simp] theorem anisotropicMaximalSplitTorus_inclusion (ha : IsAnisotropic G) :
    (anisotropicMaximalSplitTorus G ha).2.val = trivialTorusHom G := rfl

end Langlands.GroupScheme.TorusExistence
