import Langlands.GroupScheme.BaseChangeReflection
import Langlands.GroupScheme.Torus.BaseChange
import Langlands.GroupScheme.Torus.Maximal

/-! # Reflection of maximal-torus maximality under field extension -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
variable {T : CommGroupScheme (Spec (CommRingCat.of k))}
variable {G : GroupScheme (Spec (CommRingCat.of k))} {i : T.toGrp ⟶ G}

/-- A comparison with an original-field closed torus is invertible if the given inclusion
becomes a maximal torus after extending the ground field. -/
def maximalTorusComparisonIsoOfBaseChange
    (h : IsMaximalTorus (T := (CommGroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj T)
      ((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map i)) :
    ∀ (T' : CommGroupScheme (Spec (CommRingCat.of k))) (i' : T'.toGrp ⟶ G)
      (f : T.toGrp ⟶ T'.toGrp), IsTorus T'.toGrp → IsClosedSubgroup i' →
      f ≫ i' = i → (T.toGrp ≅ T'.toGrp) := by
  intro T' i' f hT' hi' hf
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have hfpqc := fieldExtension_fpqc k K
  have : Surjective b := hfpqc.1
  have : Flat b := hfpqc.2.1
  have : QuasiCompact b := hfpqc.2.2
  have hcomp : (GroupScheme.baseChange b).map f ≫
      (GroupScheme.baseChange b).map i' = (GroupScheme.baseChange b).map i := by
    rw [← Functor.map_comp, hf]
  have : IsIso ((GroupScheme.baseChange b).map f) :=
    h.2.2 ((CommGroupScheme.baseChange b).obj T')
      ((GroupScheme.baseChange b).map i') ((GroupScheme.baseChange b).map f)
      hT'.baseChange (hi'.baseChange b) hcomp
  exact isoOfBaseChange b f

@[simp]
theorem maximalTorusComparisonIsoOfBaseChange_hom
    (h : IsMaximalTorus (T := (CommGroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj T)
      ((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map i))
    (T' : CommGroupScheme (Spec (CommRingCat.of k))) (i' : T'.toGrp ⟶ G)
    (f : T.toGrp ⟶ T'.toGrp) (hT' : IsTorus T'.toGrp) (hi' : IsClosedSubgroup i')
    (hf : f ≫ i' = i) :
    (maximalTorusComparisonIsoOfBaseChange h T' i' f hT' hi' hf).hom = f :=
  rfl

/-- A closed inclusion is a maximal torus if it becomes one after a field extension. -/
theorem IsMaximalTorus.of_baseChange (hi : IsClosedSubgroup i)
    (h : IsMaximalTorus (T := (CommGroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj T)
      ((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map i)) :
    IsMaximalTorus i := by
  refine ⟨IsTorus.of_baseChange h.1, hi, ?_⟩
  intro T' i' f hT' hi' hf
  change IsIso (maximalTorusComparisonIsoOfBaseChange h T' i' f hT' hi' hf).hom
  infer_instance

end Langlands.GroupScheme
