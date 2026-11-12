import Langlands.Representation.Category.UniverseLift
import Langlands.Representation.Category.SubrepresentationSums

/-! # Invariant subspaces across independent carrier universes -/

noncomputable section

open CategoryTheory

namespace Langlands.SmoothRep

universe uG uV uW uX uI

variable {G : Type uG} [Group G] [TopologicalSpace G]
  {A : SmoothRep.{0, uG, uV} ℂ G} {B : SmoothRep.{0, uG, uW} ℂ G}

/-- Inverse image of an invariant subspace under an actual intertwiner.
The source and target carriers may lie in different universes. -/
def intertwinerPreimage (f : A.representation.IntertwiningMap B.representation)
    (S : Subrepresentation B.representation) : Subrepresentation A.representation where
  toSubmodule := S.toSubmodule.comap f.toLinearMap
  apply_mem_toSubmodule g v hv := by
    change f (A.representation g v) ∈ S
    rw [Representation.IntertwiningMap.isIntertwining]
    exact S.apply_mem_toSubmodule g hv

/-- Restrict the intertwiner to the actual inverse-image subspace. -/
def intertwinerPreimageMap
    (f : A.representation.IntertwiningMap B.representation)
    (S : Subrepresentation B.representation) :
    (subrepresentation A (intertwinerPreimage f S)).representation.IntertwiningMap
      (subrepresentation B S).representation where
  toLinearMap := f.toLinearMap.submoduleComap S.toSubmodule
  isIntertwining' g := by
    ext v
    exact Subtype.ext (Representation.IntertwiningMap.isIntertwining _ _ f g v.val)

theorem intertwinerPreimageMap_injective
    (f : A.representation.IntertwiningMap B.representation)
    (S : Subrepresentation B.representation) (hf : Function.Injective f) :
    Function.Injective (intertwinerPreimageMap f S) := by
  intro x y hxy
  exact Subtype.ext (hf (congrArg Subtype.val hxy))

/-- A spanning invariant family remains spanning on pulling back along an
actual representation equivalence, independently of its carrier universes. -/
theorem iSup_intertwinerPreimage_eq_top_of_equiv
    (e : A.representation.Equiv B.representation)
    {I : Type uI} (S : I → Subrepresentation B.representation)
    (hS : (⨆ i, S i) = ⊤) :
    (⨆ i, intertwinerPreimage e.toIntertwiningMap (S i)) = ⊤ := by
  apply Subrepresentation.toSubmodule_injective
  rw [Langlands.Subrepresentation.toSubmodule_iSup]
  let o := (Submodule.orderIsoMapComap e.toLinearEquiv).symm
  change (⨆ i, o (S i).toSubmodule) = ⊤
  rw [← o.map_iSup, ← Langlands.Subrepresentation.toSubmodule_iSup, hS]
  exact o.map_top

/-- An injective actual intertwiner identifies its source with its invariant
image, even when the source and target carriers have different universes. -/
def intertwinerImageEquiv
    (f : A.representation.IntertwiningMap B.representation)
    (hf : Function.Injective f) :
    A.representation.Equiv (subrepresentation B f.range).representation := by
  let j : A.representation.IntertwiningMap (subrepresentation B f.range).representation :=
    { toLinearMap := f.toLinearMap.rangeRestrict
      isIntertwining' g := by
        ext v
        exact Subtype.ext (Representation.IntertwiningMap.isIntertwining _ _ f g v) }
  exact j.ofBijective
    ⟨fun x y hxy => hf (congrArg Subtype.val hxy),
      fun ⟨_, x, hx⟩ => ⟨x, Subtype.ext hx⟩⟩

/-- A subquotient of the source of a cross-universe injection lifts to an
actual subquotient of its target. -/
theorem IsSubquotient.universeLift_of_injectiveIntertwiner
    {D : SmoothRep.{0, uG, uV} ℂ G}
    {C : SmoothRep.{0, uG, max uV uX} ℂ G}
    (h : IsSubquotient D A)
    (f : A.representation.IntertwiningMap C.representation)
    (hf : Function.Injective f) :
    IsSubquotient (universeLift.{uX} D) C := by
  obtain ⟨X, j, q, hj, hq⟩ := isSubquotient_iff_exists.mp h
  let X' := universeLift.{uX} X
  let eX := universeLiftEquiv.{uX} X
  let eD := universeLiftEquiv.{uX} D
  let j' := f.comp ((hom j).comp eX.symm.toIntertwiningMap)
  let q' := eD.toIntertwiningMap.comp ((hom q).comp eX.symm.toIntertwiningMap)
  exact isSubquotient_iff_exists.mpr
    ⟨X', ofHom j', ofHom q',
      hf.comp (hj.comp eX.symm.injective),
      eD.surjective.comp (hq.comp eX.symm.surjective)⟩

end Langlands.SmoothRep
