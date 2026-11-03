import Langlands.GroupScheme.Dynamic.Action
import Langlands.GroupScheme.Dynamic.ClosedSubgroup

/-! # Uniqueness and invariant morphisms for abstract dynamic subgroup functors -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AutomorphicAction

variable {S : Scheme.{u}} {H G K : GroupScheme S}

/-- A morphism is invariant if its value is unchanged by the action on every test scheme. -/
def IsInvariantMorphism (a : AutomorphicAction H G) {Y : Over S} (f : G.X ⟶ Y) : Prop :=
  ∀ {T : Over S} (h : T ⟶ H.X) (g : T ⟶ G.X), a.act h g ≫ f = g ≫ f

variable (a : AutomorphicAction (Gm S).toGrp G)

section Separated

variable [IsSeparated G.X.hom]

/-- An abstract multiplicative-group orbit has at most one affine-line extension. -/
theorem IsOrbitExtension.unique {T : Over S} {g : T ⟶ G.X}
    {e e' : T ⊗ AffineLine.scheme S ⟶ G.X} (he : a.IsOrbitExtension g e)
    (he' : a.IsOrbitExtension g e') : e = e' :=
  AffineLine.hom_ext_of_unitInclusion (he.trans he'.symm)

/-- A point has at most one limit for an action on a separated group scheme. -/
theorem HasLimit.unique {T : Over S} {g l l' : T ⟶ G.X} (hl : a.HasLimit g l)
    (hl' : a.HasLimit g l') : l = l' := by
  obtain ⟨e, he, rfl⟩ := hl
  obtain ⟨e', he', rfl⟩ := hl'
  rw [he.unique a he']

/-- A fixed point whose orbit has identity limit is the identity. -/
theorem eq_one_of_mem_centralizer_of_mem_unipotent {T : Over S} {g : T ⟶ G.X}
    (hz : g ∈ a.centralizer.carrier T) (hu : g ∈ a.unipotent.carrier T) : g = 1 :=
  (a.hasLimit_of_mem_centralizer hz).unique a hu

/-- The fixed and identity-limit subgroup functors have trivial intersection. -/
theorem centralizer_inf_unipotent_eq_bot : a.centralizer ⊓ a.unipotent = ⊥ := by
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro g
  constructor
  · intro hg
    exact Subgroup.mem_bot.mpr (a.eq_one_of_mem_centralizer_of_mem_unipotent hg.1 hg.2)
  · intro hg
    rw [SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hg
    subst g
    exact one_mem _

end Separated

section Invariant

variable {Y : Over S} (f : G.X ⟶ Y) [IsSeparated Y.hom]
    (hf : a.IsInvariantMorphism f)

include hf

/-- An invariant morphism sends an orbit extension to the constant extension of its value. -/
theorem IsOrbitExtension.comp_eq_fst_of_invariant {T : Over S} {g : T ⟶ G.X}
    {e : T ⊗ AffineLine.scheme S ⟶ G.X} (he : a.IsOrbitExtension g e) :
    e ≫ f = fst T (AffineLine.scheme S) ≫ (g ≫ f) := by
  apply AffineLine.hom_ext_of_unitInclusion
  rw [← Category.assoc, he, orbit, hf, whiskerLeft_fst_assoc, Category.assoc]

/-- An invariant morphism takes the same value on a point and any limit of its orbit. -/
theorem HasLimit.comp_eq_of_invariant {T : Over S} {g l : T ⟶ G.X}
    (hl : a.HasLimit g l) : g ≫ f = l ≫ f := by
  obtain ⟨e, he, he0⟩ := hl
  have h := congrArg Dynamic.evalZero (he.comp_eq_fst_of_invariant a f hf)
  rw [Dynamic.evalZero_comp, he0, Dynamic.evalZero_fst] at h
  exact h.symm

end Invariant

section InvariantHom

variable (f : G ⟶ K) [IsSeparated K.X.hom] (hf : a.IsInvariantMorphism f.hom.hom)

include hf

/-- An invariant group homomorphism kills every point with identity limit. -/
theorem comp_eq_one_of_mem_unipotent_of_invariant {T : Over S} {g : T ⟶ G.X}
    (hg : g ∈ a.unipotent.carrier T) : g ≫ f.hom.hom = 1 := by
  have h := HasLimit.comp_eq_of_invariant a f.hom.hom hf hg
  rwa [MonObj.one_comp] at h

/-- The identity-limit subgroup functor lies in the kernel of any invariant homomorphism. -/
theorem unipotent_le_comap_bot_of_invariant :
    a.unipotent ≤ (⊥ : SubgroupFunctor K).comap f := by
  intro T g hg
  change g ≫ f.hom.hom ∈ (⊥ : Subgroup (T ⟶ K.X))
  exact Subgroup.mem_bot.mpr (a.comp_eq_one_of_mem_unipotent_of_invariant f hf hg)

/-- The image of the identity-limit subgroup functor under an invariant homomorphism is trivial. -/
theorem unipotent_map_eq_bot_of_invariant : a.unipotent.map f = ⊥ := by
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro g
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact Subgroup.mem_bot.mpr (a.comp_eq_one_of_mem_unipotent_of_invariant f hf hx)
  · intro hg
    rw [SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hg
    subst g
    exact one_mem _

end InvariantHom

end Langlands.GroupScheme.AutomorphicAction
