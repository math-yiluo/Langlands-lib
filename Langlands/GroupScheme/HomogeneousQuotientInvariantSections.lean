import Langlands.GroupScheme.HomogeneousQuotientFromEmbedding
import Langlands.AlgebraicGeometry.Modules.UnitCocycleDescent.FunctionDescent

/-! # Global sections of a supplied homogeneous quotient -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.HomogeneousQuotientFromEmbedding

variable {S : Scheme.{u}} {G H : GroupScheme S} (i : H ⟶ G)

/-- A global section is invariant under right multiplication by the embedded subgroup
on every relative scheme test. -/
def IsRightInvariant (s : Γ(G.X.left, ⊤)) : Prop :=
  ∀ (T : Over S) (g : T ⟶ G.X) (h : T ⟶ H.X),
    (g * (h ≫ i.hom.hom)).left.appTop s = g.left.appTop s

/-- Right-invariant global functions form a subring of the actual ambient coordinate ring. -/
def rightInvariantSubring : Subring Γ(G.X.left, ⊤) where
  carrier := {s | IsRightInvariant i s}
  zero_mem' := by intro T g h; simp
  one_mem' := by intro T g h; simp
  add_mem' := by
    intro s t hs ht T g h
    simp only [map_add, hs T g h, ht T g h]
  mul_mem' := by
    intro s t hs ht T g h
    simp only [map_mul, hs T g h, ht T g h]
  neg_mem' := by
    intro s hs T g h
    simp only [map_neg, hs T g h]

/-- Right invariance is the equality of the two pullbacks to the actual coset-arrow scheme. -/
theorem isRightInvariant_iff_cosetRelation (s : Γ(G.X.left, ⊤)) :
    IsRightInvariant i s ↔
      (HomogeneousCosetRelation.target i).left.appTop s =
        (HomogeneousCosetRelation.source i).left.appTop s := by
  constructor
  · intro hs
    exact hs (HomogeneousCosetRelation.arrows i)
      (CategoryTheory.CartesianMonoidalCategory.fst G.X H.X)
      (CategoryTheory.CartesianMonoidalCategory.snd G.X H.X)
  · intro hs T g h
    have he := congrArg
      ((CategoryTheory.CartesianMonoidalCategory.lift g h).left.appTop) hs
    change ((CategoryTheory.CartesianMonoidalCategory.lift g h).left ≫
        (HomogeneousCosetRelation.target i).left).appTop s =
      ((CategoryTheory.CartesianMonoidalCategory.lift g h).left ≫
        (HomogeneousCosetRelation.source i).left).appTop s at he
    simpa only [← Over.comp_left, HomogeneousCosetRelation.lift_target,
      HomogeneousCosetRelation.lift_source] using he

namespace HomogeneousQuotient

variable {i} (Q : HomogeneousQuotient i)

/-- Right multiplication by a subgroup point leaves the supplied projection unchanged. -/
theorem right_mul_projection (T : Over S) (g : T ⟶ G.X) (h : T ⟶ H.X) :
    (g * (h ≫ i.hom.hom)) ≫ Q.projection = g ≫ Q.projection := by
  apply Eq.symm
  apply (Q.fibers T g (g * (h ≫ i.hom.hom))).mpr
  simp only [inv_mul_cancel_left]
  exact ⟨h, rfl⟩

/-- Every global function on the supplied quotient pulls back to a right-invariant one. -/
theorem isRightInvariant_appTop (s : Γ(Q.scheme.left, ⊤)) :
    IsRightInvariant i (Q.projection.left.appTop s) := by
  intro T g h
  change ((g * (h ≫ i.hom.hom)).left ≫ Q.projection.left).appTop s =
    (g.left ≫ Q.projection.left).appTop s
  rw [← Over.comp_left, ← Over.comp_left, Q.right_mul_projection]

/-- Pullback of functions, with codomain restricted to the right-invariant subring. -/
def pullbackInvariantSections :
    Γ(Q.scheme.left, ⊤) →+* rightInvariantSubring i :=
  Q.projection.left.appTop.hom.codRestrict (rightInvariantSubring i)
    Q.isRightInvariant_appTop

local instance : Smooth Q.projection.left := Q.smooth_projection
local instance : Surjective Q.projection.left := Q.surjective_projection
local instance : QuasiCompact Q.projection.left := Q.quasiCompact_projection

/-- A right-invariant section agrees along every pair of relative points in one quotient fibre. -/
theorem IsRightInvariant.eq_of_projection_eq {s : Γ(G.X.left, ⊤)}
    (hs : IsRightInvariant i s)
    {T : Over S} (g h : T ⟶ G.X) (he : g ≫ Q.projection = h ≫ Q.projection) :
    g.left.appTop s = h.left.appTop s := by
  obtain ⟨a, ha⟩ := (Q.fibers T g h).mp he
  change T ⟶ H.X at a
  change a ≫ i.hom.hom = g⁻¹ * h at ha
  have hga : g * (a ≫ i.hom.hom) = h := by
    rw [ha]
    exact mul_inv_cancel_left g h
  exact (hs T g a).symm.trans (congrArg (fun x => x.left.appTop s) hga)

/-- Every right-invariant global function descends to the same supplied quotient. -/
theorem exists_appTop_eq_of_isRightInvariant {s : Γ(G.X.left, ⊤)}
    (hs : IsRightInvariant i s) :
    ∃ t : Γ(Q.scheme.left, ⊤), Q.projection.left.appTop t = s := by
  apply Langlands.Scheme.UnitCocycleDescent.exists_appTop_eq_of_effectiveEpi
  intro U a b hab
  have hb : b ≫ G.X.hom = a ≫ G.X.hom := by
    rw [← Over.w Q.projection, ← Category.assoc, ← hab, Category.assoc]
  let a₀ : Over.mk (a ≫ G.X.hom) ⟶ G.X := Over.homMk a rfl
  let b₀ : Over.mk (a ≫ G.X.hom) ⟶ G.X := Over.homMk b hb
  exact IsRightInvariant.eq_of_projection_eq Q hs a₀ b₀ (Over.OverMorphism.ext hab)

/-- Exact all-test invariant descent identifies the invariant subring with quotient sections. -/
theorem pullbackInvariantSections_bijective :
    Function.Bijective Q.pullbackInvariantSections := by
  constructor
  · intro s t hst
    apply Langlands.Scheme.UnitCocycleDescent.appTop_injective_of_epi Q.projection.left
    exact congrArg Subtype.val hst
  · intro s
    obtain ⟨t, ht⟩ := Q.exists_appTop_eq_of_isRightInvariant s.property
    exact ⟨t, Subtype.ext ht⟩

/-- The actual quotient section ring is canonically the right-invariant ambient section ring. -/
def invariantSectionsEquiv :
    Γ(Q.scheme.left, ⊤) ≃+* rightInvariantSubring i :=
  RingEquiv.ofBijective Q.pullbackInvariantSections Q.pullbackInvariantSections_bijective

@[simp]
theorem invariantSectionsEquiv_apply (s : Γ(Q.scheme.left, ⊤)) :
    (Q.invariantSectionsEquiv s : Γ(G.X.left, ⊤)) = Q.projection.left.appTop s := rfl

/-- The descended section is the inverse of the canonical invariant-section equivalence. -/
@[simp]
theorem appTop_invariantSectionsEquiv_symm (s : rightInvariantSubring i) :
    Q.projection.left.appTop (Q.invariantSectionsEquiv.symm s) = s := by
  exact congrArg Subtype.val (Q.invariantSectionsEquiv.apply_symm_apply s)

end HomogeneousQuotient

end Langlands.GroupScheme.HomogeneousQuotientFromEmbedding
