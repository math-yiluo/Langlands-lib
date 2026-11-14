import Langlands.GroupScheme.Rational.InnerDiscrepancy
import Langlands.GroupScheme.FppfQuotientComparison

/-! # Faithfulness of supplied full-centre quotient actions over any base -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AutomorphicAction

variable {S : Scheme.{u}} {G A H : GroupScheme S}

/-- Flat surjective quotient maps suffice to check equality after local lifting;
no quasi-compactness is needed for this equality argument. -/
theorem hom_ext_of_flat_surjective_local_lift (q : G ⟶ A)
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    {T Y : Over S} (x : T ⟶ A.X) (f f' : T ⟶ Y)
    (he : ∀ (V : Over S) (b : V ⟶ T) (g : V ⟶ G.X),
      b ≫ x = g ≫ q.hom.hom → b ≫ f = b ≫ f') : f = f' := by
  let V : Over S := Over.mk (pullback.fst x.left q.hom.hom.left ≫ T.hom)
  let b : V ⟶ T := Over.homMk (pullback.fst x.left q.hom.hom.left) rfl
  let g : V ⟶ G.X := Over.homMk (pullback.snd x.left q.hom.hom.left) (by
    rw [← Over.w q.hom.hom, ← Category.assoc, ← pullback.condition,
      Category.assoc, Over.w x]
    rfl)
  have : Epi b.left := by
    change Epi (pullback.fst x.left q.hom.hom.left)
    exact Flat.epi_of_flat_of_surjective _
  have : Epi b := Over.epi_of_epi_left b
  apply (cancel_epi b).mp
  exact he V b g (Over.OverMorphism.ext pullback.condition)

/-- An action of any supplied full-centre fppf quotient which restricts to
conjugation has trivial all-refinement kernel over an arbitrary scheme base. -/
theorem kernel_eq_one_of_center_quotient (q : G ⟶ A)
    (hq : RelativeRoot.IsFppfQuotient (center G) q)
    (a : AutomorphicAction A G)
    (ha : a.restrict q = conjugation (𝟙 G))
    {T : Over S} (x : T ⟶ A.X)
    (hx : ∀ {W : Over S} (t : W ⟶ T) (g : W ⟶ G.X),
      a.act (t ≫ x) g = g) : x = 1 := by
  let := hq.1
  let := hq.2.1
  apply hom_ext_of_flat_surjective_local_lift q x x 1
  intro V b g hb
  rw [MonObj.comp_one, hb]
  apply (mem_range_kernelι_iff q g).mp
  rw [hq.2.2.2]
  intro W t y
  have h := hx (t ≫ b) y
  rw [Category.assoc, hb, ← Category.assoc, ← restrict_act, ha,
    conjugation_act, Grp.id_hom_hom, Category.comp_id] at h
  exact mul_inv_eq_iff_eq_mul.mp h

/-- The natural action of a supplied full-centre quotient is faithful, without
any reductivity, field or finiteness assumption. -/
theorem isFaithful_of_center_quotient (q : G ⟶ A)
    (hq : RelativeRoot.IsFppfQuotient (center G) q)
    (a : AutomorphicAction A G)
    (ha : a.restrict q = conjugation (𝟙 G)) : a.IsFaithful :=
  a.isFaithful_of_kernel (fun x hx =>
    kernel_eq_one_of_center_quotient q hq a ha x hx)

/-- Restricting a faithful action detects equality of acting homomorphisms. -/
theorem restrict_injective_of_isFaithful (a : AutomorphicAction A G)
    (ha : a.IsFaithful) {f g : H ⟶ A}
    (hfg : a.restrict f = a.restrict g) : f = g := by
  apply Grp.hom_ext
  apply ha f.hom.hom g.hom.hom
  intro W t x
  simpa only [restrict_act] using
    congrArg (fun b : AutomorphicAction H G => b.act t x) hfg

/-- The uniqueness part of innerness holds over every base before any
connectedness or reductivity hypotheses are used. -/
theorem restrict_injective_of_center_quotient (q : G ⟶ A)
    (hq : RelativeRoot.IsFppfQuotient (center G) q)
    (a : AutomorphicAction A G)
    (ha : a.restrict q = conjugation (𝟙 G)) {f g : H ⟶ A}
    (hfg : a.restrict f = a.restrict g) : f = g :=
  restrict_injective_of_isFaithful a (isFaithful_of_center_quotient q hq a ha) hfg

/-- The map sending a homomorphism into the full-centre quotient to its
induced action, bundled as an embedding. It parametrizes the inner actions
in its image; it does not assert that every action is inner. -/
def restrictEmbeddingOfCenterQuotient (q : G ⟶ A)
    (hq : RelativeRoot.IsFppfQuotient (center G) q)
    (a : AutomorphicAction A G)
    (ha : a.restrict q = conjugation (𝟙 G)) :
    (H ⟶ A) ↪ AutomorphicAction H G where
  toFun := a.restrict
  inj' := fun _ _ hfg => restrict_injective_of_center_quotient q hq a ha hfg

@[simp]
theorem restrictEmbeddingOfCenterQuotient_apply (q : G ⟶ A)
    (hq : RelativeRoot.IsFppfQuotient (center G) q)
    (a : AutomorphicAction A G)
    (ha : a.restrict q = conjugation (𝟙 G)) (f : H ⟶ A) :
    restrictEmbeddingOfCenterQuotient q hq a ha f = a.restrict f := rfl

end Langlands.GroupScheme.AutomorphicAction
