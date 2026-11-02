import Langlands.GroupScheme.NormalizedSubgroup
import Langlands.GroupScheme.Rational.TorusCentralizer

/-! # Automorphic group-scheme actions and all-test fixed subgroup functors -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S : Scheme.{u}}

/-- An action by group automorphisms, induced on all tests by one scheme morphism.
The three intrinsic laws are tested on every scheme over the base. -/
structure AutomorphicAction (H G : GroupScheme S) where
  hom : H.X ⊗ G.X ⟶ G.X
  one_left : ∀ {T : Over S} (g : T ⟶ G.X), lift (1 : T ⟶ H.X) g ≫ hom = g
  mul_left : ∀ {T : Over S} (h h' : T ⟶ H.X) (g : T ⟶ G.X),
    lift (h * h') g ≫ hom = lift h (lift h' g ≫ hom) ≫ hom
  mul_right : ∀ {T : Over S} (h : T ⟶ H.X) (g g' : T ⟶ G.X),
    lift h (g * g') ≫ hom = (lift h g ≫ hom) * (lift h g' ≫ hom)

namespace AutomorphicAction

variable {H G K : GroupScheme S} (a : AutomorphicAction H G)

/-- The action on points is induced by the actual action morphism. -/
def act {T : Over S} (h : T ⟶ H.X) (g : T ⟶ G.X) : T ⟶ G.X :=
  lift h g ≫ a.hom

theorem act_eq {T : Over S} (h : T ⟶ H.X) (g : T ⟶ G.X) :
    a.act h g = lift h g ≫ a.hom := rfl

@[simp] theorem act_one_left {T : Over S} (g : T ⟶ G.X) : a.act 1 g = g :=
  a.one_left g

theorem act_mul_left {T : Over S} (h h' : T ⟶ H.X) (g : T ⟶ G.X) :
    a.act (h * h') g = a.act h (a.act h' g) :=
  a.mul_left h h' g

theorem act_mul_right {T : Over S} (h : T ⟶ H.X) (g g' : T ⟶ G.X) :
    a.act h (g * g') = a.act h g * a.act h g' :=
  a.mul_right h g g'

/-- The point actions are natural under every test morphism. -/
theorem naturality {T T' : Over S} (b : T' ⟶ T) (h : T ⟶ H.X) (g : T ⟶ G.X) :
    b ≫ a.act h g = a.act (b ≫ h) (b ≫ g) := by
  unfold act
  rw [← Category.assoc, comp_lift]

/-- Each point of the acting group induces a group automorphism, with inverse
given by the inverse point. -/
def pointAut (T : Over S) (h : T ⟶ H.X) : MulAut (T ⟶ G.X) where
  toFun := a.act h
  invFun := a.act h⁻¹
  left_inv g := by
    rw [← a.act_mul_left, inv_mul_cancel, a.act_one_left]
  right_inv g := by
    rw [← a.act_mul_left, mul_inv_cancel, a.act_one_left]
  map_mul' := a.act_mul_right h

/-- The homomorphism from acting points to automorphisms of the target points. -/
def pointsAction (T : Over S) : (T ⟶ H.X) →* MulAut (T ⟶ G.X) where
  toFun := a.pointAut T
  map_one' := MulEquiv.ext a.act_one_left
  map_mul' h h' := MulEquiv.ext (a.act_mul_left h h')

@[simp] theorem pointsAction_apply (T : Over S) (h : T ⟶ H.X) (g : T ⟶ G.X) :
    a.pointsAction T h g = a.act h g := rfl

@[simp] theorem act_one {T : Over S} (h : T ⟶ H.X) : a.act h 1 = 1 :=
  (a.pointAut T h).map_one

@[simp] theorem act_inv {T : Over S} (h : T ⟶ H.X) (g : T ⟶ G.X) :
    a.act h g⁻¹ = (a.act h g)⁻¹ :=
  (a.pointAut T h).map_inv g

@[simp] theorem act_inv_act {T : Over S} (h : T ⟶ H.X) (g : T ⟶ G.X) :
    a.act h⁻¹ (a.act h g) = g :=
  (a.pointAut T h).left_inv g

@[simp] theorem act_act_inv {T : Over S} (h : T ⟶ H.X) (g : T ⟶ G.X) :
    a.act h (a.act h⁻¹ g) = g :=
  (a.pointAut T h).right_inv g

/-- Restrict an action along an actual homomorphism of group schemes. -/
def restrict (f : K ⟶ H) : AutomorphicAction K G where
  hom := (f.hom.hom ▷ G.X) ≫ a.hom
  one_left g := by
    simpa only [Category.assoc, lift_whiskerRight_assoc, MonObj.one_comp] using
      a.one_left g
  mul_left h h' g := by
    simpa only [Category.assoc, lift_whiskerRight_assoc, MonObj.mul_comp] using
      a.mul_left (h ≫ f.hom.hom) (h' ≫ f.hom.hom) g
  mul_right h g g' := by
    simpa only [Category.assoc, lift_whiskerRight_assoc] using
      a.mul_right (h ≫ f.hom.hom) g g'

@[simp] theorem restrict_act (f : K ⟶ H) {T : Over S} (k : T ⟶ K.X)
    (g : T ⟶ G.X) : (a.restrict f).act k g = a.act (k ≫ f.hom.hom) g := by
  simp only [act, restrict, lift_whiskerRight_assoc]

/-- Invariance includes every refinement and every acting point on that refinement. -/
def IsFixed {T : Over S} (g : T ⟶ G.X) : Prop :=
  ∀ (T' : Over S) (b : T' ⟶ T) (h : T' ⟶ H.X), a.act h (b ≫ g) = b ≫ g

/-- All-refinement invariance is equivalent to invariance at the universal acting point. -/
theorem isFixed_iff_universal {T : Over S} (g : T ⟶ G.X) :
    a.IsFixed g ↔
      a.act (snd T H.X) (fst T H.X ≫ g) = fst T H.X ≫ g := by
  constructor
  · intro hg
    exact hg _ (fst T H.X) (snd T H.X)
  · intro hg T' b h
    have e := congrArg (fun f => lift b h ≫ f) hg
    simpa only [naturality, lift_snd, lift_fst_assoc] using e

/-- The fixed subgroup functor on all schemes over the base. -/
def fixedSubgroup : SubgroupFunctor G where
  carrier T :=
    { carrier := {g | a.IsFixed g}
      one_mem' := by
        intro T' b h
        rw [MonObj.comp_one, a.act_one]
      mul_mem' := by
        intro g g' hg hg' T' b h
        rw [MonObj.comp_mul, a.act_mul_right, hg T' b h, hg' T' b h]
      inv_mem' := by
        intro g hg T' b h
        rw [GrpObj.comp_inv, a.act_inv, hg T' b h] }
  comp_mem b g hg T' c h := by
    rw [← Category.assoc]
    exact hg T' (c ≫ b) h

theorem mem_fixedSubgroup {T : Over S} {g : T ⟶ G.X} :
    g ∈ a.fixedSubgroup.carrier T ↔ a.IsFixed g := Iff.rfl

theorem mem_fixedSubgroup_iff_universal {T : Over S} {g : T ⟶ G.X} :
    g ∈ a.fixedSubgroup.carrier T ↔
      a.act (snd T H.X) (fst T H.X ≫ g) = fst T H.X ≫ g :=
  a.isFixed_iff_universal g

/-- Bundle the existing normalized conjugation morphism and its published action laws. -/
def ofNormalizedConjugation {A : GroupScheme S} (iG : G ⟶ A) (iH : H ⟶ A)
    (hn : (SubgroupFunctor.range iG).IsNormalizedBy (SubgroupFunctor.range iH))
    [Mono iG.hom.hom] : AutomorphicAction H G where
  hom := SubgroupFunctor.normalizedConjugation iG iH hn
  one_left := SubgroupFunctor.normalizedConjugation_one_left iG iH hn
  mul_left := SubgroupFunctor.normalizedConjugation_mul_left iG iH hn
  mul_right := SubgroupFunctor.normalizedConjugation_mul_right iG iH hn

theorem ofNormalizedConjugation_pointsAction {A : GroupScheme S}
    (iG : G ⟶ A) (iH : H ⟶ A)
    (hn : (SubgroupFunctor.range iG).IsNormalizedBy (SubgroupFunctor.range iH))
    [Mono iG.hom.hom] (T : Over S) :
    (ofNormalizedConjugation iG iH hn).pointsAction T =
      SubgroupFunctor.normalizedConjAction iG iH hn T := by
  ext h g
  rfl

/-- The whole ambient group is normalized by the image of every homomorphism. -/
theorem range_id_isNormalizedBy (i : H ⟶ G) :
    (SubgroupFunctor.range (𝟙 G)).IsNormalizedBy (SubgroupFunctor.range i) := by
  intro T g x _ _
  exact SubgroupFunctor.mem_range.2 ⟨g * x * g⁻¹, by simp⟩

/-- Conjugation along any homomorphism, reusing the normalized-conjugation construction. -/
def conjugation (i : H ⟶ G) : AutomorphicAction H G :=
  ofNormalizedConjugation (𝟙 G) i (range_id_isNormalizedBy i)

@[simp] theorem conjugation_act (i : H ⟶ G) {T : Over S}
    (h : T ⟶ H.X) (g : T ⟶ G.X) :
    (conjugation i).act h g = (h ≫ i.hom.hom) * g * (h ≫ i.hom.hom)⁻¹ := by
  simpa only [act, conjugation, ofNormalizedConjugation, Grp.id_hom_hom, Category.comp_id]
    using SubgroupFunctor.lift_comp_normalizedConjugation_comp
      (𝟙 G) i (range_id_isNormalizedBy i) h g

/-- For every commutative acting group scheme the fixed functor is the existing
all-test centralizer. No torus or smoothness hypothesis is needed. -/
theorem conjugation_fixedSubgroup_eq_torusCentralizer {C : CommGroupScheme S}
    (i : C.toGrp ⟶ G) : (conjugation i).fixedSubgroup = torusCentralizer i := by
  apply SubgroupFunctor.ext
  intro T
  ext g
  rw [mem_fixedSubgroup, mem_torusCentralizer]
  constructor
  · intro hg T' b h
    have e := hg T' b h
    rw [conjugation_act] at e
    exact ((mul_inv_eq_iff_eq_mul).mp e).symm
  · intro hg T' b h
    rw [conjugation_act, (hg T' b h).symm.eq, mul_inv_cancel_right]

end AutomorphicAction

end Langlands.GroupScheme
