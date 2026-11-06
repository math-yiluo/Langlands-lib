import Langlands.GroupScheme.Rational.QuasiSplitInnerForm

/-! # Natural inner discrepancy cocycles from faithful actions -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace AutomorphicAction

variable {S : Scheme.{u}} {A G : GroupScheme S}

/-- Equality of acting points is detected by their actions after every refinement. -/
def IsFaithful (a : AutomorphicAction A G) : Prop :=
  ∀ {T : Over S} (x y : T ⟶ A.X),
    (∀ {W : Over S} (t : W ⟶ T) (g : W ⟶ G.X),
      a.act (t ≫ x) g = a.act (t ≫ y) g) → x = y

/-- Triviality of the all-refinement kernel implies faithfulness. -/
theorem isFaithful_of_kernel (a : AutomorphicAction A G)
    (h : ∀ {T : Over S} (x : T ⟶ A.X),
      (∀ {W : Over S} (t : W ⟶ T) (g : W ⟶ G.X), a.act (t ≫ x) g = g) → x = 1) :
    a.IsFaithful := by
  intro T x y hxy
  apply mul_inv_eq_one.mp
  apply h (x * y⁻¹)
  intro W t g
  rw [MonObj.comp_mul, GrpObj.comp_inv, a.act_mul_left,
    hxy t (a.act (t ≫ y)⁻¹ g), a.act_act_inv]

end AutomorphicAction

namespace IsAdjointQuotient

variable {K : Type u} [Field K]
  {G A : GroupScheme (Spec (CommRingCat.of K))}
  {q : G ⟶ A} (hq : IsAdjointQuotient q)

/-- The actual adjoint action has trivial kernel on all relative tests. -/
theorem innerAction_kernel {T : Over (Spec (CommRingCat.of K))} (x : T ⟶ A.X)
    (hx : ∀ {W : Over (Spec (CommRingCat.of K))} (t : W ⟶ T) (g : W ⟶ G.X),
      hq.innerAction.act (t ≫ x) g = g) : x = 1 := by
  let := hq.flat
  let := hq.surjective
  let := hq.isConnectedReductive.isAffineHom
  let := hq.isAdjoint.isSemisimple.isConnectedReductive.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : IsAffine A.X.left := isAffine_of_isAffineHom A.X.hom
  apply AutomorphicAction.hom_ext_of_local_quotient_lift q x x 1
  intro V b g hb
  rw [MonObj.comp_one, hb]
  apply (hq.mem_center_iff_comp_eq_one V g).mp
  intro W t y
  have h := hx (t ≫ b) y
  rw [Category.assoc, hb, ← Category.assoc, hq.innerAction_act_lift] at h
  exact mul_inv_eq_iff_eq_mul.mp h

/-- Adjoint points acting identically after every refinement are equal. -/
theorem innerAction_isFaithful : hq.innerAction.IsFaithful :=
  hq.innerAction.isFaithful_of_kernel (fun x hx => hq.innerAction_kernel x hx)

end IsAdjointQuotient

namespace LocalGroupIso

variable {S : Scheme.{u}} {G H A : GroupScheme S} {U : Over S}
  (e : LocalGroupIso G H U) (a : AutomorphicAction A G)

/-- A point represents the discrepancy if its pullback gives the discrepancy
on every refinement of the test scheme. -/
def RepresentsDiscrepancy {T : Over S} (b c : T ⟶ U) (x : T ⟶ A.X) : Prop :=
  ∀ {W : Over S} (t : W ⟶ T) (g : W ⟶ G.X),
    e.toFun (t ≫ b) (a.act (t ≫ x) g) = e.toFun (t ≫ c) g

/-- Every pair of cover points has an inner discrepancy on all refinements. -/
def HasInnerDiscrepancy : Prop :=
  ∀ {T : Over S} (b c : T ⟶ U), ∃ x : T ⟶ A.X, e.RepresentsDiscrepancy a b c x

/-- Pulling back a representing point pulls back its discrepancy. -/
theorem RepresentsDiscrepancy.comp {T W : Over S} {b c : T ⟶ U} {x : T ⟶ A.X}
    (hx : e.RepresentsDiscrepancy a b c x) (t : W ⟶ T) :
    e.RepresentsDiscrepancy a (t ≫ b) (t ≫ c) (t ≫ x) := by
  intro V s g
  simpa only [← Category.assoc] using hx (s ≫ t) g

/-- Faithfulness makes the point representing a discrepancy unique. -/
theorem RepresentsDiscrepancy.unique (ha : a.IsFaithful)
    {T : Over S} {b c : T ⟶ U} {x y : T ⟶ A.X}
    (hx : e.RepresentsDiscrepancy a b c x) (hy : e.RepresentsDiscrepancy a b c y) : x = y := by
  apply ha x y
  intro W t g
  apply (e.toFun (t ≫ b)).injective
  exact (hx t g).trans (hy t g).symm

/-- Composition of discrepancies is multiplication in the acting group. -/
theorem RepresentsDiscrepancy.mul {T : Over S} {b c d : T ⟶ U} {x y : T ⟶ A.X}
    (hx : e.RepresentsDiscrepancy a b c x) (hy : e.RepresentsDiscrepancy a c d y) :
    e.RepresentsDiscrepancy a b d (x * y) := by
  intro W t g
  rw [MonObj.comp_mul, a.act_mul_left, hx t, hy t]

variable (ha : a.IsFaithful) (he : e.HasInnerDiscrepancy a)

/-- The cocycle is constructed from innerness; neither naturality nor the cocycle
identity is an input. -/
def innerCocycle : Cocycle A U where
  toFun b c := (he b c).choose
  naturality t b c :=
    RepresentsDiscrepancy.unique e a ha
      (he (t ≫ b) (t ≫ c)).choose_spec
      (RepresentsDiscrepancy.comp e a (he b c).choose_spec t)
  cocycle b c d :=
    RepresentsDiscrepancy.unique e a ha (he b d).choose_spec
      (RepresentsDiscrepancy.mul e a (he b c).choose_spec (he c d).choose_spec)

/-- The constructed cocycle has the required discrepancy on each original test. -/
theorem innerCocycle_hasDiscrepancy : e.HasDiscrepancy a (e.innerCocycle a ha he) := by
  intro T b c g
  simpa only [innerCocycle, Category.id_comp] using (he b c).choose_spec (𝟙 T) g

/-- The constructed cocycle is uniquely determined by its discrepancy equation. -/
theorem innerCocycle_unique (ξ : Cocycle A U) (hξ : e.HasDiscrepancy a ξ) :
    ξ = e.innerCocycle a ha he := by
  cases ξ with
  | mk f hf hc =>
    have h : @f = @(e.innerCocycle a ha he).toFun := by
      funext T b c
      apply RepresentsDiscrepancy.unique e a ha
      · intro W t g
        rw [← hf]
        exact hξ (t ≫ b) (t ≫ c) g
      · exact (he b c).choose_spec
    cases h
    rfl

end LocalGroupIso

namespace QuasiSplitInnerForm

variable {K : Type u} [Field K]
  {G H A : GroupScheme (Spec (CommRingCat.of K))}

/-- Assemble the finite-Galois presentation from structural data and local innerness,
constructing the natural adjoint discrepancy cocycle. -/
def ofInnerDiscrepancy (hH : IsQuasiSplit H) (q : H ⟶ A) (hq : IsAdjointQuotient q)
    (hA : IsQuasiSplit A) (L : Type u) [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    (e : LocalGroupIso H G (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap K L)))))
    (he : e.HasInnerDiscrepancy hq.innerAction) : QuasiSplitInnerForm G where
  model := H
  isQuasiSplit := hH
  adjoint := A
  quotient := q
  isAdjointQuotient := hq
  isQuasiSplit_adjoint := hA
  carrier := L
  localIso := e
  cocycle := e.innerCocycle hq.innerAction hq.innerAction_isFaithful he
  hasDiscrepancy := e.innerCocycle_hasDiscrepancy hq.innerAction hq.innerAction_isFaithful he

end QuasiSplitInnerForm

end Langlands.GroupScheme
