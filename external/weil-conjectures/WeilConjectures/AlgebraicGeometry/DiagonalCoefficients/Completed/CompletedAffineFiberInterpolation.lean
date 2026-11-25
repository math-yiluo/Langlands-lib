/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Completed.CompletedAffineCoefficientModel
public import WeilConjectures.AlgebraicGeometry.Morphisms.ProAffineEtale
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.Topology.Piecewise

/-! Finite interpolation by clopen stage tests.
(blueprint: lem-sfb-completed-affine-fiber-interpolation)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

/-- Scalar tests are natural functions on the representable on the slice; linearity
and descent are not part of this definition.
Source: the stage-test construction in `completedAffineFree_localDual_detect`.
(blueprint: lem-sfb-completed-affine-fiber-interpolation) -/
abbrev completedAffineScalarTest (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (U : X.ProEtᵒᵖ) (W : X.ProEt) :=
  (Over.forget W).op ⋙ uliftYoneda.{u + 1}.obj U.unop ⟶
    (SheafOfModules.unit
      ((Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l)).over W)).val.presheaf ⋙
        forget AddCommGrpCat.{u + 1}

open Limits

private def scalarTestOfSections (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (U : X.ProEtᵒᵖ) (W : X.ProEt)
    (b : ∀ V : Over W, (V.left ⟶ U.unop) →
      (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l)).obj.obj (op V.left))
    (hb : ∀ (V V' : Over W) (f : V' ⟶ V) (q : V.left ⟶ U.unop),
      (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l)).obj.map f.left.op
        (b V q) = b V' (f.left ≫ q)) : completedAffineScalarTest l X U W where
  app V := ↾fun q ↦ b V.unop q.down
  naturality := by
    intro V V' f
    ext q
    exact (hb V.unop V'.unop f.unop q.down).symm

private theorem eqLocus_isClopen {T Y X : Scheme.{u}} (p : Y ⟶ X)
    [Etale p] [IsSeparated p] (a b : T ⟶ Y) (h : a ≫ p = b ≫ p) :
    IsClopen (FormallyUnramified.eqLocus p a b h : Set T) := by
  exact ⟨(pullback.diagonal p).isClosedMap.isClosed_range.preimage
    (pullback.lift a b h).continuous,
    (FormallyUnramified.eqLocus p a b h).isOpen⟩

private theorem eqLocus_precomp {T T' Y X : Scheme.{u}} (p : Y ⟶ X)
    [Etale p] (a b : T ⟶ Y) (h : a ≫ p = b ≫ p) (f : T' ⟶ T)
    (h' : (f ≫ a) ≫ p = (f ≫ b) ≫ p) :
    FormallyUnramified.eqLocus p (f ≫ a) (f ≫ b) h' =
      f ⁻¹ᵁ FormallyUnramified.eqLocus p a b h := by
  unfold FormallyUnramified.eqLocus
  rw [← Scheme.Hom.comp_preimage]
  have he : pullback.lift (f ≫ a) (f ≫ b) h' = f ≫ pullback.lift a b h := by
    apply pullback.hom_ext <;> simp
  rw [he]

private theorem mem_eqLocus_iff {T Y X : Scheme.{u}} (p : Y ⟶ X)
    [Etale p] (a b : T ⟶ Y) (h : a ≫ p = b ≫ p) (x : T) :
    x ∈ FormallyUnramified.eqLocus p a b h ↔
      T.fromSpecResidueField x ≫ a = T.fromSpecResidueField x ≫ b := by
  let O := FormallyUnramified.eqLocus p a b h
  constructor
  · intro hx
    let c := T.fromSpecResidueField x
    have hr : Set.range c.base ⊆ Set.range O.ι.base := by
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι]
      simpa [c, Scheme.fromSpecResidueField_apply] using hx
    let f := IsOpenImmersion.lift O.ι c hr
    have hf : f ≫ O.ι = c := IsOpenImmersion.lift_fac _ _ _
    change c ≫ a = c ≫ b
    rw [← hf, Category.assoc, Category.assoc]
    exact congrArg (fun t ↦ f ≫ t) (FormallyUnramified.eqLocus_ι_comp_eq p a b h)
  · intro hx
    have he := FormallyUnramified.range_subset_eqLocus p a b h
      (T.fromSpecResidueField x) hx
    have hx' : x ∈ Set.range (T.fromSpecResidueField x).base := by
      rw [Scheme.range_fromSpecResidueField]
      exact Set.mem_singleton x
    exact he hx'

private noncomputable def clopenChar {T : Type u} [TopologicalSpace T]
    (S : Set T) (hS : IsClopen S) (l : ℕ) [Fact l.Prime] : C(T, ℤ_[l]) := by
  classical
  refine ⟨fun x ↦ if x ∈ S then 1 else 0, ?_⟩
  exact continuous_const.if (by simp [hS.frontier_eq]) continuous_const

open Classical in
private theorem clopenChar_apply {T : Type u} [TopologicalSpace T]
    (S : Set T) (hS : IsClopen S) (l : ℕ) [Fact l.Prime] (x : T) :
    clopenChar S hS l x = if x ∈ S then 1 else 0 := by
  classical
  rfl

private theorem stage_comm {X : Scheme.{u}} {U W : X.ProEt}
    {D : Scheme.{u}} (t : D ⟶ X) (s : U.left ⟶ D) (hs : s ≫ t = U.hom)
    (qi : W ⟶ U) (V : Over W) (q : V.left ⟶ U) :
    (q.left ≫ s) ≫ t = (V.hom.left ≫ qi.left ≫ s) ≫ t := by
  have hq : q.left ≫ U.hom = V.left.hom := q.w
  have hqi : qi.left ≫ U.hom = W.hom := qi.w
  have hV : V.hom.left ≫ W.hom = V.left.hom := V.hom.w
  simp only [Category.assoc, hs, hq, hqi, hV]

private noncomputable def stageSection (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (M : CompletedAffineCoefficientModel l X) (U W : X.ProEt)
    (D : Scheme.{u}) (t : D ⟶ X) [Etale t] [IsSeparated t]
    (s : U.left ⟶ D) (hs : s ≫ t = U.hom) (qi : W ⟶ U)
    (V : Over W) (q : V.left ⟶ U) :
    (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l)).obj.obj (op V.left) :=
  (M.equiv V.left).symm (clopenChar _
    (eqLocus_isClopen t (q.left ≫ s) (V.hom.left ≫ qi.left ≫ s)
      (stage_comm t s hs qi V q)) l)

private theorem stageSection_naturality (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (M : CompletedAffineCoefficientModel l X) (U W : X.ProEt)
    (D : Scheme.{u}) (t : D ⟶ X) [Etale t] [IsSeparated t]
    (s : U.left ⟶ D) (hs : s ≫ t = U.hom) (qi : W ⟶ U)
    (V V' : Over W) (f : V' ⟶ V) (q : V.left ⟶ U) :
    (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l)).obj.map f.left.op
      (stageSection l X M U W D t s hs qi V q) =
        stageSection l X M U W D t s hs qi V' (f.left ≫ q) := by
  classical
  apply (M.equiv V'.left).injective
  rw [M.naturality]
  simp only [stageSection, RingEquiv.apply_symm_apply]
  apply ContinuousMap.ext
  intro x
  simp only [ContinuousMap.comp_apply, clopenChar_apply]
  have hf : V'.hom.left = f.left.left ≫ V.hom.left := by
    exact congrArg (fun g ↦ g.left) (Over.w f).symm
  change (if f.left.left x ∈ FormallyUnramified.eqLocus t (q.left ≫ s)
    (V.hom.left ≫ qi.left ≫ s) _ then 1 else 0) =
      if x ∈ FormallyUnramified.eqLocus t ((f.left.left ≫ q.left) ≫ s)
        (V'.hom.left ≫ qi.left ≫ s) _ then 1 else 0
  simp only [hf, Category.assoc]
  rw [eqLocus_precomp t (q.left ≫ s) (V.hom.left ≫ qi.left ≫ s)
    (stage_comm t s hs qi V q) f.left.left]
  rfl

open Classical in
private theorem stageSection_eval (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (M : CompletedAffineCoefficientModel l X) (U W : X.ProEt)
    (D : Scheme.{u}) (t : D ⟶ X) [Etale t] [IsSeparated t]
    (s : U.left ⟶ D) (hs : s ≫ t = U.hom) (qi q : W ⟶ U) (x : W.left) :
    M.equiv W (stageSection l X M U W D t s hs qi (Over.mk (𝟙 W)) q) x =
      if W.left.fromSpecResidueField x ≫ q.left ≫ s =
        W.left.fromSpecResidueField x ≫ qi.left ≫ s then 1 else 0 := by
  unfold stageSection
  change (M.equiv W ((M.equiv W).symm _)) x = _
  rw [RingEquiv.apply_symm_apply, clopenChar_apply]
  apply if_congr _ rfl rfl
  change x ∈ FormallyUnramified.eqLocus t (q.left ≫ s)
    ((Over.mk (𝟙 W)).hom.left ≫ qi.left ≫ s) _ ↔ _
  rw [mem_eqLocus_iff]
  change W.left.fromSpecResidueField x ≫ q.left ≫ s =
      W.left.fromSpecResidueField x ≫ (𝟙 W.left) ≫ qi.left ≫ s ↔ _
  simp only [Category.id_comp]

open Classical in
/-- A finite set of arrows can be interpolated at one residue-field point by a natural
scalar test. This asserts only values on generators, not detection in a module or sheaf.
Source: `CompletedAffineFreeLocalDual.lean`, the clopen stage-graph part of the
finite-support proof of `completedAffineFree_localDual_detect`.
(blueprint: lem-sfb-completed-affine-fiber-interpolation)

Proof: choose an affine etale presentation of U. At a point x, arrows whose residue-field
maps differ are distinguished at some stage, by the limit universal property. For each
of the finitely many arrows different from the selected one choose such a stage.
The equality locus of two maps to that stage over X is clopen: the stage is etale
and separated over X (its source is absolutely affine). Its characteristic function
is continuous with values 0 and 1. On V over W compare an arbitrary arrow V to U
with the selected arrow restricted from W. Transport this characteristic function
through the coefficient model. Pullback of equality loci and naturality of the model
make it a natural scalar test. Multiply the finitely many tests. At x it is one
on the selected fiber class and zero on every other class. An empty product is
one; if there is no selected index the assertion is vacuous. -/
theorem completedAffine_fiber_interpolation (l : ℕ) [Fact l.Prime]
    (X : Scheme.{u}) (M : CompletedAffineCoefficientModel l X)
    (U : X.ProEtᵒᵖ) (hU : proAffineEtale U.unop.hom) (W : X.ProEt)
    {ι : Type (u + 1)} [Finite ι]
    (q : ι → (uliftYoneda.{u + 1}.obj U.unop).obj (op W)) (x : W.left) (i : ι) :
    ∃ β : completedAffineScalarTest l X U W, ∀ j : ι,
      M.equiv W (β.app (op (Over.mk (𝟙 W))) (q j)) x =
        if W.left.fromSpecResidueField x ≫ (q j).down.left =
            W.left.fromSpecResidueField x ≫ (q i).down.left then 1 else 0 := by
  classical
  let := Fintype.ofFinite ι
  obtain ⟨J, _, _, D, t, s, hs, hts⟩ := hU
  have hAff (k : J) : IsAffine (D.obj k) :=
    MorphismProperty.ofObjectProperty_top_right_iff.mp (hts k).1.2
  have (k : J) : Etale (t.app k) := (hts k).1.1
  have (k : J) : IsSeparated (t.app k) := by
    have := hAff k
    infer_instance
  have hstage (j : ι) : ∃ k : J,
      (W.left.fromSpecResidueField x ≫ (q j).down.left ≫ s.app k =
        W.left.fromSpecResidueField x ≫ (q i).down.left ≫ s.app k ↔
          W.left.fromSpecResidueField x ≫ (q j).down.left =
            W.left.fromSpecResidueField x ≫ (q i).down.left) := by
    by_cases he : W.left.fromSpecResidueField x ≫ (q j).down.left =
        W.left.fromSpecResidueField x ≫ (q i).down.left
    · obtain ⟨k⟩ := IsCofiltered.nonempty (C := J)
      refine ⟨k, ?_⟩
      simp only [← Category.assoc, he, iff_self]
    · have hn : ∃ k : J,
          W.left.fromSpecResidueField x ≫ (q j).down.left ≫ s.app k ≠
            W.left.fromSpecResidueField x ≫ (q i).down.left ≫ s.app k := by
        by_contra hn
        apply he
        apply hs.hom_ext
        intro k
        simpa only [Category.assoc] using (not_exists_not.mp hn k)
      obtain ⟨k, hk⟩ := hn
      exact ⟨k, iff_of_false hk he⟩
  choose k hk using hstage
  let b (V : Over W) (g : V.left ⟶ U.unop) :=
    (M.equiv V.left).symm (∏ j : ι, M.equiv V.left
      (stageSection l X M U.unop W (D.obj (k j)) (t.app (k j))
        (s.app (k j)) (hts (k j)).2 (q i).down V g))
  have hb (V V' : Over W) (f : V' ⟶ V) (g : V.left ⟶ U.unop) :
      (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l)).obj.map f.left.op
        (b V g) = b V' (f.left ≫ g) := by
    apply (M.equiv V'.left).injective
    rw [M.naturality]
    simp only [b, RingEquiv.apply_symm_apply]
    apply ContinuousMap.ext
    intro y
    simp only [ContinuousMap.comp_apply, ContinuousMap.prod_apply]
    apply Finset.prod_congr rfl
    intro j _
    have he := M.naturality f.left
      (stageSection l X M U.unop W (D.obj (k j)) (t.app (k j))
        (s.app (k j)) (hts (k j)).2 (q i).down V g)
    rw [stageSection_naturality] at he
    exact (congrArg (fun z ↦ z y) he).symm
  refine ⟨scalarTestOfSections l X U W b hb, ?_⟩
  intro j
  change M.equiv W (b (Over.mk (𝟙 W)) (q j).down) x = _
  dsimp only [b, Over.mk_left]
  rw [RingEquiv.apply_symm_apply]
  simp only [ContinuousMap.prod_apply, stageSection_eval]
  by_cases hj : W.left.fromSpecResidueField x ≫ (q j).down.left =
      W.left.fromSpecResidueField x ≫ (q i).down.left
  · rw [ite_eq_left hj]
    apply Finset.prod_eq_one
    intro a _
    simp only [← Category.assoc, hj, ite_true]
  · rw [ite_eq_right hj]
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    rw [ite_eq_right (fun h ↦ hj ((hk j).mp h))]

end AlgebraicGeometry.ProEtale.DiagonalCoefficients
