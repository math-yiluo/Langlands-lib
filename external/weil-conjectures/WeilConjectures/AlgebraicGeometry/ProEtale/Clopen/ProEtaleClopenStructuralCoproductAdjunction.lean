/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ClopenData.ProEtaleClopenTotalTensorKFlatDetectionData
import Mathlib.CategoryTheory.Adjunction.Limits

/-! Split coproduct and adjunction data for finite clopen restriction.

## References

* Stacks Project, Tag 0GMW
* Tag 0FPQ
-/

@[expose] public noncomputable section
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
universe t u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open WeilConjectures
namespace AlgebraicGeometry.Scheme.ProEt

/-- A fully faithful family of restrictions identifies maps to a zero insertion
with maps in its sole nonzero coordinate. -/
private def adjunctionOfZeroInsertion
    {C : Type*} [Category C] {J : Type*} {D : J → Type*}
    [∀ k, Category (D k)] (r : C ⥤ ∀ k, D k) [r.Full] [r.Faithful]
    (i : J) (e : D i ⥤ C) (c : e ⋙ r ⋙ Pi.eval D i ≅ 𝟭 _)
    (hz : ∀ k, k ≠ i → ∀ N, IsZero ((r.obj (e.obj N)) k)) :
    r ⋙ Pi.eval D i ⊣ e := by
  classical
  let p (M : C) (N : D i) (f : M ⟶ e.obj N) : (r.obj M) i ⟶ N :=
    r.map f i ≫ c.hom.app N
  have hb (M : C) (N : D i) : Function.Bijective (p M N) := by
    constructor
    · intro f g h
      apply r.map_injective
      funext k
      by_cases hk : k = i
      · subst k
        exact (cancel_mono (c.hom.app N)).mp h
      · exact (hz k hk N).eq_of_tgt _ _
    · intro f
      let g : r.obj M ⟶ r.obj (e.obj N) := fun k ↦ by
        by_cases hk : k = i
        · subst k
          exact f ≫ c.inv.app N
        · exact (hz k hk N).from_ _
      refine ⟨r.preimage g, ?_⟩
      dsimp only [p]
      rw [r.map_preimage]
      simp [g]
  let q (M : C) (N : D i) : (M ⟶ e.obj N) ≃ ((r ⋙ Pi.eval D i).obj M ⟶ N) :=
    Equiv.ofBijective (p M N) (hb M N)
  refine Adjunction.mkOfHomEquiv
    { homEquiv := fun M N ↦ (q M N).symm
      homEquiv_naturality_left_symm := ?_
      homEquiv_naturality_right := ?_ }
  · intro M' M N f g
    change r.map (f ≫ g) i ≫ c.hom.app N =
      r.map f i ≫ (r.map g i ≫ c.hom.app N)
    simp only [Functor.map_comp, Pi.comp_apply, Category.assoc]
  · intro M N N' f g
    apply (q M N').injective
    rw [Equiv.apply_symm_apply]
    change f ≫ g = r.map ((q M N).symm f ≫ e.map g) i ≫ c.hom.app N'
    rw [Functor.map_comp]
    change f ≫ g = (r.map ((q M N).symm f) i ≫
      (e ⋙ r ⋙ Pi.eval D i).map g) ≫ c.hom.app N'
    rw [Category.assoc, c.hom.naturality, ← Category.assoc]
    exact congrArg (fun k ↦ k ≫ g) ((q M N).apply_symm_apply f).symm

/-- The restriction preserves all displayed coproducts and admits the stated zero-insertion
adjunction. This is the lower structural clause used by the parent tensor theorem. -/
theorem clopen_structural_coproduct_adjunction
    (X : Scheme.{t}) (I : Type w) [Finite I] (Y : I → Scheme.{t})
    (j : ∀ i, Y i ⟶ X) [∀ i, IsOpenImmersion (j i)] [∀ i, IsClosedImmersion (j i)]
    (hdisjoint : Pairwise (fun i k ↦ Disjoint (Set.range (j i)) (Set.range (j k))))
    (hcover : ∀ x : X, ∃ i, x ∈ Set.range (j i))
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)}) :
    (∀ i (K : Type (max u (t + 1))),
      PreservesColimitsOfShape (Discrete K) (ClopenData.clopenTensorRestriction.{t, u} (j i) R)) ∧
    (∀ i
      (e : ClopenData.clopenTensorModules.{t, u}
        ((ClopenData.clopenTensorRings.{t, u} (j i)).obj R) ⥤
        ClopenData.clopenTensorModules.{t, u} R),
      Nonempty (e ⋙ ClopenData.clopenTensorRestriction.{t, u} (j i) R ≅ 𝟭 _) →
      (∀ k, k ≠ i → ∀ N, IsZero ((e ⋙ ClopenData.clopenTensorRestriction.{t, u} (j k) R).obj N)) →
      Nonempty (ClopenData.clopenTensorRestriction.{t, u} (j i) R ⊣ e)) := by
  classical
  let := Fintype.ofFinite I
  let a := (Fintype.equivFin I).symm
  have hd : Pairwise (fun i k ↦
      Disjoint (Set.range (j (a i))) (Set.range (j (a k)))) :=
    fun _ _ h ↦ hdisjoint (a.injective.ne h)
  have hc : ∀ x : X, ∃ i, x ∈ Set.range (j (a i)) := by
    intro x
    obtain ⟨i, hi⟩ := hcover x
    obtain ⟨k, rfl⟩ := a.surjective i
    exact ⟨k, hi⟩
  let R' := (sheafCompose (topology X)
    (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})).obj R
  obtain ⟨G, η, ε, _, _, _, _, _, _, _, _, _, _, ⟨e₀, hei, heoff, _⟩, _⟩ :=
    clopen_ringed_module_gluing.{t, max u (t + 1), u, 0,
      max u (t + 1), max u (t + 1), 0, 0} X _ (fun k ↦ Y (a k))
      (fun k ↦ j (a k)) hd hc R' (by
        intro U b c
        exact mul_comm (show R.obj.obj U from b) c)
  let r := clopenRestriction (fun k ↦ j (a k)) R'
  let E := CategoryTheory.Equivalence.mk r G η ε
  have : r.IsEquivalence := E.isEquivalence_functor
  constructor
  · intro i K
    obtain ⟨k, rfl⟩ := a.surjective i
    let adj := adjunctionOfZeroInsertion r k (e₀ k) (hei k).some
      (fun l hl N ↦ heoff l k hl N)
    have := adj.leftAdjoint_preservesColimits.{max u (t + 1), max u (t + 1)}
    exact inferInstanceAs (PreservesColimitsOfShape (Discrete K) (r ⋙ Pi.eval _ k))
  · intro i e hi ho
    obtain ⟨k, rfl⟩ := a.surjective i
    exact ⟨adjunctionOfZeroInsertion r k e hi.some
      (fun l hl N ↦ ho (a l) (a.injective.ne hl) N)⟩

end AlgebraicGeometry.Scheme.ProEt
