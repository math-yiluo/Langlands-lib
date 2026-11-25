/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.ZigzagModule

/-!
# Functoriality of zig-zag modules

Source: Stacks Project, Algebra, Tag 00M1, proof and preceding functoriality paragraph
(blueprint: lem-weil-pbc-double-complex-zigzag-module-functorial).
-/

@[expose] public section

universe u v

open CategoryTheory

namespace HomologicalComplex₂

set_option backward.isDefEq.respectTransparency false in
private lemma boundary_cycles {R : Type u} [CommRing R]
    (A : HomologicalComplex₂ (ModuleCat.{v} R) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (n : ℕ) :
    zigzagBoundaries A n ≤ zigzagCycles A n := by
  classical
  have index_eq_iff {m : ℕ} (i j : ZigzagIndex m) :
      i = j ↔ i.val = j.val := Subtype.ext_iff
  rintro _ ⟨b, rfl⟩
  intro p q h
  change zigzagRelation A n p q h (zigzagBoundary A n b) = 0
  suffices hz : (zigzagRelation A n p q h).comp (zigzagBoundary A n) = 0 by
    exact LinearMap.congr_fun hz b
  apply DirectSum.linearMap_ext
  rintro ⟨⟨k, l⟩, hi⟩
  ext x
  by_cases hk : k = p
  · subst k
    have hl : l = q + 2 := by omega
    subst l
    have hz := ConcreteCategory.congr_hom ((A.X p).d_comp_d (q + 2) (q + 1) q) x
    dsimp at hz
    simp only [LinearMap.comp_apply, zigzagBoundary, DirectSum.toModule_lof]
    dsimp only [zigzagBoundaryComponent]
    split_ifs <;>
      simp [LinearMap.comp_apply, zigzagRelation, DirectSum.component.of,
        index_eq_iff, hz]
  · by_cases hk1 : k = p + 1
    · subst k
      have hl : l = q + 1 := by omega
      subst l
      have hc := ConcreteCategory.congr_hom (A.d_comm (p + 1) p (q + 1) q) x
      dsimp at hc
      simpa [LinearMap.comp_apply, zigzagBoundary, zigzagBoundaryComponent,
        zigzagRelation, DirectSum.component.of, index_eq_iff, sub_eq_zero] using hc.symm
    · by_cases hk2 : k = p + 2
      · subst k
        have hl : l = q := by omega
        subst l
        have hz := ConcreteCategory.congr_hom (A.d_f_comp_d_f (p + 2) (p + 1) p q) x
        dsimp at hz
        simp only [LinearMap.comp_apply, zigzagBoundary, DirectSum.toModule_lof]
        dsimp only [zigzagBoundaryComponent]
        split_ifs <;>
          simp [LinearMap.comp_apply, zigzagRelation, DirectSum.component.of,
            index_eq_iff, hz]
      · have hkp : k - 1 ≠ p := by omega
        have hkp1 : k - 1 ≠ p + 1 := by omega
        simp only [LinearMap.comp_apply, zigzagBoundary, DirectSum.toModule_lof]
        dsimp only [zigzagBoundaryComponent]
        split_ifs <;>
          simp [LinearMap.comp_apply, zigzagRelation, DirectSum.component.of,
            index_eq_iff, hk, hk1, hkp, hkp1]

set_option backward.isDefEq.respectTransparency false in
private lemma boundary_natural {R : Type u} [CommRing R]
    {A B : HomologicalComplex₂ (ModuleCat.{v} R) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)} (Φ : A ⟶ B) (n : ℕ) :
    (zigzagTotalMap Φ n).comp (zigzagBoundary A n) =
      (zigzagBoundary B n).comp (zigzagTotalMap Φ (n + 1)) := by
  classical
  have index_eq_iff {m : ℕ} (i j : ZigzagIndex m) :
      i = j ↔ i.val = j.val := Subtype.ext_iff
  have horizontal (p r q : ℕ) (x : (A.X p).X q) :
      (B.d p r).f q ((Φ.f p).f q x) = (Φ.f r).f q ((A.d p r).f q x) := by
    exact ConcreteCategory.congr_hom (HomologicalComplex.congr_hom (Φ.comm p r) q) x
  have vertical (p q s : ℕ) (x : (A.X p).X q) :
      (B.X p).d q s ((Φ.f p).f q x) = (Φ.f p).f s ((A.X p).d q s x) := by
    exact ConcreteCategory.congr_hom ((Φ.f p).comm q s) x
  apply DirectSum.linearMap_ext
  intro i
  ext x
  simp only [LinearMap.comp_apply, zigzagBoundary, DirectSum.toModule_lof,
    zigzagTotalMap]
  dsimp only [zigzagBoundaryComponent]
  split_ifs <;> simp [map_add, LinearMap.comp_apply, horizontal, vertical]

private lemma total_comp {R : Type u} [CommRing R]
    {A B C : HomologicalComplex₂ (ModuleCat.{v} R) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)} (Φ : A ⟶ B) (Ψ : B ⟶ C) (n : ℕ) :
    zigzagTotalMap (Φ ≫ Ψ) n = (zigzagTotalMap Ψ n).comp (zigzagTotalMap Φ n) := by
  classical
  apply DirectSum.linearMap_ext
  intro i
  ext x
  simp [zigzagTotalMap, LinearMap.comp_apply]

private lemma total_id {R : Type u} [CommRing R]
    (A : HomologicalComplex₂ (ModuleCat.{v} R) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (n : ℕ) :
    zigzagTotalMap (𝟙 A) n = LinearMap.id := by
  classical
  apply DirectSum.linearMap_ext
  intro i
  ext x
  simp [zigzagTotalMap, LinearMap.comp_apply]

private lemma map_mk {R : Type u} [CommRing R]
    {A B : HomologicalComplex₂ (ModuleCat.{v} R) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)} (Φ : A ⟶ B) (n : ℕ)
    (a : zigzagCycles A n) (b : zigzagCycles B n)
    (h : b.val = zigzagTotalMap Φ n a.val) :
    zigzagMap Φ n (Submodule.Quotient.mk a) = Submodule.Quotient.mk b := by
  classical
  simp only [zigzagMap, Submodule.mapQ_apply]
  congr 1
  apply Subtype.ext
  exact h.symm

set_option backward.isDefEq.respectTransparency false in
/-- (blueprint: lem-weil-pbc-double-complex-zigzag-module-functorial)
Trivial zig-zags are zig-zags, and the quotient maps are functorial
(Stacks Project, Algebra, Tag 00M1, proof and preceding paragraph).

Proof, following the four steps of the node:
(a) For `a = D b`, apply `d` and `δ` to the two adjacent components. The `dd` and
`δδ` terms vanish; the remaining terms agree by the commuting square. Thus `B ≤ Z`,
and the intersection with `Z` is `B`.
(b) Apply the component maps of `Φ` to the zig-zag equalities. Since they commute
with both differentials, the resulting tuple is a zig-zag. Linearity and the same
commutation identities give `Φ (D b) = D (Φ b)` componentwise, so boundaries map to
boundaries. These steps use the double-complex and zig-zag definitions.
(c) Unfold the existing `zigzagMap` and use `Submodule.mapQ_apply` to obtain the
representative formula. Every quotient element has a cycle representative by
`Submodule.mkQ_surjective`, so this formula determines the linear map uniquely.
(d) Check the total-map composition and identity on `DirectSum.lof` generators.
For composition, represent a quotient element by a cycle `a`, form its cycle
images `b` and `c`, and apply the representative formula three times. For identity,
apply the formula to `a` itself. Surjectivity of the quotient map closes both laws.

In the representative formula, `b` is a cycle whose underlying tuple is `Φ(a)`;
this avoids choosing a second restriction map or a second quotient definition. -/
theorem zigzagModule_functorial
    {R : Type u} [CommRing R]
    (A B C : HomologicalComplex₂ (ModuleCat.{v} R) (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) (Φ : A ⟶ B) (Ψ : B ⟶ C) (n : ℕ) :
    zigzagBoundaries A n ≤ zigzagCycles A n ∧
    zigzagCycles A n ⊓ zigzagBoundaries A n = zigzagBoundaries A n ∧
    (zigzagCycles A n).map (zigzagTotalMap Φ n) ≤ zigzagCycles B n ∧
    (zigzagTotalMap Φ n).comp (zigzagBoundary A n) =
      (zigzagBoundary B n).comp (zigzagTotalMap Φ (n + 1)) ∧
    (zigzagBoundaries A n).map (zigzagTotalMap Φ n) ≤ zigzagBoundaries B n ∧
    (∀ (a : zigzagCycles A n) (b : zigzagCycles B n),
      b.val = zigzagTotalMap Φ n a.val →
      zigzagMap Φ n (Submodule.Quotient.mk a) = Submodule.Quotient.mk b) ∧
    (∀ f : zigzagModule A n →ₗ[R] zigzagModule B n,
      (∀ (a : zigzagCycles A n) (b : zigzagCycles B n),
        b.val = zigzagTotalMap Φ n a.val →
        f (Submodule.Quotient.mk a) = Submodule.Quotient.mk b) → f = zigzagMap Φ n) ∧
    zigzagMap (Φ ≫ Ψ) n = (zigzagMap Ψ n).comp (zigzagMap Φ n) ∧
    zigzagMap (𝟙 A) n = LinearMap.id := by
  classical
  have hcycles := boundary_cycles A n
  refine ⟨hcycles, inf_eq_right.mpr hcycles, (zigzagTotalMap_preserves Φ n).1,
    boundary_natural Φ n, (zigzagTotalMap_preserves Φ n).2, map_mk Φ n, ?_, ?_, ?_⟩
  · intro f hf
    apply LinearMap.ext
    intro z
    obtain ⟨a, rfl⟩ :=
      ((zigzagBoundaries A n).comap (zigzagCycles A n).subtype).mkQ_surjective z
    let b : zigzagCycles B n := ⟨zigzagTotalMap Φ n a.val,
      (zigzagTotalMap_preserves Φ n).1 (Submodule.mem_map_of_mem a.property)⟩
    exact (hf a b rfl).trans (map_mk Φ n a b rfl).symm
  · apply LinearMap.ext
    intro z
    obtain ⟨a, rfl⟩ :=
      ((zigzagBoundaries A n).comap (zigzagCycles A n).subtype).mkQ_surjective z
    let b : zigzagCycles B n := ⟨zigzagTotalMap Φ n a.val,
      (zigzagTotalMap_preserves Φ n).1 (Submodule.mem_map_of_mem a.property)⟩
    let c : zigzagCycles C n := ⟨zigzagTotalMap Ψ n b.val,
      (zigzagTotalMap_preserves Ψ n).1 (Submodule.mem_map_of_mem b.property)⟩
    change zigzagMap (Φ ≫ Ψ) n (Submodule.Quotient.mk a) =
      zigzagMap Ψ n (zigzagMap Φ n (Submodule.Quotient.mk a))
    rw [map_mk Φ n a b rfl, map_mk Ψ n b c rfl]
    apply map_mk
    exact (LinearMap.congr_fun (total_comp Φ Ψ n) a.val).symm
  · apply LinearMap.ext
    intro z
    obtain ⟨a, rfl⟩ :=
      ((zigzagBoundaries A n).comap (zigzagCycles A n).subtype).mkQ_surjective z
    apply map_mk
    exact (LinearMap.congr_fun (total_id A n) a.val).symm

end HomologicalComplex₂
