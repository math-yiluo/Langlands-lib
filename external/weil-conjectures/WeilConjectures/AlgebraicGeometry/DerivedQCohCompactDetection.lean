/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedQCohDirectSums
public import WeilConjectures.CategoryTheory.CompactObject
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.DerivedQCohCompactGeneration
import Mathlib.CategoryTheory.Adjunction.Additive

/-! # Isomorphism detection by compact quasi-coherent derived objects

Source: Stacks Project, Tags 09IS and 09M1; detection step of Tag 0A9R.
(blueprint: lem-sc-derived-qcoh-compact-detection).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

-- Shift equivalences preserve compactness by their additive adjunction and coproduct comparison.
-- This formal calculation is also used in CategoryTheory's BrownTelescopeAssembly module.
private theorem compact_shift
    {C : Type*} [Category C] [Preadditive C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [HasCoproducts.{u} C]
    (K : C) (hK : IsCompactObject K) (n : ℤ) :
    IsCompactObject (K⟦n⟧) := by
  classical
  intro J A
  let e := shiftEquiv C n
  have : e.functor.Additive := inferInstanceAs (shiftFunctor C n).Additive
  have : e.inverse.Additive := inferInstanceAs (shiftFunctor C (-n)).Additive
  let adj := e.toAdjunction
  let D := DirectSum.congrAddEquiv (fun j ↦ adj.homAddEquiv K (A j))
  let s := sigmaComparison e.inverse A
  let post : (K ⟶ e.inverse.obj (∐ A)) ≃+ (K ⟶ ∐ fun j ↦ e.inverse.obj (A j)) :=
    { toEquiv := Iso.homCongr (Iso.refl K) (asIso s).symm
      map_add' := by
        intro f g
        simp [Iso.homCongr, Preadditive.add_comp] }
  let Q := (adj.homAddEquiv K (∐ A)).trans post
  let φ := DirectSum.toAddMonoid (fun j ↦ Preadditive.rightComp (e.functor.obj K) (Sigma.ι A j))
  let ψ := DirectSum.toAddMonoid
    (fun j ↦ Preadditive.rightComp K (Sigma.ι (fun j ↦ e.inverse.obj (A j)) j))
  have hcomm : Q.toAddMonoidHom.comp φ = ψ.comp D.toAddMonoidHom := by
    apply DirectSum.addHom_ext
    intro j f
    change Q (φ (DirectSum.of _ j f)) = ψ (D (DirectSum.of _ j f))
    have hφof : φ (DirectSum.of _ j f) = f ≫ Sigma.ι A j :=
      DirectSum.toAddMonoid_of
        (fun j ↦ Preadditive.rightComp (e.functor.obj K) (Sigma.ι A j)) j f
    have hDof : D (DirectSum.of _ j f) =
        DirectSum.of _ j (adj.homAddEquiv K (A j) f) :=
      DirectSum.map_of (fun j ↦ (adj.homAddEquiv K (A j)).toAddMonoidHom) j f
    rw [hφof, hDof]
    rw [show ψ (DirectSum.of _ j (adj.homAddEquiv K (A j) f)) =
        adj.homAddEquiv K (A j) f ≫ Sigma.ι (fun j ↦ e.inverse.obj (A j)) j from
      DirectSum.toAddMonoid_of
        (fun j ↦ Preadditive.rightComp K (Sigma.ι (fun j ↦ e.inverse.obj (A j)) j)) j _]
    dsimp [Q, post, Iso.homCongr]
    rw [Category.id_comp]
    change adj.homEquiv K (∐ A) (f ≫ Sigma.ι A j) ≫ inv s =
      adj.homEquiv K (A j) f ≫ Sigma.ι (fun j ↦ e.inverse.obj (A j)) j
    rw [adj.homEquiv_naturality_right, Category.assoc]
    rw [map_ι_comp_inv_sigmaComparison]
  have hψ := hK J (fun j ↦ e.inverse.obj (A j))
  have hφ : Function.Bijective (fun x ↦ Q (φ x)) := by
    have hh : (fun x ↦ Q (φ x)) = (fun x ↦ ψ (D x)) :=
      funext (fun x ↦ DFunLike.congr_fun hcomm x)
    rw [hh]
    exact hψ.comp D.bijective
  constructor
  · intro x y hxy
    exact hφ.1 (congrArg Q hxy)
  · intro f
    obtain ⟨x, hx⟩ := hφ.2 (Q f)
    exact ⟨x, Q.injective hx⟩

/-- All compact objects jointly detect isomorphisms in D_QCoh(X).
Source: Stacks Project, Tags 09IS and 09M1; the detection step of Tag 0A9R.
(blueprint: lem-sc-derived-qcoh-compact-detection).

Proof: Choose small-Hom derived models on X and its opens using K-injective
resolutions. Localization equivalences preserve quasi-coherence, shifted Hom
sets, and coproducts, so they transport the hypothesis and the desired conclusion.
Complete g to a distinguished triangle A → B → C → A[1]. The cone C has
quasi-coherent cohomology by the cohomology exact sequence. Every shift of a
perfect object is perfect, hence compact by Tag 09M1. The assumed Hom bijections
and the long exact Hom sequence therefore give Hom(P[n], C) = 0 for every
perfect P and integer n. The class of objects Q with Hom(Q[n], C) = 0 for all n
is closed under isomorphisms, shifts, cones, retracts, and arbitrary coproducts:
the cone assertion follows from exactness, and the coproduct assertion from the
universal property identifying Hom from a sum with a product. Perfect generation
makes this class all of D_QCoh(X). In particular the identity of C is zero, so C
is a zero object. Exactness now makes Hom(T, g) bijective for every T; Yoneda
implies g is an isomorphism. Transport this conclusion to the given model.
For the empty scheme the derived category is zero and the same argument applies. -/
theorem derivedQCoh_compact_detection (X : Scheme.{u}) [IsNoetherian X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] :
    let _ : HasCoproducts.{u} (schemeDerivedQCohCategory X) := derivedQCohDirectSums X
    ∀ (A B : schemeDerivedQCohCategory X) (g : A ⟶ B),
      (∀ P : schemeDerivedQCohCategory X, IsCompactObject P →
        Function.Bijective (fun a : P ⟶ A ↦ a ≫ g)) → IsIso g := by
  classical
  dsimp only
  let : HasCoproducts.{u} (schemeDerivedQCohCategory X) := derivedQCohDirectSums X
  obtain ⟨htri, hsums, hgen⟩ := schemeDerivedQCoh_compactlyGenerated X
  let := htri
  obtain ⟨I, E, hcompact, hgenerate⟩ := hgen
  intro A B g hg
  let C := schemeDerivedQCohCategory X
  have hbijshift (P : C) (hP : IsCompactObject P) (n : ℤ) :
      Function.Bijective (fun a : P ⟶ A⟦n⟧ ↦ a ≫ g⟦n⟧') := by
    let adj := (shiftEquiv' C (-n) n (neg_add_cancel n)).toAdjunction
    let eA := adj.homEquiv P A
    let eB := adj.homEquiv P B
    have h := hg (P⟦-n⟧) (compact_shift P hP (-n))
    have he : (fun a : P ⟶ A⟦n⟧ ↦ a ≫ g⟦n⟧') =
        eB ∘ (fun a : P⟦-n⟧ ⟶ A ↦ a ≫ g) ∘ eA.symm := by
      funext a
      change a ≫ (shiftEquiv' C (-n) n (neg_add_cancel n)).inverse.map g =
        adj.homEquiv P B ((adj.homEquiv P A).symm a ≫ g)
      rw [adj.homEquiv_naturality_right]
      simp
    rw [he]
    exact eB.bijective.comp (h.comp eA.symm.bijective)
  obtain ⟨D, d, δ, hd⟩ := Pretriangulated.distinguished_cocone_triangle g
  have hD (P : C) (hP : IsCompactObject P) (a : P ⟶ D) : a = 0 := by
    have hδ : a ≫ δ = 0 := by
      apply (hbijshift P hP 1).1
      have hzero := Pretriangulated.comp_distTriang_mor_zero₃₁ _ hd
      change δ ≫ (shiftFunctor C (1 : ℤ)).map g = 0 at hzero
      simp only [Category.assoc, hzero, comp_zero, zero_comp]
    obtain ⟨b, hb⟩ := Pretriangulated.Triangle.coyoneda_exact₃ _ hd a hδ
    obtain ⟨b', hb'⟩ := (hg P hP).2 b
    have hgd : g ≫ d = 0 := Pretriangulated.comp_distTriang_mor_zero₁₂ _ hd
    change a = b ≫ d at hb
    rw [hb, ← hb', Category.assoc, hgd, comp_zero]
  have hDshift (i : I) (n : ℤ) (a : E i ⟶ D⟦n⟧) : a = 0 := by
    let adj := (shiftEquiv' C (-n) n (neg_add_cancel n)).toAdjunction
    have : (shiftEquiv' C (-n) n (neg_add_cancel n)).functor.Additive :=
      inferInstanceAs (shiftFunctor C (-n)).Additive
    have : (shiftEquiv' C (-n) n (neg_add_cancel n)).inverse.Additive :=
      inferInstanceAs (shiftFunctor C n).Additive
    apply (adj.homEquiv (E i) D).symm.injective
    rw [hD ((E i)⟦-n⟧) (compact_shift (E i) (hcompact i) (-n))
      ((adj.homEquiv (E i) D).symm a)]
    exact (adj.homAddEquiv_symm_zero _ _).symm
  have hzD : IsZero D := by
    by_contra hn
    obtain ⟨n, a, ha⟩ := hgenerate D hn
    apply ha
    apply Sigma.hom_ext
    intro i
    simpa only [comp_zero] using hDshift i n (Sigma.ι E i ≫ a)
  exact (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _ hd).mp hzD

end AlgebraicGeometry
