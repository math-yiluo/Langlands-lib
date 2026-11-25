/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.FilteredComplexSubquotients

@[expose] public section

universe uA vA
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.Functor

/-- A stable antitone family of degreewise subobjects assembles into a filtration.
Source: Stacks Project, Tag 0121 (definition of filtration); the elementary
subcomplex construction, also proved privately in
Sheaf.Algebra.Homology.FirstQuadrantVerticalConeFiltration.filtration_of_degreewise.
Proof: factor each differential through the target monomorphism. Cancellation
of that monomorphism proves square-zero and the chain-map equations. The
component inclusions define a monic map of complexes. Degreewise containment
induces a chain map between these complexes, again by monic cancellation,
so their subobjects are antitone. The representative of each subobject differs
from this inclusion by an isomorphism. Evaluation preserves that isomorphism,
and composing with an isomorphism leaves the image subobject unchanged.
Thus the filtration has exactly the specified degreewise subobjects.
(blueprint: lem-sp-cartan-eilenberg-cone-filtration-data-assemble). -/
theorem filtration_of_degreewise
    {C : Type uA} [Category.{vA} C] [Abelian C]
    (K : CochainComplex C ℤ) (S : ℤ → ∀ n : ℤ, Subobject (K.X n))
    (hS : ∀ n, Antitone (fun p ↦ S p n))
    (hd : ∀ p n, (S p (n + 1)).Factors ((S p n).arrow ≫ K.d n (n + 1))) :
    ∃ F : DecreasingFiltration K, ∀ p n, F.complexStep p n = S p n := by
  let d := fun p n ↦ (S p (n + 1)).factorThru
    ((S p n).arrow ≫ K.d n (n + 1)) (hd p n)
  have hd' (p n : ℤ) : d p n ≫ (S p (n + 1)).arrow =
      (S p n).arrow ≫ K.d n (n + 1) := Subobject.factorThru_arrow _ _ _
  have hsq (p n : ℤ) : d p n ≫ d p (n + 1) = 0 := by
    apply (cancel_mono (S p ((n + 1) + 1)).arrow).1
    rw [Category.assoc, hd', ← Category.assoc, hd', Category.assoc,
      K.d_comp_d, CategoryTheory.Limits.comp_zero, CategoryTheory.Limits.zero_comp]
  let L := fun p ↦ CochainComplex.of (fun n ↦ (S p n : C)) (d p) (hsq p)
  let i : ∀ p, L p ⟶ K := fun p ↦ CochainComplex.ofHom
    (fun n ↦ (S p n).arrow) (fun n ↦ by
      simpa only [L, CochainComplex.of_d] using (hd' p n).symm)
  have hi (p : ℤ) : Mono (i p) :=
    HomologicalComplex.mono_of_mono_f _ (fun _ ↦ inferInstance)
  let F : DecreasingFiltration K := {
    F := fun p ↦ Subobject.mk (i p)
    F_succ_le := by
      intro p
      let q : ℤ := p + 1
      have hpq : p ≤ q := by dsimp [q]; omega
      let l : L q ⟶ L p := CochainComplex.ofHom
        (fun n ↦ Subobject.ofLE (S q n) (S p n) (hS n hpq)) (by
          intro n
          simp only [L, CochainComplex.of_d]
          apply (cancel_mono (S p (n + 1)).arrow).1
          rw [Category.assoc, hd', ← Category.assoc, Subobject.ofLE_arrow,
            Category.assoc, Subobject.ofLE_arrow, hd'])
      apply Subobject.mk_le_mk_of_comm l
      ext n
      exact Subobject.ofLE_arrow _ }
  refine ⟨F, ?_⟩
  intro p n
  have he : ((Subobject.mk (i p)).arrow).f n =
      ((Subobject.underlyingIso (i p)).hom).f n ≫ (i p).f n := by
    have h := congrArg (fun a : (Subobject.mk (i p) : CochainComplex C ℤ) ⟶ K ↦ a.f n)
      (Subobject.underlyingIso_hom_comp_eq_mk (i p))
    exact h.symm
  change imageSubobject (((Subobject.mk (i p)).arrow).f n) = S p n
  rw [he, imageSubobject_iso_comp]
  change imageSubobject (S p n).arrow = S p n
  rw [imageSubobject_mono, Subobject.mk_arrow]


end CategoryTheory.Functor
