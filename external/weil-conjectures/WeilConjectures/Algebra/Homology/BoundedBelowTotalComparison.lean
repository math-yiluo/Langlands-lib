/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.TotalComplexSymmetry
import WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns

/-!
# Comparison of total complexes bounded below in both directions

Source: Stacks Project, Homology, Tags 012X and 0132.
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits ComplexShape

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{0} C]

set_option backward.defeqAttrib.useBackward true in
private theorem totalProjection_isIso
    (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) (Q M n : ℤ)
    (hK : ∀ p q : ℤ, q < Q → IsZero ((K.X p).X q)) (hn : n ≤ M + Q) :
    IsIso ((total.map (K.πStupidTrunc (embeddingUpIntLE M)) (up ℤ)).f n) := by
  apply GradedObject.isIso_mapMap_apply
  rintro ⟨p, q⟩ (hpq : p + q = n)
  by_cases hp : p ≤ M
  · obtain ⟨i, hi⟩ : ∃ i, (embeddingUpIntLE M).f i = p := by
      obtain ⟨k, hk⟩ := Int.le.dest hp
      exact ⟨k, by dsimp; omega⟩
    have := HomologicalComplex.isIso_πStupidTrunc_f K (embeddingUpIntLE M) hi
    change IsIso ((HomologicalComplex.eval _ _ q).map _)
    infer_instance
  · exact (hK p q (by omega)).isIso
      ((HomologicalComplex.eval _ _ q).map_isZero
        (K.isZero_stupidTrunc_X (embeddingUpIntLE M) p (by
          intro i hi
          dsimp at hi
          omega))) _

private theorem totalProjection_quasiIsoAt
    (K : HomologicalComplex₂ C (up ℤ) (up ℤ)) (Q M n : ℤ)
    (hK : ∀ p q : ℤ, q < Q → IsZero ((K.X p).X q)) (hn : n < M + Q) :
    QuasiIsoAt (total.map (K.πStupidTrunc (embeddingUpIntLE M)) (up ℤ)) n := by
  rw [quasiIsoAt_iff' _ (n - 1) n (n + 1) (by simp) (by simp)]
  have : IsIso ((HomologicalComplex.shortComplexFunctor' C (up ℤ) (n - 1) n (n + 1)).map
      (total.map (K.πStupidTrunc (embeddingUpIntLE M)) (up ℤ))) := by
    rw [ShortComplex.isIso_iff]
    exact ⟨totalProjection_isIso K Q M _ hK (by omega),
      totalProjection_isIso K Q M _ hK (by omega),
      totalProjection_isIso K Q M _ hK (by omega)⟩
  exact ShortComplex.quasiIso_of_isIso _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- A columnwise quasi-isomorphism of double complexes uniformly bounded below in both
coordinates is a quasi-isomorphism on coproduct total complexes.
Source: Stacks Project, Homology, Tags 012X and 0132.
(auxiliary; not a blueprint node).

Proof: in total homology degree n discard columns p>M=n-Q+1. The projection changes
none of the three terms computing that homology: every discarded summand has q<Q
and is zero. The remaining bicomplexes have finitely many columns P,...,M.
Their column maps are quasi-isomorphisms, since the cutoff projection is an
isomorphism in every retained column. Finite-column total comparison applies.
Totalize the naturality square of cutoff projections and use two-out-of-three in
degree n. This works also for n<P+Q, when the effective diagonal is empty. -/
theorem quasiIso_totalMap_of_boundedBelow_columns
    {K L : HomologicalComplex₂ C (up ℤ) (up ℤ)} (f : K ⟶ L) (P Q : ℤ)
    (hK : ∀ p q : ℤ, p < P ∨ q < Q → IsZero ((K.X p).X q))
    (hL : ∀ p q : ℤ, p < P ∨ q < Q → IsZero ((L.X p).X q))
    (hf : ∀ p : ℤ, QuasiIso (f.f p)) : QuasiIso (total.map f (up ℤ)) := by
  have hGE (A : HomologicalComplex₂ C (up ℤ) (up ℤ))
      (hA : ∀ p q : ℤ, p < P ∨ q < Q → IsZero ((A.X p).X q)) :
      CochainComplex.IsStrictlyGE A P := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro p hp
    rw [IsZero.iff_id_eq_zero]
    apply HomologicalComplex.hom_ext
    intro q
    exact (hA p q (Or.inl hp)).eq_of_src _ _
  have := hGE K hK
  have := hGE L hL
  rw [quasiIso_iff]
  intro n
  let M := n - Q + 1
  let g := HomologicalComplex.stupidTruncMap f (embeddingUpIntLE M)
  have hg : QuasiIso (total.map g (up ℤ)) := by
    apply total.quasiIso_map_of_finitely_many_columns g P M
    intro p hp₁ hp₂
    obtain ⟨i, hi⟩ : ∃ i, (embeddingUpIntLE M).f i = p := by
      obtain ⟨k, hk⟩ := Int.le.dest hp₂
      exact ⟨k, by dsimp; omega⟩
    have hπ (A : HomologicalComplex₂ C (up ℤ) (up ℤ)) :
        IsIso ((A.πStupidTrunc (embeddingUpIntLE M)).f p) :=
      HomologicalComplex.isIso_πStupidTrunc_f A (embeddingUpIntLE M) hi
    have := hπ K
    have := hπ L
    apply (quasiIso_iff_of_arrow_mk_iso (f.f p) (g.f p)
      (Arrow.isoMk (asIso ((K.πStupidTrunc (embeddingUpIntLE M)).f p))
        (asIso ((L.πStupidTrunc (embeddingUpIntLE M)).f p)) ?_)).mp (hf p)
    exact HomologicalComplex.πStupidTrunc_f_naturality f (embeddingUpIntLE M) p
  have := totalProjection_quasiIsoAt K Q M n (fun p q hq ↦ hK p q (Or.inr hq))
    (by dsimp [M]; omega)
  have := totalProjection_quasiIsoAt L Q M n (fun p q hq ↦ hL p q (Or.inr hq))
    (by dsimp [M]; omega)
  rw [← quasiIsoAt_iff_comp_right _
    (total.map (L.πStupidTrunc (embeddingUpIntLE M)) (up ℤ)),
    ← total.map_comp, ← HomologicalComplex.πStupidTrunc_naturality, total.map_comp]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- The transposed form of bounded-below column comparison.
Source: Stacks Project, Tag 0133, using signed symmetry of total complexes.
(auxiliary; not a blueprint node).
Proof: flip both bicomplexes, apply column comparison, and conjugate by the
natural signed total-flip isomorphisms. -/
theorem quasiIso_totalMap_of_boundedBelow_rows
    {K L : HomologicalComplex₂ C (up ℤ) (up ℤ)} (f : K ⟶ L) (P Q : ℤ)
    (hK : ∀ p q : ℤ, p < P ∨ q < Q → IsZero ((K.X p).X q))
    (hL : ∀ p q : ℤ, p < P ∨ q < Q → IsZero ((L.X p).X q))
    (hf : ∀ q : ℤ, QuasiIso (((flipFunctor C (up ℤ) (up ℤ)).map f).f q)) :
    QuasiIso (total.map f (up ℤ)) := by
  have ht := quasiIso_totalMap_of_boundedBelow_columns
    ((flipFunctor C (up ℤ) (up ℤ)).map f) Q P
    (fun q p h ↦ hK p q h.symm) (fun q p h ↦ hL p q h.symm) hf
  apply (quasiIso_iff_of_arrow_mk_iso _ _
    (Arrow.isoMk (K.totalFlipIso (up ℤ)) (L.totalFlipIso (up ℤ)) ?_)).mp ht
  apply HomologicalComplex.hom_ext
  intro n
  apply total.hom_ext
  intro q p h
  dsimp only [Arrow.mk_hom, HomologicalComplex.comp_f]
  simp only [ιTotal_totalFlipIso_f_hom_assoc, Linear.units_smul_comp,
    ιTotal_map, ιTotal_map_assoc]
  change _ = (f.f p).f q ≫ L.flip.ιTotal (up ℤ) q p n h ≫ _
  rw [ιTotal_totalFlipIso_f_hom, Linear.comp_units_smul]

end HomologicalComplex₂
