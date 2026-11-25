/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Homology.QuasiIso
import WeilConjectures.Algebra.Homology.FirstQuadrantTotalComparisonFinite
import WeilConjectures.FromJoel.Algebra.Homology.BicomplexColumns

/-! # Columnwise comparison of first-quadrant total complexes

Source: Stacks Project, Homology, Section 12.25, finite filtration and diagonal arguments.
-/

@[expose] public section

universe v u

open CategoryTheory

namespace HomologicalComplex₂

private def finiteRowShape (N : ℕ) : ComplexShape (Fin (N + 1)) where
  Rel i j := (i : ℕ) + 1 = j
  next_eq h h' := Fin.ext (h.symm.trans h')
  prev_eq h h' := Fin.ext (by omega)

private def finiteRowEmbedding (N : ℕ) :
    (finiteRowShape N).Embedding (ComplexShape.up ℕ) :=
  ComplexShape.Embedding.mk' _ _ Fin.val Fin.val_injective (fun _ _ ↦ Iff.rfl)

private instance (N : ℕ) : (finiteRowEmbedding N).IsRelIff := by
  dsimp [finiteRowEmbedding]
  infer_instance

private instance (N : ℕ) : (finiteRowEmbedding N).IsTruncLE where
  mem_prev {i'} {j} h := ⟨⟨i', by change i' + 1 = (j : ℕ) at h; omega⟩, rfl⟩

private noncomputable def rowCut {C : Type u} [Category.{v} C] [Abelian C] (N : ℕ) :=
  (finiteRowEmbedding N).stupidTruncFunctor C

private instance {C : Type u} [Category.{v} C] [Abelian C] (N : ℕ) :
    (rowCut (C := C) N).PreservesZeroMorphisms := by
  change ((finiteRowEmbedding N).restrictionFunctor C ⋙
    (finiteRowEmbedding N).extendFunctor C).PreservesZeroMorphisms
  infer_instance

private noncomputable def rowCutMap {C : Type u} [Category.{v} C] [Abelian C] (N : ℕ)
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)) :
    K ⟶ ((rowCut (C := C) N).mapHomologicalComplex (ComplexShape.up ℕ)).obj K where
  f p := (K.X p).πStupidTrunc (finiteRowEmbedding N)
  comm' _ _ _ := HomologicalComplex.πStupidTrunc_naturality _ _

private lemma rowCut_zero {C : Type u} [Category.{v} C] [Abelian C] (N : ℕ)
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (p q : ℕ) (hq : N < q) :
    Limits.IsZero (((((rowCut (C := C) N).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj K).X p).X q) := by
  apply HomologicalComplex.isZero_stupidTrunc_X
  intro i hi
  change (i : ℕ) = q at hi
  omega

private lemma rowCutMap_isIso_f {C : Type u} [Category.{v} C] [Abelian C] (N : ℕ)
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (p q : ℕ) (hq : q ≤ N) : IsIso (((rowCutMap N K).f p).f q) := by
  change IsIso (((K.X p).πStupidTrunc (finiteRowEmbedding N)).f q)
  exact HomologicalComplex.isIso_πStupidTrunc_f _ _ (i := ⟨q, by omega⟩) rfl

private lemma rowCutMap_total_quasiIsoAt {C : Type u} [Category.{v} C] [Abelian C]
    (N : ℕ) (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (n : ℕ) (hn : n < N) :
    QuasiIsoAt (total.map (rowCutMap N K) (ComplexShape.up ℕ)) n := by
  have hi (m : ℕ) (hm : m ≤ N) :
      IsIso ((total.map (rowCutMap N K) (ComplexShape.up ℕ)).f m) := by
    apply CategoryTheory.GradedObject.isIso_mapMap_apply
    rintro ⟨p, q⟩ (hpq : p + q = m)
    exact rowCutMap_isIso_f N K p q (by omega)
  rw [quasiIsoAt_iff' _ ((ComplexShape.up ℕ).prev n) n (n + 1) rfl (by simp)]
  have : IsIso ((HomologicalComplex.shortComplexFunctor' C (ComplexShape.up ℕ)
      ((ComplexShape.up ℕ).prev n) n (n + 1)).map
      (total.map (rowCutMap N K) (ComplexShape.up ℕ))) := by
    rw [ShortComplex.isIso_iff]
    refine ⟨hi _ ?_, hi _ (by omega), hi _ (by omega)⟩
    cases n with
    | zero => simp
    | succ n => simpa using (show n ≤ N by omega)
  exact ShortComplex.quasiIso_of_isIso _

/-- A columnwise quasi-isomorphism of first-quadrant bicomplexes induces a
quasi-isomorphism on their total complexes.
Source: Stacks Project, Section 12.25 (Tags 012X and 0133), finite filtration argument.
(blueprint: lem-sc-first-quadrant-total-column-comparison).

Proof: in each homology degree n truncate the vertical complexes above N=n+1
by restricting to the finite shape 0,...,N and extending by zero. The canonical
projections commute with f. At every retained row they are isomorphisms of
horizontal complexes; at every omitted row the truncated objects are zero.
Thus the truncated map satisfies finite-row comparison. In total degree m≤N,
every diagonal summand has vertical degree q≤m≤N, so each total projection is
an isomorphism. In particular it is invertible on the three terms computing
homology in degree n (including prev(0)=0), hence a quasi-isomorphism at n.
Totalizing the naturality square and applying two-out-of-three transfers the
finite-row result to the original map in degree n. Repeat for all n.
No choice of an unproved existence witness enters any definition. -/
theorem quasiIso_totalMap_of_columns {C : Type u} [Category.{v} C] [Abelian C]
    {K L : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)}
    (f : K ⟶ L)
    (hf : ∀ n : ℕ, QuasiIso
      (((flipFunctor C (ComplexShape.up ℕ) (ComplexShape.up ℕ)).map f).f n)) :
    QuasiIso (total.map f (ComplexShape.up ℕ)) := by
  rw [quasiIso_iff]
  intro n
  let N := n + 1
  let T := (rowCut (C := C) N).mapHomologicalComplex (ComplexShape.up ℕ)
  let F := flipFunctor C (ComplexShape.up ℕ) (ComplexShape.up ℕ)
  have hnat : rowCutMap N K ≫ T.map f = f ≫ rowCutMap N L := by
    ext p q
    exact HomologicalComplex.πStupidTrunc_f_naturality _ _ _
  have hcolumns (q : ℕ) : QuasiIso ((F.map (T.map f)).f q) := by
    by_cases hq : q ≤ N
    · have hπ (M : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)) :
          IsIso ((F.map (rowCutMap N M)).f q) := by
        have : ∀ p, IsIso (((F.map (rowCutMap N M)).f q).f p) :=
          fun p ↦ rowCutMap_isIso_f N M p q hq
        exact HomologicalComplex.Hom.isIso_of_components _
      have := hπ K
      have := hπ L
      apply (quasiIso_iff_of_arrow_mk_iso ((F.map f).f q) _
        (Arrow.isoMk (asIso ((F.map (rowCutMap N K)).f q))
          (asIso ((F.map (rowCutMap N L)).f q)) ?_)).mp (hf q)
      have h := congrArg (fun g ↦ (F.map g).f q) hnat
      simpa only [Functor.map_comp, HomologicalComplex.comp_f, asIso_hom, Arrow.mk_hom] using h
    · have hi (p : ℕ) : IsIso (((F.map (T.map f)).f q).f p) :=
        (rowCut_zero N K p q (by omega)).isIso
          (rowCut_zero N L p q (by omega)) _
      have : IsIso ((F.map (T.map f)).f q) :=
        HomologicalComplex.Hom.isIso_of_components _
      infer_instance
  have : QuasiIso (total.map (T.map f) (ComplexShape.up ℕ)) :=
    quasiIso_totalMap_of_columns_of_finite_rows (T.map f) N
      (rowCut_zero N K) (rowCut_zero N L) hcolumns
  have := rowCutMap_total_quasiIsoAt N K n (by omega)
  have := rowCutMap_total_quasiIsoAt N L n (by omega)
  rw [← quasiIsoAt_iff_comp_right _ (total.map (rowCutMap N L) (ComplexShape.up ℕ)),
    ← total.map_comp, ← hnat, total.map_comp]
  infer_instance

end HomologicalComplex₂
