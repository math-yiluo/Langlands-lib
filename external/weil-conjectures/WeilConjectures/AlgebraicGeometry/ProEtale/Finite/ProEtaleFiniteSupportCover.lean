/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Topology.Spectral.Prespectral

/-!
# Finite supports from local representatives

## References

* Stacks Project, Tags 00WK and 09AE
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme.ProEt

/-- A section on a quasi-compact test scheme which locally vanishes or lies over an
open has a finite affine covering whose nonzero restrictions lie over one compact
open contained in that open. Refine the given covering by finitely many affine opens,
take the union of the images of the nonzero members, and enclose this compact set in
a compact open using the compact-open basis of a scheme. Empty supports are allowed. -/
theorem finiteSupportCover (R : Type (u + 1)) [Ring R]
    {X T : Scheme.{u}} (Q : X.ProEt) [CompactSpace Q.left] [QuasiSeparatedSpace Q.left]
    (q : Q.left ⟶ T) (U : T.Opens)
    (F : Sheaf (topology X) (ModuleCat.{u + 1} R)) (s : F.obj.obj (op Q))
    (S : Sieve Q) (hS : S ∈ topology X Q)
    (h : ∀ (Z : X.ProEt) (f : Z ⟶ Q), S f →
      Set.range (f.left ≫ q) ⊆ U ∨ F.obj.map f.op s = 0) :
    ∃ (O : T.Opens), IsCompact (O : Set T) ∧ O ≤ U ∧
      ∃ (I : Type (u + 1)) (_ : Finite I) (Z : I → X.ProEt) (f : ∀ i, Z i ⟶ Q),
        Sieve.ofArrows Z f ∈ topology X Q ∧
        ∀ i, Set.range ((f i).left ≫ q) ⊆ O ∨ F.obj.map (f i).op s = 0 := by
  classical
  obtain ⟨S₀, hS₀, hS₀S⟩ := mem_topology_iff.mp hS
  let E := S₀.preZeroHypercover
  let forgetSite := ProEt.forget X ⋙ Over.forget X
  let E' := E.map forgetSite
  have hE' : E'.presieve₀ ∈ Scheme.proetalePrecoverage Q.left := by
    have he : E'.presieve₀ = Presieve.map forgetSite S₀ := by
      dsimp only [E']
      rw [PreZeroHypercover.presieve₀_map]
      exact congrArg (Presieve.map forgetSite) S₀.presieve₀_preZeroHypercover
    rw [he]
    exact hS₀
  let C : Q.left.Cover (Scheme.precoverage @WeaklyEtale) := ⟨E', hE'.2⟩
  let : QuasiCompactCover C.toPreZeroHypercover :=
    Scheme.presieve₀_mem_qcPrecoverage_iff.mp hE'.1
  obtain ⟨B, r, hfin, _⟩ := QuasiCompactCover.exists_hom C
  let := hfin
  have (i : B.I₀) : QuasiCompact (B.cover.f i) := by
    apply quasiCompact_of_compactSpace
  have : Finite B.cover.I₀ := hfin
  have : QuasiCompactCover B.cover.toPreZeroHypercover := .of_finite
  have (i : B.I₀) : WeaklyEtale (B.f i) := B.cover.map_prop i
  let Z : B.I₀ → X.ProEt := fun i ↦ ProEt.mk (B.f i ≫ Q.hom)
  let f : ∀ i, Z i ⟶ Q := fun i ↦ MorphismProperty.Over.homMk (B.f i) (by rfl)
  have hf (i : B.I₀) : S (f i) := by
    let e := r.s₀ i
    let g : Z i ⟶ E.X e := MorphismProperty.Over.homMk (r.h₀ i) (by
      change r.h₀ i ≫ (E.X e).hom = B.f i ≫ Q.hom
      have he : r.h₀ i ≫ (E.f e).left = B.f i := r.w₀ i
      rw [← he, Category.assoc]
      congr 1
      simp)
    have hg : g ≫ E.f e = f i := by
      apply (ProEt.forget X).map_injective
      apply Over.OverMorphism.ext
      exact r.w₀ i
    rw [← hg]
    exact S.downward_closed (hS₀S _ _ e.2) g
  let K (i : B.I₀) : Set T :=
    if F.obj.map (f i).op s = 0 then ∅ else Set.range ((f i).left ≫ q)
  have hK (i : B.I₀) : IsCompact (K i) := by
    dsimp only [K]
    split_ifs
    · exact isCompact_empty
    · have : IsAffine (Z i).left := inferInstanceAs (IsAffine (Spec _))
      exact isCompact_range ((f i).left ≫ q).continuous
  have hKU : (⋃ i, K i) ⊆ U := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    dsimp only [K] at hi
    split_ifs at hi with hz
    · exact False.elim (Set.notMem_empty x hi)
    · exact (h (Z i) (f i) (hf i)).resolve_right hz hi
  obtain ⟨O, hOc, hOo, hKO, hOU⟩ :=
    PrespectralSpace.exists_isCompact_and_isOpen_between (isCompact_iUnion hK) U.isOpen hKU
  refine ⟨⟨O, hOo⟩, hOc, hOU, B.I₀, hfin, Z, f, ?_, ?_⟩
  · apply Precoverage.generate_mem_toGrothendieck
    change Presieve.map forgetSite (Presieve.ofArrows Z f) ∈
      Scheme.proetalePrecoverage Q.left
    rw [Presieve.map_ofArrows]
    change B.cover.presieve₀ ∈ Scheme.proetalePrecoverage Q.left
    exact ⟨Scheme.presieve₀_mem_qcPrecoverage_iff.mpr inferInstance, B.cover.mem₀⟩
  · intro i
    by_cases hz : F.obj.map (f i).op s = 0
    · exact Or.inr hz
    · left
      intro x hx
      apply hKO
      exact Set.mem_iUnion.mpr ⟨i, by simpa only [K, ite_eq_right hz] using hx⟩

end AlgebraicGeometry.Scheme.ProEt
