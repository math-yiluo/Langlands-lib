/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectHomTransport


public import WeilConjectures.AlgebraicGeometry.PerfectHomTransportExtension
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.AlgebraicGeometry.QuasiCompactOpenInduction
import WeilConjectures.AlgebraicGeometry.PerfectHomContinuityAffine
import WeilConjectures.AlgebraicGeometry.PerfectHomContinuityUnion
import WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition

/-! # Continuity of Hom sets for perfect complexes in a ring-colimit system.
Source: Stacks Project, perfect.tex, Tag 09RE, affine calculation and open induction.
(blueprint: lem-pc-perfect-hom-continuity).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The canonical Hom map is surjective on every cofinal tail, and two representatives
with the same image agree on some entire later tail. These are the set-colimit
consequences of continuity of Hom; no isomorphism descent or finite collection of
relations is asserted here.
Source: Stacks Project, perfect.tex, Tag 09RE, proof of lemma-descend-homomorphisms
(blueprint: lem-pc-perfect-hom-continuity).

Proof: Define `PerfectHomContinuityOn` for each open, quantifying over all
perfect pairs and all open-immersion presentations of that open. The affine
case is `perfect_hom_continuity_affine`; the Mayer--Vietoris induction step is
`perfect_hom_continuity_union`. The quasi-compact and quasi-separated structure
map to an affine scheme makes X quasi-compact and quasi-separated. Apply
`quasiCompactOpen_induction` to these two lemmas and the compact top open.
Finally specialize its open-local conclusion to the identity presentation of
X and the given P and Q. The predicate includes every perfect pair, so the
gluing lemma has access to all adjacent shifts; its two input lemmas carry the
remaining affine comparison and exact-sequence compatibility work. -/
theorem perfect_hom_continuity
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (hc : IsColimit c)
    (i : I) (X : Scheme.{u}) (s : X ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation s] [QuasiCompact s] [QuasiSeparated s]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (P Q : schemeDerivedCategory X) (hP : X.IsPerfect P) (hQ : X.IsPerfect Q) :
    (∀ (j₀ : I) (hij₀ : i ≤ j₀)
      (φ : (derivedPullback (pullback.fst s (Spec.map (c.ι.app i)))).obj P ⟶
        (derivedPullback (pullback.fst s (Spec.map (c.ι.app i)))).obj Q),
      ∃ (j : I) (hj₀j : j₀ ≤ j)
        (f : (derivedPullback
            (pullback.fst s (Spec.map (R.map (homOfLE (hij₀.trans hj₀j)))))).obj P ⟶
          (derivedPullback
            (pullback.fst s (Spec.map (R.map (homOfLE (hij₀.trans hj₀j)))))).obj Q),
        perfectLimitMap R c s (hij₀.trans hj₀j) f = φ) ∧
    (∀ (j : I) (hij : i ≤ j)
      (a b : (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE hij))))).obj P ⟶
        (derivedPullback (pullback.fst s (Spec.map (R.map (homOfLE hij))))).obj Q),
      perfectLimitMap R c s hij a = perfectLimitMap R c s hij b →
      ∃ (k : I) (hjk : j ≤ k), ∀ (l : I) (hkl : k ≤ l),
        perfectStageMap R s hij (hjk.trans hkl) a =
          perfectStageMap R s hij (hjk.trans hkl) b) := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace s
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated s
  have htop := quasiCompactOpen_induction X (PerfectHomContinuityOn R c i X s)
    (perfect_hom_continuity_affine R c hc i X s)
    (perfect_hom_continuity_union R c i X s) ⊤
    CompactSpace.isCompact_univ
  have hrange : Scheme.Hom.opensRange (𝟙 X) = ⊤ := by
    ext x
    simp
  exact htop X (𝟙 X) hrange s (by simp) P Q hP hQ

end AlgebraicGeometry
