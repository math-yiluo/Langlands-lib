/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomological.CohomologicalDimensionSupplement
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Filtered.Basic
public import Mathlib.CategoryTheory.Limits.IsLimit
import Mathlib.AlgebraicGeometry.AffineTransitionLimit
import WeilConjectures.AlgebraicGeometry.Etale.EtaleCohomologyContinuity
import WeilConjectures.AlgebraicGeometry.EtaleSheafHExtDerivedComparison
import WeilConjectures.AlgebraicGeometry.Affine.Limit.AffineLimitSheafReconstruction
import WeilConjectures.AlgebraicGeometry.Curve.HighDegreeVanishing
import WeilConjectures.AlgebraicGeometry.Sites.TorsionSheaf

/-!
# Torsion cohomological dimension at an affine inverse limit

Source: literature/blueprint/master/blueprint/sec-smooth-purity/sk-prop-sf-cbc/
lem-sc-cd-affine-limit.md (blueprint: lemma-uniform-bounds-pro-etale-affines).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A uniform torsion étale cohomological dimension bound passes to a cofiltered
limit of quasi-compact quasi-separated schemes with affine transition morphisms.

Source: blueprint sec-smooth-purity/sk-prop-sf-cbc, lemma lemma-uniform-bounds-pro-etale-affines,
statement and proof (blueprint: lemma-uniform-bounds-pro-etale-affines).

Proof:
1. Mathlib's affine-limit results show that the limit is qcqs. Construct the
   pull-push approximations p_i^* p_i* F with their adjunction transitions.
   The reconstruction theorem proves that the counit cocone is a colimit:
   direct images are jointly faithful by descent of affine étale basis objects;
   a germ in a counit kernel becomes zero at a later stage by finite-data descent.
2. If n > 0 kills F, additivity of direct image shows that it kills F_i = p_i* F.
   Hence F_i and all its inverse images are torsion. Étale cohomology continuity
   represents any class in H^q(X, p_i^* F_i) by a class on a later stage.
   The stagewise bound kills that class when q > c. The comparison between
   Sheaf.H and derived étale cohomology identifies the two vanishing statements.
3. Commutation of Sheaf.H with filtered colimits now kills H^q(X, F) for a fixed
   exponent. The existing bounded-exponent reduction for torsion sheaves applies
   this vanishing to the factorial-torsion filtration and gives the result for
   every torsion sheaf. Transport back through the derived comparison. -/
theorem hasTorsionEtaleCohomologicalDimensionLE_of_isLimit
    {I : Type u} [SmallCategory I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
    [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    (s : Cone D) (hs : IsLimit s) (c : ℕ)
    (h : ∀ i : I, HasTorsionEtaleCohomologicalDimensionLE (D.obj i) c) :
    HasTorsionEtaleCohomologicalDimensionLE s.pt c := by
  classical
  have : CompactSpace s.pt := compactSpace_of_isLimit D s hs
  obtain ⟨i₀⟩ := IsCofiltered.nonempty (C := I)
  have : IsAffineHom (s.π.app i₀) := isAffineHom_π_app D s hs i₀
  have : QuasiSeparatedSpace s.pt := quasiSeparatedSpace_of_quasiSeparated (s.π.app i₀)
  intro F hF q hq
  obtain ⟨eH⟩ := nonempty_sheafH_extDerivedIso s.pt q
  have hbounded (G : Sheaf s.pt.smallEtaleTopology AddCommGrpCat.{u + 1})
      (n : ℕ) (hn : 0 < n) (hG : n • 𝟙 G = 0) : Subsingleton (Sheaf.H G q) := by
    let A := Etale.AffineLimitSheafApproximation.approximationDiagram D s G
    obtain ⟨hA⟩ := nonempty_isColimit_affineLimitSheafApproximation D s hs G
    refine subsingleton_of_forall_eq 0 fun x ↦ ?_
    obtain ⟨i, y, rfl⟩ := (H_map_isColimit_of_isFiltered s.pt hA q).1 x
    let Gi := (Etale.lowerStar AddCommGrpCat.{u + 1} (s.π.app i.unop)).obj G
    have hGi : n • 𝟙 Gi = 0 := by
      let L := Etale.lowerStar AddCommGrpCat.{u + 1} (s.π.app i.unop)
      calc
        n • 𝟙 Gi = n • L.map (𝟙 G) := by rw [L.map_id]
        _ = L.map (n • 𝟙 G) := (Functor.map_nsmul L).symm
        _ = 0 := by rw [hG, L.map_zero]
    have htGi : Gi.IsTorsion := isTorsion_of_nsmul_id_eq_zero hn hGi
    have hvan : Subsingleton
        (Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1} (s.π.app i.unop)).obj Gi) q) := by
      refine subsingleton_of_forall_eq 0 fun z ↦ ?_
      obtain ⟨j, f, y, rfl⟩ :=
        (Etale.cohomology_continuity_of_isLimit D s hs i.unop Gi htGi q).1 z
      let Gj := (Etale.upperStar AddCommGrpCat.{u + 1} (D.map f)).obj Gi
      have : Subsingleton ((DerivedCategory.singleFunctor _ 0 ⋙
          Etale.cohomology AddCommGrpCat.{u + 1} (D.obj j) (q : ℤ)).obj Gj) :=
        h j Gj (Etale.isTorsion_upperStar (D.map f) htGi) q hq
      obtain ⟨ej⟩ := nonempty_sheafH_extDerivedIso (D.obj j) q
      have : Subsingleton (Sheaf.H Gj q) :=
        (ej.app Gj).addCommGroupIsoToAddEquiv.injective.subsingleton
      rw [Subsingleton.elim y 0, map_zero, map_zero]
    have : Subsingleton (Sheaf.H (A.obj i) q) := hvan
    rw [Subsingleton.elim y 0, map_zero]
  have : Subsingleton ((Sheaf.functorH s.pt.smallEtaleTopology q).obj F) :=
    Etale.subsingleton_H_of_isTorsion hF q hbounded
  exact (eH.app F).addCommGroupIsoToAddEquiv.symm.injective.subsingleton

end AlgebraicGeometry.Scheme
