/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import Mathlib.CategoryTheory.Presentable.Directed
import WeilConjectures.AlgebraicGeometry.ConstantModuleSheavesForgetColimits
import WeilConjectures.AlgebraicGeometry.EtaleDirectedCohomologyColimit
import WeilConjectures.AlgebraicGeometry.EtaleSheafHExtDerivedComparison

/-!
# Canonical filtered colimit cocones of restricted cohomology

Source: Stacks Project, Tag 03Q5 (lemma-colimit-cohomology), with the colimit
preservation and module compatibility used in the proof of Tag 03SA(3).
(blueprint: lem-weil-pbc-restricted-cohomology-colimit).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Restricted underlying abelian cohomology carries a supplied filtered colimit
cocone to a colimit cocone. This asserts the universal property, with the canonical
legs, before any representative is selected.
Source: Stacks Project, Tag 03Q5, with Tags 03DB, 03CO and 03D6.
(blueprint: lem-weil-pbc-restricted-cohomology-colimit)

Proof:
1. Forget the module structure in the supplied colimit cocone. Module-sheaf
   colimits are sheafifications of sectionwise colimits, and their underlying
   abelian sheaves have the same colimit universal property (Tags 03DB and 03CO).
2. Apply abelian inverse image, a left adjoint, to this cocone. It preserves
   colimits. The natural compatibility of module inverse image and forgetting
   identifies the result with the underlying abelian restriction of the supplied
   module cocone (Tag 03D6). Naturality identifies each coprojection.
3. Choose a nonempty directed index A' and a final functor F:A'→A using
   `lem-weil-pbc-filtered-category-exists-directed-final`
   (Mathlib `CategoryTheory.IsFiltered.exists_directed`). Clause (1) of
   `lem-weil-pbc-filtered-category-directed-cofinal` explains the resulting
   reindexed colimit cocone. The index remains in universe u+1.
   Here is the filtered-cohomology argument at that size, following the proof
   of `lemma-finiteness-small-etale-topoi--2`. Work on qcqs etale objects,
   where every cover admits a finite qcqs refinement and its finite fibre
   products are qcqs. Sections commute with the directed colimit: local
   representatives and their finitely many matching equalities can all be
   moved to one upper stage. Sheafification therefore supplies no additional
   sections on such an object. This proves the degree-zero comparison.
   Embed the abelian sheaf diagram functorially into injective sheaves J_a,
   and let Q_a be its cokernel diagram. Filtered colimits are exact, so this
   gives a short exact sequence after colimiting. On every finite qcqs cover,
   each term of the Cech complex of colim J_a is the colimit of the Cech terms
   of J_a: sections commute with colimits and the products are finite.
   Each injective's augmented Cech complex is exact; exactness of filtered
   abelian-group colimits gives positive-degree Cech vanishing for colim J_a.
   The Cech vanishing criterion on this basis then makes colim J_a acyclic
   on every qcqs object. Compare the long exact sequences of the stagewise
   short exact sequences and of their colimit. In degree one, both groups
   are the cokernel of the same comparison of degree-zero sections. In each
   higher degree, vanishing for J_a and colim J_a identifies the comparison
   with the preceding-degree comparison for Q_a. Induction simultaneously
   for all sheaf diagrams proves it in every degree. No step bounds the
   cardinality of A': finite upper bounds and exact filtered colimits suffice.
   For the final functor
   F:A'→A supplied by clause (1) of
   `lem-weil-pbc-filtered-category-directed-cofinal`, apply clause (1) of
   `lem-weil-pbc-initial-functor-cofiltered-criterion`: its canonical map from
   the colimit of the reindexed cohomology diagram to the colimit over A is an
   isomorphism.  Equivalently, `Functor.Final.isColimitWhiskerEquiv F t`
   identifies `IsColimit (t.whisker F)` with `IsColimit t`, so colimithood of
   the directed cohomology cocone reflects back to A.  Finally identify derived
   global sections with the Ext-from-the-constant-integer-sheaf description of
   `Sheaf.functorH`, naturally in the sheaf.  The comparison carries every leg
   to `Sheaf.H.map` of that leg, so the displayed image cocone has the colimit
   universal property.

This is only the comparison step; it does not assert element representatives.
For a singleton identity diagram the image cocone is an identity cocone. For
zero coefficients or empty X₀ it is the zero cocone. These are colimits, since
filtered categories are nonempty and connected. No constructibility is needed.
The proof uses the finite-cover/degree induction just described and the natural
Ext comparison; no element representative is selected. -/
theorem restrictedCohomology_isColimit
    {X X₀ : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace X₀] [QuasiSeparatedSpace X₀] (i : X₀ ⟶ X)
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {A : Type (u + 1)} [SmallCategory A] [IsFiltered A]
    {D : A ⥤ Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    {F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (ι : D ⟶ (Functor.const A).obj F)
    (hc : Nonempty (IsColimit (Cocone.mk F ι)))
    (q : ℕ) :
    Nonempty (IsColimit
      (((i)^*[ModuleCat.{u + 1} Λ] ⋙
        sheafCompose X₀.smallEtaleTopology
          (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) ⋙
        Sheaf.functorH X₀.smallEtaleTopology q).mapCocone (Cocone.mk F ι))) := by
  obtain ⟨hc⟩ := hc
  let U := (i)^*[ModuleCat.{u + 1} Λ]
  let V := sheafCompose X₀.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})
  let E := Sheaf.functorH X₀.smallEtaleTopology q
  let c := V.mapCocone (U.mapCocone (Cocone.mk F ι))
  have : PreservesColimitsOfSize.{u + 1, u + 1} V :=
    constantModuleSheaves_forget_preservesColimits X₀ Λ
  have h : IsColimit c := isColimitOfPreserves V (isColimitOfPreserves U hc)
  obtain ⟨I, horder, hdirected, hnonempty, T, hfinal⟩ := IsFiltered.exists_directed A
  let := horder
  let := hdirected
  let := hnonempty
  let := hfinal
  have hT : IsColimit (c.whisker T) :=
    (Functor.Final.isColimitWhiskerEquiv T c).symm h
  obtain ⟨hR⟩ := Scheme.etaleCohomology_isColimit_of_isDirected X₀ hT q
  obtain ⟨e⟩ := Scheme.nonempty_sheafH_extDerivedIso X₀ q
  have hE : IsColimit (E.mapCocone (c.whisker T)) :=
    IsColimit.mapCoconeEquiv e.symm hR
  exact ⟨(Functor.Final.isColimitWhiskerEquiv T (E.mapCocone c)) hE⟩

end AlgebraicGeometry.Etale
