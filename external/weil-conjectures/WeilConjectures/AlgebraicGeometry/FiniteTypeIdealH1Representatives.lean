/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.OpenModuleCohomologyDirectedColimit
import WeilConjectures.Compactification.FiniteTypeDirected
import WeilConjectures.AlgebraicGeometry.FiniteTypeIdealDiagram
import WeilConjectures.Topology.ModuleCohomologyTopComparison
import Mathlib.AlgebraicGeometry.Properties

/-! # Finite-type representatives for first cohomology of ideal sheaves

Source: Stacks Project, Tag 01XG, first two sentences of the proof, using
Tags 01PG and 01FF (blueprint: lem-pqf-finite-type-ideal-h1-representatives).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- Every first cohomology class of a quasi-coherent ideal on a qcqs scheme comes
from a finite-type subideal. The morphism is the inclusion of the subideal, as witnessed
by its compatibility with the two inclusions into the structure sheaf.

Source: Stacks Project, Tag 01XG, first two sentences of the proof; Properties,
Tag 01PG; Cohomology, Tag 01FF
(blueprint: lem-pqf-finite-type-ideal-h1-representatives).

Proof:
1. Index the finite-type quasi-coherent subideals of I by inclusion, including the zero
ideal. The sum of two finite-type subideals is a finite-type subideal, so this is a
nonempty directed preorder. Tag 01PG, expressed by `sSup_ofFiniteType_le_eq`, says its
union is I. The transition maps and maps to I are the inclusions of module sheaves.
Their composites with the inclusions into the structure sheaf agree. Affine-locally,
`range_toModulesι_app` identifies their images with the corresponding ideals. Thus the
union assertion gives the colimit universal property for I.toModules: compatible maps
on the subideals glue to a map on their union, uniquely because they cover every local
section. Finite generation of those ideals on affine opens is precisely finite type
of their associated module sheaves, via finite local generators.
2. A scheme has a basis of compact affine opens. The larger collection of all compact
opens is also a basis. Quasi-separatedness makes intersections of compact opens
compact, and compactness of X makes the top open compact. Apply
`openModuleCohomology_directedColimit` to the diagram of step 1 at the top open in
degree 1, using its surjectivity clause.
3. At the top open, module-valued global cohomology and group-valued open cohomology
have the same underlying group. Both are obtained from the same injective module
resolution; the exact forgetful functor from global modules to abelian groups commutes
with homology. This identification is natural in the module sheaf and therefore carries
the structural maps in step 2 to the moduleCohomology maps in the statement. Transport
the representative back across this identification. The index supplies K and its finite
local generators; the colimit map supplies f and its inclusion identity.
The zero ideal belongs to the diagram even when I is zero. For the empty scheme all
cohomology groups are zero, and the zero ideal and zero class give the conclusion. -/
theorem ideal_h1_finiteType_representative (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    (I : X.IdealSheafData) (_hI : I.toModules.IsQuasicoherent)
    (x : (RingedSpace.moduleCohomology X.toRingedSpace 1).obj I.toModules) :
    ∃ (K : X.IdealSheafData), K ≤ I ∧ K.toModules.IsFiniteType ∧
      ∃ (f : K.toModules ⟶ I.toModules)
        (y : (RingedSpace.moduleCohomology X.toRingedSpace 1).obj K.toModules),
        f ≫ I.toModulesι = K.toModulesι ∧
          ((RingedSpace.moduleCohomology X.toRingedSpace 1).map f).hom y = x := by
  let A := {K : X.IdealSheafData // K ≤ I ∧ K.ofFiniteType}
  have : Nonempty A := ⟨⟨⊥, bot_le, IdealSheafData.ofFiniteType_bot⟩⟩
  have : IsDirected A (· ≤ ·) := ⟨fun a b ↦ by
    obtain ⟨K, hK, haK, hbK⟩ := I.directedOn_ofFiniteType_le a.val a.property b.val b.property
    exact ⟨⟨K, hK⟩, haK, hbK⟩⟩
  obtain ⟨D, τ, hc, hstage⟩ := exists_finiteType_ideal_module_diagram X I _hI
  obtain ⟨e⟩ := RingedSpace.nonempty_moduleCohomology_top_iso X.toRingedSpace 1
  let H := RingedSpace.moduleCohomology X.toRingedSpace 1
  obtain ⟨a, z, hz⟩ := (openModuleCohomology_directedColimit X
    PrespectralSpace.isTopologicalBasis D (Cocone.mk I.toModules τ) hc ⊤
    (by simpa using (isCompact_univ : IsCompact (Set.univ : Set X))) 1).1
      ((e.hom.app I.toModules).hom x)
  obtain ⟨hfinite, b, hb⟩ := hstage a
  let w : H.obj (D.obj a) := (e.inv.app (D.obj a)).hom z
  have hw : (H.map (τ.app a)).hom w = x := by
    have hn := congrArg (fun f ↦ f.hom z) (e.inv.naturality (τ.app a))
    change (e.inv.app I.toModules).hom
      (((RingedSpace.openModuleCohomology X.toRingedSpace 1 ⊤).map (τ.app a)).hom z) =
        (H.map (τ.app a)).hom w at hn
    rw [hz] at hn
    rw [← hn]
    exact ConcreteCategory.congr_hom (e.hom_inv_id_app I.toModules) x
  refine ⟨a.val, a.property.1, hfinite, b.inv ≫ τ.app a, (H.map b.hom).hom w, ?_, ?_⟩
  · exact hb
  · change (H.map (b.inv ≫ τ.app a)).hom ((H.map b.hom).hom w) = x
    rw [← LinearMap.comp_apply, ← ModuleCat.hom_comp, ← H.map_comp,
      ← Category.assoc, b.hom_inv_id, Category.id_comp]
    exact hw

end AlgebraicGeometry.Scheme
