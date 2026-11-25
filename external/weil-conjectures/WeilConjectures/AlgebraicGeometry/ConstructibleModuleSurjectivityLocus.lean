/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSheafComparisonExtension
import WeilConjectures.AlgebraicGeometry.ConstructibleEtaleModuleSupport
import WeilConjectures.ConstructibleSheaf.KernelCokernel
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Constructible failure locus of a map of constructible module sheaves

Source: Stacks Project, Tag 095N, the subsets T_{I'} in its proof.
(blueprint: lem-weil-pbc-constructible-module-surjectivity-locus).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- The points where a morphism of constructible module sheaves fails to be surjective
on the geometric stalk at the algebraic closure of the residue field form a constructible
subset. The source need not be a sum of affine free sheaves.

Source: Stacks Project, Tag 095N, construction of T_{I'}, with Tags 095E and 04FN.
(blueprint: lem-weil-pbc-constructible-module-surjectivity-locus).

Proof: The cokernel is constructible, since constructible module sheaves form an abelian
subcategory. Exactness of the geometric stalk functor identifies its stalk with the
cokernel of the given stalk map. For modules that cokernel is zero exactly when the map
is surjective. Forgetting scalars preserves and reflects zero stalks. Independence of
vanishing from the choice of geometric point identifies the displayed locus with the
support of the underlying abelian cokernel sheaf. The constructible support theorem
therefore applies. Empty schemes and zero sheaves give the empty failure locus. -/
theorem isConstructible_module_stalk_nonsurjective
    {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]
    (G F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hG : IsConstructibleEtaleModuleSheaf G) (hF : IsConstructibleEtaleModuleSheaf F)
    (g : G ⟶ F) :
    Topology.IsConstructible {x : X | ¬ Function.Surjective
      (((pointSmallEtale (X.algClosurePoint x)).sheafFiber
        (A := ModuleCat.{u + 1} Λ)).map g)}  := by
  have := (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf G).mp hG
  have := (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf F).mp hF
  have hC := (isConstructibleEtaleModuleSheaf_iff_isConstructibleSheaf (cokernel g)).mpr
    (IsConstructibleSheaf.cokernel g)
  let C := (sheafCompose X.smallEtaleTopology
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj (cokernel g)
  obtain ⟨hind, _, hc⟩ := constructibleEtaleModuleSupport (cokernel g) hC
  have heq : {x : X | ¬ Function.Surjective
      (((pointSmallEtale (X.algClosurePoint x)).sheafFiber
        (A := ModuleCat.{u + 1} Λ)).map g)} = etaleSheafSupport C := by
    ext x
    let s := X.algClosurePoint x
    let Q := (pointSmallEtale s).sheafFiber (A := ModuleCat.{u + 1} Λ)
    have hz : IsZero (Q.obj (cokernel g)) ↔ Function.Surjective (Q.map g) := by
      exact (PreservesCokernel.iso Q g).isZero_iff.trans
        ((Preadditive.epi_iff_isZero_cokernel (Q.map g)).symm.trans
          (ModuleCat.epi_iff_surjective _))
    let : PreservesColimitsOfSize.{u, u}
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) :=
      ModuleCat.forget₂PreservesColimitsOfSize.{u + 1, u + 1, u, u} Λ
    let e := ((pointSmallEtale s).sheafFiberCompIso
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).app (cokernel g)
    have hzero : IsZero ((pointSmallEtale s).sheafFiber.obj C) ↔
        Function.Surjective (Q.map g) := by
      refine e.isZero_iff.trans (?_ : IsZero
        ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj
          (Q.obj (cokernel g))) ↔ Function.Surjective (Q.map g))
      rw [AddCommGrpCat.isZero_iff_subsingleton]
      change Subsingleton (Q.obj (cokernel g)) ↔ Function.Surjective (Q.map g)
      exact ModuleCat.isZero_iff_subsingleton.symm.trans hz
    constructor
    · intro hn
      exact ⟨AlgebraicClosure (X.residueField x), inferInstance, inferInstance,
        s, by simp [s], fun h => hn (hzero.mp h)⟩
    · rintro ⟨Ω, hfield, hclosed, s', hs', hn⟩ hsurj
      exact hn ((hind x _ Ω s s' (by simp [s]) hs').mp (hzero.mpr hsurj))
  rw [heq]
  exact hc

end AlgebraicGeometry.Scheme
