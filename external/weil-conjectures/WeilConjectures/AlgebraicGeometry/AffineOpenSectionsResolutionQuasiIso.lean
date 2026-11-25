/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AlternatingCechTotalComplex
public import WeilConjectures.AlgebraicGeometry.Coherent
import WeilConjectures.AlgebraicGeometry.AffineBasisSectionsDerivedUnit
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Cech

/-! # Affine sections of an unbounded quasi-coherent resolution

Source: Stacks Project, Cohomology, Lemma 08C2, with affine vanishing 01XB.
(blueprint: lem-sc-affine-open-sections-resolution-quasi-iso).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The global-ring module presheaf functor is additive.
Source: Stacks Project, 08C2 (blueprint: lem-sc-affine-open-sections-resolution-quasi-iso).
Proof: its maps apply the given module map on each open; addition is componentwise. -/
instance alternatingCechModulePresheaf_additive (X : Scheme.{u}) :
    (alternatingCechModulePresheaf (X := X)).Additive where
  map_add := by
    intro F G f g
    ext V x
    rfl

private theorem quasiCoherent_homology (X : Scheme.{u})
    (F : CochainComplex X.Modules ℤ) (hF : ∀ n : ℤ, (F.X n).IsQuasicoherent)
    (n : ℤ) : (F.homology n).IsQuasicoherent := by
  let S := F.sc n
  have : S.X₁.IsQuasicoherent := hF _
  have : S.X₂.IsQuasicoherent := hF _
  have : S.X₃.IsQuasicoherent := hF _
  have : (kernel S.g).IsQuasicoherent := Scheme.Modules.isQuasicoherent_kernel S.g
  have : (cokernel (kernel.lift S.g S.f S.zero)).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_cokernel _
  exact (SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace)).prop_of_iso
    S.homologyIsoCokernelLift.symm this

private theorem affine_basis_vanishing (X : Scheme.{u}) (M : X.Modules)
    [M.IsQuasicoherent] (W : X.Opens) (hW : IsAffineOpen W) (q : ℕ) :
    Subsingleton ((M.restrict W.ι).H (q + 1)) := by
  have : IsAffine W.toScheme := hW
  have : (M.restrict W.ι).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_restrictFunctor W.ι M
  exact Scheme.Modules.subsingleton_H_succ_of_isAffine (M.restrict W.ι) q

/-- Evaluating a resolution map on an affine open gives a quasi-isomorphism of
complexes of modules over the global section ring.

Source: Stacks Project, Cohomology, Lemma 08C2, and Cohomology of Schemes, 01XB.
(blueprint: lem-sc-affine-open-sections-resolution-quasi-iso).

Proof: Restrict F, J and i to V. Open restriction is exact and preserves
K-injectivity (08BS), so the restricted i is still a K-injective resolution.
Restriction preserves quasi-coherence. Kernels, images and cokernels of maps
between quasi-coherent modules are quasi-coherent. On the basis of affine
opens of V, the terms, differential cokernels, and cohomology sheaves of F
therefore all have vanishing higher cohomology by 01XB. Apply 08C2 to this
basis and the singleton cover of V by itself: all three acyclicity conditions
in that lemma hold, including those on differential cokernels and cohomology.
For the unbounded case, use good truncations tau_ge(-n): the cokernel
vanishing verifies the bounded-below hypotheses. Choose the compatible
K-injective resolution tower of 08C2; its section cohomology is eventually
constant in each degree because the singleton Cech complex has only one
column. The Mittag-Leffler argument in 08C2 identifies the cohomology of
the inverse limit with that constant value. This proves the unbounded
comparison without assuming sections preserve arbitrary quasi-isomorphisms.
It identifies the ordinary section complex of F with its derived sections,
by the actual ordinary-to-derived comparison. Compute derived sections using
the restricted resolution J; compatibility with this comparison identifies
the map with the ordinary sections of i. One may first use a K-injective
resolution with injective terms, then compare it with J by a homotopy
equivalence; the additive section functor preserves that equivalence.
Finally restrict scalars along Gamma(X,O_X) to Gamma(V,O_X). This is exact
and preserves the underlying homology isomorphisms. This gives precisely the
presheaf evaluation in the conclusion. For empty V, both section complexes
are zero. No boundedness or quasi-coherence of the terms of J is needed. -/
theorem affineOpenSections_resolution_quasiIso
    (X : Scheme.{u}) (V : X.Opens) (hV : IsAffineOpen V)
    (F J : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hF : ∀ n : ℤ, (F.X n).IsQuasicoherent)
    [J.IsKInjective] (i : F ⟶ J) [QuasiIso i] :
    QuasiIso (((alternatingCechModulePresheaf (X := X) ⋙
      (CategoryTheory.evaluation X.Opensᵒᵖ
        (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤)))).obj
          (op V)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map i) := by
  let S := SheafOfModules.evaluation.{u} (moduleRings X.toRingedSpace) (op V)
  have : S.Additive := inferInstanceAs
    ((SheafOfModules.forget.{u} (moduleRings X.toRingedSpace) ⋙
      PresheafOfModules.evaluation.{u} (moduleRings X.toRingedSpace).obj (op V)).Additive)
  let : HasDerivedCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
    HasDerivedCategory.standard _
  let : HasDerivedCategory
      (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op V))) :=
    HasDerivedCategory.standard _
  let Q := HomotopyCategory.quotient
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ)
  have : IsIso (S.rightDerivedFunctorUnit.app (Q.obj F)) := by
    apply affineBasisSections_isIso_derivedUnit X V hV F
    · intro W hW _ n q
      have := hF n
      exact affine_basis_vanishing X (F.X n) W hW q
    · intro W hW _ n q
      have := hF (n - 1)
      have := hF n
      have := Scheme.Modules.isQuasicoherent_cokernel (F.d (n - 1) n)
      exact affine_basis_vanishing X (cokernel (F.d (n - 1) n)) W hW q
    · intro W hW _ n q
      have := quasiCoherent_homology X F hF n
      exact affine_basis_vanishing X (F.homology n) W hW q
  have : IsIso (DerivedCategory.Qh.map (Q.map i)) := by
    apply (DerivedCategory.isIso_Qh_map_iff _).mpr
    apply (HomotopyCategory.quotient_map_mem_quasiIso_iff _).mpr
    change QuasiIso i
    infer_instance
  have hmap : IsIso (DerivedCategory.Qh.map
      ((S.mapHomotopyCategory (ComplexShape.up ℤ)).map (Q.map i))) := by
    have hnat := S.rightDerivedFunctorUnit.naturality (Q.map i)
    have : IsIso (DerivedCategory.Qh.map
        ((S.mapHomotopyCategory (ComplexShape.up ℤ)).map (Q.map i)) ≫
        S.rightDerivedFunctorUnit.app (Q.obj J)) := by
      change IsIso (((S.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh).map (Q.map i)) ≫ _)
      rw [hnat]
      dsimp only [Functor.comp_map]
      infer_instance
    exact IsIso.of_isIso_comp_right _ (S.rightDerivedFunctorUnit.app (Q.obj J))
  have : QuasiIso ((S.mapHomologicalComplex (ComplexShape.up ℤ)).map i) := by
    apply (HomotopyCategory.quotient_map_mem_quasiIso_iff _).mp
    exact (DerivedCategory.isIso_Qh_map_iff _).mp hmap
  let A := forget₂
    (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))) AddCommGrpCat
  let B := forget₂
    (ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op V))) AddCommGrpCat
  apply (HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ A).mp
  change QuasiIso ((B.mapHomologicalComplex (ComplexShape.up ℤ)).map
    ((S.mapHomologicalComplex (ComplexShape.up ℤ)).map i))
  infer_instance

end AlgebraicGeometry
