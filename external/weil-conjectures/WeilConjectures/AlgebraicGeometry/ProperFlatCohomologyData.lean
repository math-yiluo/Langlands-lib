/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections
import WeilConjectures.AlgebraicGeometry.FiniteAffineCechModelFlatOver
import WeilConjectures.AlgebraicGeometry.FiniteAffineCechModelComparison
import WeilConjectures.AlgebraicGeometry.FlatOverAffineOpenRestriction
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.RingHom.Flat

/-! # Bounded flat models for quasi-compact separated cohomology -/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A finite affine alternating complex gives a bounded flat universal cohomology model.
Properness and finite presentation are not needed for this construction.
Source: Stacks Project, Tags 0A1D and 01XK; the construction preceding Tag 0A1H.
(blueprint: lem-pc-proper-flat-cohomology-model-data).
Proof: choose an affine neighbourhood U of t. Quasi-compactness gives a finite affine
cover of its inverse image; separatedness makes all its nonempty finite intersections
affine. In degree n take the finite direct sum of sections of F on increasing
(n+1)-tuples of members of the cover, with signed restriction differential, and associate
sheaves over U. Above the number of cover members there are no such tuples; negative
terms are zero. The affine local flatness criterion makes the section modules flat over
Gamma(U,O), so their associated sheaves are flat and quasi-coherent. On any affine new
base the inverse-image affine cover has section modules obtained by tensoring these
modules with the new base ring. The alternating complex and its differential therefore
base-change termwise. Affine acyclicity and Cech comparison identify its homology with
higher direct images. These identifications are induced by the Cech augmentation and
hence agree on overlaps, giving the assertion for arbitrary new bases. Transport the
standard fibre-product result along the unique isomorphism associated to the given
cartesian square. An empty inverse image uses the zero complex and d=0. -/
theorem exists_proper_flat_cohomology_model_data {X T : Scheme.{u}} (f : X ⟶ T) (F : X.Modules)
    [IsSeparated f] [QuasiCompact f]
    [HasInjectiveResolutions X.Modules] [F.IsQuasicoherent]
    (hF : F.IsFlatOver f) (t : T) :
    ∃ (U : T.Opens) (C : CochainComplex U.toScheme.Modules ℤ) (d : ℕ),
      t ∈ U ∧ IsAffine U.toScheme ∧ C.IsStrictlyGE 0 ∧ C.IsStrictlyLE d ∧
      (∀ n : ℤ, (C.X n).IsFlatOver (𝟙 U.toScheme)) ∧
      (∀ n : ℤ, (C.X n).IsQuasicoherent) ∧
      ∀ {T' X' : Scheme.{u}} (g : T' ⟶ U.toScheme) (g' : X' ⟶ X) (f' : X' ⟶ T')
        [HasInjectiveResolutions X'.Modules], IsPullback g' f' f (g ≫ U.ι) → ∀ q : ℕ,
        Nonempty ((((Modules.pullback g).mapHomologicalComplex _).obj C).homology q ≅
          (higherDirectImage f' q).obj ((Modules.pullback g').obj F)) := by
  classical
  obtain ⟨U, hU, ht, _⟩ := exists_isAffineOpen_mem_and_subset
    (TopologicalSpace.Opens.mem_top t)
  have : IsAffine U.toScheme := hU
  let Y := (f ⁻¹ᵁ U).toScheme
  have : CompactSpace Y :=
    isCompact_iff_compactSpace.mp (f.isCompact_preimage hU.isCompact)
  let cover := Y.affineCover.finiteSubcover
  let r := Fintype.card cover.I₀
  let index : Fin r ≃ cover.I₀ := (Fintype.equivFin cover.I₀).symm
  let V : Fin r → Y.Opens := fun i ↦ (cover.f (index i)).opensRange
  have hcover : iSup V = ⊤ := by
    simpa [V] using (index.iSup_comp (g := fun i ↦ (cover.f i).opensRange)).trans
      cover.iSup_opensRange
  have hV : ∀ i, IsAffineOpen (V i) := fun i ↦
    isAffineOpen_opensRange (cover.f (index i))
  let G := F.restrict (f ⁻¹ᵁ U).ι
  let C := finiteAffineCechModel (f ∣_ U) G V
  have hchart := isFlatOver_affineOpenRestriction f F hF ⟨U, hU⟩
  let k := hU.isoSpec
  let H := (schemeOpenRestriction X (f ⁻¹ᵁ U)).obj F
  have hchartG : G.IsFlatOver ((f ∣_ U) ≫ k.hom) := by
    let eGH : G ≅ H := ((Scheme.Modules.overFunctorEquiv (f ⁻¹ᵁ U)).app F).symm
    intro W Z e
    let φ := (((f ∣_ U) ≫ k.hom).appLE W.1 Z.1 e).hom
    let : Module Γ(Spec Γ(T, U), W.1) Γ(G, Z.1) := Module.compHom _ φ
    let : Module Γ(Spec Γ(T, U), W.1) Γ(H, Z.1) := Module.compHom _ φ
    have : Module.Flat Γ(Spec Γ(T, U), W.1) Γ(H, Z.1) := hchart W Z e
    let E := (ModuleCat.restrictScalars φ).mapIso
      ((SheafOfModules.evaluation (R := Y.ringCatSheaf) (Opposite.op Z.1)).mapIso eGH)
    exact (Module.Flat.equiv_iff E.toLinearEquiv).mpr (hchart W Z e)
  have hflat : G.IsFlatOver (f ∣_ U) := by
    have hcomp : G.IsFlatOver (((f ∣_ U) ≫ k.hom) ≫ k.inv) := by
      intro W Z e
      let W1 : (Spec Γ(T, U)).affineOpens :=
        ⟨k.inv ⁻¹ᵁ W.1, W.2.preimage_of_isIso k.inv⟩
      have e1 : Z.1 ≤ ((f ∣_ U) ≫ k.hom) ⁻¹ᵁ W1.1 := by
        simpa only [Scheme.Hom.comp_preimage] using e
      let φ := k.inv.app W.1
      let ψ := (((f ∣_ U) ≫ k.hom).appLE W1.1 Z.1 e1)
      let : Module Γ(Spec Γ(T, U), W1.1) Γ(G, Z.1) := Module.compHom _ ψ.hom
      have : Module.Flat Γ(Spec Γ(T, U), W1.1) Γ(G, Z.1) := hchartG W1 Z e1
      let : Algebra Γ(U.toScheme, W.1) Γ(Spec Γ(T, U), W1.1) := φ.hom.toAlgebra
      have : Module.Flat Γ(U.toScheme, W.1) Γ(Spec Γ(T, U), W1.1) :=
        RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso φ)
      let : Module Γ(U.toScheme, W.1) Γ(G, Z.1) := Module.compHom _ φ.hom
      let : IsScalarTower Γ(U.toScheme, W.1) Γ(Spec Γ(T, U), W1.1) Γ(G, Z.1) :=
        ⟨fun a b m ↦ mul_smul _ _ _⟩
      have hh := Module.Flat.trans Γ(U.toScheme, W.1) Γ(Spec Γ(T, U), W1.1) Γ(G, Z.1)
      simpa only [Scheme.Hom.comp_appLE] using hh
    simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using hcomp
  refine ⟨U, C, r, ht, hU, finiteAffineCechModel_ge _ _ _,
    finiteAffineCechModel_le _ _ _, finiteAffineCechModel_flatOver _ _ hflat V hV,
    finiteAffineCechModel_quasicoherent _ _ _, ?_⟩
  exact finiteAffineCechModel_comparison f F U hU V hV hcover

end AlgebraicGeometry.Scheme.Modules
