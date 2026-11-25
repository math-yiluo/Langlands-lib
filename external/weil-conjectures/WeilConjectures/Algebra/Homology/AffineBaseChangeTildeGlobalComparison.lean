/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.AffineBaseChangeTildeCoordinates
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import WeilConjectures.Algebra.Homology.AffineBaseChangeTildeCanonicalGlobalComparison
import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModelIndependence

/-! # AffineBaseChangeTildeGlobalComparison

Source: Stacks Project, Tag 0DJ8.
(blueprint: lem-pc-affine-base-change-tilde-global-comparison). -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w wM
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
noncomputable section
namespace AlgebraicGeometry

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- The global base-change square for the explicit tensor cohomology module and arrow.
Source: Stacks Project, perfect.tex, Tag 0DJ8, affine proof; Tags 08HY and 06Y6.
(blueprint: lem-pc-affine-base-change-tilde-global-comparison).

Proof: use an R-K-flat resolution of the restricted M. The universal property of
m.derived identifies it, compatibly with m.counit, with the module scalar-extension
derived functor. Exact tilde identifies its cohomology with tilde of the restriction
of m.cohomology. The cartesian tensor-algebra isomorphism transports that module to
U. The canonical affine direct-image comparison is natural: affine vanishing and
the unbounded bound N=1 identify H(Rf'_*) with f'_*H, and the tilde/Gamma counit
identifies f'_*H with restriction of its cohomology module. This gives d and eU.
On the common K-flat span, the derived base-change mate is scalar extension of the
ordinary tensor comparison. The defining equation m.comparison_eq identifies it
with m.comparison; m.localized_eq identifies its extension to A' with the specified
module arrow. The target coordinate is the inverse pullback counit followed by e,
exactly affineBaseChangeTildeCohomologyIso. Applying H therefore gives the displayed
square. No stalk calculation is needed here. The construction uses no boundedness,
Tor independence or nonzero-ring hypothesis. -/
theorem exists_affineBaseChangeTildeGlobalComparison
    (R A R' A' : Type u) [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
    [Algebra R A] [Algebra R R'] [Algebra (A ⊗[R] R') A']
    [HasDerivedCategory.{wM} (ModuleCat.{u} R)]
    [HasDerivedCategory.{wM} (ModuleCat.{u} R')]
    (φg' : A →+* A') (φf' : R' →+* A')
    (hφg' : (algebraMap (A ⊗[R] R') A').comp
      (algebraMap A (A ⊗[R] R')) = φg')
    (hφf' : (algebraMap (A ⊗[R] R') A').comp
      Algebra.TensorProduct.includeRight.toRingHom = φf')
    (sq : IsPullback (Spec.map (CommRingCat.ofHom φg')) (Spec.map (CommRingCat.ofHom φf'))
      (Spec.map (CommRingCat.ofHom (algebraMap R A)))
      (Spec.map (CommRingCat.ofHom (algebraMap R R'))))
    (K : schemeDerivedCategory (Spec (.of A)))
    (hK : schemeDerivedQCohProperty (Spec (.of A)) K)
    (hL : schemeDerivedQCohProperty (Spec (.of A'))
      ((derivedPullback (Spec.map (CommRingCat.ofHom φg'))).obj K))
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (hM : (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat M)
    (e : DerivedCategory.Q.obj
      ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
        (@id (ModuleCat.{u} A ⥤
          SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj M) ≅ K)
    (hc : IsIso ((SingleComplexBaseChange.counit (Spec.map (CommRingCat.ofHom φg'))).app
      ((HomotopyCategory.quotient _ (.up ℤ)).obj ((@Functor.mapHomologicalComplex _ _ _ _ _ _ _
        (@id (ModuleCat.{u} A ⥤
          SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
          (tilde.functor (.of A))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj M)))) (i : ℤ)
    (m : ModuleCat.BaseDerivedTensorCohomologyModel R A R' M A') :
    ∃ d : affineDerivedCohomologyModules A' i ⋙
          (ModuleCat.restrictScalars φf' ⋙ tilde.functor (.of R')) ≅
        (schemeDerivedQCohProperty (Spec (.of A'))).ι ⋙
          schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom φf')) ⋙
          DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings (Spec (.of R')).toRingedSpace)) i,
    let L : schemeDerivedQCohCategory (Spec (.of A')) := ⟨_, hL⟩
    let V := (affineDerivedCohomologyModules A' i).obj L
    let F := ModuleCat.restrictScalars φf' ⋙ tilde.functor (.of R')
    let H := DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (Spec (.of R')).toRingedSpace)) i
    let U := affineBaseChangeTildeModule R A R' A' M m i
    let b := affineBaseChangeTildeCohomologyIso A A' φg' K M e hc i
    let a := affineBaseChangeTildeModuleMap R A R' A' M m φg' hφg' i V b
    ∃ eU : F.obj U ≅ H.obj ((derivedPullback (Spec.map (CommRingCat.ofHom (algebraMap R R')))).obj
        ((schemeDerivedDirectImage (Spec.map (CommRingCat.ofHom (algebraMap R A)))).obj K)),
      eU.hom ≫ H.map (schemeDerivedBaseChangeMap (Spec.map (CommRingCat.ofHom (algebraMap R A)))
        (Spec.map (CommRingCat.ofHom φf')) (Spec.map (CommRingCat.ofHom (algebraMap R R')))
        (Spec.map (CommRingCat.ofHom φg')) sq.w K) = F.map a ≫ d.hom.app L := by
  let m₀ := ModuleCat.baseDerivedTensorCohomologyModel R A R' M A'
  obtain ⟨d, e₀, h₀⟩ := exists_affineBaseChangeTildeCanonicalGlobalComparison
    R A R' A' φg' φf' hφg' hφf' sq K hK hL M hM e hc i
  obtain ⟨s, hs⟩ := ModuleCat.baseDerivedTensorCohomologyModel_localized_independence
    R A R' A' M m m₀ i
  let F := ModuleCat.restrictScalars φf' ⋙ tilde.functor (.of R')
  refine ⟨d, F.mapIso s ≪≫ e₀, ?_⟩
  dsimp only [Iso.trans_hom, Functor.mapIso_hom]
  rw [Category.assoc, h₀, ← Category.assoc, ← F.map_comp]
  congr 1
  dsimp only [affineBaseChangeTildeModuleMap]
  rw [← Category.assoc, ← Category.assoc, hs]
  simp only [Category.assoc]
  rfl


end AlgebraicGeometry
