/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Topology.InverseImageModule
public import WeilConjectures.Algebra.Homology.KFlat
import WeilConjectures.AlgebraicGeometry.InverseImageTensorPullbackComparison
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # Exact inverse image and K-flat resolutions

Source: Stacks Project, Cohomology, Tags 06YI and 06YC.
(blueprint: lem-pc-inverse-image-exact-kflat-resolution).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

set_option synthInstance.maxSize 256 in
private theorem isKFlat_of_iso {X : TopCat.{u}}
    {R : CategoryTheory.Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
    {K L : CochainComplex (SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ}
    (e : K ≅ L) (hK : CochainComplex.IsKFlatTensor (R := R) K) :
    CochainComplex.IsKFlatTensor (R := R) L := by
  let := SheafOfModules.monoidalCategory R
  intro F hF i
  let tensor := (MonoidalCategory.curriedTensor (SheafOfModules.{u}
    ((sheafCompose (Opens.grothendieckTopology X)
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R))).mapBifunctorHomologicalComplex
        (ComplexShape.up ℤ) (ComplexShape.up ℤ)
  exact (hK F hF i).of_iso
    (HomologicalComplex₂.total.mapIso ((tensor.obj F).mapIso e) (ComplexShape.up ℤ))

/-- Exact module inverse image carries K-flat resolutions to K-flat resolutions.
Source: Stacks Project, Cohomology, Tags 06YI and 06YC.

Proof: the inverse-image maps preserve identities, composition and addition because
these identities hold for the underlying abelian inverse-image functor. At each point
of T its stalk is the source stalk at the image point. Stalks detect exactness, so this
additive functor preserves finite limits and colimits, and hence quasi-isomorphisms
of complexes. Apply K-flat pullback preservation to the ringed-space morphism with
ring sheaf g⁻¹ O_S on T and identity adjoint ring map. Tensoring with that same ring
is naturally the identity, identifying this pullback complex with termwise inverse
image. It is therefore K-flat. The two conclusions give preservation of resolutions.
For the empty space the stalk criterion is vacuous and the module category is trivial;
no surjectivity or flatness hypothesis on g is required.
(blueprint: lem-pc-inverse-image-exact-kflat-resolution). -/
theorem exists_inverseImage_exact_kFlat {T S : Scheme.{u}} (g : T ⟶ S) :
    ∃ (I : SheafOfModules.{u} (moduleRings S.toRingedSpace) ⥤
          SheafOfModules.{u} ((sheafCompose (Opens.grothendieckTopology T)
            (forget₂ CommRingCat.{u} RingCat.{u})).obj
              (TopCat.Sheaf.inverseImageRing g.base S.sheaf)))
        (hI : ∀ M, I.obj M = TopCat.Sheaf.inverseImageModule g.base S.sheaf M)
        (_ : ∀ {M N} (a : M ⟶ N),
          I.map a = eqToHom (hI M) ≫
            TopCat.Sheaf.inverseImageModuleMap g.base S.sheaf M a ≫
              eqToHom (hI N).symm)
        (_ : I.Additive),
        PreservesFiniteLimits I ∧ PreservesFiniteColimits I ∧
        (∀ {P G : CochainComplex (SheafOfModules.{u} (moduleRings S.toRingedSpace)) ℤ}
          (s : P ⟶ G), CochainComplex.IsKFlatTensorResolution (R := S.sheaf) s →
            CochainComplex.IsKFlatTensorResolution
              (R := TopCat.Sheaf.inverseImageRing g.base S.sheaf)
              ((I.mapHomologicalComplex (ComplexShape.up ℤ)).map s)) := by
  let I := TopCat.Sheaf.inverseImageModuleFunctor g.base S.sheaf
  obtain ⟨hadd, hlim, hcolim⟩ :=
    TopCat.Sheaf.inverseImageModuleFunctor_exact g.base S.sheaf
  refine ⟨I, fun _ ↦ rfl, ?_, hadd, hlim, hcolim, ?_⟩
  · intro M N a
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  · intro P G s hs
    have : QuasiIso s := hs.1
    refine ⟨inferInstance, ?_⟩
    obtain ⟨e⟩ := TopCat.Sheaf.exists_inverseImage_tensorPullback_iso g.base S.sheaf P
    have hP := CochainComplex.isKFlat_pullback g.base
      (TopCat.Sheaf.inverseImageRing g.base S.sheaf) S.sheaf
      ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (TopologicalSpace.Opens.map g.base) CommRingCat.{u} _ _).unit.app S.sheaf) P hs.2
    exact isKFlat_of_iso (R := TopCat.Sheaf.inverseImageRing g.base S.sheaf) e hP

end AlgebraicGeometry
