/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.AlgebraicGeometry.PerfectPseudoCoherentLocallyFiniteTor
import WeilConjectures.AlgebraicGeometry.QuasiCompactFiniteTorDimension
import Mathlib.CategoryTheory.Localization.Equivalence
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.AlgebraicGeometry.KFlatDerivedTensorComparison
import WeilConjectures.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat
import WeilConjectures.AlgebraicGeometry.RelativeFlatOfStalks
import WeilConjectures.AlgebraicGeometry.FlatSheafStalk
import WeilConjectures.CategoryTheory.DerivedCategory.FlatModel
import WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent

/-! # Eventual finite locally free kernels of an affine lift

Source: Stacks Project, Tag 08EG, the common Tor bound and kernel paragraphs.
(blueprint: lem-sc-affine-lift-eventual-free-kernels).
-/

@[expose] public section

set_option autoImplicit false

universe u w wA

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

@[instance_reducible]
private noncomputable def derivedCategoryOfEquivalence
    {C D : Type u} [Category.{wA} C] [Category.{wA} D] [Abelian C] [Abelian D]
    [HasDerivedCategory.{w} C] (e : C ≌ D) : HasDerivedCategory.{w} D := by
  have : e.functor.Additive := Functor.additive_of_preserves_binary_products _
  have : e.inverse.Additive := Functor.additive_of_preserves_binary_products _
  let ec := e.mapHomologicalComplex (ComplexShape.up ℤ)
  let L := ec.inverse ⋙ DerivedCategory.Q
  have hL : L.IsLocalization (HomologicalComplex.quasiIso D (ComplexShape.up ℤ)) := by
    apply Functor.IsLocalization.of_equivalence_source DerivedCategory.Q
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) L
      (HomologicalComplex.quasiIso D (ComplexShape.up ℤ)) ec
    · intro K K' f hf
      let : QuasiIso f := hf
      exact MorphismProperty.le_isoClosure _ _
        (HomologicalComplex.quasiIso_map_of_preservesHomology _ _)
    · exact e.inverse.mapHomologicalComplex_upToQuasiIso_Q_inverts_quasiIso _
    · exact (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight ec.unitIso.symm _ ≪≫ Functor.leftUnitor _
  exact { L := L }

open MonoidalCategory in
/-- Tensoring with the unit detects ordinary cohomology vanishing. -/
private theorem exactAt_of_tensor_unit_vanishes (Y : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (L : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (E : schemeDerivedCategory Y) (e : DerivedCategory.Q.obj L ≅ E) (i : ℤ)
    (h : letI := SheafOfModules.monoidalCategory Y.sheaf
      schemeDerivedTensorCohomologyVanishes Y E
        (𝟙_ (SheafOfModules.{u} (moduleRings Y.toRingedSpace))) i) : L.ExactAt i := by
  let := SheafOfModules.monoidalCategory Y.sheaf
  obtain ⟨P, _, ⟨eP⟩, hz⟩ := h
  let c := CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _)
    (𝟙_ (SheafOfModules.{u} (moduleRings Y.toRingedSpace))) P ≪≫
    (NatIso.mapHomologicalComplex (rightUnitorNatIso _) (.up ℤ)).app P ≪≫
    (Functor.mapHomologicalComplexIdIso _ (.up ℤ)).app P
  have hp : IsZero (P.homology i) :=
    hz.of_iso ((HomologicalComplex.homologyFunctor _ (.up ℤ) i).mapIso c).symm
  let d : L.homology i ≅ P.homology i :=
    ((DerivedCategory.homologyFunctorFactors _ i).app L).symm ≪≫
    (DerivedCategory.homologyFunctor _ i).mapIso (e ≪≫ eP.symm) ≪≫
    (DerivedCategory.homologyFunctorFactors _ i).app P
  exact (L.exactAt_iff_isZero_homology i).mpr (hp.of_iso d)

open MonoidalCategory in
/-- Finite free module sheaves are flat for the sheaf tensor product. -/
private theorem flat_of_finiteFree (Y : Scheme.{u})
    (M : SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (m : ℕ)
    (e : M ≅ SheafOfModules.free
      (R := moduleRings Y.toRingedSpace) (ULift.{u} (Fin m))) :
    SheafOfModules.IsFlat M := by
  let := SheafOfModules.monoidalCategory Y.sheaf
  let := SheafOfModules.symmetricCategory Y.sheaf
  obtain ⟨⟨mp⟩, ⟨mc⟩, _⟩ := SheafOfModules.tensorClosed Y.sheaf
  let := mp
  let := mc
  have := SheafOfModules.isGrothendieckAbelian (moduleRings Y.toRingedSpace)
  have hf : ObjectProperty.flat
      (SheafOfModules.free (R := moduleRings Y.toRingedSpace) (ULift.{u} (Fin m))) :=
    ObjectProperty.flat_coproduct _ (fun _ ↦ ObjectProperty.prop_unit _)
  exact (ObjectProperty.flat_of_retract ⟨e.hom, e.inv, e.hom_inv_id⟩ hf).2

set_option backward.isDefEq.respectTransparency false in
/-- Opcycles of a finite free complex have a finite presentation by its two defining terms. -/
private theorem finitePresentation_opcycles (Y : Scheme.{u})
    (L : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (hfree : ∀ i : ℤ, ∃ r : ℕ, Nonempty (L.X i ≅ SheafOfModules.free
      (R := moduleRings Y.toRingedSpace) (ULift.{u} (Fin r)))) (i : ℤ) :
    (L.opcycles i).IsFinitePresentation := by
  obtain ⟨m, ⟨em⟩⟩ := hfree (i - 1)
  obtain ⟨n, ⟨en⟩⟩ := hfree i
  let f := em.inv ≫ L.d (i - 1) i ≫ en.hom
  let g := en.inv ≫ L.pOpcycles i
  have hfg : f ≫ g = 0 := by simp [f, g]
  have hg : IsColimit (CokernelCofork.ofπ g hfg) :=
    IsCokernel.ofIso (L.d (i - 1) i) (L.opcyclesIsCokernel (i - 1) i (by simp))
      (CokernelCofork.ofπ g hfg) em en (Iso.refl _) (by simp [f]) (by simp [g])
  let P := SheafOfModules.presentationOfIsCokernelFree f g hfg hg
  have : P.IsFinite := by
    exact ⟨⟨inferInstanceAs (Finite (ULift.{u} (Fin n)))⟩,
      ⟨inferInstanceAs (Finite (ULift.{u} (Fin m)))⟩⟩
  exact P.isFinitePresentation

set_option backward.isDefEq.respectTransparency false in
/-- Finitely presented tensor-flat sheaves are finite locally free. -/
private theorem finiteLocallyFree_of_flat_finitePresentation (Y : Scheme.{u})
    (M : SheafOfModules.{u} (moduleRings Y.toRingedSpace)) [M.IsFinitePresentation]
    (hflat : SheafOfModules.IsFlat M) : M.IsFiniteLocallyFree := by
  apply Modules.isFiniteLocallyFree_of_isAffineOpen
  intro V hV
  have hr : Modules.IsFlatOver (X := Y) M (𝟙 Y) := relative_flat_of_stalks (𝟙 Y) M (by
    intro x
    let := RingedSpace.flat_stalk_of_isFlat Y.toRingedSpace M hflat x
    change Module.Flat (Y.presheaf.stalk x) _
    exact Module.Flat.of_linearEquiv
      (ModuleCat.restrictScalarsId'App ((𝟙 Y : Y ⟶ Y).stalkMap x).hom
        (by simp) ((RingedSpace.moduleStalkFunctor Y.toRingedSpace x).obj M)).toLinearEquiv)
  have hs := hr ⟨V, hV⟩ ⟨V, hV⟩ le_rfl
  change @Module.Flat Γ(Y, V) Γ(M, V) _ _
    (Module.compHom _ ((𝟙 Y : Y ⟶ Y).appLE V V le_rfl).hom) at hs
  have hid : ((𝟙 Y : Y ⟶ Y).appLE V V le_rfl).hom = RingHom.id Γ(Y, V) := by
    simp only [Scheme.Hom.appLE, Scheme.Hom.id_base, Scheme.Hom.id_app,
      homOfLE_refl, op_id, Category.id_comp]
    exact congrArg CommRingCat.Hom.hom (Y.presheaf.map_id (Opposite.op V))
  rw [hid] at hs
  exact ⟨Modules.finitePresentation_sections_of_isFinitePresentation M hV, hs⟩

set_option backward.isDefEq.respectTransparency false in
open MonoidalCategory in
/-- A fixed K-flat model computes the existential tensor-vanishing predicate. -/
private theorem tensor_exactAt_of_vanishes (Y : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (L : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (hL : CochainComplex.IsKFlatTensor (R := Y.sheaf) L)
    (E : schemeDerivedCategory Y) (e : DerivedCategory.Q.obj L ≅ E)
    (G : SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (i : ℤ)
    (h : schemeDerivedTensorCohomologyVanishes Y E G i) :
    letI := SheafOfModules.monoidalCategory Y.sheaf
    (((tensorRight G).mapHomologicalComplex (.up ℤ)).obj L).ExactAt i := by
  let := SheafOfModules.monoidalCategory Y.sheaf
  let N := (HomologicalComplex.single _ (.up ℤ) 0).obj G
  obtain ⟨P, hP, ⟨eP⟩, hz⟩ := h
  obtain ⟨cL⟩ := kFlat_derivedTensor_comparison_natIso Y
    ((Functor.const (Discrete PUnit.{1})).obj L)
    ((Functor.const (Discrete PUnit.{1})).obj N) (fun _ ↦ hL)
  obtain ⟨cP⟩ := kFlat_derivedTensor_comparison_natIso Y
    ((Functor.const (Discrete PUnit.{1})).obj P)
    ((Functor.const (Discrete PUnit.{1})).obj N) (fun _ ↦ hP)
  let d := ((cL.app ⟨PUnit.unit⟩).app ⟨PUnit.unit⟩).symm ≪≫
    tensorIso (e ≪≫ eP.symm) (Iso.refl (DerivedCategory.Q.obj N)) ≪≫
    (cP.app ⟨PUnit.unit⟩).app ⟨PUnit.unit⟩
  have hzL : IsZero ((CochainComplex.mapBifunctor L N (curriedTensor _)).homology i) :=
    hz.of_iso (((DerivedCategory.homologyFunctorFactors _ i).app _).symm ≪≫
      (DerivedCategory.homologyFunctor _ i).mapIso d ≪≫
      (DerivedCategory.homologyFunctorFactors _ i).app _)
  exact ((HomologicalComplex.exactAt_iff_isZero_homology _ i).mpr hzL).of_iso
    (CochainComplex.mapBifunctorSingle₂Iso (curriedTensor _) G L)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The restricted finite-free lift is exact in all sufficiently low degrees, and
its outgoing kernels in those degrees are finite locally free.
Source: Stacks Project, Tag 08EG, first two paragraphs of the proof of Lemma 36.13.6.
(blueprint: lem-sc-affine-lift-eventual-free-kernels).

Proof: Perfectness gives locally finite Tor dimension. Compactness of U gives a
common Tor interval [a,b]. Let L be the termwise restricted complex. Exact
restriction identifies Q(L) with F. Tensoring a K-flat representative with the
unit computes ordinary homology, so L is exact below a. Restriction preserves
finite free sheaves, and bounded-above finite free complexes are K-flat. Comparing
K-flat tensor models transfers the Tor bound to ordinary L tensor G for every G.
The categorical flat-opcycles criterion makes L.opcycles (r-1) flat for r < a.
Its two finite free defining terms give a finite presentation. Flat stalks and
the affine sections/stalk tensor presentation imply flat affine sections by the
maximal-ideal localization criterion. Thus these opcycles are finite locally free.
Exactness at r-1 makes the opcycles-to-cycles map monic; exactness at r makes it
epic. Its isomorphism identifies the opcycles with the outgoing kernel. Choose
N = a-1. Empty opens and rank-zero terms are included by the same arguments.
No transport of the ambient affine scheme to a spectrum is required.
-/
theorem affine_lift_eventual_free_kernels
    (X : Scheme.{u}) [IsAffine X] (U : X.Opens) (hU : IsCompact (U : Set X))
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ V : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [∀ V : U.toScheme.Opens,
      HasDerivedCategory.{w}
        (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over V))]
    (F : schemeDerivedCategory U.toScheme) (hF : IsPerfect U.toScheme F)
    (K : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hbounded : ∃ N : ℤ, ∀ i : ℤ, N < i → IsZero (K.X i))
    (hfree : ∀ i : ℤ, ∃ r : ℕ, Nonempty (K.X i ≅ SheafOfModules.free
      (R := moduleRings X.toRingedSpace) (ULift.{u} (Fin r))))
    (hrep : Nonempty
      (((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
        Equivalence.functor
          (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
          (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
          (Modules.overEquiv U)).mapDerivedCategory.obj (DerivedCategory.Q.obj K) ≅ F)) :
    let R := (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
      Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
        (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
        (Modules.overEquiv U)
    ∃ N : ℤ, ∀ r : ℤ, r ≤ N →
      (∀ i : ℤ, i ≤ r → ((R.mapHomologicalComplex (.up ℤ)).obj K).ExactAt i) ∧
      (kernel (R.map (K.d r (r + 1)))).IsFiniteLocallyFree := by
  classical
  -- Reuse the sheaf abelian structures throughout the restriction comparisons.
  let _ : Abelian (SheafOfModules.{u} (moduleRings X.toRingedSpace)) := inferInstance
  let _ (V : X.Opens) :
      Abelian (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V)) := inferInstance
  let _ : Abelian (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) :=
    inferInstance
  let R := (SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
    Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Modules.overEquiv U)
  have : R.Additive := Functor.additive_of_preserves_binary_products _
  let openDerived (V : U.toScheme.Opens) :
      HasDerivedCategory.{w}
        (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace)) :=
    derivedCategoryOfEquivalence (Modules.overEquiv V)
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
  obtain ⟨_, hlocal⟩ :=
    perfect_isPseudoCoherent_and_hasLocallyFiniteTorDimension U.toScheme F hF
  obtain ⟨a, b, hab, htor⟩ :=
    hasFiniteTorDimension_of_locallyFinite U.toScheme F hlocal
  obtain ⟨e⟩ := hrep
  let L := (R.mapHomologicalComplex (.up ℤ)).obj K
  let eL : DerivedCategory.Q.obj L ≅ F :=
    (R.mapDerivedCategoryFactors.app K).symm ≪≫ e
  have hexact (i : ℤ) (hi : i < a) : L.ExactAt i := by
    let := SheafOfModules.monoidalCategory U.toScheme.sheaf
    exact exactAt_of_tensor_unit_vanishes U.toScheme L F eL i
      (htor _ i (Or.inl hi))
  have hLfree (i : ℤ) : ∃ n : ℕ, Nonempty (L.X i ≅ SheafOfModules.free
      (R := moduleRings U.toScheme.toRingedSpace) (ULift.{u} (Fin n))) := by
    obtain ⟨n, ⟨en⟩⟩ := hfree i
    refine ⟨n, ⟨R.mapIso en ≪≫ ?_⟩⟩
    exact (Modules.overFunctorEquiv U).app _ ≪≫
      (Modules.restrictFunctorIsoPullback U.ι).app _ ≪≫
      Modules.pullbackFreeIso U.ι _
  have hLb : ∃ n : ℤ, ∀ i : ℤ, n < i → IsZero (L.X i) := by
    obtain ⟨n, hn⟩ := hbounded
    exact ⟨n, fun i hi ↦ R.map_isZero (hn i hi)⟩
  let := SheafOfModules.monoidalCategory U.toScheme.sheaf
  let := SheafOfModules.symmetricCategory U.toScheme.sheaf
  have : MonoidalPreadditive (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) :=
    Classical.choice (SheafOfModules.tensorClosed U.toScheme.sheaf).1
  let : MonoidalClosed (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) :=
    Classical.choice (SheafOfModules.tensorClosed U.toScheme.sheaf).2.1
  have hLflat (i : ℤ) : SheafOfModules.IsFlat (L.X i) := by
    obtain ⟨n, ⟨en⟩⟩ := hLfree i
    exact flat_of_finiteFree U.toScheme (L.X i) n en
  have hLk := CochainComplex.isKFlat_of_boundedAbove_flat_ringedSpace
    U.toScheme.toRingedSpace L hLb hLflat
  have htensor (G : SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (i : ℤ) (hi : i < a) :
      (((MonoidalCategory.tensorRight G).mapHomologicalComplex (.up ℤ)).obj L).ExactAt i :=
    tensor_exactAt_of_vanishes U.toScheme L hLk F eL G i (htor G i (Or.inl hi))
  have hcatflat (i : ℤ) : ObjectProperty.flat (L.X i) := by
    have : PreservesFiniteLimits (MonoidalCategory.tensorRight (L.X i)) := (hLflat i).1
    exact (ObjectProperty.flat_iff_preservesFiniteLimits _).mpr
      (preservesFiniteLimits_of_natIso
        (BraidedCategory.tensorLeftIsoTensorRight (L.X i)).symm)
  refine ⟨a - 1, fun r hr ↦ ⟨fun i hi ↦ hexact i (by omega), ?_⟩⟩
  have hopflat : ObjectProperty.flat (L.opcycles (r - 1)) :=
    ObjectProperty.flat_opcycles_of_exactAt L (r - 1) (hcatflat _) (hcatflat _)
      (fun G ↦ htensor G ((r - 1) - 1) (by omega))
  have : (L.opcycles (r - 1)).IsFinitePresentation :=
    finitePresentation_opcycles U.toScheme L hLfree (r - 1)
  have : (L.opcycles (r - 1)).IsFiniteLocallyFree :=
    finiteLocallyFree_of_flat_finitePresentation U.toScheme _ hopflat.2
  have hprev : (L.sc' (r - 2) (r - 1) r).Exact :=
    (L.exactAt_iff' (r - 2) (r - 1) r (by simp; omega) (by simp)).mp
      (hexact (r - 1) (by omega))
  have hcurr : (L.sc' (r - 1) r (r + 1)).Exact :=
    (L.exactAt_iff' (r - 1) r (r + 1) (by simp) (by simp)).mp
      (hexact r (by omega))
  have hm : Mono (L.fromOpcycles (r - 1) r) := by
    have := hprev.mono_fromOpcycles
    have h := L.opcyclesIsoSc'_inv_fromOpcycles (r - 2) (r - 1) r
      (by simp; omega) (by simp)
    have : Mono ((L.opcyclesIsoSc' (r - 2) (r - 1) r
        (by simp; omega) (by simp)).inv ≫ L.fromOpcycles (r - 1) r) := by
      rw [h]
      infer_instance
    exact (mono_comp_iff_of_isIso _ _).mp this
  have he : Epi (L.toCycles (r - 1) r) := by
    have := hcurr.epi_toCycles
    have h := L.toCycles_cyclesIsoSc'_hom (r - 1) r (r + 1) (by simp) (by simp)
    have : Epi (L.toCycles (r - 1) r ≫
        (L.cyclesIsoSc' (r - 1) r (r + 1) (by simp) (by simp)).hom) := by
      rw [h]
      infer_instance
    exact (epi_comp_iff_of_isIso _ _).mp this
  have hm' : Mono (L.opcyclesToCycles (r - 1) r) :=
    mono_of_mono_fac (L.opcyclesToCycles_iCycles (r - 1) r)
  have he' : Epi (L.opcyclesToCycles (r - 1) r) :=
    epi_of_epi_fac (L.pOpcycles_opcyclesToCycles (r - 1) r)
  have : IsIso (L.opcyclesToCycles (r - 1) r) := isIso_of_mono_of_epi _
  let c : L.opcycles (r - 1) ≅ kernel (L.d r (r + 1)) :=
    asIso (L.opcyclesToCycles (r - 1) r) ≪≫
      L.cyclesIsoSc' (r - 1) r (r + 1) (by simp) (by simp) ≪≫
      (L.sc' (r - 1) r (r + 1)).cyclesIsoKernel
  exact SheafOfModules.IsFiniteLocallyFree.of_iso.{u, u, u} c

end AlgebraicGeometry.Scheme
