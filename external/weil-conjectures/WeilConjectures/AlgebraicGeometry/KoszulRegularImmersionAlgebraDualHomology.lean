/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import WeilConjectures.AlgebraicGeometry.LocallyRankedExteriorComplex
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import WeilConjectures.AlgebraicGeometry.TensorPullback
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import WeilConjectures.RingTheory.KoszulRegularSequence
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.LinearAlgebra.Dimension.Finrank
import WeilConjectures.AlgebraicGeometry.AffineDerivedHomEvaluationCounit
import WeilConjectures.AlgebraicGeometry.KoszulRegularImmersionDerivedHom
import Mathlib.Algebra.Homology.ShortComplex.Homology
import WeilConjectures.AlgebraicGeometry.DerivedRHomAlgebraModule
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import Mathlib.Topology.Sheaves.LocallySurjective
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.HasSheafComposeForgetCommRingCat

/-! # Cohomology of the algebra-valued Koszul dual

Source: Stacks Project, Tags 0BQZ, 0AX3 and 0AVW.
-/

@[expose] public section

universe u wY wA

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem closedImmersion_scalar_locallySurjective
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i] :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y)
      (Functor.whiskerRight i.c (forget₂ CommRingCat RingCat)) := by
  apply (TopCat.Presheaf.isLocallySurjective_iff _).mpr
  intro U t y hy
  obtain ⟨V, hV, hyV, hVU⟩ := exists_isAffineOpen_mem_and_subset hy
  obtain ⟨s, hs⟩ := i.app_surjective V hV
    (((directImageAlgebraSpace i).presheaf.map (homOfLE hVU).op) t)
  exact ⟨V, hVU, ⟨s, hs⟩, hyV⟩

private noncomputable def scalarRestriction_fullyFaithful
    {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R R' : Sheaf J RingCat.{u}} (α : R ⟶ R')
    [Presheaf.IsLocallySurjective J α.hom] :
    (SheafOfModules.restrictScalars.{u} α).FullyFaithful := by
  refine ⟨(fun {M N} f ↦
    ⟨(PresheafOfModules.restrictHomEquivOfIsLocallySurjective α.hom N.isSheaf).symm
      f.val⟩), ?_, ?_⟩
  · intro M N f
    apply SheafOfModules.hom_ext
    exact (PresheafOfModules.restrictHomEquivOfIsLocallySurjective
      α.hom N.isSheaf).apply_symm_apply f.val
  · intro M N f
    apply SheafOfModules.hom_ext
    exact (PresheafOfModules.restrictHomEquivOfIsLocallySurjective
      α.hom N.isSheaf).symm_apply_apply f.val

/-- The scalar cohomology calculation, without an algebra action or a choice of right adjoint.

Source: Stacks Project, Tag 0BQZ, proof of Lemma 48.15.5
(blueprint: lem-sc-koszul-regular-immersion-algebra-dual-homology).

Proof: Compute derived internal Hom using the same K-injective resolution in both
the given derived universe and the standard derived universe. In the standard universe,
`koszulRegularImmersion_derivedInternalHom` gives the Koszul identification. Apply homology:
the pushed-forward locally-ranked exterior complex has zero differentials, so its
cohomology is its degree term. The comparison with the common Hom complex then transports
this calculation to the given derived universe. No derived category on Z is required in
that given universe. Empty schemes, negative degrees and rank zero are included because
the computation of zero-differential homology works in every degree. -/
private theorem koszulRegularImmersion_scalar_homology
    {Z Y : Scheme.{u}} (i : Z ⟶ Y) [IsClosedImmersion i]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (hregular : ∀ z : Z, ∃ U : Y.affineOpens, i z ∈ U.1 ∧
      ∃ (n : ℕ) (f : Fin n → Γ(Y, U.1)),
        Ideal.span (Set.range f) = i.ker.ideal U ∧
          RingTheory.Sequence.IsKoszulRegular f)
    (r : LocallyConstant Z ℕ)
    (hr : ∀ z : Z, r z = Module.finrank (Z.presheaf.stalk z)
      ((RingedSpace.moduleStalkFunctor Z.toRingedSpace z).obj
        ((Scheme.Modules.tensorPullback i).obj i.ker.toModules))) (n : ℤ) :
    Nonempty ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) n).obj
        ((derivedInternalHom (Opens.grothendieckTopology Y) Y.toRingedSpace.sheaf).obj
          (Opposite.op ((DerivedCategory.singleFunctor
            (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
              ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf))),
            (DerivedCategory.singleFunctor
              (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
                (SheafOfModules.unit Y.ringCatSheaf))) ≅
      (Scheme.Modules.pushforward i).obj
        (Scheme.Modules.locallyRankedExteriorTerm
          (SheafOfModules.homObj (R := Z.sheaf)
            ((Scheme.Modules.tensorPullback i).obj i.ker.toModules)
            (SheafOfModules.unit Z.ringCatSheaf)) r n)) := by
  let A := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let Lc := (HomologicalComplex.single A (.up ℤ) 0).obj
    ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf))
  let Gc := (HomologicalComplex.single A (.up ℤ) 0).obj
    (SheafOfModules.unit Y.ringCatSheaf)
  let : IsGrothendieckAbelian.{u} A := SheafOfModules.isGrothendieckAbelian _
  let I := CochainComplex.kInjectiveResolutionFunctor.{u} A
  let η := CochainComplex.toKInjectiveResolution.{u} A
  let Ic := I.obj Gc
  have : Ic.IsKInjective :=
    CochainComplex.isKInjective_kInjectiveResolutionFunctor_obj.{u} A Gc
  have : QuasiIso (η.app Gc) :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{u} A Gc).2
  let C := CategoryTheory.homComplex (R := Y.sheaf) Lc Ic
  have hc : Nonempty (C.homology n ≅
      (Scheme.Modules.pushforward i).obj
        (Scheme.Modules.locallyRankedExteriorTerm
          (SheafOfModules.homObj (R := Z.sheaf)
            ((Scheme.Modules.tensorPullback i).obj i.ker.toModules)
            (SheafOfModules.unit Z.ringCatSheaf)) r n)) := by
    let := HasDerivedCategory.standard A
    let := HasDerivedCategory.standard
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))
    obtain ⟨e⟩ := koszulRegularImmersion_derivedInternalHom i hregular r hr
    obtain ⟨eR⟩ := derivedInternalHom_obj_iso
      (Opens.grothendieckTopology Y) Y.sheaf
      (DerivedCategory.Q.obj Lc) (DerivedCategory.Q.obj Gc)
      Lc Ic (Iso.refl _) (asIso (DerivedCategory.Q.map (η.app Gc))).symm
    let K := ((Scheme.Modules.pushforward i).mapHomologicalComplex (.up ℤ)).obj
      (Scheme.Modules.locallyRankedExteriorComplex
        (SheafOfModules.homObj (R := Z.sheaf)
          ((Scheme.Modules.tensorPullback i).obj i.ker.toModules)
          (SheafOfModules.unit Z.ringCatSheaf)) r)
    have hf : (K.sc n).f = 0 := by
      dsimp [K, Scheme.Modules.locallyRankedExteriorComplex]
      simp [CochainComplex.of.d]
    have hg : (K.sc n).g = 0 := by
      dsimp [K, Scheme.Modules.locallyRankedExteriorComplex]
      simp [CochainComplex.of.d]
    let z : K.homology n ≅ K.X n :=
      (ShortComplex.HomologyData.ofZeros (K.sc n) hf hg).left.homologyIso
    exact ⟨((DerivedCategory.homologyFunctorFactors A n).app C).symm ≪≫
      (DerivedCategory.homologyFunctor A n).mapIso (eR.symm ≪≫ e) ≪≫
      (DerivedCategory.homologyFunctorFactors A n).app K ≪≫ z⟩
  obtain ⟨eR⟩ := derivedInternalHom_obj_iso
    (Opens.grothendieckTopology Y) Y.sheaf
    (DerivedCategory.Q.obj Lc) (DerivedCategory.Q.obj Gc)
    Lc Ic (Iso.refl _) (asIso (DerivedCategory.Q.map (η.app Gc))).symm
  obtain ⟨ec⟩ := hc
  exact ⟨(DerivedCategory.homologyFunctor A n).mapIso eR ≪≫
    (DerivedCategory.homologyFunctorFactors A n).app C ≪≫ ec⟩

/-- The intrinsic Koszul Ext identifications glue as direct-image-algebra module maps.
This computes cohomology only; it does not identify the derived objects or split
extensions between different cohomological degrees.

Source: Stacks Project, Tag 0BQZ, proof of Lemma 48.15.5; Tag 0AX3 and Tag 0AVW
(blueprint: lem-sc-koszul-regular-immersion-algebra-dual-homology).

Proof:
1. Use `exists_affine_derivedHom_evaluation_counit` for the closed immersion, which
   is affine. Uniqueness of right adjoints transports its cohomology calculation
   to H. Restriction of derived internal Hom to opens gives the local calculation.
   Its algebra action on Hom(i_* OZ,J), for a K-injective resolution J of
   OY, is precomposition by multiplication on i_* OZ.
2. Near a point of Z use a finite free Koszul resolution of the quotient A/I.
   Koszul-regularity makes its augmentation a quasi-isomorphism; bounded finite
   free Hom computes derived sheaf Hom. The dual Koszul cohomology theorem kills
   all degrees except the length n and identifies degree n with the determinant
   of the dual conormal, as an A/I-module. Its intrinsic Ext comparison identifies
   precomposition by multiplication with the ordinary A/I scalar action.
3. The conormal of this quotient is I/I², and the regular generators form a basis
   there. After passing to a stalk on Z its finrank is n. Thus hr gives r(z)=n.
   Restrict to the clopen rank-n locus. Affine module correspondence identifies
   the determinant module with the exterior sheaf of the dual of the recorded
   tensor pullback of the ideal sheaf.
4. The intrinsic Ext comparison is independent of regular generators and commutes
   with localization, by the change-of-generators and localization statements of
   the dual-Koszul theorem. Hence the algebra-linear cohomology identifications
   agree on chart intersections and glue. On the rank-n locus only degree n
   survives, so the result in degree k is precisely the direct image of the
   locallyRankedExteriorTerm in degree k. Negative degrees are zero.
5. Off the closed image of Z the algebra sheaf is zero, and so are all its modules.
   This proves the comparison on all of Y. If Z is empty both sides are zero;
   if the length is zero the calculation is Hom(A,A)=A in degree zero.
No lifting of a cohomology map to a derived morphism is asserted here. -/
theorem koszulRegularImmersion_algebraDual_homology {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [IsNoetherian Y] [IsClosedImmersion i]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [HasDerivedCategory.{wA} (SheafOfModules.{u}
      (moduleRings (directImageAlgebraSpace i)))]
    (hregular : ∀ z : Z, ∃ U : Y.affineOpens, i z ∈ U.1 ∧
      ∃ (n : ℕ) (f : Fin n → Γ(Y, U.1)),
        Ideal.span (Set.range f) = i.ker.ideal U ∧
          RingTheory.Sequence.IsKoszulRegular f)
    (r : LocallyConstant Z ℕ)
    (hr : ∀ z : Z, r z = Module.finrank (Z.presheaf.stalk z)
      ((RingedSpace.moduleStalkFunctor Z.toRingedSpace z).obj
        ((Scheme.Modules.tensorPullback i).obj i.ker.toModules)))
    (H : schemeDerivedCategory Y ⥤ DerivedCategory (SheafOfModules.{u}
      (moduleRings (directImageAlgebraSpace i))))
    (adjH : (SheafOfModules.restrictScalars
      (R := moduleRings Y.toRingedSpace)
      (R' := moduleRings (directImageAlgebraSpace i))
      ⟨Functor.whiskerRight i.c (forget₂ CommRingCat RingCat)⟩).rightDerivedFunctor ⊣ H) (n : ℤ) :
    Nonempty ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace i))) n).obj
        (H.obj ((DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
            (SheafOfModules.unit Y.ringCatSheaf))) ≅
      (RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace i)).obj
        (Scheme.Modules.locallyRankedExteriorTerm
          (SheafOfModules.homObj (R := Z.sheaf)
            ((Scheme.Modules.tensorPullback i).obj i.ker.toModules)
            (SheafOfModules.unit Z.ringCatSheaf)) r n)) := by
  let B : Y.CommAlgebraSheaf := Under.mk (⟨i.c⟩ : Y.sheaf ⟶
    (TopCat.Sheaf.pushforward CommRingCat i.base).obj Z.sheaf)
  let T := SheafOfModules.restrictScalars
    (R := moduleRings Y.toRingedSpace)
    (R' := moduleRings (directImageAlgebraSpace i))
    ⟨Functor.whiskerRight i.c (forget₂ CommRingCat RingCat)⟩
  have : HasDerivedCategory.{wA} (SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology Y)
        (forget₂ CommRingCat RingCat)).obj B.right)) := by
    dsimp [B]
    exact inferInstanceAs (HasDerivedCategory.{wA}
      (SheafOfModules.{u} (moduleRings (directImageAlgebraSpace i))))
  have : PreservesFiniteLimits T := sheafAlgebraRestrictScalars_preservesFiniteLimits Y B
  have : PreservesFiniteColimits T := sheafAlgebraRestrictScalars_preservesFiniteColimits Y B
  have : Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y)
      (Functor.whiskerRight i.c (forget₂ CommRingCat RingCat)) :=
    closedImmersion_scalar_locallySurjective i
  let full := scalarRestriction_fullyFaithful
    (show moduleRings Y.toRingedSpace ⟶ moduleRings (directImageAlgebraSpace i) from
      ⟨Functor.whiskerRight i.c (forget₂ CommRingCat RingCat)⟩)
  obtain ⟨H₀, adj₀, _, hd⟩ := exists_affine_derivedHom_evaluation_counit i
  let OY := (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
      (SheafOfModules.unit Y.ringCatSheaf)
  obtain ⟨d, _⟩ := hd OY
  let eH := Adjunction.rightAdjointUniq adjH adj₀
  let hY := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) n
  obtain ⟨eK⟩ := koszulRegularImmersion_scalar_homology i hregular r hr n
  let e := (T.rightDerivedFunctorHomologyFunctorIso n).app (H.obj OY) ≪≫
    hY.mapIso (T.rightDerivedFunctor.mapIso (eH.app OY)) ≪≫ hY.mapIso d ≪≫ eK
  exact ⟨full.preimageIso e⟩

end AlgebraicGeometry
