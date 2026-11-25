/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyExtension
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.DenseOpen
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineSmooth

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.Scheme.FiniteEtale
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedLisseExtensionInertia

/-- The open immersion and fundamental-group surjectivity needed by the reverse extension.
Source: `theorem-purity-real-sheaves-curves` and the projective-line open construction.
(blueprint: lem-dl-a1-condensed-lisse-dense-open-surjectivity).

The source proof obtains regularity and connectedness from the projective-line pullback,
then applies the published surjectivity theorem to the induced open immersion.  The
point is presented over an algebraic closure by transport along the supplied field
embedding, and the resulting path identity is unchanged by that transport. -/
theorem dense_open_pullbackPathHom_surjective
    (D : WeilConjectures.FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime]
    (U₀ C₀ : (ProjectiveLine (Spec (.of D.k₀))).Opens)
    (_hl : l ≠ D.p)
    (_hdense : Dense (U₀ : Set (ProjectiveLine (Spec (.of D.k₀)))))
    (hUC : U₀ ≤ C₀) (U C : Scheme.{u})
    (eU : U ≅ pullback (U₀.ι ≫ ProjectiveLine (Spec (.of D.k₀)) ↘ Spec (.of D.k₀))
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
    (eC : C ≅ pullback (C₀.ι ≫ ProjectiveLine (Spec (.of D.k₀)) ↘ Spec (.of D.k₀))
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))))
    (j₀ : Over.mk (U₀.ι ≫ ProjectiveLine (Spec (.of D.k₀)) ↘ Spec (.of D.k₀)) ⟶
      Over.mk (C₀.ι ≫ ProjectiveLine (Spec (.of D.k₀)) ↘ Spec (.of D.k₀)))
    (hj₀ : j₀.left = (ProjectiveLine (Spec (.of D.k₀))).homOfLE hUC)
    (j : U ⟶ C) (hj : j = eU.hom ≫
      ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀).left ≫
        eC.inv)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (b : Spec (.of Ω) ⟶ U)
    (σ : Aut (fiber (b ≫ j))) :
    ∃ τ : Aut (fiber b), Aut.of (pullbackPathIso j τ.asIso) = σ := by
  have : IsOpenImmersion j := by
    subst hj
    have : IsOpenImmersion j₀.left := by
      rw [hj₀]
      infer_instance
    have : IsOpenImmersion
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))).map j₀).left :=
      inferInstanceAs (IsOpenImmersion
        (pullback.map _ _ _ _ j₀.left (𝟙 _) (𝟙 _) (by simp) (by simp)))
    infer_instance
  have : Nonempty U := ⟨b (IsLocalRing.closedPoint Ω)⟩
  have : Nonempty C := ⟨j (b (IsLocalRing.closedPoint Ω))⟩
  have := SmoothOfRelativeDimension.smooth 1
    (ProjectiveLine (Spec (.of D.k₀)) ↘ Spec (.of D.k₀))
  have : IrreducibleSpace (pullback (C := Scheme.{u})
      (ProjectiveLine (Spec (.of D.k₀)) ↘ Spec (.of D.k₀))
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))) :=
    (Scheme.homeoOfIso ((IsPullback.of_hasPullback _ _).isoIsPullback _ _
      (ProjectiveSpace.isPullback_map _ _)).symm).irreducibleSpace_iff.1 inferInstance
  have : ConnectedSpace C := connectedSpace_of_isOpenImmersion
    (eC.hom ≫ pullback.map (C₀.ι ≫ ProjectiveLine (Spec (.of D.k₀)) ↘ Spec (.of D.k₀))
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k)))
      (ProjectiveLine (Spec (.of D.k₀)) ↘ Spec (.of D.k₀))
      (Spec.map (CommRingCat.ofHom (algebraMap D.k₀ D.k))) C₀.ι (𝟙 _) (𝟙 _) (by simp)
      (by simp))
  have : IsRegular C := IsRegular.of_smooth (eC.hom ≫ pullback.snd _ _)
  have : IsLocallyNoetherian C :=
    LocallyOfFiniteType.isLocallyNoetherian (eC.hom ≫ pullback.snd _ _)
  have := IsRegular.irreducibleSpace C
  have := connectedSpace_of_isOpenImmersion j
  obtain ⟨GU, _, _⟩ := exists_isFundamentalGroup b
  obtain ⟨GC, _, _⟩ := exists_isFundamentalGroup (b ≫ j)
  obtain ⟨g', rfl⟩ := (PreGaloisCategory.toAut_bijective (fiber (b ≫ j)) GC).2 σ
  obtain ⟨g, rfl⟩ :=
    fundamentalGroupMap_surjective_of_isRegular j (pullbackFiberIso j b) GU GC g'
  refine ⟨PreGaloisCategory.toAut (fiber b) GU g, ?_⟩
  ext P x
  obtain ⟨y, rfl⟩ : ∃ y, (pullbackFiberIso j b).hom.app P y = x :=
    ⟨(pullbackFiberIso j b).inv.app P x,
      ConcreteCategory.congr_hom ((pullbackFiberIso j b).inv_hom_id_app P) x⟩
  simp only [pullbackPathIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, ConcreteCategory.comp_apply]
  rw [Iso.hom_inv_id_app_apply, PreGaloisCategory.toAut_hom_app_apply]
  exact (fundamentalGroupMap_smul (pullbackFiberIso j b) GU GC g P y).symm

end AlgebraicGeometry.ProEtale.CondensedLisseExtensionInertia
