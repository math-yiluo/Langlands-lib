/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FormallyUnramifiedConormal
import WeilConjectures.AlgebraicGeometry.OpenRestrictionKernelModule

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- The conormal comparison for the open restriction data.
Source: Stacks Project, More on Morphisms, Lemma 04FA and Definition 01R2
(blueprint: lem-weil-pbc-universal-thickening-open-restriction-conormal).
The restriction of the kernel ideal along an open immersion identifies with the
kernel ideal of the restricted thickening; tensor pullback composition and the
open-immersion pullback/restriction comparison then give the displayed module
isomorphism. Independence of the chosen universal thickening supplies the
formally unramified witness and the displayed `HV`. -/
theorem universalFirstOrderThickening_open_restriction_conormal
    {Z X Z' : Scheme.{u}} (h : Z ⟶ X) (i : Z ⟶ Z') (h' : Z' ⟶ X)
    (H : IsUniversalFirstOrderThickening h i h')
    (hform : FormallyUnramified h)
    {V : Z.Opens} {U : X.Opens}
    {hV : V.toScheme ⟶ U.toScheme} {V' : Z'.Opens}
    {iV : V.toScheme ⟶ V'.toScheme} {hV' : V'.toScheme ⟶ U.toScheme}
    (hdata : i ⁻¹ᵁ V' = V ∧ V' ≤ h' ⁻¹ᵁ U ∧
      iV ≫ V'.ι = V.ι ≫ i ∧ hV' ≫ U.ι = V'.ι ≫ h' ∧
      iV ≫ hV' = hV ∧ IsUniversalFirstOrderThickening hV iV hV') :
    ∃ (hVform : FormallyUnramified hV),
      ∃ (HV : IsUniversalFirstOrderThickening hV iV hV'),
        Nonempty
          ((Scheme.Modules.restrictFunctor V.ι).obj
              (@formallyUnramifiedConormal _ _ _ h hform i h' H) ≅
            @formallyUnramifiedConormal _ _ _ hV hVform iV hV' HV) := by
  have hcompat : i ≫ h' = h := H.2.1
  have hfactor : hV ≫ U.ι = V.ι ≫ h := by
    rw [← hdata.2.2.2.2.1, Category.assoc, hdata.2.2.2.1,
      ← Category.assoc, hdata.2.2.1, Category.assoc, hcompat]
  let : FormallyUnramified h := hform
  have : FormallyUnramified (V.ι ≫ h) :=
    MorphismProperty.comp_mem _ _ _ inferInstance inferInstance
  have : FormallyUnramified (hV ≫ U.ι) := by rw [hfactor]; infer_instance
  have hVform : FormallyUnramified hV := FormallyUnramified.of_comp hV U.ι
  let HV := hdata.2.2.2.2.2
  let : IsClosedImmersion i := H.1.1
  let : IsClosedImmersion iV := HV.1.1
  obtain ⟨e⟩ := nonempty_tensorPullback_open_kernel i iV hdata.1 hdata.2.2.1
  let a := (Scheme.Modules.restrictAdjunction V.ι).leftAdjointUniq
    (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction V.ι))
  obtain ⟨b⟩ := Scheme.Modules.nonempty_tensorPullbackComp V.ι i
  obtain ⟨c⟩ := Scheme.Modules.nonempty_tensorPullbackComp iV V'.ι
  have d : Scheme.Modules.tensorPullback (V.ι ≫ i) ≅
      Scheme.Modules.tensorPullback (iV ≫ V'.ι) :=
    eqToIso (congrArg Scheme.Modules.tensorPullback hdata.2.2.1.symm)
  refine ⟨hVform, HV, ⟨?_⟩⟩
  exact a.app _ ≪≫ (b.app _).symm ≪≫ d.app _ ≪≫ c.app _ ≪≫
    (Scheme.Modules.tensorPullback iV).mapIso e

end AlgebraicGeometry
