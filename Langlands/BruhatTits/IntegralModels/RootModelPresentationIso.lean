import Langlands.BruhatTits.IntegralModels.RootFiltrationModelComparison
import Langlands.BruhatTits.IntegralModels.RootDepthKernelStatement
import Langlands.GroupScheme.IntegralModel.FixedFieldExtension
import Langlands.GroupScheme.IntegralModel.SmoothHomExtensionProof
import Langlands.GroupScheme.IntegralModel.SpecialFibreKernelIso
import Langlands.GroupScheme.KernelIsoGeometry
import Langlands.GroupScheme.Reductive.TrivialUnipotentRadical

/-! # Isomorphisms and kernel comparisons for root-model presentations -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.Geometry.Building

namespace Langlands.BruhatTits.IntegralModels.RootFiltrationModelData

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K]
  [Algebra R K] [IsFractionRing R K]
  {S : CommGroupScheme (Spec (CommRingCat.of K))}
  {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom G.X.hom]
  {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] {ω : Kˣ → ℝ}
  {C : KPApartmentData i ω} {x : C.Apartment} {a : relativeRoots i} {r s : ℝ}
  (U : RootFiltrationModelData R K C x a r)
  (V : RootFiltrationModelData R K C x a s)

/-- A generic map commuting with the actual root inclusions is uniquely
determined, even when the supplied representatives differ. -/
theorem genericMap_eq (f : U.rootGroup ⟶ V.rootGroup)
    (hf : f ≫ V.inclusion = U.inclusion) :
    f = (U.genericIso V).hom := by
  have : Mono V.inclusion.hom.hom := V.isRootSubgroup.1
  apply Grp.hom_ext
  apply (cancel_mono V.inclusion.hom.hom).mp
  change (f ≫ V.inclusion).hom.hom =
    ((U.genericIso V).hom ≫ V.inclusion).hom.hom
  rw [hf, U.genericIso_hom_comp V]

/-- The inverse of the canonical generic isomorphism also commutes with the
actual root inclusions. -/
theorem genericIso_inv_comp :
    (U.genericIso V).inv ≫ U.inclusion = V.inclusion := by
  rw [← U.genericIso_hom_comp V, Iso.inv_hom_id_assoc]

/-- Inclusion of the specified ambient filtration groups implies inclusion
of integral-point images under every compatible generic map. -/
theorem map_mem_integralPoints_of_filtration_le
    (h : C.filtration x a r ≤ C.filtration x a s)
    (f : U.rootGroup ⟶ V.rootGroup) (hf : f ≫ V.inclusion = U.inclusion)
    {g : rationalPoints U.rootGroup} (hg : g ∈ U.model.integralPoints) :
    rationalPoints.map f g ∈ V.model.integralPoints := by
  have hg' : rationalPoints.map U.inclusion g ∈ C.filtration x a r := by
    rw [← U.integralPoints_eq]
    exact ⟨g, hg, rfl⟩
  have hg'' := h hg'
  rw [← V.integralPoints_eq] at hg''
  obtain ⟨z, hz, hinc⟩ := hg''
  have : Mono V.inclusion.hom.hom := V.isRootSubgroup.1
  have heq : z = rationalPoints.map f g := by
    apply (cancel_mono V.inclusion.hom.hom).mp
    change rationalPoints.map V.inclusion z =
      rationalPoints.map V.inclusion (rationalPoints.map f g)
    rw [hinc]
    simp only [rationalPoints.map_apply, Category.assoc, ← Grp.comp_hom_hom, hf]
  exact heq ▸ hz

/-- Equal specified filtration subgroups determine compatibly isomorphic
smooth models, conditional only on the extension criterion for the base. -/
def modelIsoOfFiltrationEq
    (hext : IntegralModel.HasSmoothHomExtension (R := R) (L := K))
    (h : C.filtration x a r = C.filtration x a s) :
    U.model.Iso V.model (U.genericIso V) :=
  IntegralModel.Iso.ofHoms
    (Classical.choice (hext U.rootGroup V.rootGroup (U.genericIso V).hom
      U.model V.model U.smooth (fun _ hg =>
        U.map_mem_integralPoints_of_filtration_le V h.le _
          (U.genericIso_hom_comp V) hg)))
    (Classical.choice (hext V.rootGroup U.rootGroup (U.genericIso V).inv
      V.model U.model V.smooth (fun _ hg =>
        V.map_mem_integralPoints_of_filtration_le U h.symm.le _
          (U.genericIso_inv_comp V) hg)))

section Squares

variable
  (U' : RootFiltrationModelData R K C x a r)
  (V' : RootFiltrationModelData R K C x a s)

/-- The canonical generic presentation identifications intertwine all maps
that commute with their ambient root inclusions. -/
theorem genericMap_square
    (f : V.rootGroup ⟶ U.rootGroup) (hf : f ≫ U.inclusion = V.inclusion)
    (f' : V'.rootGroup ⟶ U'.rootGroup) (hf' : f' ≫ U'.inclusion = V'.inclusion) :
    (V.genericIso V').hom ≫ f' = f ≫ (U.genericIso U').hom := by
  have : Mono U'.inclusion.hom.hom := U'.isRootSubgroup.1
  apply Grp.hom_ext
  apply (cancel_mono U'.inclusion.hom.hom).mp
  change (((V.genericIso V').hom ≫ f') ≫ U'.inclusion).hom.hom =
    ((f ≫ (U.genericIso U').hom) ≫ U'.inclusion).hom.hom
  simp only [Category.assoc, hf', U.genericIso_hom_comp U',
    V.genericIso_hom_comp V', hf]

/-- The integral presentation identifications intertwine every compatible
pair of depth maps; generic rigidity supplies the integral square. -/
theorem modelIso_square
    (hext : IntegralModel.HasSmoothHomExtension (R := R) (L := K))
    (f : V.rootGroup ⟶ U.rootGroup) (hf : f ≫ U.inclusion = V.inclusion)
    (f' : V'.rootGroup ⟶ U'.rootGroup) (hf' : f' ≫ U'.inclusion = V'.inclusion)
    (φ : V.model.Hom U.model f) (ψ : V'.model.Hom U'.model f') :
    (V.modelIsoOfFiltrationEq V' hext rfl).iso.hom ≫ ψ.hom =
      φ.hom ≫ (U.modelIsoOfFiltrationEq U' hext rfl).iso.hom := by
  let e := V.modelIsoOfFiltrationEq V' hext rfl
  let d := U.modelIsoOfFiltrationEq U' hext rfl
  change e.iso.hom ≫ ψ.hom = φ.hom ≫ d.iso.hom
  apply IntegralModel.hom_eq_of_generic
  apply (cancel_mono U'.model.genericIso.hom).mp
  simp only [Functor.map_comp, Category.assoc]
  rw [ψ.generic_comm, ← Category.assoc, e.generic_comm, Category.assoc,
    U.genericMap_square V U' V' f hf f' hf',
    d.generic_comm]
  simpa only [Category.assoc] using
    congrArg (fun q => q ≫ (U.genericIso U').hom) φ.generic_comm.symm

variable [IsLocalRing R]

/-- Actual scheme-theoretic special-fibre kernels are independent of the
chosen root-model presentations. -/
def specialFibreKernelPresentationIso
    (hext : IntegralModel.HasSmoothHomExtension (R := R) (L := K))
    (f : V.rootGroup ⟶ U.rootGroup) (hf : f ≫ U.inclusion = V.inclusion)
    (f' : V'.rootGroup ⟶ U'.rootGroup) (hf' : f' ≫ U'.inclusion = V'.inclusion)
    (φ : V.model.Hom U.model f) (ψ : V'.model.Hom U'.model f') :
    kernel φ.specialFibreMap ≅ kernel ψ.specialFibreMap :=
  kernelSquareIso φ.specialFibreMap ψ.specialFibreMap
    (V.modelIsoOfFiltrationEq V' hext rfl).specialFibreIso
    (U.modelIsoOfFiltrationEq U' hext rfl).specialFibreIso
    (by
      change (GroupScheme.baseChange (IntegralModel.residueBaseMap R)).map
            (V.modelIsoOfFiltrationEq V' hext rfl).iso.hom ≫
          (GroupScheme.baseChange (IntegralModel.residueBaseMap R)).map ψ.hom =
        (GroupScheme.baseChange (IntegralModel.residueBaseMap R)).map φ.hom ≫
          (GroupScheme.baseChange (IntegralModel.residueBaseMap R)).map
            (U.modelIsoOfFiltrationEq U' hext rfl).iso.hom
      simpa only [Functor.map_comp] using congrArg
        (GroupScheme.baseChange (IntegralModel.residueBaseMap R)).map
        (U.modelIso_square V U' V' hext f hf f' hf' φ ψ))

/-- Smoothness, connectedness and unipotence of the actual kernel transfer
from any one presentation to every compatible supplied presentation. -/
theorem specialFibreKernel_properties_of_presentation
    (hext : IntegralModel.HasSmoothHomExtension (R := R) (L := K))
    (f : V.rootGroup ⟶ U.rootGroup) (hf : f ≫ U.inclusion = V.inclusion)
    (f' : V'.rootGroup ⟶ U'.rootGroup) (hf' : f' ≫ U'.inclusion = V'.inclusion)
    (φ : V.model.Hom U.model f) (ψ : V'.model.Hom U'.model f')
    (hψ : Smooth (kernel ψ.specialFibreMap).X.hom ∧
      ConnectedSpace (kernel ψ.specialFibreMap).X.left ∧
        IsUnipotent (kernel ψ.specialFibreMap)) :
    Smooth (kernel φ.specialFibreMap).X.hom ∧
      ConnectedSpace (kernel φ.specialFibreMap).X.left ∧
        IsUnipotent (kernel φ.specialFibreMap) :=
  smooth_connected_unipotent_of_groupIso
    (U.specialFibreKernelPresentationIso V U' V' hext f hf f' hf' φ ψ) hψ

end Squares

section EqualFiltration

variable [IsLocalRing R]

/-- When the filtration subgroups coincide, every compatible depth map is
an isomorphism, and its special-fibre kernel is the trivial group scheme. -/
theorem specialFibreKernel_properties_of_filtration_eq
    (hext : IntegralModel.HasSmoothHomExtension (R := R) (L := K))
    (h : C.filtration x a r = C.filtration x a s)
    (f : V.rootGroup ⟶ U.rootGroup) (hf : f ≫ U.inclusion = V.inclusion)
    (φ : V.model.Hom U.model f) :
    Smooth (kernel φ.specialFibreMap).X.hom ∧
      ConnectedSpace (kernel φ.specialFibreMap).X.left ∧
        IsUnipotent (kernel φ.specialFibreMap) := by
  have hf' := V.genericMap_eq U f hf
  subst f
  let e := V.modelIsoOfFiltrationEq U hext h.symm
  have hφ : φ.hom = e.iso.hom := φ.hom_eq e.toHom
  have : IsIso φ.hom := by rw [hφ]; infer_instance
  have : IsIso φ.specialFibreMap :=
    (GroupScheme.baseChange (IntegralModel.residueBaseMap R)).map_isIso φ.hom
  refine ⟨(smooth_isAffineHom_kernel_of_isIso φ.specialFibreMap).1,
    connectedSpace_kernel_of_isIso φ.specialFibreMap, ?_⟩
  exact isUnipotent_trivial.of_iso
    (asIso (CategoryTheory.Limits.pullback.snd φ.specialFibreMap
      (kernelUnit U.model.specialFibre)))

end EqualFiltration

section Unramified

open Langlands.LocalGalois.Separable

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G₀ : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
  [IsAffineHom G₀.X.hom] {B : MaximalUnramified.BuildingData F G₀}
  {y : B.Apartment} {b : relativeRoots B.i} {t t' : ℝ}
  (P : RootFiltrationModelData (fixedFieldIntegers F) (inertiaFixedField F)
    B.apartment y b t)
  (Q : RootFiltrationModelData (fixedFieldIntegers F) (inertiaFixedField F)
    B.apartment y b t')

/-- The model presentation comparison over the actual maximal-unramified
integers has no unproved extension premise. -/
def unramifiedModelIsoOfFiltrationEq
    (h : B.apartment.filtration y b t = B.apartment.filtration y b t') :
    P.model.Iso Q.model (P.genericIso Q) :=
  P.modelIsoOfFiltrationEq Q
    (IntegralModel.fixedField_hasSmoothHomExtension IntegralModel.smoothHomExtension F) h

/-- Presentation invariance for the actual maximal-unramified base uses
the proved extension theorem, with no additional extension premise. -/
theorem unramifiedSpecialFibreKernel_properties_of_presentation
    (P' : RootFiltrationModelData (fixedFieldIntegers F) (inertiaFixedField F)
      B.apartment y b t)
    (Q' : RootFiltrationModelData (fixedFieldIntegers F) (inertiaFixedField F)
      B.apartment y b t')
    (f : Q.rootGroup ⟶ P.rootGroup) (hf : f ≫ P.inclusion = Q.inclusion)
    (f' : Q'.rootGroup ⟶ P'.rootGroup) (hf' : f' ≫ P'.inclusion = Q'.inclusion)
    (φ : Q.model.Hom P.model f) (ψ : Q'.model.Hom P'.model f')
    (hψ : Smooth (kernel ψ.specialFibreMap).X.hom ∧
      ConnectedSpace (kernel ψ.specialFibreMap).X.left ∧
        IsUnipotent (kernel ψ.specialFibreMap)) :
    Smooth (kernel φ.specialFibreMap).X.hom ∧
      ConnectedSpace (kernel φ.specialFibreMap).X.left ∧
        IsUnipotent (kernel φ.specialFibreMap) :=
  P.specialFibreKernel_properties_of_presentation Q P' Q'
    (IntegralModel.fixedField_hasSmoothHomExtension IntegralModel.smoothHomExtension F)
    f hf f' hf' φ ψ hψ

/-- Equality of the ambient filtration subgroups gives the full kernel
conclusion over the actual maximal-unramified integers. -/
theorem unramifiedSpecialFibreKernel_properties_of_filtration_eq
    (h : B.apartment.filtration y b t = B.apartment.filtration y b t')
    (f : Q.rootGroup ⟶ P.rootGroup) (hf : f ≫ P.inclusion = Q.inclusion)
    (φ : Q.model.Hom P.model f) :
    Smooth (kernel φ.specialFibreMap).X.hom ∧
      ConnectedSpace (kernel φ.specialFibreMap).X.left ∧
        IsUnipotent (kernel φ.specialFibreMap) :=
  P.specialFibreKernel_properties_of_filtration_eq Q
    (IntegralModel.fixedField_hasSmoothHomExtension IntegralModel.smoothHomExtension F)
    h f hf φ

end Unramified

end Langlands.BruhatTits.IntegralModels.RootFiltrationModelData
