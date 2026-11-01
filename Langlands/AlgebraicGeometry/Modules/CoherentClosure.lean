import Langlands.AlgebraicGeometry.Modules.QuasicoherentLocal.Closure
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! # Quasi-coherence and finite affine sections under abelian constructions -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace Langlands.AlgebraicGeometry.Modules

namespace QuasicoherentLocal

variable {X : Scheme.{u}}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Quasi-coherence of a restriction gives quasi-coherence on the corresponding slice site. -/
lemma isQuasicoherent_over_of_restrict (M : X.Modules) (U : X.Opens)
    [(M.restrict U.ι).IsQuasicoherent] : (M.over U).IsQuasicoherent := by
  have : IsIso ((U.sheafRestrictSheafEquivOver.app X.ringCatSheaf).inv) :=
    Iso.isIso_inv _
  have (V : Over U) :
      (Over.post U.overEquivalence.functor).IsContinuous
        (((_root_.Opens.grothendieckTopology X).over U).over V)
        ((_root_.Opens.grothendieckTopology ↥U).over (U.overEquivalence.functor.obj V)) := by
    exact Functor.isContinuous_of_coverPreserving (compatiblePreservingOfFlat _ _)
      ((CoverPreserving.of_isContinuous U.overEquivalence.functor
        ((_root_.Opens.grothendieckTopology X).over U)
        (_root_.Opens.grothendieckTopology ↥U)).overPost V)
  have h : ((Scheme.Modules.overEquiv U).inverse.obj (M.restrict U.ι)).IsQuasicoherent := by
    exact SheafOfModules.isQuasicoherent_pushforward_of_isLeftAdjoint
      U.overEquivalence.functor (U.sheafRestrictSheafEquivOver.app X.ringCatSheaf).inv
      (U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf)
      (M := M.restrict U.ι)
  let e : M.over U ≅ (Scheme.Modules.overEquiv U).inverse.obj (M.restrict U.ι) :=
    (Scheme.Modules.overEquiv U).unitIso.app (M.over U) ≪≫
      (Scheme.Modules.overEquiv U).inverse.mapIso ((Scheme.Modules.overFunctorEquiv U).app M)
  exact (SheafOfModules.isQuasicoherent (X.ringCatSheaf.over U)).prop_of_iso e.symm h

/-- Quasi-coherence on every affine open implies global quasi-coherence. -/
lemma IsAffineLocallyQuasicoherent.isQuasicoherent {M : X.Modules}
    (hM : IsAffineLocallyQuasicoherent M) : M.IsQuasicoherent := by
  classical
  obtain ⟨U, hU, hxU⟩ : ∃ U : X → X.Opens,
      (∀ x, IsAffineOpen (U x)) ∧ ∀ x, x ∈ U x := by
    choose U hU hxU hle using fun x : X =>
      (Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens) (show x ∈ (⊤ : X.Opens) from trivial)
    exact ⟨U, hU, hxU⟩
  have hcover : (_root_.Opens.grothendieckTopology X).CoversTop U := by
    apply (_root_.Opens.coversTop_iff X U).2
    apply top_le_iff.mp
    intro x _
    exact Opens.mem_iSup.2 ⟨x, hxU x⟩
  have (x : X) : (M.restrict (U x).ι).IsQuasicoherent := by
    have := hM (U x) (hU x)
    have hQ : ((M.restrict (hU x).fromSpec).restrict (hU x).isoSpec.hom).IsQuasicoherent :=
      inferInstance
    let e : (M.restrict (hU x).fromSpec).restrict (hU x).isoSpec.hom ≅
        M.restrict (U x).ι :=
      ((Scheme.Modules.restrictFunctorComp (hU x).isoSpec.hom (hU x).fromSpec).app M).symm ≪≫
        (Scheme.Modules.restrictFunctorCongr (by
          simp only [IsAffineOpen.fromSpec, Iso.hom_inv_id_assoc])).app M
    exact (SheafOfModules.isQuasicoherent (U x).toScheme.ringCatSheaf).prop_of_iso e hQ
  have (x : X) : (M.over (U x)).IsQuasicoherent := isQuasicoherent_over_of_restrict M (U x)
  exact SheafOfModules.IsQuasicoherent.of_coversTop M U hcover

/-- Kernels of morphisms of quasi-coherent modules are quasi-coherent. -/
lemma isQuasicoherent_kernel {M N : X.Modules} (φ : M ⟶ N)
    [M.IsQuasicoherent] [N.IsQuasicoherent] : (kernel φ).IsQuasicoherent :=
  (IsAffineLocallyQuasicoherent.kernel φ
    (.of_isQuasicoherent M) (.of_isQuasicoherent N)).isQuasicoherent

/-- Cokernels of morphisms of quasi-coherent modules are quasi-coherent. -/
lemma isQuasicoherent_cokernel {M N : X.Modules} (φ : M ⟶ N)
    [M.IsQuasicoherent] [N.IsQuasicoherent] : (cokernel φ).IsQuasicoherent :=
  (IsAffineLocallyQuasicoherent.cokernel φ
    (.of_isQuasicoherent M) (.of_isQuasicoherent N)).isQuasicoherent

/-- Images of morphisms of quasi-coherent modules are quasi-coherent. -/
lemma isQuasicoherent_image {M N : X.Modules} (φ : M ⟶ N)
    [M.IsQuasicoherent] [N.IsQuasicoherent] : (image φ).IsQuasicoherent := by
  have := isQuasicoherent_cokernel φ
  have := isQuasicoherent_kernel (cokernel.π φ)
  exact (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (Abelian.imageIsoImage φ) this

/-- Affine pushforward preserves quasi-coherence. -/
lemma isQuasicoherent_pushforward {Y : Scheme.{u}} (j : Y ⟶ X) [IsAffineHom j]
    (M : Y.Modules) [M.IsQuasicoherent] :
    ((Scheme.Modules.pushforward j).obj M).IsQuasicoherent :=
  (IsAffineLocallyQuasicoherent.pushforward j (.of_isQuasicoherent M)).isQuasicoherent

/-- Binary direct sums of quasi-coherent modules over an affine scheme are quasi-coherent. -/
lemma isQuasicoherent_biprod_spec {R : CommRingCat.{u}} (M N : (Spec R).Modules)
    [M.IsQuasicoherent] [N.IsQuasicoherent] : (M ⊞ N).IsQuasicoherent := by
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts (tilde.functor R)
  let e : (tilde.functor R).obj (moduleSpecΓFunctor.obj M ⊞ moduleSpecΓFunctor.obj N) ≅
      M ⊞ N :=
    (tilde.functor R).mapBiprod _ _ ≪≫
      biprod.mapIso (asIso M.fromTildeΓ) (asIso N.fromTildeΓ)
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso e inferInstance

/-- Binary direct sums of quasi-coherent modules are quasi-coherent. -/
lemma isQuasicoherent_biprod (M N : X.Modules)
    [M.IsQuasicoherent] [N.IsQuasicoherent] : (M ⊞ N).IsQuasicoherent := by
  apply IsAffineLocallyQuasicoherent.isQuasicoherent
  intro V hV
  have := preservesBinaryBiproducts_of_preservesBinaryCoproducts
    (Scheme.Modules.restrictFunctor hV.fromSpec)
  have := isQuasicoherent_biprod_spec (M.restrict hV.fromSpec) (N.restrict hV.fromSpec)
  exact (SheafOfModules.isQuasicoherent (Spec Γ(X, V)).ringCatSheaf).prop_of_iso
    ((Scheme.Modules.restrictFunctor hV.fromSpec).mapBiprod M N).symm this

/-- Global sections of an epimorphism between quasi-coherent modules on an affine
scheme form a surjective linear map. -/
lemma surjective_moduleSpecΓ_map {R : CommRingCat.{u}} {M N : (Spec R).Modules}
    (φ : M ⟶ N) [Epi φ] [M.IsQuasicoherent] [N.IsQuasicoherent] :
    Function.Surjective (moduleSpecΓFunctor.map φ) := by
  let α := Scheme.Modules.fromTildeΓNatTrans (R := R)
  have : IsIso (α.app M) := (inferInstance : IsIso M.fromTildeΓ)
  have : IsIso (α.app N) := (inferInstance : IsIso N.fromTildeΓ)
  have : Epi ((tilde.functor R).map (moduleSpecΓFunctor.map φ) ≫ α.app N) := by
    change Epi ((moduleSpecΓFunctor ⋙ tilde.functor R).map φ ≫ α.app N)
    rw [α.naturality]
    change Epi (α.app M ≫ φ)
    infer_instance
  have : Epi ((tilde.functor R).map (moduleSpecΓFunctor.map φ)) :=
    (epi_comp_iff_of_isIso _ (α.app N)).1 inferInstance
  have : Epi (moduleSpecΓFunctor.map φ) := (tilde.functor R).epi_of_epi_map inferInstance
  exact (ModuleCat.epi_iff_surjective _).1 this

/-- An epimorphism between quasi-coherent modules is surjective on every affine
open's sections. -/
lemma surjective_app_of_epi {M N : X.Modules} (φ : M ⟶ N) [Epi φ]
    [M.IsQuasicoherent] [N.IsQuasicoherent] (V : X.Opens) (hV : IsAffineOpen V) :
    Function.Surjective (φ.app V) := by
  have hsurj := surjective_moduleSpecΓ_map
    ((Scheme.Modules.restrictFunctor hV.fromSpec).map φ)
  have he : hV.fromSpec ''ᵁ ⊤ = V := AffineVanishing.image_fromSpec_top hV
  intro t
  obtain ⟨s, hs⟩ := hsurj
    ((N.restrictAppIso hV.fromSpec ⊤).inv
      (Langlands.Cohomology.Cech.res he.le t))
  refine ⟨Langlands.Cohomology.Cech.res he.ge
    ((M.restrictAppIso hV.fromSpec ⊤).hom s), ?_⟩
  have hh : φ.app (hV.fromSpec ''ᵁ ⊤)
      ((M.restrictAppIso hV.fromSpec ⊤).hom s) =
      Langlands.Cohomology.Cech.res he.le t :=
    congrArg (N.restrictAppIso hV.fromSpec ⊤).hom hs
  rw [← res_app, hh, Langlands.Cohomology.Cech.res_res,
    Langlands.Cohomology.Cech.res_self]

end QuasicoherentLocal

/-- Finite generation of the actual sections over each affine open. -/
def HasFiniteAffineSections {X : Scheme.{u}} (M : X.Modules) : Prop :=
  ∀ U : X.affineOpens, Module.Finite Γ(X, U.1) Γ(M, U.1)

namespace HasFiniteAffineSections

variable {X : Scheme.{u}} {M N : X.Modules}

/-- Finite affine sections are invariant under module isomorphisms. -/
lemma of_iso (e : M ≅ N) (hM : HasFiniteAffineSections M) :
    HasFiniteAffineSections N := by
  intro U
  have : Module.Finite Γ(X, U.1)
      ((SheafOfModules.evaluation.{u} X.ringCatSheaf (op U.1)).obj M) := hM U
  exact Module.Finite.equiv
    ((SheafOfModules.evaluation X.ringCatSheaf (op U.1)).mapIso e).toLinearEquiv

/-- A submodule sheaf of a module with finite affine sections has finite affine
sections on a locally noetherian scheme. -/
lemma of_mono [IsLocallyNoetherian X] (φ : M ⟶ N) [Mono φ]
    (hN : HasFiniteAffineSections N) : HasFiniteAffineSections M := by
  intro U
  have := hN U
  have := IsLocallyNoetherian.component_noetherian U
  let f : Γ(M, U.1) →ₗ[Γ(X, U.1)] Γ(N, U.1) := (φ.val.app (op U.1)).hom
  have : Mono ((PushforwardInjectiveAcyclic.toAbSheaf X).map φ) :=
    (PushforwardInjectiveAcyclic.toAbSheaf X).map_mono φ
  exact Module.Finite.of_injective (σ' := RingHom.id _) f
    (QuasicoherentLocal.injective_app_of_mono
      ((PushforwardInjectiveAcyclic.toAbSheaf X).map φ) U.1)

/-- A quasi-coherent quotient has finite affine sections when its source does. -/
lemma of_epi (φ : M ⟶ N) [Epi φ] [M.IsQuasicoherent] [N.IsQuasicoherent]
    (hM : HasFiniteAffineSections M) : HasFiniteAffineSections N := by
  intro U
  have : Module.Finite (X.ringCatSheaf.obj.obj (op U.1)) (M.val.obj (op U.1)) := hM U
  exact Module.Finite.of_surjective (φ.val.app (op U.1)).hom
    (QuasicoherentLocal.surjective_app_of_epi φ U.1 U.2)

/-- Finite affine sections pass to kernels over a locally noetherian scheme. -/
lemma kernel [IsLocallyNoetherian X] (φ : M ⟶ N)
    (hM : HasFiniteAffineSections M) : HasFiniteAffineSections (Limits.kernel φ) :=
  of_mono (Limits.kernel.ι φ) hM

/-- Finite affine sections pass to cokernels of quasi-coherent module morphisms. -/
lemma cokernel (φ : M ⟶ N) [M.IsQuasicoherent] [N.IsQuasicoherent]
    (hN : HasFiniteAffineSections N) : HasFiniteAffineSections (Limits.cokernel φ) := by
  have := QuasicoherentLocal.isQuasicoherent_cokernel φ
  exact of_epi (Limits.cokernel.π φ) hN

/-- Finite affine sections pass to images over a locally noetherian scheme. -/
lemma image [IsLocallyNoetherian X] (φ : M ⟶ N)
    (hN : HasFiniteAffineSections N) : HasFiniteAffineSections (Limits.image φ) :=
  of_mono (Limits.image.ι φ) hN

/-- Binary direct sums preserve finite affine sections. -/
lemma biprod (hM : HasFiniteAffineSections M) (hN : HasFiniteAffineSections N) :
    HasFiniteAffineSections (M ⊞ N) := by
  intro U
  have := hM U
  have := hN U
  let F := SheafOfModules.evaluation.{u} X.ringCatSheaf (op U.1)
  have := preservesBinaryBiproducts_of_preservesBinaryProducts F
  let e : F.obj (M ⊞ N) ≅ ModuleCat.of Γ(X, U.1) (Γ(M, U.1) × Γ(N, U.1)) :=
    F.mapBiprod M N ≪≫ ModuleCat.biprodIsoProd _ _
  exact Module.Finite.equiv e.symm.toLinearEquiv

end HasFiniteAffineSections

end Langlands.AlgebraicGeometry.Modules
