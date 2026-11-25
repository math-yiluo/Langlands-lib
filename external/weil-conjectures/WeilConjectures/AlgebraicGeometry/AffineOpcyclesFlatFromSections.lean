/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentCokernel
import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeAffine
import WeilConjectures.AlgebraicGeometry.IntrinsicFlatModuleStalkTensorPresentation

/-! # Flat affine module opcycles give flat sheaf opcycles

Source: Stacks Project, Tags 01IB and 01U4, and step 4 of
lem-pc-affine-universally-exact-opcycles-flat.
-/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
private theorem identity_appLE_self (S : Scheme.{u}) (V : S.Opens) :
    ((𝟙 S : S ⟶ S).appLE V V le_rfl).hom = RingHom.id Γ(S, V) := by
  simp only [Scheme.Hom.appLE, Scheme.Hom.id_base, Scheme.Hom.id_app,
    homOfLE_refl, op_id, Category.id_comp]
  exact congrArg CommRingCat.Hom.hom (S.presheaf.map_id (Opposite.op V))

set_option backward.isDefEq.respectTransparency false in
private theorem flat_sections_of_flat_top (S : Scheme.{u}) (hS : IsAffine S)
    (M : S.Modules) [M.IsQuasicoherent] (hflat : Module.Flat Γ(S, ⊤) Γ(M, ⊤))
    (U : S.affineOpens) : Module.Flat Γ(S, U.1) Γ(M, U.1) := by
  let := hS
  have hmod (V : S.Opens) : Module.compHom Γ(M, V)
      ((𝟙 S : S ⟶ S).appLE V V le_rfl).hom =
      (inferInstance : Module Γ(S, V) Γ(M, V)) := by
    rw [identity_appLE_self]
    rfl
  have hstalk (x : S) : Module.Flat (S.presheaf.stalk x)
      ((RingedSpace.moduleStalkFunctor S.toRingedSpace x).obj M) := by
    let : Algebra Γ(S, ⊤) (S.presheaf.stalk x) :=
      TopCat.Presheaf.algebra_section_stalk S.presheaf ⟨x, by trivial⟩
    have := hflat
    have ht := affine_sections_stalk_tensor_presentation M
      ⟨⊤, isAffineOpen_top S⟩ x (by trivial)
    dsimp only at ht
    rw [hmod] at ht
    obtain ⟨e⟩ := ht
    have : Module.Flat (S.presheaf.stalk x)
        (TensorProduct Γ(S, ⊤) (S.presheaf.stalk x) Γ(M, ⊤)) :=
      Module.Flat.baseChange _ _ _
    exact Module.Flat.of_linearEquiv e.symm
  let B := Γ(S, U.1)
  let x (P : Ideal B) [hP : P.IsMaximal] := U.2.fromSpec ⟨P, hP.isPrime⟩
  have hx (P : Ideal B) [hP : P.IsMaximal] : x P ∈ U.1 :=
    (U.2.isoSpec.inv ⟨P, hP.isPrime⟩).2
  let (P : Ideal B) [P.IsMaximal] : Algebra B (S.presheaf.stalk (x P)) :=
    TopCat.Presheaf.algebra_section_stalk S.presheaf ⟨x P, hx P⟩
  have (P : Ideal B) [hP : P.IsMaximal] :
      IsLocalization.AtPrime (S.presheaf.stalk (x P)) P :=
    U.2.isLocalization_stalk' ⟨P, hP.isPrime⟩ (hx P)
  let N (P : Ideal B) [P.IsMaximal] :=
    TensorProduct B (S.presheaf.stalk (x P)) Γ(M, U.1)
  let f (P : Ideal B) [P.IsMaximal] : Γ(M, U.1) →ₗ[B] N P :=
    TensorProduct.mk B (S.presheaf.stalk (x P)) Γ(M, U.1) 1
  let Hloc : ∀ (P : Ideal B) [P.IsMaximal], IsLocalizedModule.AtPrime P (f P) :=
    fun P _ ↦ by
      dsimp [f, N]
      infer_instance
  refine @Module.flat_of_isLocalized_maximal B B _ _ _ Γ(M, U.1) _ _ _ _
    N _ _ _ _ f Hloc ?_
  intro P hP
  have ht := affine_sections_stalk_tensor_presentation M U (x P) (hx P)
  rw [hmod] at ht
  obtain ⟨e⟩ := ht
  have := hstalk (x P)
  have hN : Module.Flat (S.presheaf.stalk (x P)) (N P) :=
    Module.Flat.of_linearEquiv e
  exact (Module.flat_iff_of_isLocalization (S.presheaf.stalk (x P)) P.primeCompl
    (N P)).mp hN

set_option backward.isDefEq.respectTransparency false in
private noncomputable def sections_cokernel_iso (S : Scheme.{u}) (hS : IsAffine S)
    {M N : S.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent] (φ : M ⟶ N) :
    cokernel ((SheafOfModules.evaluation (R := S.ringCatSheaf) (.op ⊤)).map φ) ≅
      (SheafOfModules.evaluation (R := S.ringCatSheaf) (.op ⊤)).obj (cokernel φ) := by
  let := hS
  let F := SheafOfModules.evaluation (R := S.ringCatSheaf) (.op ⊤)
  let htop := isAffineOpen_top S
  let J := restrictFunctor htop.fromSpec
  let E := moduleSpecΓFunctor (R := Γ(S, ⊤))
  let φ' := J.map φ
  let eM : E.obj (J.obj M) ≅ F.obj M :=
    (sectionsRestrictFromSpecLinearEquiv M htop).toModuleIso
  let eN : E.obj (J.obj N) ≅ F.obj N :=
    (sectionsRestrictFromSpecLinearEquiv N htop).toModuleIso
  have he : E.map φ' ≫ eN.hom = eM.hom ≫ F.map φ := by
    ext x
    change N.presheaf.map _ (φ.app _ x) = φ.app ⊤ (M.presheaf.map _ x)
    exact (congrArg (fun q ↦ q x) (φ.mapPresheaf.naturality
      (homOfLE (show (⊤ : S.Opens) ≤ htop.fromSpec ''ᵁ ⊤ by
        rw [Scheme.Hom.image_top_eq_opensRange, htop.opensRange_fromSpec])).op)).symm
  have : IsIso (J.obj M).fromTildeΓ := isIso_fromTildeΓ_of_isQuasicoherent _
  have : IsIso (J.obj N).fromTildeΓ := isIso_fromTildeΓ_of_isQuasicoherent _
  exact (cokernel.mapIso (E.map φ') (F.map φ) eM eN he).symm ≪≫
    tilde.isoTop (cokernel (E.map φ')) ≪≫
    E.mapIso (tildeCokernelIso φ') ≪≫
    E.mapIso (PreservesCokernel.iso J φ).symm ≪≫
    (sectionsRestrictFromSpecLinearEquiv (cokernel φ) htop).toModuleIso

set_option backward.isDefEq.respectTransparency false in
/-- Transfer flatness of module opcycles to affine-local flatness of sheaf opcycles.
Source: Stacks Project, Tags 01IB (affine equivalence), 01HV (localization of
associated sheaves), and 01U4 (affine-local flatness).
(blueprint: lem-pc-affine-opcycles-flat-from-sections).

Proof: Let P be the global-sections complex and Q its degree-a opcycles.
The counit of the affine quasi-coherent equivalence identifies the two terms
of C defining this cokernel with the sheafifications of their global sections,
naturally in the differential. Sheafification is a left adjoint and preserves
cokernels, so C.opcycles a is the associated sheaf of Q. Localizing a flat
module gives flat stalks over the localized structure rings. On any affine
open U, the prime-local criterion implies that the sections of this associated
sheaf are flat over Gamma(U,O). For affine U contained in affine V, the open
immersion U to V gives a flat map Gamma(V,O) to Gamma(U,O). Transitivity of
module flatness gives flatness of Gamma(U,C.opcycles a) over Gamma(V,O), with
the scalar action obtained by restricting along the identity's appLE. This
proves every test in IsFlatOver(identity). Only the two displayed terms need
quasi-coherence, since opcycles are their cokernel; no other degree or homology
is involved. The empty scheme and zero cokernel are included. -/
theorem affine_opcycles_flat_from_sections (S : Scheme.{u}) (hS : IsAffine S)
    (C : CochainComplex S.Modules ℤ) (a : ℤ)
    (hprev : (C.X (a - 1)).IsQuasicoherent) (hcurr : (C.X a).IsQuasicoherent)
    (hflat : Module.Flat Γ(S, ⊤)
      ((((SheafOfModules.evaluation (R := S.ringCatSheaf) (.op ⊤) :
        S.Modules ⥤ ModuleCat.{u} Γ(S, ⊤)).mapHomologicalComplex
        (.up ℤ)).obj C).opcycles a)) :
    (C.opcycles a).IsFlatOver (𝟙 S) := by
  let := hprev
  let := hcurr
  let F : S.Modules ⥤ ModuleCat.{u} Γ(S, ⊤) :=
    SheafOfModules.evaluation (R := S.ringCatSheaf) (.op ⊤)
  have : F.PreservesZeroMorphisms := ⟨fun _ _ ↦ rfl⟩
  let P := (F.mapHomologicalComplex (.up ℤ)).obj C
  let eC : C.opcycles a ≅ cokernel (C.d (a - 1) a) :=
    (C.opcyclesIsCokernel (i := a - 1) (j := a) (by simp)).coconePointUniqueUpToIso
      (colimit.isColimit _)
  let eP : P.opcycles a ≅ cokernel (F.map (C.d (a - 1) a)) :=
    (P.opcyclesIsCokernel (i := a - 1) (j := a) (by simp)).coconePointUniqueUpToIso
      (colimit.isColimit _)
  have hqc : (cokernel (C.d (a - 1) a)).IsQuasicoherent := isQuasicoherent_cokernel _
  have : (C.opcycles a).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).prop_of_iso eC.symm hqc
  let e : P.opcycles a ≅ F.obj (C.opcycles a) :=
    eP ≪≫ sections_cokernel_iso S hS (C.d (a - 1) a) ≪≫ F.mapIso eC.symm
  have := hflat
  have htop : Module.Flat Γ(S, ⊤) Γ(C.opcycles a, ⊤) :=
    Module.Flat.of_linearEquiv e.toLinearEquiv.symm
  intro V U hUV
  let := ((𝟙 S : S ⟶ S).appLE V.1 U.1 hUV).hom.toAlgebra
  have : Module.Flat Γ(S, V.1) Γ(S, U.1) :=
    HasRingHomProperty.appLE @Flat (𝟙 S) inferInstance V U hUV
  have := flat_sections_of_flat_top S hS (C.opcycles a) htop U
  let : Module Γ(S, V.1) Γ(C.opcycles a, U.1) :=
    Module.compHom _ ((𝟙 S : S ⟶ S).appLE V.1 U.1 hUV).hom
  have : IsScalarTower Γ(S, V.1) Γ(S, U.1) Γ(C.opcycles a, U.1) :=
    ⟨fun r b m ↦ mul_smul _ _ _⟩
  exact Module.Flat.trans Γ(S, V.1) Γ(S, U.1) Γ(C.opcycles a, U.1)

end AlgebraicGeometry.Scheme.Modules
