/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.AlgebraicGeometry.IdealPowerProductZeroAffineCover
import all WeilConjectures.AlgebraicGeometry.AffineDerivedTildeHomologyComparison
import WeilConjectures.AlgebraicGeometry.Modules.LocallyFreeAffine

/-! # Affine formal gluing comparison

Source: Stacks Project, Tags 087W, 0888 and 0889(1).
(blueprint: lem-weil-pbc-affine-map-annihilation-sheafification).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def affineAssociatedSectionsIso (X : Scheme.{u}) [IsAffine X]
    (M : ModuleCat.{u} Γ(X, ⊤)) :
    M ≃ₗ[Γ(X, ⊤)]
      Γ((Scheme.Modules.pullback X.isoSpec.hom).obj ((tilde.functor Γ(X, ⊤)).obj M), ⊤) := by
  let H := (Scheme.Modules.pullback X.isoSpec.hom).obj ((tilde.functor Γ(X, ⊤)).obj M)
  let e : H.restrict X.isoSpec.inv ≅ (tilde.functor Γ(X, ⊤)).obj M :=
    (Scheme.Modules.restrictFunctor X.isoSpec.inv).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback X.isoSpec.hom).app _).symm ≪≫
    ((Scheme.Modules.restrictFunctorComp X.isoSpec.inv X.isoSpec.hom).symm.app _) ≪≫
    (Scheme.Modules.restrictFunctorCongr X.isoSpec.inv_hom_id).app _ ≪≫
      Scheme.Modules.restrictFunctorId.app _
  let eΓ := (moduleSpecΓFunctor.mapIso e).toLinearEquiv
  let eH := Scheme.Modules.sectionsRestrictFromSpecLinearEquiv H (isAffineOpen_top X)
  let eR :=
    (Scheme.Modules.restrictFunctorCongr (IsAffineOpen.fromSpec_top (X := X))).app H
  exact (tilde.isoTop M).toLinearEquiv ≪≫ₗ eΓ.symm ≪≫ₗ
    (moduleSpecΓFunctor.mapIso eR.symm).toLinearEquiv ≪≫ₗ eH

set_option backward.isDefEq.respectTransparency false in
private theorem idealPower_zero_of_sections_iso {X : Scheme.{u}} [IsAffine X]
    (J : X.IdealSheafData) (H : X.Modules) [H.IsQuasicoherent]
    (M : ModuleCat.{u} Γ(X, ⊤)) (e : M ≃ₗ[Γ(X, ⊤)] Γ(H, ⊤)) (t : ℕ)
    (h : J.ideal ⟨⊤, isAffineOpen_top X⟩ ^ t ≤ Module.annihilator Γ(X, ⊤) M) :
    IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι t).2 H) := by
  apply (Scheme.idealPowerProduct_isZero_iff_affine_cover X H J
    {⟨⊤, isAffineOpen_top X⟩} (fun x ↦ ⟨⟨⊤, isAffineOpen_top X⟩, rfl, trivial⟩) t).mpr
  intro U hU
  have he : U = ⟨⊤, isAffineOpen_top X⟩ := Set.mem_singleton_iff.mp hU
  subst U
  rw [← e.annihilator_eq]
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- Sheafification transfers a fixed annihilating power for an algebraic map.

Source: Stacks Project, Tags 01I7, 01IB and 0889(1).
(blueprint: lem-weil-pbc-affine-map-annihilation-sheafification).

Proof: exactness of tilde identifies its sheaf kernel and cokernel with tilde of
the algebraic kernel and cokernel. The given ideal annihilator inclusions say that
the product by I^t is zero in both modules. The affine ideal-product formula identifies
the sheaf product with tilde of that module product; hence both are zero sheaves.
Transport along the canonical affine scheme isomorphism and along ε. Pullback by
an isomorphism is exact and identifies the ideal sheaf of I with J, so the same
exponent t annihilates the kernel and cokernel of the displayed sheaf map. This
holds for arbitrary T and P; neither coherence nor finite generation is used.
For t=0 it says the kernel and cokernel themselves are zero, and the same argument
applies. The empty scheme is covered by the same exact functors.
-/
theorem affine_map_annihilation_sheafification
    {X : Scheme.{u}} [IsNoetherian X] [IsAffine X] (J : X.IdealSheafData) :
    let A := Γ(X, ⊤)
    let I := J.ideal ⟨⊤, isAffineOpen_top X⟩
    let L := tilde.functor A ⋙ Scheme.Modules.pullback X.isoSpec.hom
    ∀ (T P : ModuleCat.{u} A) (ψ : T →ₗ[A] P) (G : X.Modules)
      (ε : L.obj P ≅ G) (t : ℕ),
      I ^ t ≤ Module.annihilator A ψ.ker →
      I ^ t ≤ Module.annihilator A (P ⧸ ψ.range) →
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι t).2
        (kernel (L.map (ModuleCat.ofHom ψ) ≫ ε.hom))) ∧
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower J.toModulesι t).2
        (cokernel (L.map (ModuleCat.ofHom ψ) ≫ ε.hom))) := by
  dsimp only
  intro T P ψ G ε t hk hc
  let L := tilde.functor Γ(X, ⊤) ⋙ Scheme.Modules.pullback X.isoSpec.hom
  let f := ModuleCat.ofHom ψ
  have : PreservesLimitsOfSize.{u, u} (Scheme.Modules.pullback X.isoSpec.hom) :=
    preservesLimits_of_natIso (Scheme.Modules.restrictFunctorIsoPullback X.isoSpec.hom)
  have : PreservesLimit (parallelPair f 0) (tilde.functor Γ(X, ⊤)) :=
    tilde_preservesKernel (Γ(X, ⊤) : Type u) f
  have hLkernel : PreservesLimit (parallelPair f 0) L := by infer_instance
  let eK : L.obj (ModuleCat.of Γ(X, ⊤) ψ.ker) ≅ kernel (L.map f ≫ ε.hom) :=
    L.mapIso (ModuleCat.kernelIsoKer f).symm ≪≫ PreservesKernel.iso L f ≪≫
      (kernelCompMono (L.map f) ε.hom).symm
  let eC : L.obj (ModuleCat.of Γ(X, ⊤) (P ⧸ ψ.range)) ≅
      cokernel (L.map f ≫ ε.hom) :=
    L.mapIso (ModuleCat.cokernelIsoRangeQuotient f).symm ≪≫ PreservesCokernel.iso L f ≪≫
      (cokernelCompIsIso (L.map f) ε.hom).symm
  have hqc (M : ModuleCat.{u} Γ(X, ⊤)) : (L.obj M).IsQuasicoherent := by
    have : ((tilde.functor Γ(X, ⊤)).obj M).IsQuasicoherent := by
      change (tilde M).IsQuasicoherent
      infer_instance
    exact Scheme.Modules.isQuasicoherent_pullback _ _
  have hKqc : (kernel (L.map f ≫ ε.hom)).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso eK (hqc _)
  have hCqc : (cokernel (L.map f ≫ ε.hom)).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso eC (hqc _)
  let E := SheafOfModules.evaluation.{u} X.ringCatSheaf (op ⊤)
  constructor
  · exact idealPower_zero_of_sections_iso J _ (ModuleCat.of Γ(X, ⊤) ψ.ker)
      (affineAssociatedSectionsIso X _ ≪≫ₗ (E.mapIso eK).toLinearEquiv) t hk
  · exact idealPower_zero_of_sections_iso J _ (ModuleCat.of Γ(X, ⊤) (P ⧸ ψ.range))
      (affineAssociatedSectionsIso X _ ≪≫ₗ (E.mapIso eC).toLinearEquiv) t hc

end AlgebraicGeometry
