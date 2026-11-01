import Mathlib.Topology.Sheaves.AddCommGrpCat
import Langlands.AlgebraicGeometry.Modules.PushforwardInjectiveAcyclicProof
import Langlands.AlgebraicGeometry.Modules.QuasicoherentLocal.Basic

/-!
# Kernels, cokernels and pushforwards of modules that are quasi-coherent on affine opens

An `𝒪_X`-module `M` is *affine-locally quasi-coherent* if its restriction along
`hV.fromSpec : Spec Γ(X, V) ⟶ X` is quasi-coherent for every affine open `V`. Every
quasi-coherent module has this property. The property is stable under kernels, cokernels and
isomorphisms, and under pushforward along an affine morphism from a scheme carrying a
quasi-coherent module.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace Langlands.AlgebraicGeometry.Modules

namespace QuasicoherentLocal

open Langlands.Cohomology AffineVanishing

variable {X : Scheme.{u}}

section Sections

variable {M N : X.Modules} (φ : M ⟶ N)

lemma res_app {U W : X.Opens} (h : U ≤ W) (x : Γ(M, W)) :
    Cech.res h (φ.app W x) = φ.app U (Cech.res h x) :=
  (ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE h).op) x).symm

lemma app_kernel_ι_app (W : X.Opens) (k : Γ(kernel φ, W)) :
    φ.app W ((kernel.ι φ).app W k) = 0 := by
  change ((kernel.ι φ ≫ φ).app W) k = 0
  rw [kernel.condition, Scheme.Modules.Hom.zero_app]
  rfl

lemma injective_app_of_mono {T : TopCat.{u}}
    {F G : TopCat.Sheaf AddCommGrpCat.{u} T} (f : F ⟶ G) [Mono f] (V : Opens T) :
    Function.Injective (f.hom.app (op V)) := by
  have : Mono f.hom := (TopCat.Sheaf.forget AddCommGrpCat T).map_mono f
  exact (AddCommGrpCat.mono_iff_injective _).1 inferInstance

lemma kernel_ι_app_injective (W : X.Opens) : Function.Injective ((kernel.ι φ).app W) := by
  have : Mono ((PushforwardInjectiveAcyclic.toAbSheaf X).map (kernel.ι φ)) :=
    (PushforwardInjectiveAcyclic.toAbSheaf X).map_mono (kernel.ι φ)
  exact injective_app_of_mono
    ((PushforwardInjectiveAcyclic.toAbSheaf X).map (kernel.ι φ)) W

lemma exists_kernel_ι_app_eq {W : X.Opens} (m : Γ(M, W)) (hm : φ.app W m = 0) :
    ∃ k, (kernel.ι φ).app W k = m := by
  let S := ShortComplex.mk (kernel.ι φ) φ (kernel.condition φ)
  have hS : S.Exact := S.exact_of_f_is_kernel (kernelIsKernel φ)
  have hS' := hS.map (PushforwardInjectiveAcyclic.toAbSheaf X)
  have : Mono (S.map (PushforwardInjectiveAcyclic.toAbSheaf X)).f :=
    (PushforwardInjectiveAcyclic.toAbSheaf X).map_mono (kernel.ι φ)
  exact TopCat.Sheaf.sections_exact_of_left_exact hS' inferInstance m hm

end Sections

/-- The localization property passes to kernels. -/
theorem isLocalizingAt_kernel {M N : X.Modules} (φ : M ⟶ N) {V : X.Opens}
    (hM : IsLocalizingAt M V) (hN : IsLocalizingAt N V) : IsLocalizingAt (kernel φ) V where
  exists_res_eq h s := by
    obtain ⟨n, t, ht⟩ := hM.exists_res_eq h ((kernel.ι φ).app _ s)
    obtain ⟨m, hm⟩ := hN.exists_pow_smul_eq_zero h (φ.app V t) (by
      rw [res_app, ht, Scheme.Modules.Hom.app_smul, app_kernel_ι_app, smul_zero])
    obtain ⟨k, hk⟩ := exists_kernel_ι_app_eq φ (h ^ m • t) (by
      rw [Scheme.Modules.Hom.app_smul, hm])
    refine ⟨m + n, k, kernel_ι_app_injective φ _ ?_⟩
    rw [← res_app, hk, res_smul, ht, Scheme.Modules.Hom.app_smul, smul_smul, map_pow, ← pow_add]
  exists_pow_smul_eq_zero h t ht := by
    obtain ⟨n, hn⟩ := hM.exists_pow_smul_eq_zero h ((kernel.ι φ).app V t) (by
      rw [res_app, ht, map_zero])
    refine ⟨n, kernel_ι_app_injective φ _ ?_⟩
    rw [Scheme.Modules.Hom.app_smul, hn, map_zero]

section Pushforward

variable {Y : Scheme.{u}} (j : Y ⟶ X)

lemma pushforward_smul (G : Y.Modules) {W : X.Opens} (r : Γ(X, W))
    (x : Γ((Scheme.Modules.pushforward j).obj G, W)) :
    r • x = (j.app W r • (show Γ(G, j ⁻¹ᵁ W) from x) : Γ(G, j ⁻¹ᵁ W)) :=
  rfl

lemma app_rres {A B : X.Opens} (hAB : A ≤ B) (r : Γ(X, B)) :
    j.app A (rres hAB r) =
      rres (show j ⁻¹ᵁ A ≤ j ⁻¹ᵁ B from fun _ hx => hAB hx) (j.app B r) :=
  ConcreteCategory.congr_hom (j.naturality (homOfLE hAB).op) r

/-- The localization property of `G` over `j ⁻¹ᵁ U` gives that of the pushforward over `U`. -/
theorem isLocalizingAt_pushforward {G : Y.Modules} {U : X.Opens}
    (hG : IsLocalizingAt G (j ⁻¹ᵁ U)) :
    IsLocalizingAt ((Scheme.Modules.pushforward j).obj G) U where
  exists_res_eq h s := by
    obtain ⟨s, rfl⟩ : ∃ s' : Γ(G, j ⁻¹ᵁ X.basicOpen h), s' = s := ⟨s, rfl⟩
    have e : j ⁻¹ᵁ X.basicOpen h = Y.basicOpen (j.app U h) := Scheme.preimage_basicOpen j h
    obtain ⟨n, t, ht⟩ := hG.exists_res_eq (j.app U h) (Cech.res (P := G.presheaf) e.ge s)
    refine ⟨n, t, ?_⟩
    have h1 := congrArg (Cech.res (P := G.presheaf) e.le) ht
    rw [Cech.res_res, res_smul, Cech.res_res, Cech.res_self, map_pow, rres_rres] at h1
    have h2 : j.app (X.basicOpen h) (rres (X.basicOpen_le h) h ^ n) =
        rres (show j ⁻¹ᵁ X.basicOpen h ≤ j ⁻¹ᵁ U from fun _ hx => X.basicOpen_le h hx)
          (j.app U h) ^ n := by
      rw [map_pow, app_rres]
    refine Eq.trans ?_
      (pushforward_smul j G (W := X.basicOpen h) (rres (X.basicOpen_le h) h ^ n) s).symm
    refine h1.trans ?_
    rw [h2]
  exists_pow_smul_eq_zero h t ht := by
    obtain ⟨t, rfl⟩ : ∃ t' : Γ(G, j ⁻¹ᵁ U), t' = t := ⟨t, rfl⟩
    have e : j ⁻¹ᵁ X.basicOpen h = Y.basicOpen (j.app U h) := Scheme.preimage_basicOpen j h
    have hle : j ⁻¹ᵁ X.basicOpen h ≤ j ⁻¹ᵁ U := fun _ hx => X.basicOpen_le h hx
    have h1 : Cech.res (P := G.presheaf) hle t = 0 := ht
    obtain ⟨n, hn⟩ := hG.exists_pow_smul_eq_zero (j.app U h) t (by
      rw [← Cech.res_res e.ge hle, h1, map_zero])
    refine ⟨n, (pushforward_smul j G (h ^ n) t).trans ?_⟩
    rw [map_pow]
    exact hn

end Pushforward

section Cokernel

variable {R : CommRingCat.{u}}

/-- On `Spec R`, the cokernel of a morphism of quasi-coherent modules is quasi-coherent:
it is the tilde of the cokernel of global sections, since tilde is a left adjoint. -/
theorem isQuasicoherent_cokernel_spec {M N : (Spec R).Modules} (φ : M ⟶ N)
    [M.IsQuasicoherent] [N.IsQuasicoherent] : (cokernel φ).IsQuasicoherent := by
  let α := Scheme.Modules.fromTildeΓNatTrans (R := R)
  have : IsIso (α.app M) := (inferInstance : IsIso M.fromTildeΓ)
  have : IsIso (α.app N) := (inferInstance : IsIso N.fromTildeΓ)
  have w : φ ≫ (asIso (α.app N)).symm.hom =
      (asIso (α.app M)).symm.hom ≫ (tilde.functor R).map (moduleSpecΓFunctor.map φ) := by
    rw [Iso.symm_hom, Iso.symm_hom, asIso_inv, asIso_inv, IsIso.eq_inv_comp, ← Category.assoc,
      IsIso.comp_inv_eq]
    exact (α.naturality φ).symm
  let e : cokernel φ ≅ (tilde.functor R).obj (cokernel (moduleSpecΓFunctor.map φ)) :=
    cokernel.mapIso φ ((tilde.functor R).map (moduleSpecΓFunctor.map φ)) _ _ w ≪≫
      (PreservesCokernel.iso (tilde.functor R) (moduleSpecΓFunctor.map φ)).symm
  exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso e.symm inferInstance

end Cokernel

/-- `M` is quasi-coherent over every affine open `V`: its restriction along
`hV.fromSpec : Spec Γ(X, V) ⟶ X` is quasi-coherent. -/
def IsAffineLocallyQuasicoherent (M : X.Modules) : Prop :=
  ∀ (V : X.Opens) (hV : IsAffineOpen V), (M.restrict hV.fromSpec).IsQuasicoherent

namespace IsAffineLocallyQuasicoherent

theorem of_isQuasicoherent (M : X.Modules) [M.IsQuasicoherent] :
    IsAffineLocallyQuasicoherent M :=
  fun _ _ => inferInstance

theorem of_iso {M N : X.Modules} (e : M ≅ N) (hM : IsAffineLocallyQuasicoherent M) :
    IsAffineLocallyQuasicoherent N := fun V hV =>
  have := hM V hV
  (SheafOfModules.isQuasicoherent (Spec Γ(X, V)).ringCatSheaf).prop_of_iso
    ((Scheme.Modules.restrictFunctor hV.fromSpec).mapIso e) this

theorem kernel {M N : X.Modules} (φ : M ⟶ N) (hM : IsAffineLocallyQuasicoherent M)
    (hN : IsAffineLocallyQuasicoherent N) : IsAffineLocallyQuasicoherent (kernel φ) :=
  fun V hV =>
    have := hM V hV
    have := hN V hV
    isQuasicoherent_of_isLocalizingAt hV (isLocalizingAt_kernel φ
      (isLocalizingAt_of_isQuasicoherent hV M) (isLocalizingAt_of_isQuasicoherent hV N))

theorem cokernel {M N : X.Modules} (φ : M ⟶ N) (hM : IsAffineLocallyQuasicoherent M)
    (hN : IsAffineLocallyQuasicoherent N) : IsAffineLocallyQuasicoherent (cokernel φ) :=
  fun V hV => by
    have := hM V hV
    have := hN V hV
    have := isQuasicoherent_cokernel_spec ((Scheme.Modules.restrictFunctor hV.fromSpec).map φ)
    exact (SheafOfModules.isQuasicoherent (Spec Γ(X, V)).ringCatSheaf).prop_of_iso
      (PreservesCokernel.iso (Scheme.Modules.restrictFunctor hV.fromSpec) φ).symm this

theorem pushforward {Y : Scheme.{u}} (j : Y ⟶ X) [IsAffineHom j] {G : Y.Modules}
    (hG : IsAffineLocallyQuasicoherent G) :
    IsAffineLocallyQuasicoherent ((Scheme.Modules.pushforward j).obj G) := fun U hU => by
  have hU' : IsAffineOpen (j ⁻¹ᵁ U) := hU.preimage j
  have := hG _ hU'
  exact isQuasicoherent_of_isLocalizingAt hU
    (isLocalizingAt_pushforward j (isLocalizingAt_of_isQuasicoherent hU' G))

end IsAffineLocallyQuasicoherent

end QuasicoherentLocal

end Langlands.AlgebraicGeometry.Modules
