import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Langlands.AlgebraicGeometry.Modules.AffineQuasicoherentHigherDirectImageVanishingProof
import Langlands.AlgebraicGeometry.Modules.PullbackUnitProofs
import Langlands.Cohomology.RightDerivedSequence

/-!
# Degree-one cohomology classes as Čech cocycles

Let `f : P ⟶ Spec R` and let `M` be an `𝒪_P`-module whose Čech complexes for standard covers of
affine opens are exact, for instance a quasi-coherent module. For a cover of `P` by affine opens
`Z a`, every class `c ∈ H¹(P, M)` is represented by a Čech `1`-cocycle `z` on the cover. The
class is computed from the embedding `0 ⟶ M ⟶ I ⟶ Q ⟶ 0` of `M` into an injective module:
`c` is the image of a global section `q` of `Q` under the connecting morphism, `q` lifts on each
`Z a` to a section `t a` of `I`, and `z a b = t b - t a` on `Z a ⊓ Z b`.

The representative is compatible with module maps `u : M ⟶ G`: if `H¹(u) c = 0` then the
cocycle `u z` is a coboundary. If `z` itself is a coboundary, then `c = 0`.

The file also records that the structure sheaf is quasi-coherent and that a class killed by
the unit `𝒪_P ⟶ i_* i^* 𝒪_P` of a morphism `i` is killed by `𝒪_P ⟶ i_* 𝒪_X`.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace Langlands.AlgebraicGeometry.Modules.CechDegreeOne

open Langlands.Cohomology

variable {P : Scheme.{u}}

section Sections

variable {A B C : P.Modules}

lemma app_comp_apply (φ : A ⟶ B) (ψ : B ⟶ C) (U : P.Opens) (x : Γ(A, U)) :
    (φ ≫ ψ).app U x = ψ.app U (φ.app U x) := rfl

lemma app_res (φ : A ⟶ B) {V W : P.Opens} (h : V ≤ W) (x : Γ(A, W)) :
    φ.app V (Cech.res h x) = Cech.res h (φ.app W x) :=
  Cech.map_res φ.mapPresheaf h x

lemma relativeGlobalSections_map_apply {R : CommRingCat.{u}} (f : P ⟶ Spec R) (φ : A ⟶ B)
    (x : (DerivedSections.relativeGlobalSections f).obj A) :
    ((DerivedSections.relativeGlobalSections f).map φ).hom x = φ.app ⊤ x := rfl

variable (M : P.Modules)

lemma ι_app_injective (U : P.Opens) : Function.Injective ((Injective.ι M).app U) :=
  AffineVanishing.injective_f_app (PushforwardInjectiveAcyclic.toSheaf_injectiveSc_shortExact M) U

lemma exists_ι_app_eq {U : P.Opens} (b : Γ(Injective.under M, U))
    (hb : (cokernel.π (Injective.ι M)).app U b = 0) : ∃ a, (Injective.ι M).app U a = b :=
  AffineVanishing.exists_f_app_eq (PushforwardInjectiveAcyclic.toSheaf_injectiveSc_shortExact M)
    b hb

lemma π_app_ι_app (U : P.Opens) (a : Γ(M, U)) :
    (cokernel.π (Injective.ι M)).app U ((Injective.ι M).app U a) = 0 := by
  rw [← app_comp_apply, cokernel.condition, Scheme.Modules.Hom.zero_app]
  rfl

lemma π_app_surjective (hM : AffineVanishing.IsCechAcyclic M) {U : P.Opens}
    (hU : IsAffineOpen U) : Function.Surjective ((cokernel.π (Injective.ι M)).app U) :=
  AffineVanishing.surjective_app_of_exactAt
    (PushforwardInjectiveAcyclic.toSheaf_injectiveSc_shortExact M) hU
    (fun κ _ g hg => hM U hU κ g hg 0)

end Sections

variable {ι : Type*} (Z : ι → P.Opens)

/-- Sections of `G` over the pairwise intersections `Z a ⊓ Z b` satisfying the Čech cocycle
condition `z a b + z b c = z a c` on every open contained in `Z a ⊓ Z b ⊓ Z c`. -/
def IsCocycle {G : P.Modules} (z : ∀ a b, Γ(G, Z a ⊓ Z b)) : Prop :=
  ∀ a b c {O : P.Opens} (h₁ : O ≤ Z a ⊓ Z b) (h₂ : O ≤ Z b ⊓ Z c) (h₃ : O ≤ Z a ⊓ Z c),
    Cech.res (P := G.presheaf) h₁ (z a b) + Cech.res (P := G.presheaf) h₂ (z b c) =
      Cech.res (P := G.presheaf) h₃ (z a c)

/-- Sections of `G` over the pairwise intersections `Z a ⊓ Z b` of the form `g b - g a`. -/
def IsCoboundary {G : P.Modules} (z : ∀ a b, Γ(G, Z a ⊓ Z b)) : Prop :=
  ∃ g : ∀ a, Γ(G, Z a), ∀ a b,
    z a b = Cech.res (P := G.presheaf) inf_le_right (g b) -
      Cech.res (P := G.presheaf) inf_le_left (g a)

variable {Z}

/-- A class `c ∈ H¹(P, M)` of a Čech-acyclic module is represented by a Čech `1`-cocycle on any
cover of `P` by affine opens. The representative is compatible with module maps `u : M ⟶ G`
killing `c`, and `c = 0` if the representative is a coboundary. -/
theorem exists_cocycle {R : CommRingCat.{u}} (f : P ⟶ Spec R) {M : P.Modules}
    (hM : AffineVanishing.IsCechAcyclic M) (hZ : ∀ a, IsAffineOpen (Z a)) (hcov : iSup Z = ⊤)
    (c : (DerivedSections.relativeCohomology f 1).obj M) :
    ∃ z : ∀ a b, Γ(M, Z a ⊓ Z b), IsCocycle Z z ∧
      (∀ (G : P.Modules) (u : M ⟶ G),
        ((DerivedSections.relativeCohomology f 1).map u).hom c = 0 →
          IsCoboundary Z (fun a b => u.app _ (z a b))) ∧
      (IsCoboundary Z z → c = 0) := by
  classical
  let := HasDerivedCategory.standard P.Modules
  let := HasDerivedCategory.standard (ModuleCat.{u} R)
  let F := DerivedSections.relativeGlobalSections f
  let S := PushforwardInjectiveAcyclic.injectiveSc M
  have hS : S.ShortExact := PushforwardInjectiveAcyclic.injectiveSc_shortExact M
  have hδ : Epi (DerivedPlus.rightDerivedδ F hS 0 1 rfl) :=
    DerivedPlus.epi_rightDerivedδ_of_isZero F hS 0 1 rfl
      (F.isZero_rightDerived_obj_injective_succ 0 (Injective.under M))
  obtain ⟨q₀, hq₀⟩ := (ModuleCat.epi_iff_surjective _).1 hδ c
  let q : Γ(cokernel (Injective.ι M), ⊤) := (F.rightDerivedZeroIsoSelf.hom.app S.X₃).hom q₀
  have hZW : ∀ a, Z a ≤ ⊤ := fun _ => le_top
  have hcov' : (⊤ : P.Opens) ≤ iSup Z := hcov.ge
  choose t ht using fun a => π_app_surjective M hM (hZ a) (Cech.res (hZW a) q)
  have hd : ∀ a b, (cokernel.π (Injective.ι M)).app (Z a ⊓ Z b)
      (Cech.res inf_le_right (t b) - Cech.res inf_le_left (t a)) = 0 := by
    intro a b
    rw [map_sub, app_res, app_res, ht, ht, Cech.res_res, Cech.res_res, sub_self]
  choose z hz using fun a b => exists_ι_app_eq M _ (hd a b)
  refine ⟨z, ?_, ?_, ?_⟩
  · intro a b c O h₁ h₂ h₃
    apply ι_app_injective M O
    simp only [map_add, app_res, hz, map_sub, Cech.res_res]
    abel
  · intro G u hu
    let SG := PushforwardInjectiveAcyclic.injectiveSc G
    have hSG : SG.ShortExact := PushforwardInjectiveAcyclic.injectiveSc_shortExact G
    let τ₂ : Injective.under M ⟶ Injective.under G :=
      Injective.factorThru (u ≫ Injective.ι G) (Injective.ι M)
    have hτ₂ : Injective.ι M ≫ τ₂ = u ≫ Injective.ι G := Injective.comp_factorThru _ _
    let τ₃ : cokernel (Injective.ι M) ⟶ cokernel (Injective.ι G) :=
      cokernel.desc _ (τ₂ ≫ cokernel.π _) (by
        rw [← Category.assoc, hτ₂, Category.assoc, cokernel.condition, comp_zero])
    have hτ₃ : cokernel.π (Injective.ι M) ≫ τ₃ = τ₂ ≫ cokernel.π (Injective.ι G) :=
      cokernel.π_desc _ _ _
    let φ : S ⟶ SG := ⟨u, τ₂, τ₃, hτ₂.symm, hτ₃.symm⟩
    have hnat := congrArg (fun k => k.hom q₀)
      (DerivedPlus.rightDerivedδ_naturality F hS hSG φ 0 1 rfl)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hnat
    have hzero : (DerivedPlus.rightDerivedδ F hSG 0 1 rfl).hom
        (((F.rightDerived 0).map τ₃).hom q₀) = 0 := by
      rw [← hnat]
      change ((F.rightDerived 1).map u).hom ((DerivedPlus.rightDerivedδ F hS 0 1 rfl) q₀) = 0
      rw [hq₀]
      exact hu
    obtain ⟨s₀, hs₀⟩ := (ShortComplex.moduleCat_exact_iff _).1
      (DerivedPlus.rightDerived_exact₃ F hSG 0 1 rfl) _ hzero
    let s : Γ(Injective.under G, ⊤) := (F.rightDerivedZeroIsoSelf.hom.app SG.X₂).hom s₀
    have hs : (cokernel.π (Injective.ι G)).app ⊤ s = τ₃.app ⊤ q := by
      have e₁ := congrArg (fun k => k.hom s₀) (F.rightDerivedZeroIsoSelf.hom.naturality SG.g)
      have e₂ := congrArg (fun k => k.hom q₀) (F.rightDerivedZeroIsoSelf.hom.naturality τ₃)
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e₁ e₂
      have hs₀' : ((F.rightDerived 0).map SG.g).hom s₀ = ((F.rightDerived 0).map τ₃).hom q₀ :=
        hs₀
      exact e₁.symm.trans ((congrArg _ hs₀').trans e₂)
    have hg : ∀ a, (cokernel.π (Injective.ι G)).app (Z a)
        (τ₂.app (Z a) (t a) - Cech.res (hZW a) s) = 0 := by
      intro a
      rw [map_sub, ← app_comp_apply, ← hτ₃, app_comp_apply, ht, app_res, app_res, hs, sub_self]
    choose g hg' using fun a => exists_ι_app_eq G _ (hg a)
    refine ⟨g, fun a b => ?_⟩
    apply ι_app_injective G
    rw [← app_comp_apply, ← hτ₂, app_comp_apply, hz]
    simp only [map_sub, app_res, hg', Cech.res_res]
    abel
  · rintro ⟨w, hw⟩
    let sf : ∀ a, Γ(Injective.under M, Z a) := fun a => t a - (Injective.ι M).app (Z a) (w a)
    have hsf : ∀ a b, Cech.res (inf_le_left : Z a ⊓ Z b ≤ Z a) (sf a) =
        Cech.res (inf_le_right : Z a ⊓ Z b ≤ Z b) (sf b) := by
      intro a b
      have e := congrArg ((Injective.ι M).app (Z a ⊓ Z b)) (hw a b)
      rw [hz, map_sub, app_res, app_res] at e
      simp only [sf, map_sub]
      rw [sub_eq_sub_iff_sub_eq_sub] at e
      exact e.symm
    let IS := (PushforwardInjectiveAcyclic.toAbSheaf P).obj (Injective.under M)
    have hglue : ∃ T : Γ(Injective.under M, ⊤), ∀ a, Cech.res (hZW a) T = sf a := by
      obtain ⟨T, hT, -⟩ := IS.existsUnique_gluing' Z ⊤ (fun a => homOfLE (hZW a)) hcov' sf
        (fun a b => hsf a b)
      exact ⟨T, hT⟩
    obtain ⟨T, hT⟩ := hglue
    have hπT : (cokernel.π (Injective.ι M)).app ⊤ T = q := by
      apply ((PushforwardInjectiveAcyclic.toAbSheaf P).obj
        (cokernel (Injective.ι M))).eq_of_locally_eq' Z ⊤ (fun a => homOfLE (hZW a)) hcov'
      intro a
      change Cech.res (hZW a) ((cokernel.π (Injective.ι M)).app ⊤ T) = Cech.res (hZW a) q
      rw [← app_res, hT a, ← ht a]
      simp only [sf, map_sub, π_app_ι_app, sub_zero]
    have e₁ := congrArg (fun k => k.hom T) (F.rightDerivedZeroIsoSelf.inv.naturality S.g)
    have e₂ := congrArg (fun k => k.hom q₀) (F.rightDerivedZeroIsoSelf.hom_inv_id_app S.X₃)
    have e₃ := congrArg (fun k => k.hom ((F.rightDerivedZeroIsoSelf.inv.app S.X₂).hom T))
      (DerivedPlus.rightDerived_map_comp_δ F hS 0 1 rfl)
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply,
      ModuleCat.hom_zero, LinearMap.zero_apply] at e₁ e₂ e₃
    have e₄ : ((F.rightDerived 0).map S.g).hom ((F.rightDerivedZeroIsoSelf.inv.app S.X₂).hom T) =
        q₀ := by
      refine e₁.symm.trans ?_
      change (F.rightDerivedZeroIsoSelf.inv.app S.X₃).hom
        ((cokernel.π (Injective.ι M)).app ⊤ T) = q₀
      rw [hπT]
      exact e₂
    rw [← hq₀, ← e₄]
    exact e₃

/-- A class killed by the unit `𝒪_P ⟶ i_* i^* 𝒪_P` of a morphism `i : X ⟶ P` is killed by the
structure morphism `𝒪_P ⟶ i_* 𝒪_X`. -/
lemma map_unitToPushforwardUnit_eq_zero {R : CommRingCat.{u}} (f : P ⟶ Spec R) {X : Scheme.{u}}
    (i : X ⟶ P) (n : ℕ)
    (c : (DerivedSections.relativeCohomology f n).obj (SheafOfModules.unit P.ringCatSheaf))
    (hc : ((DerivedSections.relativeCohomology f n).map
      ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
        (SheafOfModules.unit P.ringCatSheaf))).hom c = 0) :
    ((DerivedSections.relativeCohomology f n).map
      (Langlands.Scheme.Modules.unitToPushforwardUnit i)).hom c = 0 := by
  have e : Langlands.Scheme.Modules.unitToPushforwardUnit i =
      (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
          (SheafOfModules.unit P.ringCatSheaf) ≫
        (Scheme.Modules.pushforward i).map (Langlands.Scheme.Modules.pullbackUnitIso i).hom := by
    rw [← Langlands.Scheme.Modules.pullbackUnitAdjunction X P i]
    exact Adjunction.homEquiv_unit _ _ _ _
  let g₁ := (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
    (SheafOfModules.unit P.ringCatSheaf)
  let g₂ := (Scheme.Modules.pushforward i).map (Langlands.Scheme.Modules.pullbackUnitIso i).hom
  calc ((DerivedSections.relativeCohomology f n).map
        (Langlands.Scheme.Modules.unitToPushforwardUnit i)).hom c
      = ((DerivedSections.relativeCohomology f n).map (g₁ ≫ g₂)).hom c :=
        congrArg (fun k => ((DerivedSections.relativeCohomology f n).map k).hom c) e
    _ = ((DerivedSections.relativeCohomology f n).map g₂).hom
          (((DerivedSections.relativeCohomology f n).map g₁).hom c) := by
        rw [Functor.map_comp]
        rfl
    _ = 0 := by rw [hc, map_zero]

/-- The structure sheaf is quasi-coherent. -/
instance isQuasicoherent_unit (X : Scheme.{u}) :
    (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent X.ringCatSheaf).prop_of_iso
    (coproductUniqueIso (fun _ : PUnit.{u + 1} => SheafOfModules.unit X.ringCatSheaf))
    (inferInstanceAs (SheafOfModules.free (R := X.ringCatSheaf) PUnit.{u + 1}).IsQuasicoherent)

end Langlands.AlgebraicGeometry.Modules.CechDegreeOne
