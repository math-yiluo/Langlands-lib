/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.CategoryTheory.Subobject.Basic
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Tilde

/-! # Detecting equality of quasi-coherent subobjects on an affine cover

Source: Stacks Project, Cohomology of Schemes, Tag 01Y8, proof;
Schemes, Tag 01I6 (affine quasi-coherent modules)
(blueprint: lem-weil-pbc-quasicoherent-subobject-affine-cover-ext).
-/

@[expose] public section

universe u v

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
/-- An inclusion into a quasi-coherent subobject is equality if its section images agree
on an affine open cover. The smaller subobject need not be quasi-coherent, and no
finiteness or Noetherian hypothesis is needed.
Source: Stacks Project, Tag 01Y8, proof; the basic-open localization of Tag 01IA
and sheaf gluing supply the local-to-global step
(blueprint: lem-weil-pbc-quasicoherent-subobject-affine-cover-ext).

Proof: The inequality gives the inclusion from G to H. It is injective on every open
because it is a monomorphism. On each covering affine, equality of the images of G and H
in F makes the inclusion surjective on sections, using the injectivity of H into F.
The basic opens in all the covering affines form a basis. Given a section of H on a
basic open D(f), quasi-coherence of H expresses a power of f times the section as the
restriction of a section on the covering affine. Lift the latter section to G there
and restrict it to D(f). The restriction of f is a unit on D(f), so multiplying this
lift by its inverse power gives a lift of the original section. Thus the inclusion
is bijective on each member of the basis. Mathlib's basis test for sheaf isomorphisms
makes it a global isomorphism. The isomorphism commutes with the subobject arrows,
so the subobjects are equal. This also covers an empty scheme and an empty cover. -/
theorem quasicoherent_subobject_eq_of_affine_cover (X : Scheme.{u}) (F : X.Modules)
    (G H : Subobject F) (hH : (H : X.Modules).IsQuasicoherent) (hGH : G ≤ H)
    (I : Type v) (U : I → X.affineOpens) (hU : ⨆ i, (U i).1 = ⊤)
    (hsections : ∀ i,
      LinearMap.range (G.arrow.val.app (.op (U i).1)).hom =
        LinearMap.range (H.arrow.val.app (.op (U i).1)).hom) : G = H  := by
  classical
  let φ : (G : X.Modules) ⟶ (H : X.Modules) := Subobject.ofLE G H hGH
  have hfac : φ ≫ H.arrow = G.arrow := Subobject.ofLE_arrow hGH
  have hHinj (V : X.Opens) : Function.Injective (H.arrow.val.app (.op V)).hom := by
    have : Mono ((SheafOfModules.evaluation X.ringCatSheaf (.op V)).map H.arrow) := inferInstance
    exact (ModuleCat.mono_iff_injective _).mp this
  have hφinj (V : X.Opens) : Function.Injective (φ.val.app (.op V)).hom := by
    have : Mono φ := inferInstanceAs (Mono (Subobject.ofLE G H hGH))
    have : Mono ((SheafOfModules.evaluation X.ringCatSheaf (.op V)).map φ) := inferInstance
    exact (ModuleCat.mono_iff_injective _).mp this
  have hsurj (i : I) : Function.Surjective (φ.val.app (.op (U i).1)).hom := by
    intro t
    have ht : (H.arrow.val.app (.op (U i).1)).hom t ∈
        LinearMap.range (G.arrow.val.app (.op (U i).1)).hom := by
      rw [hsections i]
      exact ⟨t, rfl⟩
    obtain ⟨s, hs⟩ := ht
    refine ⟨s, hHinj _ ?_⟩
    have h := congrArg (fun f ↦ (f.val.app (.op (U i).1)).hom) hfac
    exact (congrArg (fun f ↦ f s) h).trans hs
  let B := Σ i : I, Γ(X, (U i).1)
  let V : B → X.Opens := fun b ↦ X.basicOpen b.2
  have hB : TopologicalSpace.Opens.IsBasis (Set.range V) := by
    rw [TopologicalSpace.Opens.isBasis_iff_nbhd]
    intro W x hx
    have hxU : x ∈ ⨆ i, (U i).1 := hU.symm ▸ (Set.mem_univ x)
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hxU
    obtain ⟨g, hgW, hxg⟩ := (U i).2.exists_basicOpen_le ⟨x, hx⟩ hi
    exact ⟨X.basicOpen g, ⟨⟨i, g⟩, rfl⟩, hxg, hgW⟩
  have hbasic (b : B) : Function.Surjective (φ.val.app (.op (V b))).hom := by
    change Function.Surjective (φ.app (X.basicOpen b.2))
    intro t
    obtain ⟨n, s, hs⟩ := exists_map_eq_pow_smul_of_isAffineOpen
      (H : X.Modules) (U b.1).2 b.2 t
    obtain ⟨s', hs'⟩ := hsurj b.1 s
    have hunit : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le b.2)).op b.2) := by
      have := (U b.1).2.isLocalization_basicOpen b.2
      exact IsLocalization.map_units Γ(X, X.basicOpen b.2)
        (⟨b.2, Submonoid.mem_powers _⟩ : Submonoid.powers b.2)
    obtain ⟨r, hr⟩ := hunit
    let s'' := (G : X.Modules).presheaf.map (homOfLE (X.basicOpen_le b.2)).op s'
    refine ⟨((↑(r⁻¹) : Γ(X, X.basicOpen b.2)) ^ n) • s'', ?_⟩
    have heq : φ.app (X.basicOpen b.2) s'' = (↑r : Γ(X, X.basicOpen b.2)) ^ n • t := by
      dsimp only [s'', V]
      have hn := PresheafOfModules.naturality_apply φ.val
        (homOfLE (X.basicOpen_le b.2)).op s'
      change _ = _ at hn
      rw [hs'] at hn
      exact hn.trans (hs.trans (by rw [hr]))
    rw [Scheme.Modules.Hom.app_smul, heq, ← smul_assoc]
    simp [← mul_pow]
  let A : TopCat.Sheaf AddCommGrpCat X := ⟨(G : X.Modules).presheaf, (G : X.Modules).isSheaf⟩
  let C : TopCat.Sheaf AddCommGrpCat X := ⟨(H : X.Modules).presheaf, (H : X.Modules).isSheaf⟩
  let ψ : A ⟶ C := Sheaf.homEquiv.symm ((Scheme.Modules.toPresheaf X).map φ)
  have hψ : IsIso ψ := TopCat.Sheaf.isIso_iff_isIso_basis hB (fun b ↦
    (ConcreteCategory.isIso_iff_bijective _).mpr ⟨hφinj (V b), hbasic b⟩)
  have : IsIso ((Scheme.Modules.toPresheaf X).map φ) := by
    obtain ⟨g, hg₁, hg₂⟩ := hψ.out
    exact ⟨g.hom, congrArg (fun a ↦ a.hom) hg₁, congrArg (fun a ↦ a.hom) hg₂⟩
  have : IsIso φ := isIso_of_reflects_iso φ (Scheme.Modules.toPresheaf X)
  exact Subobject.eq_of_comm (asIso φ) hfac

end AlgebraicGeometry.Scheme.Modules
