import Langlands.AlgebraicGeometry.Modules.AffineVanishing.QuasicoherentCech

/-!
# Quasi-coherence over an affine open, in terms of sections

For an affine open `V` of a scheme `X` and an `𝒪_X`-module `M`, the restriction of `M` along
`hV.fromSpec : Spec Γ(X, V) ⟶ X` is quasi-coherent if and only if `M` has the following
localization property over `V`: for every `h ∈ Γ(X, V)`, a section of `M` over `D(h)` extends
to `V` after multiplication by a power of `h`, and a section of `M` over `V` that vanishes on
`D(h)` is killed by a power of `h`.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace Langlands.AlgebraicGeometry.Modules

namespace QuasicoherentLocal

open Langlands.Cohomology AffineVanishing

variable {X : Scheme.{u}}

/-- The localization property of the sections of `M` over the open `V`. -/
structure IsLocalizingAt (M : X.Modules) (V : X.Opens) : Prop where
  exists_res_eq (h : Γ(X, V)) (s : Γ(M, X.basicOpen h)) :
    ∃ (n : ℕ) (t : Γ(M, V)), Cech.res (X.basicOpen_le h) t = rres (X.basicOpen_le h) h ^ n • s
  exists_pow_smul_eq_zero (h : Γ(X, V)) (t : Γ(M, V))
    (ht : Cech.res (X.basicOpen_le h) t = 0) : ∃ n : ℕ, h ^ n • t = 0

variable {V : X.Opens} (hV : IsAffineOpen V)

include hV in
/-- If the restriction of `M` along `hV.fromSpec` is quasi-coherent, then `M` has the
localization property over `V`. -/
theorem isLocalizingAt_of_isQuasicoherent (M : X.Modules)
    [(M.restrict hV.fromSpec).IsQuasicoherent] : IsLocalizingAt M V where
  exists_res_eq h s := by
    let D' : (Spec Γ(X, V)).Opens := PrimeSpectrum.basicOpen h
    have e₁ : hV.fromSpec ''ᵁ D' = X.basicOpen h := hV.fromSpec_image_basicOpen h
    have e₂ : hV.fromSpec ''ᵁ ⊤ = V := image_fromSpec_top hV
    obtain ⟨n, x, hx⟩ := spec_exists_pow_smul_eq_map (M.restrict hV.fromSpec) h (D := D') rfl
      ((M.restrictAppIso hV.fromSpec D').inv (Cech.res e₁.le s))
    refine ⟨n, Cech.res e₂.ge ((M.restrictAppIso hV.fromSpec ⊤).hom x), ?_⟩
    have hx' : Cech.res (P := M.presheaf) (Scheme.Hom.image_mono _ le_top :
        hV.fromSpec ''ᵁ D' ≤ hV.fromSpec ''ᵁ ⊤) ((M.restrictAppIso hV.fromSpec ⊤).hom x) =
        rres (image_fromSpec_le hV D') (h ^ n) • Cech.res e₁.le s := by
      have := congrArg (M.restrictAppIso hV.fromSpec D').hom hx
      rw [restrictAppIso_hom_smul, Iso.inv_hom_id_apply] at this
      exact this
    calc Cech.res (X.basicOpen_le h) (Cech.res e₂.ge ((M.restrictAppIso hV.fromSpec ⊤).hom x))
        = Cech.res e₁.ge (Cech.res (Scheme.Hom.image_mono _ le_top)
            ((M.restrictAppIso hV.fromSpec ⊤).hom x)) := by
          rw [Cech.res_res, Cech.res_res]
      _ = Cech.res e₁.ge (rres (image_fromSpec_le hV D') (h ^ n) • Cech.res e₁.le s) := by
          rw [hx']
      _ = rres (X.basicOpen_le h) h ^ n • s := by
          rw [res_smul, rres_rres, Cech.res_res, Cech.res_self, ← map_pow]
  exists_pow_smul_eq_zero h t ht := by
    let D' : (Spec Γ(X, V)).Opens := PrimeSpectrum.basicOpen h
    have e₁ : hV.fromSpec ''ᵁ D' = X.basicOpen h := hV.fromSpec_image_basicOpen h
    have e₂ : hV.fromSpec ''ᵁ ⊤ = V := image_fromSpec_top hV
    have h₀ : Cech.res (P := M.presheaf) (Scheme.Hom.image_mono _ le_top :
        hV.fromSpec ''ᵁ D' ≤ hV.fromSpec ''ᵁ ⊤) (Cech.res e₂.le t) = 0 := by
      rw [Cech.res_res, ← Cech.res_res e₁.le (X.basicOpen_le h), ht, map_zero]
    obtain ⟨n, hn⟩ := spec_exists_pow_smul_eq_zero (M.restrict hV.fromSpec) h (D := D') rfl
      ((M.restrictAppIso hV.fromSpec ⊤).inv (Cech.res e₂.le t)) h₀
    refine ⟨n, ?_⟩
    have h₁ := congrArg (fun x => Cech.res (P := M.presheaf) e₂.ge
      ((M.restrictAppIso hV.fromSpec ⊤).hom x)) hn
    simp only [restrictAppIso_hom_smul, Iso.inv_hom_id_apply, map_zero, res_smul, rres_rres,
      rres_self, Cech.res_res, Cech.res_self] at h₁
    exact h₁

include hV in
/-- Conversely, the localization property of `M` over `V` makes the restriction of `M` along
`hV.fromSpec` quasi-coherent. -/
theorem isQuasicoherent_of_isLocalizingAt {M : X.Modules} (hM : IsLocalizingAt M V) :
    (M.restrict hV.fromSpec).IsQuasicoherent := by
  rw [isQuasicoherent_iff_isIso_fromTildeΓ, isIso_fromTildeΓ_iff_isLocalizing]
  intro f
  let D' : (Spec Γ(X, V)).Opens := PrimeSpectrum.basicOpen f
  have e₁ : hV.fromSpec ''ᵁ D' = X.basicOpen f := hV.fromSpec_image_basicOpen f
  have e₂ : hV.fromSpec ''ᵁ ⊤ = V := image_fromSpec_top hV
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨_, n, rfl⟩
    rw [map_pow]
    exact (Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen
      (M := M.restrict hV.fromSpec) f le_rfl).pow n
  · intro y
    obtain ⟨n, t, ht⟩ := hM.exists_res_eq f
      (Cech.res e₁.ge ((M.restrictAppIso hV.fromSpec D').hom y))
    refine ⟨((M.restrictAppIso hV.fromSpec ⊤).inv (Cech.res e₂.le t), ⟨f ^ n, n, rfl⟩), ?_⟩
    have key : Cech.res (P := M.presheaf) (Scheme.Hom.image_mono _ le_top :
        hV.fromSpec ''ᵁ D' ≤ hV.fromSpec ''ᵁ ⊤) (Cech.res e₂.le t) =
        rres (image_fromSpec_le hV D') (f ^ n) • (M.restrictAppIso hV.fromSpec D').hom y := by
      have := congrArg (Cech.res (P := M.presheaf) e₁.le) ht
      rw [Cech.res_res, res_smul, map_pow, rres_rres, Cech.res_res, Cech.res_self] at this
      rw [Cech.res_res, map_pow]
      exact this
    apply (ConcreteCategory.bijective_of_isIso (M.restrictAppIso hV.fromSpec D').hom).1
    change (M.restrictAppIso hV.fromSpec D').hom
        ((f ^ n : Γ(X, V)) • (y : Γ(M.restrict hV.fromSpec, D'))) =
      (M.restrictAppIso hV.fromSpec D').hom ((M.restrict hV.fromSpec).presheaf.map
        (homOfLE le_top : D' ⟶ ⊤).op ((M.restrictAppIso hV.fromSpec ⊤).inv (Cech.res e₂.le t)))
    refine (restrictAppIso_hom_smul hV M D' (f ^ n) y).trans ?_
    rw [Scheme.Modules.map_restrictAppIso_hom_apply, Iso.inv_hom_id_apply]
    exact key.symm
  · intro x₁ x₂ hx
    have h0 : ((modulesSpecToSheaf.obj (M.restrict hV.fromSpec)).obj.map
        (PrimeSpectrum.basicOpen f).leTop.op).hom (x₁ - x₂) = 0 := by
      rw [map_sub, hx, sub_self]
    obtain ⟨n, hn⟩ := hM.exists_pow_smul_eq_zero f
      (Cech.res e₂.ge ((M.restrictAppIso hV.fromSpec ⊤).hom (x₁ - x₂))) (by
        have h1 : Cech.res (P := M.presheaf) (Scheme.Hom.image_mono _ le_top :
            hV.fromSpec ''ᵁ D' ≤ hV.fromSpec ''ᵁ ⊤)
            ((M.restrictAppIso hV.fromSpec ⊤).hom (x₁ - x₂)) = 0 := h0
        have h2 := congrArg (Cech.res (P := M.presheaf) e₁.ge) h1
        rw [map_zero] at h2
        rw [Cech.res_res, ← h2, Cech.res_res])
    refine ⟨⟨f ^ n, n, rfl⟩, ?_⟩
    rw [← sub_eq_zero, ← smul_sub]
    apply (ConcreteCategory.bijective_of_isIso (M.restrictAppIso hV.fromSpec ⊤).hom).1
    change (M.restrictAppIso hV.fromSpec ⊤).hom
        ((f ^ n : Γ(X, V)) • ((x₁ - x₂ : Γ(M.restrict hV.fromSpec, ⊤)))) =
      (M.restrictAppIso hV.fromSpec ⊤).hom 0
    refine (restrictAppIso_hom_smul hV M ⊤ (f ^ n) _).trans ?_
    rw [map_zero]
    have h3 := congrArg (Cech.res (P := M.presheaf) e₂.le) hn
    rw [res_smul, map_zero, Cech.res_res, Cech.res_self] at h3
    exact h3

end QuasicoherentLocal

end Langlands.AlgebraicGeometry.Modules
