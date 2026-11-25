/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.AlgebraicGeometry.AffineSpace.Subtraction
public import WeilConjectures.FourierTransform.AffineSpace.Unit

/-!
# Convolution of Fourier kernels

The ingredients of the computation `𝒦_{ψ⁻¹} ∗ 𝒦_ψ ≅ Δ_* Λ(-r)[-2r]` of the convolution of the
two Fourier kernels on `V = 𝔸(n; S)`. On the triple product `V ×_S V ×_S V` with points
`(x, ξ, y)`:

* the integrand `ℒ_{ψ(⟨x, ξ⟩)} ⊗ᴸ ℒ_{ψ⁻¹(⟨ξ, y⟩)}` is the pullback `ℒ_{ψ(⟨ξ, x - y⟩)}` of the
  Fourier kernel along the shear `(x, ξ, y) ↦ (ξ, x - y)`
  (`AlgebraicGeometry.Etale.nonempty_iso_fourierKernel_convolution_integrand`);
* the shear exhibits the outer projection `r₁₃` as the base change of the second projection
  `p₂` along the subtraction, so the convolution is `sub^* Rp₂,! 𝒦_ψ`
  (`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_tripleProj₁₃_tripleShear`);
* `Rp₂,! 𝒦_ψ` is `FT_ψ(Λ)[-r] ≅ z_* Λ(-r)[-2r]`
  (`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerShriek_fourierKernel`);
* the diagonal is the base change of the zero section along the subtraction, so
  `sub^* z_* ≅ Δ_* π^*` (`AlgebraicGeometry.Etale.nonempty_iso_leftDerivedUpperStar_sub`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open AlgebraicGeometry.AffineSpace

section General

variable (A : Type*) [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]
variable {S V V' V'' : Scheme.{u}} (π : V ⟶ S) (π' : V' ⟶ S) (π'' : V'' ⟶ S)

/-- The convolution unfolded, `𝒦' ∗ 𝒦 = Rr₁₃,!(r₁₂^* 𝒦 ⊗ᴸ r₂₃^* 𝒦')`. Rewriting with this lemma,
proved in the generic setting, spares the kernel from unfolding the convolution of concrete
coefficients. -/
theorem kernelConvolution_eq [HasCompactification (pullback.tripleProj₁₃ π π' π'')]
    (𝒦 : DerivedCategory (Sheaf (pullback π π').smallEtaleTopology A))
    (𝒦' : DerivedCategory (Sheaf (pullback π' π'').smallEtaleTopology A)) :
    kernelConvolution A π π' π'' 𝒦 𝒦' =
      (R(pullback.tripleProj₁₃ π π' π'')_![A]).obj
        ((derivedTensorRight A (pullback (pullback.snd π π') (pullback.fst π' π''))
          ((D((pullback.snd (pullback.snd π π') (pullback.fst π' π''))^*[A])).obj 𝒦')).obj
          ((D((pullback.fst (pullback.snd π π') (pullback.fst π' π''))^*[A])).obj 𝒦)) :=
  rfl

end General

section ArtinSchreier

variable (Λ : Type (u + 1)) [CommRing Λ] {p : ℕ} [Fact p.Prime] [Invertible (p : Λ)]

/-- If the global sections of `Y` have characteristic `p` and there are morphisms `X ⟶ Y` and
`Y ⟶ X`, then the global sections of `X` have characteristic `p`: `p` vanishes on `X`, which is
nonempty. -/
lemma charP_appTop_of_hom {X Y : Scheme.{u}} (f : X ⟶ Y) (s : Y ⟶ X) [CharP Γ(Y, ⊤) p] :
    CharP Γ(X, ⊤) p := by
  have : Nontrivial Γ(Y, ⊤) := CharP.nontrivial_of_char_ne_one (Fact.out : p.Prime).ne_one
  have : Nontrivial Γ(X, ⊤) := s.appTop.hom.domain_nontrivial
  exact (CharP.charP_iff_prime_eq_zero Fact.out).2 (by
    rw [← map_natCast f.appTop.hom, CharP.cast_eq_zero, map_zero])

/-- An Artin–Schreier sheaf is flat, having a tensor inverse. -/
lemma flat_artinSchreierSheafZMod (X : Scheme.{u}) [CharP Γ(X, ⊤) p] (Ψ : AddChar (ZMod p) Λ)
    (f : Γ(X, ⊤)) : ObjectProperty.flat (artinSchreierSheafZMod X Ψ f) := by
  let := X.overSpecZModOfCharP p
  obtain ⟨e⟩ := nonempty_iso_artinSchreierSheafOf_neg X
    (Ψ.compAddMonoidHom AddEquiv.ulift.toAddMonoidHom) f
  exact ObjectProperty.flat_of_tensorIso e

/-- Artin–Schreier sheaves of the same character multiply as the functions add:
`ℒ_{ψ(f)} ⊗ ℒ_{ψ(g)} ≅ ℒ_{ψ(f + g)}`. -/
lemma nonempty_iso_artinSchreierSheafZMod_add (X : Scheme.{u}) [CharP Γ(X, ⊤) p]
    (Ψ : AddChar (ZMod p) Λ) (f g : Γ(X, ⊤)) :
    Nonempty (artinSchreierSheafZMod X Ψ f ⊗ artinSchreierSheafZMod X Ψ g ≅
      artinSchreierSheafZMod X Ψ (f + g)) := by
  let := X.overSpecZModOfCharP p
  unfold artinSchreierSheafZMod
  exact nonempty_iso_artinSchreierSheafOf_add _ _ f g

/-- The Artin–Schreier sheaf of the inverse character is that of the opposite function:
`ℒ_{ψ⁻¹(f)} ≅ ℒ_{ψ(-f)}`. -/
lemma nonempty_iso_artinSchreierSheafZMod_inv (X : Scheme.{u}) [CharP Γ(X, ⊤) p]
    (Ψ : AddChar (ZMod p) Λ) (f : Γ(X, ⊤)) :
    Nonempty (artinSchreierSheafZMod X Ψ⁻¹ f ≅ artinSchreierSheafZMod X Ψ (-f)) := by
  let := X.overSpecZModOfCharP p
  have hΨ : Ψ⁻¹.compAddMonoidHom AddEquiv.ulift.toAddMonoidHom =
      (Ψ.compAddMonoidHom AddEquiv.ulift.toAddMonoidHom)⁻¹ := by
    ext; simp
  unfold artinSchreierSheafZMod
  rw [hΨ]
  exact ⟨(nonempty_iso_artinSchreierSheafOf_neg_inv X _ f).some.symm⟩

/-- For a flat sheaf `F`, if `F ⊗ G ≅ H` as sheaves then `F[0] ⊗ᴸ G[0] ≅ H[0]`.
The derived tensor product is written with `AlgebraicGeometry.Etale.derivedTensor`, not with
`⊗`, which the kernel is slow to identify with it. -/
lemma nonempty_iso_derivedTensor_singleFunctor (X : Scheme.{u})
    {F G H : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (hF : ObjectProperty.flat F) (e : Nonempty (F ⊗ G ≅ H)) :
    Nonempty (((derivedTensor _ X).obj ((DerivedCategory.singleFunctor _ 0).obj F)).obj
        ((DerivedCategory.singleFunctor _ 0).obj G) ≅
      (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj
        H) :=
  ⟨singleFunctorObjTensorIso _ _ hF ≪≫ (DerivedCategory.singleFunctor _ 0).mapIso e.some⟩

/-- The derived tensor product of two Artin–Schreier sheaves of the same character, placed in
degree zero, is the Artin–Schreier sheaf of the sum: `ℒ_{ψ(f)} ⊗ᴸ ℒ_{ψ(g)} ≅ ℒ_{ψ(f + g)}`. -/
lemma nonempty_iso_singleFunctor_artinSchreierSheafZMod_tensor (X : Scheme.{u})
    [CharP Γ(X, ⊤) p] (Ψ : AddChar (ZMod p) Λ) (f g : Γ(X, ⊤)) :
    Nonempty (((derivedTensor _ X).obj
        ((DerivedCategory.singleFunctor _ 0).obj (artinSchreierSheafZMod X Ψ f))).obj
        ((DerivedCategory.singleFunctor _ 0).obj (artinSchreierSheafZMod X Ψ g)) ≅
      (DerivedCategory.singleFunctor (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0).obj
        (artinSchreierSheafZMod X Ψ (f + g))) :=
  nonempty_iso_derivedTensor_singleFunctor Λ X (flat_artinSchreierSheafZMod Λ X Ψ f)
    (nonempty_iso_artinSchreierSheafZMod_add Λ X Ψ f g)

/-- `T.flip N M ≅ R` from `M ≅ M'`, `N ≅ N'` and `T M' N' ≅ R`, stated for an abstract bifunctor
so that the kernel never unfolds the concrete derived tensor product. -/
private lemma nonempty_iso_flip_obj_obj {C : Type*} [Category C] (T : C ⥤ C ⥤ C)
    {M M' N N' R : C} (a : M ≅ M') (b : N ≅ N') (t : (T.obj M').obj N' ≅ R) :
    Nonempty ((T.flip.obj N).obj M ≅ R) :=
  ⟨(T.flip.obj N).mapIso a ≪≫ (T.obj M').mapIso b ≪≫ t⟩

/-- The pullback of an Artin–Schreier sheaf placed in degree zero:
`g^* ℒ_{ψ(b)}[0] ≅ ℒ_{ψ(g^* b)}[0]`, composed with a given isomorphism out of the latter. -/
lemma nonempty_iso_mapDerivedCategory_artinSchreierSheafZMod {X Y : Scheme.{u}}
    [CharP Γ(X, ⊤) p] [CharP Γ(Y, ⊤) p] (g : X ⟶ Y) (Ψ : AddChar (ZMod p) Λ) (b : Γ(Y, ⊤))
    {F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (e : artinSchreierSheafZMod X Ψ (g.appTop b) ≅ F) :
    Nonempty ((D((g)^*[ModuleCat.{u + 1} Λ])).obj
        ((DerivedCategory.singleFunctor _ 0).obj (artinSchreierSheafZMod Y Ψ b)) ≅
      (DerivedCategory.singleFunctor _ 0).obj F) :=
  ⟨(((g)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso (artinSchreierSheafZModPullbackIso g Ψ b ≪≫ e)⟩

/-- The integrand of a convolution of two Artin–Schreier kernels. For morphisms
`g₁ g₂ g₃ : X ⟶ Y`, a function `b` on `Y`, and an identification `ℒ_{ψ'(g₂^* b)} ≅ ℒ_{ψ(c)}`
with `g₁^* b + c = g₃^* b`, one has `g₁^* ℒ_{ψ(b)} ⊗ᴸ g₂^* ℒ_{ψ'(b)} ≅ g₃^* ℒ_{ψ(b)}`. -/
lemma nonempty_iso_derivedTensorRight_artinSchreierSheafZMod {X Y : Scheme.{u}}
    [CharP Γ(X, ⊤) p] [CharP Γ(Y, ⊤) p] (g₁ g₂ g₃ : X ⟶ Y) (Ψ Ψ' : AddChar (ZMod p) Λ)
    (b : Γ(Y, ⊤)) (c : Γ(X, ⊤))
    (e : artinSchreierSheafZMod X Ψ' (g₂.appTop b) ≅ artinSchreierSheafZMod X Ψ c)
    (hb : g₁.appTop b + c = g₃.appTop b) :
    Nonempty ((derivedTensorRight (ModuleCat.{u + 1} Λ) X
        ((D((g₂)^*[ModuleCat.{u + 1} Λ])).obj
          ((DerivedCategory.singleFunctor _ 0).obj (artinSchreierSheafZMod Y Ψ' b)))).obj
        ((D((g₁)^*[ModuleCat.{u + 1} Λ])).obj
          ((DerivedCategory.singleFunctor _ 0).obj (artinSchreierSheafZMod Y Ψ b))) ≅
      (L((g₃)^*[ModuleCat.{u + 1} Λ])).obj
        ((DerivedCategory.singleFunctor _ 0).obj (artinSchreierSheafZMod Y Ψ b))) := by
  obtain ⟨a₁⟩ := nonempty_iso_mapDerivedCategory_artinSchreierSheafZMod Λ g₁ Ψ b (Iso.refl _)
  obtain ⟨a₂⟩ := nonempty_iso_mapDerivedCategory_artinSchreierSheafZMod Λ g₂ Ψ' b e
  obtain ⟨t⟩ := nonempty_iso_singleFunctor_artinSchreierSheafZMod_tensor Λ X Ψ (g₁.appTop b) c
  rw [hb] at t
  obtain ⟨e₃⟩ := nonempty_iso_leftDerivedUpperStar_singleFunctor Λ g₃ _ _
    (artinSchreierSheafZModPullbackIso g₃ Ψ b)
  exact nonempty_iso_flip_obj_obj (derivedTensor _ X) a₁ a₂ (t ≪≫ e₃.symm)

end ArtinSchreier
section Convolution

variable (Λ : Type (u + 1)) [CommRing Λ] {p : ℕ} [Fact p.Prime] [Invertible (p : Λ)]
variable (n : Type u) (S : Scheme.{u})

/-- The global sections of the triple product `𝔸(n; S) ×_S 𝔸(n; S) ×_S 𝔸(n; S)` have
characteristic `p` when those of `𝔸(n; S) ×_S 𝔸(n; S)` do: the projection `r₁₂` and the
morphism `(x, ξ) ↦ (x, ξ, x)` go back and forth. -/
lemma charP_appTop_tripleProduct [CharP Γ(pullback (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S), ⊤) p] :
    CharP Γ(pullback (pullback.snd (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))
      (pullback.fst (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S)), ⊤) p :=
  charP_appTop_of_hom (pullback.fst _ _)
    (pullback.lift (𝟙 _) (pullback.lift (pullback.snd _ _) (pullback.fst _ _)
      pullback.condition.symm) (by rw [Category.id_comp, pullback.lift_fst]))

variable [Fintype n]

/-- The integrand of the convolution `𝒦_{ψ⁻¹} ∗ 𝒦_ψ` on the triple product with points
`(x, ξ, y)`: `r₁₂^* 𝒦_ψ ⊗ᴸ r₂₃^* 𝒦_{ψ⁻¹} = ℒ_{ψ(⟨x, ξ⟩ - ⟨ξ, y⟩)}` is the pullback of the
Fourier kernel `𝒦_ψ` along the shear `(x, ξ, y) ↦ (ξ, x - y)`.
(sketch blueprint: `proposition-fourier-inversion`) -/
theorem nonempty_iso_fourierKernel_convolution_integrand
    [CharP Γ(pullback (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S), ⊤) p] (Ψ : AddChar (ZMod p) Λ) :
    Nonempty ((derivedTensorRight (ModuleCat.{u + 1} Λ)
        (pullback (pullback.snd (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))
          (pullback.fst (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S)))
        ((D((pullback.snd (pullback.snd (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))
          (pullback.fst (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S)))^*[ModuleCat.{u + 1} Λ])).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            (fourierKernel Λ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) Ψ⁻¹ (stdPairing n S))))).obj
        ((D((pullback.fst (pullback.snd (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))
          (pullback.fst (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S)))^*[ModuleCat.{u + 1} Λ])).obj
          ((DerivedCategory.singleFunctor _ 0).obj
            (fourierKernel Λ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) Ψ (stdPairing n S)))) ≅
      (L((pullback.tripleShear (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S)
          (sub_over n S))^*[ModuleCat.{u + 1} Λ])).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (fourierKernel Λ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) Ψ (stdPairing n S)))) := by
  have := charP_appTop_tripleProduct n S (p := p)
  obtain ⟨e⟩ := nonempty_iso_artinSchreierSheafZMod_inv Λ _ Ψ
    ((pullback.snd (pullback.snd (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))
      (pullback.fst (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))).appTop (stdPairing n S))
  exact nonempty_iso_derivedTensorRight_artinSchreierSheafZMod Λ _ _ _ Ψ Ψ⁻¹ (stdPairing n S) _ e
    (by rw [tripleShear_sub_appTop_stdPairing, sub_eq_add_neg])

omit [Fintype n] in
/-- The shear `(x, ξ, y) ↦ (ξ, x - y)` exhibits the outer projection `r₁₃` of the triple
product as the base change of the second projection `p₂` along the subtraction, so by
compact-support base change `Rr₁₃,! sh^* K ≅ sub^* Rp₂,! K`. -/
theorem nonempty_iso_rightDerivedLowerShriek_tripleProj₁₃_tripleShear [Finite Λ]
    [HasCompactification (pullback.snd (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))]
    [HasCompactification
      (pullback.tripleProj₁₃ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))]
    (K : DerivedCategory (Sheaf (pullback (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S)).smallEtaleTopology
      (ModuleCat.{u + 1} Λ))) :
    Nonempty ((R(pullback.tripleProj₁₃ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S)
        (𝔸(n; S) ↘ S))_![ModuleCat.{u + 1} Λ]).obj
        ((L((pullback.tripleShear (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S)
          (sub_over n S))^*[ModuleCat.{u + 1} Λ])).obj K) ≅
      (L((sub n S)^*[ModuleCat.{u + 1} Λ])).obj
        ((R(pullback.snd (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))_![ModuleCat.{u + 1} Λ]).obj K)) := by
  have sq := pullback.isPullback_tripleShear_tripleProj₁₃ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S)
    (𝔸(n; S) ↘ S) (sub_over n S)
  have : QuasiCompact (pullback.tripleProj₁₃ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S)) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) sq inferInstance
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ sq
  exact ⟨((asIso (rightDerivedLowerShriekBaseChangeMap Λ sq)).app K).symm⟩

/-- `H Y ≅ (F ⋙ G ⋙ H ⋙ [r]) X [-r]` from `F X ≅ X'` and `G X' ≅ Y`, stated for abstract functors
so that the kernel never unfolds the concrete derived functors. -/
private lemma nonempty_iso_shiftFunctor_comp_obj {C₁ C₂ C₃ D : Type*} [Category C₁]
    [Category C₂] [Category C₃] [Category D] [HasShift D ℤ] (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃)
    (H : C₃ ⥤ D) {X : C₁} {X' : C₂} {Y : C₃} (a : F.obj X ≅ X') (b : G.obj X' ≅ Y) (r : ℤ) :
    Nonempty (H.obj Y ≅
      (shiftFunctor D (-r)).obj ((F ⋙ G ⋙ H ⋙ shiftFunctor D r).obj X)) :=
  ⟨H.mapIso (G.mapIso a ≪≫ b).symm ≪≫
    ((shiftFunctorCompIsoId D r (-r) (add_neg_cancel r)).app _).symm⟩

/-- `T' (R U) [m][m] ≅ R O [2m]` for a functor `R` commuting with shifts, from
`R (T U [2m]) ≅ T' (R U) [2m]` and `T U ≅ O`, stated for abstract functors so that the kernel
never unfolds the concrete derived functors. -/
private lemma nonempty_iso_shiftFunctor_shiftFunctor_obj {C D : Type*} [Category C]
    [Category D] [HasShift C ℤ] [HasShift D ℤ] (R : C ⥤ D) [R.CommShift ℤ] (T : C ⥤ C)
    (T' : D ⥤ D) {U O : C} (o : T.obj U ≅ O) (m : ℤ)
    (t : R.obj ((T ⋙ shiftFunctor C (2 * m)).obj U) ≅
      (T' ⋙ shiftFunctor D (2 * m)).obj (R.obj U)) :
    Nonempty ((shiftFunctor D m).obj ((shiftFunctor D m).obj (T'.obj (R.obj U))) ≅
      (shiftFunctor D (2 * m)).obj (R.obj O)) :=
  ⟨((shiftFunctorAdd' D m m (2 * m) (by ring)).app _).symm ≪≫ t.symm ≪≫
    (R.commShiftIso (2 * m)).app _ ≪≫ (shiftFunctor D (2 * m)).mapIso (R.mapIso o)⟩

/-- The Tate twist of the constant complex is the Tate twisting object: `Λ(m) ≅ Λ_X(m)`. -/
lemma nonempty_iso_tateTwist_obj_unit [HasTateTwist Λ] (X : Scheme.{u}) (m : ℤ) :
    Nonempty ((tateTwist Λ X m).obj (𝟙_ _) ≅ tateObject Λ X m) :=
  ⟨derivedTensorLeftUnitor _ X _⟩

/-- `Rp₂,! 𝒦_ψ ≅ FT_ψ(Λ)[-r]`, `r = #n`: the transform of `Λ` is `Rp₂,!(p₁^* Λ ⊗ᴸ 𝒦_ψ)[r]`. -/
lemma nonempty_iso_rightDerivedLowerShriek_fourierKernel_affineFourierTransform
    [CharP Γ(pullback (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S), ⊤) p]
    [HasCompactification (pullback.snd (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))]
    (Ψ : AddChar (ZMod p) Λ) :
    Nonempty ((R(pullback.snd (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))_![ModuleCat.{u + 1} Λ]).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (fourierKernel Λ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) Ψ (stdPairing n S))) ≅
      (shiftFunctor _ (-(Fintype.card n : ℤ))).obj
        ((affineFourierTransform Λ n S Ψ).obj (𝟙_ _))) :=
  nonempty_iso_shiftFunctor_comp_obj
    D((pullback.fst (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))^*[ModuleCat.{u + 1} Λ])
    (derivedTensorRight _ _ ((DerivedCategory.singleFunctor _ 0).obj
      (fourierKernel Λ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) Ψ (stdPairing n S))))
    (R(pullback.snd (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))_![ModuleCat.{u + 1} Λ])
    (((leftDerivedUpperStarIsoMapDerivedCategory _ _).app _).symm ≪≫
      leftDerivedUpperStarUnitIso _ _) (derivedTensorLeftUnitor _ _ _) (Fintype.card n : ℤ)

/-- `δ₀(-r)[-r][-r] ≅ z_* Λ(-r)[-2r]`, by the projection formula for the zero section `z`. -/
lemma nonempty_iso_shiftFunctor_tateTwist_skyscraperZero [Finite Λ] [HasTateTwist Λ]
    [HasInvertibleExponent Λ S] :
    Nonempty ((shiftFunctor _ (-(Fintype.card n : ℤ))).obj
          ((shiftFunctor _ (-(Fintype.card n : ℤ))).obj
            ((tateTwist Λ (𝔸(n; S)) (-(Fintype.card n : ℤ))).obj (skyscraperZero Λ n S))) ≅
      (shiftFunctor _ (2 * -(Fintype.card n : ℤ))).obj
        ((R((zeroSection n S)_*[ModuleCat.{u + 1} Λ])).obj
          (tateObject Λ S (-(Fintype.card n : ℤ))))) := by
  obtain ⟨o⟩ := nonempty_iso_tateTwist_obj_unit Λ S (-(Fintype.card n : ℤ))
  obtain ⟨t⟩ := nonempty_iso_rightDerivedLowerStar_twistShift Λ (zeroSection n S)
    (-(Fintype.card n : ℤ)) (𝟙_ _)
  exact nonempty_iso_shiftFunctor_shiftFunctor_obj (R((zeroSection n S)_*[ModuleCat.{u + 1} Λ]))
    (tateTwist Λ S (-(Fintype.card n : ℤ))) (tateTwist Λ 𝔸(n; S) (-(Fintype.card n : ℤ)))
    o (-(Fintype.card n : ℤ)) t

/-- `Rp₂,! 𝒦_ψ = FT_ψ(Λ)[-r]` is the skyscraper `z_* Λ(-r)[-2r]` at the origin, `r = #n`, by
`AlgebraicGeometry.Etale.nonempty_iso_affineFourierTransform_unit`. -/
theorem nonempty_iso_rightDerivedLowerShriek_fourierKernel [Finite Λ] [HasInvertibleExponent Λ S]
    [HasTateTwist Λ] [HasTateTwist.IsNormalized Λ]
    [CharP Γ(pullback (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S), ⊤) p]
    [HasCompactification (pullback.snd (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))]
    (Ψ : AddChar (ZMod p) Λ) (hΨ : IsUnit (Ψ 1 - 1)) :
    Nonempty ((R(pullback.snd (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S))_![ModuleCat.{u + 1} Λ]).obj
        ((DerivedCategory.singleFunctor _ 0).obj
          (fourierKernel Λ (𝔸(n; S) ↘ S) (𝔸(n; S) ↘ S) Ψ (stdPairing n S))) ≅
      (shiftFunctor _ (2 * -(Fintype.card n : ℤ))).obj
        ((R((zeroSection n S)_*[ModuleCat.{u + 1} Λ])).obj
          (tateObject Λ S (-(Fintype.card n : ℤ))))) := by
  obtain ⟨e₁⟩ := nonempty_iso_rightDerivedLowerShriek_fourierKernel_affineFourierTransform Λ n S Ψ
  obtain ⟨e⟩ := nonempty_iso_affineFourierTransform_unit Λ n S Ψ hΨ
  obtain ⟨e₂⟩ := nonempty_iso_shiftFunctor_tateTwist_skyscraperZero Λ n S
  exact ⟨e₁ ≪≫ (shiftFunctor _ (-(Fintype.card n : ℤ))).mapIso e ≪≫ e₂⟩

omit [Fintype n] in
/-- The diagonal is the base change of the zero section along the subtraction
(`AlgebraicGeometry.AffineSpace.isPullback_diagonal_sub`), so
`sub^* (Rz_* M)[a] ≅ (RΔ_* π^* M)[a]` by proper base change. -/
theorem nonempty_iso_leftDerivedUpperStar_sub [Finite Λ] (a : ℤ)
    (M : DerivedCategory (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty ((L((sub n S)^*[ModuleCat.{u + 1} Λ])).obj
        ((shiftFunctor _ a).obj ((R((zeroSection n S)_*[ModuleCat.{u + 1} Λ])).obj M)) ≅
      (shiftFunctor _ a).obj ((R((pullback.diagonal (𝔸(n; S) ↘ S))_*[ModuleCat.{u + 1} Λ])).obj
        ((L((𝔸(n; S) ↘ S)^*[ModuleCat.{u + 1} Λ])).obj M))) := by
  let A := ModuleCat.{u + 1} Λ
  have sq := isPullback_diagonal_sub n S
  have := isIso_rightDerivedLowerShriekBaseChangeMap Λ sq
  exact ⟨((L((sub n S)^*[A])).commShiftIso a).app _ ≪≫ (shiftFunctor _ a).mapIso
    ((L((sub n S)^*[A])).mapIso
        ((rightDerivedLowerShriekIsoRightDerivedLowerStar A (zeroSection n S)).app M).symm ≪≫
      (asIso (rightDerivedLowerShriekBaseChangeMap Λ sq)).app M ≪≫
      (rightDerivedLowerShriekIsoRightDerivedLowerStar A
        (pullback.diagonal (𝔸(n; S) ↘ S))).app _)⟩

/-- `sub^* (z_* Λ(-r)[-2r]) ≅ Δ_* Λ(-r)[-2r]`, `r = #n`: the diagonal is the fibre of the
subtraction over the zero section. -/
theorem nonempty_iso_leftDerivedUpperStar_sub_tateObject [Finite Λ] [HasTateTwist Λ]
    [HasInvertibleExponent Λ S] :
    Nonempty ((L((sub n S)^*[ModuleCat.{u + 1} Λ])).obj
        ((shiftFunctor _ (2 * -(Fintype.card n : ℤ))).obj
          ((R((zeroSection n S)_*[ModuleCat.{u + 1} Λ])).obj
            (tateObject Λ S (-(Fintype.card n : ℤ))))) ≅
      (shiftFunctor _ (-2 * (Fintype.card n : ℤ))).obj
        ((R((pullback.diagonal (𝔸(n; S) ↘ S))_*[ModuleCat.{u + 1} Λ])).obj
          (tateObject Λ (𝔸(n; S)) (-(Fintype.card n : ℤ))))) := by
  have := HasInvertibleExponent.of_hom (Λ := Λ) (𝔸(n; S) ↘ S)
  obtain ⟨e⟩ := nonempty_iso_leftDerivedUpperStar_sub Λ n S (2 * -(Fintype.card n : ℤ))
    (tateObject Λ S (-(Fintype.card n : ℤ)))
  exact ⟨e ≪≫ (shiftFunctor _ _).mapIso
      ((R((pullback.diagonal (𝔸(n; S) ↘ S))_*[ModuleCat.{u + 1} Λ])).mapIso
        (leftDerivedUpperStarTateObjectIso _ _)) ≪≫
    eqToIso (congrArg (fun a : ℤ ↦ (shiftFunctor _ a).obj _) (by ring))⟩

end Convolution

end AlgebraicGeometry.Etale
