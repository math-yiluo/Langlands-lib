/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackMonoidal
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import WeilConjectures.AlgebraicGeometry.PicardFunctor

/-!
# Pullback, tensor products and the projection formula

We record how the pullback of `𝒪`-modules along a morphism of schemes `g : X ⟶ Y` interacts with
the tensor product, and the projection formula `g_* (ℱ ⊗ g^* N) ≅ g_* ℱ ⊗ N` for an invertible
`𝒪_Y`-module `N`.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.nonempty_pullback_tensorObj_iso`: the pullback of a tensor
  product is the tensor product of the pullbacks.
- `AlgebraicGeometry.Scheme.Modules.nonempty_pullback_tensorPow_iso`: the pullback of a tensor
  power is the tensor power of the pullback.
- `AlgebraicGeometry.Scheme.Modules.IsInvertible.tensorObj`,
  `AlgebraicGeometry.Scheme.Modules.IsInvertible.tensorPow`: tensor products and tensor powers of
  invertible modules are invertible.
- `AlgebraicGeometry.Scheme.Modules.IsInvertible.isQuasicoherent`: an invertible module is
  quasi-coherent.
- `AlgebraicGeometry.Scheme.Modules.IsInvertible.of_sheafOfModules`,
  `AlgebraicGeometry.Scheme.Modules.IsInvertible.sheafOfModules_isInvertible`: the two notions of
  invertibility, `AlgebraicGeometry.Scheme.Modules.IsInvertible` and
  `SheafOfModules.IsInvertible`, agree.
- `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_tensorObj`,
  `AlgebraicGeometry.Scheme.Modules.isFinitePresentation_tensorObj`: twisting by an invertible
  module preserves quasi-coherence and finite presentation.
- `AlgebraicGeometry.Scheme.Modules.projectionHom`: the projection morphism
  `g_* ℱ ⊗ N ⟶ g_* (ℱ ⊗ g^* N)`, `x ⊗ n ↦ x ⊗ η n`.
- `AlgebraicGeometry.Scheme.Modules.isIso_projectionHom`: the projection formula, i.e.
  `projectionHom` is an isomorphism for an invertible module `N`.
- `AlgebraicGeometry.Scheme.Modules.nonempty_pushforward_tensorObj_pullback_iso`: the projection
  formula `g_* (ℱ ⊗ g^* N) ≅ g_* ℱ ⊗ N` for an invertible module `N`.
- `AlgebraicGeometry.Scheme.Modules.nonempty_pushforward_pullback_iso`: its case `ℱ = 𝒪_X`.
- `AlgebraicGeometry.Scheme.Modules.nonempty_pushforward_pullback_iso_self`: if `g_* 𝒪_X ≅ 𝒪_Y`,
  then `g_* (g^* N) ≅ N` for every invertible `𝒪_Y`-module `N`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

section Tensor

/-- **The pullback of a tensor product is the tensor product of the pullbacks.** For
`g : X ⟶ Y` and `𝒪_Y`-modules `M` and `N`, `g^* (M ⊗ N) ≅ g^* M ⊗ g^* N`. -/
theorem nonempty_pullback_tensorObj_iso (g : X ⟶ Y) (M N : Y.Modules) :
    Nonempty ((pullback g).obj (M ⊗ N) ≅ (pullback g).obj M ⊗ (pullback g).obj N) :=
  ⟨(Functor.Monoidal.μIso (pullback g) M N).symm⟩

/-- **The pullback of a tensor power is the tensor power of the pullback.**
`g^* (M^{⊗ m}) ≅ (g^* M)^{⊗ m}`. -/
theorem nonempty_pullback_tensorPow_iso (g : X ⟶ Y) (M : Y.Modules) (m : ℕ) :
    Nonempty ((pullback g).obj (M.tensorPow m) ≅ ((pullback g).obj M).tensorPow m) := by
  induction m with
  | zero => exact ⟨pullbackObjUnitIso g⟩
  | succ m ih =>
    obtain ⟨e⟩ := nonempty_pullback_tensorObj_iso g M (M.tensorPow m)
    exact ⟨e ≪≫ (Iso.refl _ ⊗ᵢ ih.some)⟩

/-- **A tensor product of invertible modules is invertible.** If `M` and `N` are invertible, so is
`M ⊗ N`. -/
instance IsInvertible.tensorObj (M N : X.Modules) [M.IsInvertible] [N.IsInvertible] :
    (M ⊗ N).IsInvertible where
  exists_isoUnit x := by
    obtain ⟨U, hU, ⟨e⟩⟩ := IsInvertible.exists_isoUnit (M := M) x
    obtain ⟨V, hV, ⟨e'⟩⟩ := IsInvertible.exists_isoUnit (M := N) x
    refine ⟨U ⊓ V, ⟨hU, hV⟩, ?_⟩
    have hW (P : X.Modules) {W : X.Opens} (hW : U ⊓ V ≤ W)
        (eP : (Modules.pullback W.ι).obj P ≅ SheafOfModules.unit _) :
        Nonempty ((Modules.pullback (U ⊓ V).ι).obj P ≅ SheafOfModules.unit _) :=
      ⟨(pullbackCongr (X.homOfLE_ι hW).symm).app P ≪≫ (pullbackComp _ _).symm.app P ≪≫
        (Modules.pullback (X.homOfLE hW)).mapIso eP ≪≫ pullbackObjUnitIso _⟩
    obtain ⟨eM⟩ := hW M inf_le_left e
    obtain ⟨eN⟩ := hW N inf_le_right e'
    obtain ⟨t⟩ := nonempty_pullback_tensorObj_iso (U ⊓ V).ι M N
    exact ⟨t ≪≫ (eM ⊗ᵢ eN) ≪≫ λ_ _⟩

/-- **A tensor power of an invertible module is invertible.** -/
instance IsInvertible.tensorPow (M : X.Modules) [M.IsInvertible] (m : ℕ) :
    (M.tensorPow m).IsInvertible := by
  induction m with
  | zero => exact isInvertible_tensorUnit
  | succ m ih => exact IsInvertible.tensorObj M (M.tensorPow m)

end Tensor

section Comparison

/-- A sheaf of modules which is invertible in the sense of `SheafOfModules.IsInvertible` (locally
free of rank one) is invertible in the sense of `AlgebraicGeometry.Scheme.Modules.IsInvertible`
(locally isomorphic to `𝒪_X`). -/
lemma IsInvertible.of_sheafOfModules (M : X.Modules) [SheafOfModules.IsInvertible.{u, u, u} M] :
    M.IsInvertible where
  exists_isoUnit x := by
    obtain ⟨U, hx, ⟨e⟩⟩ := exists_mem_over_iso_unit M x
    exact ⟨U, hx, ⟨pullbackIotaUnitIsoOfOverIso e⟩⟩

/-- Conversely, an invertible module in the sense of
`AlgebraicGeometry.Scheme.Modules.IsInvertible` is invertible in the sense of
`SheafOfModules.IsInvertible`. -/
lemma IsInvertible.sheafOfModules_isInvertible (M : X.Modules) [M.IsInvertible] :
    SheafOfModules.IsInvertible.{u, u, u} M := by
  choose U hU e using fun x : X ↦ IsInvertible.exists_isoUnit (M := M) x
  refine SheafOfModules.isInvertible_of_forall_over_unit (M := M) U ?_ ?_
  · rw [Opens.coversTop_iff]
    exact IsOpenCover.mk (eq_top_iff.mpr fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hU x⟩)
  · exact fun x ↦ ⟨overIsoUnitOfPullbackIotaIso (e x).some⟩

end Comparison

section Quasicoherent

/-- **An invertible module is quasi-coherent**, being locally isomorphic to the structure
sheaf. -/
instance IsInvertible.isQuasicoherent (M : X.Modules) [M.IsInvertible] : M.IsQuasicoherent := by
  choose U hU e using fun x : X ↦ IsInvertible.exists_isoUnit (M := M) x
  have (x : X) : (M.over (U x)).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (X.ringCatSheaf.over (U x))).prop_of_iso
      (overIsoUnitOfPullbackIotaIso (e x).some).symm
      (SheafOfModules.isQuasicoherent_unit (R := X.ringCatSheaf.over (U x)))
  refine SheafOfModules.IsQuasicoherent.of_coversTop M U ?_
  rw [Opens.coversTop_iff]
  exact IsOpenCover.mk (eq_top_iff.mpr fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hU x⟩)

/-- If an invertible module `N` is trivial on an open `U`, then `(M ⊗ N)|_U ≅ M|_U`. -/
lemma nonempty_over_tensorObj_iso (M N : X.Modules) {U : X.Opens}
    (e : (pullback U.ι).obj N ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) :
    Nonempty ((M ⊗ N).over U ≅ M.over U) := by
  obtain ⟨t⟩ := nonempty_pullback_tensorObj_iso U.ι M N
  exact ⟨(overEquiv U).functor.preimageIso (overEquivObjOverIso (M ⊗ N) U ≪≫ t ≪≫
    (Iso.refl _ ⊗ᵢ e) ≪≫ ρ_ _ ≪≫ (overEquivObjOverIso M U).symm)⟩

/-- **Twisting by an invertible module preserves quasi-coherence.** If `M` is
quasi-coherent and `N` is invertible, then `M ⊗ N` is quasi-coherent. -/
theorem isQuasicoherent_tensorObj (M N : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) M] [N.IsInvertible] :
    (M ⊗ N).IsQuasicoherent := by
  choose U hU e using fun x : X ↦ IsInvertible.exists_isoUnit (M := N) x
  have (x : X) : ((M ⊗ N).over (U x)).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent (X.ringCatSheaf.over (U x))).prop_of_iso
      (nonempty_over_tensorObj_iso M N (e x).some).some.symm
      (SheafOfModules.isQuasicoherent_over M (U x))
  refine SheafOfModules.IsQuasicoherent.of_coversTop (tensorObj M N) U ?_
  rw [Opens.coversTop_iff]
  exact IsOpenCover.mk (eq_top_iff.mpr fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hU x⟩)

/-- **Twisting by an invertible module preserves finite presentation.** If `M`
is of finite presentation and `N` is invertible, then so is `M ⊗ N`. -/
theorem isFinitePresentation_tensorObj (M N : X.Modules)
    [SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) M] [N.IsInvertible] :
    (M ⊗ N).IsFinitePresentation := by
  choose U hU e using fun x : X ↦ IsInvertible.exists_isoUnit (M := N) x
  have (x : X) : SheafOfModules.IsFinitePresentation.{u} (M.over (U x)) :=
    SheafOfModules.isFinitePresentation_pushforward_of_isLeftAdjoint (Over.forget (U x)) (𝟙 _)
      (Iso.refl _)
  have (x : X) : ((M ⊗ N).over (U x)).IsFinitePresentation :=
    (SheafOfModules.isFinitePresentation (X.ringCatSheaf.over (U x))).prop_of_iso
      (nonempty_over_tensorObj_iso M N (e x).some).some.symm (this x)
  refine SheafOfModules.IsFinitePresentation.of_coversTop (tensorObj M N) U ?_
  rw [Opens.coversTop_iff]
  exact IsOpenCover.mk (eq_top_iff.mpr fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hU x⟩)

end Quasicoherent

section ProjectionHom

open Opposite

attribute [local instance] presheafMonoidalCategory presheafSymmetricCategory
  SheafOfModules.sheafificationMonoidal SheafOfModules.sheafificationBraided
  sheafificationMonoidal sheafificationBraided forgetToPresheafOfModulesLaxMonoidal

variable (g : X ⟶ Y) (F : X.Modules) (N : Y.Modules)

/-- The bilinear map `Γ(g_* F, U) × Γ(N, U) → Γ(g_* (F ⊗ g^* N), U)`,
`(x, n) ↦ x ⊗ η n`, where `η : N ⟶ g_* g^* N` is the unit of the adjunction. -/
noncomputable def projectionSectionsMap (U : Y.Opens) :
    Γ((pushforward g).obj F, U) →ₗ[Γ(Y, U)] Γ(N, U) →ₗ[Γ(Y, U)]
      Γ((pushforward g).obj (F ⊗ (pullback g).obj N), U) :=
  LinearMap.mk₂ Γ(Y, U)
    (fun x n ↦ tmulSection (M := F) (N := (pullback g).obj N) (U := g ⁻¹ᵁ U) x
      (((pullbackPushforwardAdjunction g).unit.app N).app U n))
    (fun x x' n ↦ add_tmulSection _ _ _)
    (fun r x n ↦ smul_tmulSection _ _ _)
    (fun x n n' ↦ by rw [map_add, tmulSection_add])
    (fun r x n ↦ (congrArg (tmulSection (M := F) (U := g ⁻¹ᵁ U) x) (Hom.app_smul _ r n)).trans
      (tmulSection_smul _ _ _))

/-- The sections `x ⊗ η n` of `F ⊗ g^* N` are compatible with restriction. -/
lemma tmulSection_unit_app_presheaf_map {U V : Y.Opens} (i : V ⟶ U) (x : Γ(F, g ⁻¹ᵁ U))
    (n : Γ(N, U)) :
    tmulSection (F.presheaf.map ((TopologicalSpace.Opens.map g.base).map i).op x)
        (((pullbackPushforwardAdjunction g).unit.app N).app V (N.presheaf.map i.op n)) =
      (F ⊗ (pullback g).obj N).presheaf.map ((TopologicalSpace.Opens.map g.base).map i).op
        (tmulSection x (((pullbackPushforwardAdjunction g).unit.app N).app U n)) := by
  have h₁ : ((pullbackPushforwardAdjunction g).unit.app N).app V (N.presheaf.map i.op n) =
      ((pullback g).obj N).presheaf.map ((TopologicalSpace.Opens.map g.base).map i).op
        (((pullbackPushforwardAdjunction g).unit.app N).app U n) :=
    Hom.app_presheaf_map _ i n
  rw [h₁]
  exact (tmulSection_map (M := F) (N := (pullback g).obj N)
    (leOfHom ((TopologicalSpace.Opens.map g.base).map i)) _ _).symm

/-- The morphism of presheaves of modules `g_* F ⊗ₚ N ⟶ g_* (F ⊗ g^* N)` given on sections by
`x ⊗ n ↦ x ⊗ η n`. -/
noncomputable def projectionPresheafHom :
    (forgetToPresheafOfModules Y).obj ((pushforward g).obj F) ⊗
        (forgetToPresheafOfModules Y).obj N ⟶
      (forgetToPresheafOfModules Y).obj ((pushforward g).obj (F ⊗ (pullback g).obj N)) where
  app U := ModuleCat.ofHom
    (TensorProduct.lift (R := Γ(Y, U.unop)) (projectionSectionsMap g F N U.unop))
  naturality {U U'} i := by
    ext1
    refine LinearMap.ext fun t ↦ ?_
    induction t using TensorProduct.inductionOn with
    | tmul x n =>
      have := PresheafOfModules.Monoidal.tensorObj_map_tmul (R := Y.presheaf) i x n
      refine (congrArg (TensorProduct.lift (projectionSectionsMap g F N U'.unop)) this).trans ?_
      refine (TensorProduct.lift.tmul _ _).trans ?_
      refine Eq.trans ?_ (congrArg (((forgetToPresheafOfModules Y).obj
        ((pushforward g).obj (F ⊗ (pullback g).obj N))).map i).hom
          (TensorProduct.lift.tmul _ _).symm)
      dsimp only [projectionSectionsMap, LinearMap.mk₂_apply]
      exact tmulSection_unit_app_presheaf_map g F N i.unop x n
    | add a b ha hb => rw [map_add, map_add, ha, hb]

/-- The comparison map `a(M ⊗ₚ N) ⟶ M ⊗ N` from the sheafification of the presheaf tensor
product is an isomorphism. -/
instance isIso_δ_comp_tensorHom_counit (M N : Y.Modules) :
    IsIso (Functor.OplaxMonoidal.δ (sheafification Y)
      ((forgetToPresheafOfModules Y).obj M) ((forgetToPresheafOfModules Y).obj N) ≫
        ((sheafificationAdjunction Y).counit.app M ⊗ₘ
          (sheafificationAdjunction Y).counit.app N)) := by
  have : IsIso (sheafificationAdjunction Y).counit :=
    (inferInstance : IsIso (_root_.PresheafOfModules.sheafificationAdjunction.{u}
      (𝟙 Y.ringCatSheaf.obj)).counit)
  infer_instance

/-- The projection morphism `g_* F ⊗ N ⟶ g_* (F ⊗ g^* N)`, given on sections by
`x ⊗ n ↦ x ⊗ η n` where `η : N ⟶ g_* g^* N` is the unit of the adjunction `g^* ⊣ g_*`. -/
noncomputable def projectionHom :
    (pushforward g).obj F ⊗ N ⟶ (pushforward g).obj (F ⊗ (pullback g).obj N) :=
  inv (Functor.OplaxMonoidal.δ (sheafification Y) _ _ ≫
      ((sheafificationAdjunction Y).counit.app ((pushforward g).obj F) ⊗ₘ
        (sheafificationAdjunction Y).counit.app N)) ≫
    ((sheafificationAdjunction Y).homEquiv _ _).symm (projectionPresheafHom g F N)

/-- On the presheaf tensor product, the projection morphism is `projectionPresheafHom`. -/
lemma μ_comp_map_projectionHom :
    Functor.LaxMonoidal.μ (forgetToPresheafOfModules Y) ((pushforward g).obj F) N ≫
      (forgetToPresheafOfModules Y).map (projectionHom g F N) = projectionPresheafHom g F N := by
  rw [Adjunction.rightAdjointLaxMonoidal_μ, Adjunction.homEquiv_unit, Category.assoc,
    ← Functor.map_comp, projectionHom, IsIso.hom_inv_id_assoc, ← Adjunction.homEquiv_unit,
    Equiv.apply_symm_apply]

/-- The projection morphism sends `x ⊗ n` to `x ⊗ η n`. -/
lemma projectionHom_app_tmulSection (U : Y.Opens) (x : Γ(F, g ⁻¹ᵁ U)) (n : Γ(N, U)) :
    (projectionHom g F N).app U (tmulSection (M := (pushforward g).obj F) x n) =
      tmulSection (M := F) (N := (pullback g).obj N) (U := g ⁻¹ᵁ U) x
        (((pullbackPushforwardAdjunction g).unit.app N).app U n) :=
  (congr_arg (fun φ ↦ φ.app (op U) (x ⊗ₜ n)) (μ_comp_map_projectionHom g F N)).trans
    (TensorProduct.lift.tmul _ _)

/-- The projection morphism is bijective on sections over opens on which `N` has a free
generator. -/
lemma bijective_projectionHom_app {V : Y.Opens} {e : Γ(N, V)} (he : IsFreeGenerator e)
    {W : Y.Opens} (hW : W ≤ V) : Function.Bijective ((projectionHom g F N).app W) := by
  have h₁ := he.bijective_tmulSection_right (M := (pushforward g).obj F) hW
  have h₂ := (he.pullback_unit_app g).bijective_tmulSection_right (M := F) (g.preimage_mono hW)
  have : (projectionHom g F N).app W ∘
      (fun x : Γ(F, g ⁻¹ᵁ W) ↦ tmulSection (M := (pushforward g).obj F) x
        (N.presheaf.map (homOfLE hW).op e)) =
      fun x : Γ(F, g ⁻¹ᵁ W) ↦ tmulSection x (((pullback g).obj N).presheaf.map
        (homOfLE (g.preimage_mono hW)).op
          (((pullbackPushforwardAdjunction g).unit.app N).app V e)) := by
    funext x
    rw [Function.comp_apply, projectionHom_app_tmulSection]
    exact congrArg (tmulSection x) (Hom.app_presheaf_map _ (homOfLE hW) e)
  rw [← this] at h₂
  exact (Function.Bijective.of_comp_iff _ h₁).1 h₂

/-- **The projection formula** for an invertible module. For `g: X ⟶ Y`, an `𝒪_X`-module `ℱ`
and an invertible `𝒪_Y`-module `N`, the natural map `projectionHom: g_* ℱ ⊗ N ⟶ g_* (ℱ ⊗ g^* N)`,
`x ⊗ n ↦ x ⊗ η n` with `η: N ⟶ g_* g^* N` the unit of the adjunction, is an isomorphism. -/
theorem isIso_projectionHom [N.IsInvertible] : IsIso (projectionHom g F N) := by
  have := IsInvertible.sheafOfModules_isInvertible N
  refine Hom.isIso_of_forall_bijective_app _ fun y ↦ ?_
  obtain ⟨U, hy, -, e, he⟩ := exists_isFreeGenerator N (W := ⊤) (x := y) trivial
  exact ⟨U.1, hy, fun W hW ↦ bijective_projectionHom_app g F N he hW⟩

end ProjectionHom

section ProjectionFormula

/-- **The projection formula** for an invertible module: `g_* (ℱ ⊗ g^* N) ≅ g_* ℱ ⊗ N`, the
inverse of the isomorphism `projectionHom` (`isIso_projectionHom`). -/
theorem nonempty_pushforward_tensorObj_pullback_iso (g : X ⟶ Y) (F : X.Modules) (N : Y.Modules)
    [N.IsInvertible] :
    Nonempty ((pushforward g).obj (F ⊗ (pullback g).obj N) ≅ (pushforward g).obj F ⊗ N) :=
  have := isIso_projectionHom g F N
  ⟨(asIso (projectionHom g F N)).symm⟩

/-- **The projection formula** for an invertible module and the structure sheaf. For
`g : X ⟶ Y` and an invertible `𝒪_Y`-module `N`, `g_* (g^* N) ≅ g_* 𝒪_X ⊗ N`. -/
theorem nonempty_pushforward_pullback_iso (g : X ⟶ Y) (N : Y.Modules) [N.IsInvertible] :
    Nonempty ((pushforward g).obj ((pullback g).obj N) ≅
      (pushforward g).obj (𝟙_ X.Modules) ⊗ N) := by
  obtain ⟨e⟩ := nonempty_pushforward_tensorObj_pullback_iso g (𝟙_ X.Modules) N
  exact ⟨(pushforward g).mapIso (λ_ _).symm ≪≫ e⟩

/-- If `g_* 𝒪_X ≅ 𝒪_Y`, then `g_* (g^* N) ≅ N` for every invertible `𝒪_Y`-module `N`. -/
theorem nonempty_pushforward_pullback_iso_self (g : X ⟶ Y)
    (e : (pushforward g).obj (𝟙_ X.Modules) ≅ 𝟙_ Y.Modules) (N : Y.Modules) [N.IsInvertible] :
    Nonempty ((pushforward g).obj ((pullback g).obj N) ≅ N) := by
  obtain ⟨e'⟩ := nonempty_pushforward_pullback_iso g N
  exact ⟨e' ≪≫ (e ⊗ᵢ Iso.refl N) ≪≫ λ_ N⟩

end ProjectionFormula

end AlgebraicGeometry.Scheme.Modules
