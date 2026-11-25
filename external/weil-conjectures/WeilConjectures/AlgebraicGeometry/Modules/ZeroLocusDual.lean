/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
public import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus

/-!
# The ideal of the zero scheme of a section is the image of its dual

Let `ℳ` be an invertible `𝒪_X`-module and `s: 𝒪_X ⟶ ℳ` a global section. The zero scheme
`Z(s)` is defined by its local equations (`AlgebraicGeometry.Scheme.Modules.Hom.zeroLocus`);
this file shows that its ideal sheaf is the image of the transpose `s^∨: ℳ^∨ ⟶ 𝒪_X^∨ ≅ 𝒪_X`,
as subobjects of `𝒪_X` in the abelian category of `𝒪_X`-modules.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.dualUnitIso`: the identification `𝒪_X^∨ ≅ 𝒪_X`, `λ ↦ λ(1)`.
- `AlgebraicGeometry.Scheme.Modules.Hom.adjointSection`: the global section
  `s: 𝒪_X ⟶ M ⊗ N^∨` corresponding to a morphism `φ: N ⟶ M` with `N` invertible.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.Hom.imageSubobject_eq_mk_toModulesι`: for a morphism
  `ψ: ℒ ⟶ 𝒪_X` from an invertible module, the image of `ψ` is the ideal sheaf of `Z(ψ)`.
- `AlgebraicGeometry.Scheme.Modules.Hom.zeroLocus_dualMap_comp_dualUnitIso`: `Z(s^∨) = Z(s)`.
- `AlgebraicGeometry.Scheme.Modules.Hom.imageSubobject_dualMap_comp_dualUnitIso`: the ideal sheaf
  of `Z(s)` is the image of `s^∨: ℳ^∨ ⟶ 𝒪_X`.
- `AlgebraicGeometry.Scheme.Modules.Hom.zeroLocus_adjointSection`: the section `s` of
  `M ⊗ N^{-1}` corresponding to a morphism `φ: N ⟶ M` of invertible modules has `Z(s) = Z(φ)`.
- `AlgebraicGeometry.Scheme.Modules.nonempty_dual_pullback_iso_pullback_dual`:
  `(g^* N)^∨ ≅ g^* (N^∨)` for invertible `N`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The identification `𝒪_X^∨ = Hom(𝒪_X, 𝒪_X) ≅ 𝒪_X`, `λ ↦ λ(1)`, given by the evaluation
`𝒪_X ⊗ 𝒪_X^∨ ⟶ 𝒪_X`. -/
noncomputable def dualUnitIso : (𝟙_ X.Modules)ᵛ ≅ 𝟙_ X.Modules :=
  (λ_ _).symm ≪≫ asIso (dualEvaluation (𝟙_ X.Modules))

/-- The evaluation `M ⊗ M^∨ ⟶ 𝒪_X` is the counit of the tensor-hom adjunction. -/
lemma dualEvaluation_eq_tensorHomEquiv_symm (M : X.Modules) :
    dualEvaluation M = (SheafOfModules.tensorHomEquiv M Mᵛ (𝟙_ X.Modules)).symm (𝟙 _) :=
  rfl

/-- The transpose `s^∨ : M^∨ ⟶ 𝒪_X^∨ ≅ 𝒪_X` of a section `s : 𝒪_X ⟶ M` is
`λ ↦ λ(s)`, i.e. the evaluation `𝒪_X ⊗ M^∨ ⟶ M ⊗ M^∨ ⟶ 𝒪_X`. -/
lemma dualMap_comp_dualUnitIso_hom {M : X.Modules} (s : 𝟙_ X.Modules ⟶ M) :
    dualMap s ≫ dualUnitIso.hom = (λ_ _).inv ≫ s ▷ Mᵛ ≫ dualEvaluation M := by
  have h := MonoidalClosed.id_tensor_pre_app_comp_ev s (𝟙_ X.Modules)
  rw [pre_app] at h
  rw [dualUnitIso, Iso.trans_hom, Iso.symm_hom, asIso_hom, leftUnitor_inv_naturality_assoc]
  congr 1

namespace Hom

/-- A morphism `ψ : L ⟶ 𝒪_X` from an invertible module lands in the ideal sheaf of its zero
scheme: its composite with the restriction `𝒪_X ⟶ (ι_{Z(ψ)})_* 𝒪_{Z(ψ)}` vanishes. -/
lemma comp_toPushforwardSubscheme_zeroLocus {L : X.Modules}
    [SheafOfModules.IsInvertible.{u, u, u} L] (ψ : L ⟶ Modules.unit X) :
    ψ ≫ ψ.zeroLocus.toPushforwardSubscheme = 0 := by
  refine Modules.hom_ext _ _ fun W ↦ ?_
  ext m
  have key (x : W) : ∃ V : X.affineOpens, x.1 ∈ V.1 ∧ V.1 ≤ W := by
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open x.2 W.2
    exact ⟨⟨V, hV⟩, hxV, hVW⟩
  choose V hxV hVW using key
  let T : X.Modules := (SheafOfModules.pushforward ψ.zeroLocus.subschemeι.toRingCatSheafHom).obj
    (SheafOfModules.unit ψ.zeroLocus.subscheme.ringCatSheaf)
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨T.presheaf, T.isSheaf⟩ (fun x ↦ (V x).1) W
    (fun x ↦ homOfLE (hVW x))
    (fun x hx ↦ TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxV _⟩) _ _ fun x ↦ ?_
  have h1 := Hom.app_presheaf_map (ψ ≫ ψ.zeroLocus.toPushforwardSubscheme) (homOfLE (hVW x)) m
  have h2 : ψ.zeroLocus.subschemeι.app (V x).1
      (ψ.app (V x).1 (L.presheaf.map (homOfLE (hVW x)).op m)) = 0 := by
    rw [← IdealSheafData.mem_idealOfOpens_iff, IdealSheafData.idealOfOpens_eq_ideal]
    exact ψ.app_mem_ideal_zeroLocus _ _
  refine h1.symm.trans (h2.trans ?_)
  exact (map_zero _).symm

/-- The factorization of a morphism `ψ : L ⟶ 𝒪_X` from an invertible module through the ideal
sheaf of its zero scheme. -/
noncomputable def toZeroLocusToModules {L : X.Modules} [SheafOfModules.IsInvertible.{u, u, u} L]
    (ψ : L ⟶ Modules.unit X) : L ⟶ ψ.zeroLocus.toModules :=
  kernel.lift _ ψ ψ.comp_toPushforwardSubscheme_zeroLocus

@[reassoc (attr := simp)]
lemma toZeroLocusToModules_toModulesι {L : X.Modules} [SheafOfModules.IsInvertible.{u, u, u} L]
    (ψ : L ⟶ Modules.unit X) : ψ.toZeroLocusToModules ≫ ψ.zeroLocus.toModulesι = ψ :=
  kernel.lift_ι _ ψ _

/-- A morphism `ψ : L ⟶ 𝒪_X` from an invertible module maps onto the ideal sheaf of its zero
scheme. -/
instance epi_toZeroLocusToModules {L : X.Modules} [SheafOfModules.IsInvertible.{u, u, u} L]
    (ψ : L ⟶ Modules.unit X) : Epi ψ.toZeroLocusToModules := by
  have : SheafOfModules.IsInvertible.{u, u, u} (Modules.unit X) :=
    IsInvertible.sheafOfModules_isInvertible (𝟙_ X.Modules)
  refine epi_of_forall_exists_app_eq _ fun W y x hx ↦ ?_
  obtain ⟨V, hxV, hVW, e, he⟩ := exists_isFreeGenerator L hx
  refine ⟨V.1, hVW, hxV, ?_⟩
  -- the restriction of `y` to `V` lies in the ideal `(ψ(e))` of `Z(ψ)` over `V`
  let y₀ : Γ(X, V.1) :=
    ψ.zeroLocus.toModulesι.app V.1 (ψ.zeroLocus.toModules.presheaf.map (homOfLE hVW).op y)
  let b : Γ(X, V.1) := ψ.app V.1 e
  have hy : y₀ ∈ ψ.zeroLocus.ideal V := by
    rw [← SetLike.mem_coe, ← IdealSheafData.range_toModulesι_app]
    exact ⟨_, rfl⟩
  rw [Hom.ideal_zeroLocus ψ V he (isFreeGenerator_one V.1) (b := b) (mul_one b).symm,
    Ideal.mem_span_singleton'] at hy
  obtain ⟨r, hr⟩ := hy
  refine ⟨r • e, IdealSheafData.injective_toModulesι_app _ V.1 ?_⟩
  exact (congrArg (fun f ↦ f.app V.1 (r • e)) ψ.toZeroLocusToModules_toModulesι).trans
    ((Hom.app_smul ψ r e).trans hr)

/-- **The image of a morphism to `𝒪_X` is the ideal of its zero scheme.** For a morphism
`ψ : L ⟶ 𝒪_X` from an invertible module, the image of `ψ`, as a subobject of `𝒪_X`, is the
ideal sheaf `𝓘_{Z(ψ)}`. -/
theorem imageSubobject_eq_mk_toModulesι {L : X.Modules}
    [SheafOfModules.IsInvertible.{u, u, u} L] (ψ : L ⟶ Modules.unit X) :
    imageSubobject ψ = Subobject.mk ψ.zeroLocus.toModulesι :=
  have : StrongEpi ψ.toZeroLocusToModules := strongEpi_of_epi _
  Subobject.mk_eq_mk_of_comm _ _
    (image.isoStrongEpiMono _ _ ψ.toZeroLocusToModules_toModulesι).symm
    (image.isoStrongEpiMono_inv_comp_mono _ _ ψ.toZeroLocusToModules_toModulesι)

/-- **The zero scheme of the transpose.** For a section `s : 𝒪_X ⟶ M` of an invertible module,
the transpose `s^∨ : M^∨ ⟶ 𝒪_X^∨ ≅ 𝒪_X` has the same zero scheme as `s`. -/
theorem zeroLocus_dualMap_comp_dualUnitIso {M : X.Modules}
    [SheafOfModules.IsInvertible.{u, u, u} M] (s : 𝟙_ X.Modules ⟶ M) :
    (dualMap s ≫ dualUnitIso.hom).zeroLocus = s.zeroLocus := by
  have := IsInvertible.of_sheafOfModules M
  have : SheafOfModules.IsInvertible.{u, u, u} (𝟙_ X.Modules) :=
    IsInvertible.sheafOfModules_isInvertible (𝟙_ X.Modules)
  have := IsInvertible.sheafOfModules_isInvertible Mᵛ
  rw [← s.zeroLocus_whiskerRight Mᵛ, dualMap_comp_dualUnitIso_hom]
  exact zeroLocus_eq_of_arrowIso _ _
    (Arrow.isoMk (λ_ _).symm (asIso (dualEvaluation M)).symm (by simp))

/-- **The ideal of the zero scheme of a section is the image of its dual.** For a global section
`s: 𝒪_X ⟶ ℳ` of an invertible module, the ideal sheaf `𝓘_{Z(s)}` is the image of the transpose
`s^∨: ℳ^∨ ⟶ 𝒪_X^∨ ≅ 𝒪_X`, `λ ↦ λ(s)`, as a subobject of `𝒪_X`. -/
theorem imageSubobject_dualMap_comp_dualUnitIso {M : X.Modules}
    [SheafOfModules.IsInvertible.{u, u, u} M] (s : 𝟙_ X.Modules ⟶ M) :
    imageSubobject (dualMap s ≫ dualUnitIso.hom) = Subobject.mk s.zeroLocus.toModulesι := by
  have := IsInvertible.of_sheafOfModules M
  have := IsInvertible.sheafOfModules_isInvertible Mᵛ
  rw [imageSubobject_eq_mk_toModulesι, zeroLocus_dualMap_comp_dualUnitIso]

/-- **The section corresponding to a morphism of invertible modules.** For an invertible
`𝒪_X`-module `N` and a morphism `φ : N ⟶ M`, the global section `s : 𝒪_X ⟶ M ⊗ N^∨` of
`M ⊗ N^{-1}` corresponding to `φ` under `Hom(N, M) ≅ H⁰(X, M ⊗ N^∨)`: the coevaluation
`𝒪_X ≅ N ⊗ N^∨` (the inverse of the evaluation, an isomorphism since `N` is invertible)
followed by `φ ⊗ N^∨`. -/
noncomputable def adjointSection {N M : X.Modules} [N.IsInvertible] (φ : N ⟶ M) :
    𝟙_ X.Modules ⟶ M ⊗ Nᵛ :=
  inv (dualEvaluation N) ≫ φ ▷ Nᵛ

/-- **The zero scheme of the corresponding section.** For a morphism `φ: N ⟶ M` of invertible
modules and any identification `e: N^∨ ≅ P` of `N^{-1}`, the section
`s: 𝒪_X ⟶ M ⊗ N^∨ ≅ M ⊗ P` corresponding to `φ` has the same zero scheme as `φ`:
`Z(s) = Z(φ)`. -/
theorem zeroLocus_adjointSection_comp_whiskerLeft {N M P : X.Modules} [N.IsInvertible]
    [M.IsInvertible] (φ : N ⟶ M) (e : Nᵛ ≅ P) :
    (adjointSection φ ≫ M ◁ e.hom).zeroLocus = φ.zeroLocus := by
  have := IsInvertible.sheafOfModules_isInvertible N
  have := IsInvertible.sheafOfModules_isInvertible M
  have := IsInvertible.sheafOfModules_isInvertible Nᵛ
  rw [← φ.zeroLocus_whiskerRight Nᵛ]
  exact zeroLocus_eq_of_arrowIso _ _
    (Arrow.isoMk (asIso (dualEvaluation N)).symm (whiskerLeftIso M e).symm
      (by simp [adjointSection]))

/-- **The zero scheme of the corresponding section.** For a morphism `φ: N ⟶ M` of invertible
modules, the section `s: 𝒪_X ⟶ M ⊗ N^∨` corresponding to `φ` satisfies `Z(s) = Z(φ)`. -/
theorem zeroLocus_adjointSection {N M : X.Modules} [N.IsInvertible] [M.IsInvertible]
    (φ : N ⟶ M) : (adjointSection φ).zeroLocus = φ.zeroLocus := by
  simpa using zeroLocus_adjointSection_comp_whiskerLeft φ (Iso.refl _)

end Hom

/-- **Pullback commutes with duals of invertible modules.** For an invertible `𝒪_X`-module `N`
and `g : Y ⟶ X`, `(g^* N)^∨ ≅ g^* (N^∨)`: both are tensor inverses of `g^* N`. -/
theorem nonempty_dual_pullback_iso_pullback_dual {Y : Scheme.{u}} (g : Y ⟶ X) (N : X.Modules)
    [N.IsInvertible] : Nonempty (((pullback g).obj N)ᵛ ≅ (pullback g).obj Nᵛ) := by
  obtain ⟨t⟩ := nonempty_pullback_tensorObj_iso g N Nᵛ
  let e : (pullback g).obj N ⊗ (pullback g).obj Nᵛ ≅ 𝟙_ Y.Modules :=
    t.symm ≪≫ (pullback g).mapIso (asIso (dualEvaluation N)) ≪≫ pullbackObjUnitIso g
  exact ⟨(λ_ _).symm ≪≫ whiskerRightIso ((β_ _ _) ≪≫ e).symm _ ≪≫ α_ _ _ _ ≪≫
    whiskerLeftIso _ (asIso (dualEvaluation _)) ≪≫ ρ_ _⟩

end AlgebraicGeometry.Scheme.Modules
