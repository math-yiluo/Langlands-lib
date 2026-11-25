/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Leray
public import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.Vanishing
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Sections
public import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# The Čech complex as a complex of modules over the base

Let `f : X ⟶ S` be a morphism of schemes, `U : ι → X.Opens` a family of opens and `ℱ` an
`𝒪_X`-module. The Čech cochains `c y ∈ Γ(ℱ, U (y 0) ⊓ ⋯ ⊓ U (y k))` form modules over
`A = Γ(S, ⊤)`, through `f^♯ : A ⟶ Γ(X, ⊤)`, and the Čech differential is `A`-linear. This gives
the Čech complex `Č(U, ℱ)` as a cochain complex of `A`-modules,
`AlgebraicGeometry.Scheme.Modules.cechModuleComplex f U ℱ`, indexed by `ℤ` and concentrated in
degrees `≥ 0`: an object of the derived category `D(A)`.

When `S` is affine, `f` quasi-compact and separated, `U` a finite cover of `X` by affine opens
and `ℱ` quasi-coherent, this complex computes the higher direct images of `ℱ` over the affine
base: `H^q(Č(U, ℱ)) ≅ Γ(S, R^q f_* ℱ)` as `A`-modules
(`AlgebraicGeometry.Scheme.Modules.nonempty_homology_cechModuleComplex_linearEquiv`), and it is
exact in degrees `≥ #ι` (`AlgebraicGeometry.Scheme.Modules.exactAt_cechModuleComplex`). Over an
affine base, where quasi-coherent `𝒪_S`-modules are `A`-modules, it is the module-theoretic
incarnation of the derived direct image `Rf_* ℱ`; this is the form in which the blueprint's Čech
resolution is used.
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X S : Scheme.{u}} (f : X ⟶ S) (ℱ : X.Modules)

/-- The sections `Γ(ℱ, W)` of an `𝒪_X`-module over an open `W`, as a module over the global
functions `Γ(S, ⊤)` of the target of `f : X ⟶ S`, through `f^♯ : Γ(S, ⊤) ⟶ Γ(X, ⊤)` followed by
restriction to `W`. -/
noncomputable abbrev sectionsModule (W : X.Opens) : ModuleCat.{u} Γ(S, ⊤) :=
  (ModuleCat.restrictScalars f.appTop.hom).obj (ℱ.presheafModuleCat.obj (op W))

/-- Restriction of sections `Γ(ℱ, W) ⟶ Γ(ℱ, V)`, as a `Γ(S, ⊤)`-linear map. -/
noncomputable def sectionsModuleRestrict {V W : X.Opens} (h : V ≤ W) :
    sectionsModule f ℱ W →ₗ[Γ(S, ⊤)] sectionsModule f ℱ V :=
  ((ModuleCat.restrictScalars f.appTop.hom).map (ℱ.presheafModuleCat.map (homOfLE h).op)).hom

lemma sectionsModuleRestrict_apply {V W : X.Opens} (h : V ≤ W) (m : sectionsModule f ℱ W) :
    sectionsModuleRestrict f ℱ h m = ℱ.presheaf.map (homOfLE h).op m :=
  rfl

lemma sectionsModuleRestrict_comp {V W Z : X.Opens} (h₁ : V ≤ W) (h₂ : W ≤ Z)
    (m : sectionsModule f ℱ Z) :
    sectionsModuleRestrict f ℱ h₁ (sectionsModuleRestrict f ℱ h₂ m) =
      sectionsModuleRestrict f ℱ (h₁.trans h₂) m :=
  TopCat.Presheaf.map_homOfLE_map_homOfLE_apply ℱ.presheaf h₁ h₂ m

lemma sectionsModuleRestrict_self {W : X.Opens} (h : W ≤ W) (m : sectionsModule f ℱ W) :
    sectionsModuleRestrict f ℱ h m = m :=
  TopCat.Presheaf.map_homOfLE_self_apply ℱ.presheaf h m

variable {ι : Type u} (U : ι → X.Opens)

open TopCat.Presheaf

/-- The Čech differential `(d c) y = ∑ᵢ (-1)ⁱ c (y ∘ δᵢ)|`, as a `Γ(S, ⊤)`-linear map. -/
noncomputable def cechModuleD (k : ℕ) :
    (∀ y : Fin (k + 1) → ι, sectionsModule f ℱ (⨅ l, U (y l))) →ₗ[Γ(S, ⊤)]
      (∀ y : Fin (k + 1 + 1) → ι, sectionsModule f ℱ (⨅ l, U (y l))) :=
  ∑ i : Fin (k + 2), ((-1 : ℤ) ^ (i : ℕ)) • LinearMap.pi fun y ↦
    sectionsModuleRestrict f ℱ (iInf_le_iInf_comp U y i.succAbove) ∘ₗ
      LinearMap.proj (y ∘ i.succAbove)

lemma cechModuleD_apply_apply (k : ℕ)
    (c : ∀ y : Fin (k + 1) → ι, sectionsModule f ℱ (⨅ l, U (y l))) (y : Fin (k + 1 + 1) → ι) :
    cechModuleD f ℱ U k c y = ∑ i : Fin (k + 2), ((-1 : ℤ) ^ (i : ℕ)) •
      sectionsModuleRestrict f ℱ (iInf_le_iInf_comp U y i.succAbove) (c (y ∘ i.succAbove)) := by
  simp only [cechModuleD, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply]
  rfl

lemma cechModuleD_apply (k : ℕ) (c : ∀ y : Fin (k + 1) → ι, sectionsModule f ℱ (⨅ l, U (y l))) :
    cechModuleD f ℱ U k c = ((cechComplex U).obj ℱ.presheaf).d k (k + 1) c := by
  funext y
  rw [cechComplex_d_apply]
  simp only [cechModuleD, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply,
    Function.comp_apply]
  rfl

lemma cechModuleD_apply' (k : ℕ)
    (c : ∀ y : Fin (k + 1) → ι, sectionsModule f ℱ (⨅ l, U (y l))) :
    cechModuleD f ℱ U k c = ((cechComplex U).obj
      (ℱ.presheafModuleCat ⋙ forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u})).d k (k + 1) c := by
  funext y
  rw [cechComplex_d_apply]
  simp only [cechModuleD, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply,
    Function.comp_apply]
  rfl

/-- The Čech complex `Č(U, ℱ)` as a complex of `Γ(S, ⊤)`-modules, indexed by `ℕ`. -/
noncomputable def cechModuleComplexNat : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℕ :=
  CochainComplex.of
    (fun k ↦ ModuleCat.of Γ(S, ⊤) (∀ y : Fin (k + 1) → ι, sectionsModule f ℱ (⨅ l, U (y l))))
    (fun k ↦ ModuleCat.ofHom (cechModuleD f ℱ U k))
    (fun k ↦ by
      ext c : 2
      change cechModuleD f ℱ U (k + 1) (cechModuleD f ℱ U k c) = 0
      rw [cechModuleD_apply, cechModuleD_apply]
      exact congr($(((cechComplex U).obj ℱ.presheaf).d_comp_d k (k + 1) (k + 1 + 1)) c))

lemma cechModuleComplexNat_d (k : ℕ) :
    (cechModuleComplexNat f ℱ U).d k (k + 1) = ModuleCat.ofHom (cechModuleD f ℱ U k) :=
  by simp only [cechModuleComplexNat, CochainComplex.of_d]

/-- **The Čech complex over the base.** The Čech complex `Č(U, ℱ)` of an `𝒪_X`-module for a
family `U` of opens, as a cochain complex of modules over `Γ(S, ⊤)` for `f : X ⟶ S`, indexed by
`ℤ` and concentrated in degrees `≥ 0`. -/
noncomputable def cechModuleComplex : CochainComplex (ModuleCat.{u} Γ(S, ⊤)) ℤ :=
  (cechModuleComplexNat f ℱ U).extend ComplexShape.embeddingUpNat

instance : (cechModuleComplex f ℱ U).IsStrictlyGE 0 := by
  dsimp [cechModuleComplex]
  infer_instance

/-! ### Comparison with Mathlib's Čech complex -/

/-- The Čech cochains of Mathlib's Čech complex of `ℱ.presheafModuleCat` are the explicit ones,
`Γ(S, ⊤)`-linearly. -/
noncomputable def cechComplexFunctorXLinearEquiv (k : ℕ) :
    ((ModuleCat.restrictScalars f.appTop.hom).obj
      (((cechComplexFunctor U).obj ℱ.presheafModuleCat).X k)) ≃ₗ[Γ(S, ⊤)]
      (∀ y : Fin (k + 1) → ι, sectionsModule f ℱ (⨅ l, U (y l))) :=
  { cechComplexFunctorXAddEquiv U ℱ.presheafModuleCat k with
    map_smul' a x := by
      funext y
      change ℱ.presheafModuleCat.map _ (cechComplexFunctorπ U ℱ.presheafModuleCat k y
        (f.appTop a • x)) = f.appTop a • ℱ.presheafModuleCat.map _
          (cechComplexFunctorπ U ℱ.presheafModuleCat k y x)
      rw [_root_.map_smul, _root_.map_smul] }

/-- The Čech complex over the base is Mathlib's Čech complex with scalars restricted. -/
noncomputable def cechModuleComplexNatIso :
    ((ModuleCat.restrictScalars f.appTop.hom).mapHomologicalComplex _).obj
      ((cechComplexFunctor U).obj ℱ.presheafModuleCat) ≅ cechModuleComplexNat f ℱ U :=
  HomologicalComplex.Hom.isoOfComponents
    (fun k ↦ (cechComplexFunctorXLinearEquiv f ℱ U k).toModuleIso) (by
      rintro k _ rfl
      ext x : 2
      rw [cechModuleComplexNat_d]
      change cechModuleD f ℱ U k (cechComplexFunctorXLinearEquiv f ℱ U k x) =
        cechComplexFunctorXLinearEquiv f ℱ U (k + 1)
          ((((cechComplexFunctor U).obj ℱ.presheafModuleCat).d k (k + 1)).hom x)
      rw [cechModuleD_apply']
      have h := congr($((cechComplexFunctorIso U ℱ.presheafModuleCat).hom.comm k (k + 1)) x)
      rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h
      exact h)


/-! ### The Čech complex computes the higher direct images over an affine base -/

/-- The cohomology of `Č(U, ℱ)` in degree `q ≥ 0`, with scalars `Γ(S, ⊤)`, is that of Mathlib's
Čech complex with scalars restricted along `f^♯`. -/
noncomputable def cechModuleComplexHomologyIso (q : ℕ) :
    (cechModuleComplex f ℱ U).homology q ≅ (ModuleCat.restrictScalars f.appTop.hom).obj
      (((cechComplexFunctor U).obj ℱ.presheafModuleCat).homology q) :=
  (cechModuleComplexNat f ℱ U).extendHomologyIso ComplexShape.embeddingUpNat rfl ≪≫
    HomologicalComplex.homologyMapIso (cechModuleComplexNatIso f ℱ U).symm q ≪≫
    ModuleCat.restrictScalarsHomologyIso _ _ q

/-- **Leray's theorem over the base.** For `f : X ⟶ S` separated, `S` affine, `U` a cover of `X`
by affine opens and `ℱ` quasi-coherent, `H^q(Č(U, ℱ)) ≅ H^q(X, ℱ)`, the action of `Γ(S, ⊤)` on
`H^q(X, ℱ)` being through `f^♯`. -/
theorem exists_homology_cechModuleComplex_equiv_H [IsAffine S] [IsSeparated f]
    (hU : ∀ i, IsAffineOpen (U i)) (hU' : iSup U = ⊤)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] (q : ℕ) :
    ∃ e : (cechModuleComplex f ℱ U).homology q ≃+ ℱ.H q,
      ∀ (a : Γ(S, ⊤)) x, e (a • x) = f.appTop a • e x := by
  obtain ⟨e₄⟩ := nonempty_cechComplex_linearEquiv_H_of_isSeparated f U hU hU' ℱ q
  let E := (cechModuleComplexHomologyIso f ℱ U q).toLinearEquiv
  refine ⟨E.toAddEquiv.trans e₄.toAddEquiv, fun a x ↦ ?_⟩
  change e₄ (E (a • x)) = f.appTop a • e₄ (E x)
  rw [E.map_smul]
  exact e₄.map_smul (f.appTop a) (E x)

/-- **The Čech resolution computes the derived direct image over an affine base.** Let
`f : X ⟶ S` be quasi-compact and separated with `S = Spec A` affine, `U` a cover of `X` by affine
opens (whose finite intersections are then affine) and `ℱ` a quasi-coherent `𝒪_X`-module. Then
the Čech complex `Č(U, ℱ)`, a complex of `A`-modules, computes the higher direct images of `ℱ`:
`H^q(Č(U, ℱ)) ≅ Γ(S, R^q f_* ℱ)` as `A`-modules. Over the affine base, where quasi-coherent
`𝒪_S`-modules are `A`-modules, this says that `Č(U, ℱ)` represents `Rf_* ℱ` (its cohomology
modules are the `Γ(S, R^q f_* ℱ)`, and `R^q f_* ℱ` is quasi-coherent).

The blueprint proves this by showing that the sheafified Čech complex is a resolution of `ℱ` by
`f_*`-acyclic sheaves; here it is the combination of Leray's theorem
(`AlgebraicGeometry.Scheme.Modules.nonempty_cechComplex_linearEquiv_H_of_isSeparated`) and of the
identification `Γ(S, R^q f_* ℱ) ≅ H^q(X, ℱ)` over an affine base
(`AlgebraicGeometry.Scheme.Modules.exists_bijective_semilinearMap_sections_higherDirectImage_H`).
The complex is concentrated in degrees `≥ 0` and is exact in degrees `≥ #ι`
(`AlgebraicGeometry.Scheme.Modules.exactAt_cechModuleComplex`).

(blueprint: `lemma-coherent-base-change-invertible-sheaves`) -/
theorem nonempty_homology_cechModuleComplex_linearEquiv [IsAffine S] [QuasiCompact f]
    [IsSeparated f] [HasInjectiveResolutions X.Modules] (hU : ∀ i, IsAffineOpen (U i))
    (hU' : iSup U = ⊤) [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] (q : ℕ) :
    Nonempty ((cechModuleComplex f ℱ U).homology q ≃ₗ[Γ(S, ⊤)]
      Γ((higherDirectImage f q).obj ℱ, ⊤)) := by
  obtain ⟨e, he⟩ := exists_homology_cechModuleComplex_equiv_H f ℱ U hU hU' q
  obtain ⟨g, hg⟩ := exists_bijective_semilinearMap_sections_higherDirectImage_H f ℱ q
  let G : Γ((higherDirectImage f q).obj ℱ, ⊤) ≃+ ℱ.H q := AddEquiv.ofBijective g.toAddMonoidHom hg
  have hG (y : Γ((higherDirectImage f q).obj ℱ, ⊤)) : G y = g y := rfl
  refine ⟨{ e.trans G.symm with
    map_smul' := fun a x ↦ G.injective ?_ }⟩
  change G (G.symm (e (a • x))) = G (a • G.symm (e x))
  rw [G.apply_symm_apply, hG, g.map_smulₛₗ, ← hG, G.apply_symm_apply, he]

/-- **Vanishing of the Čech cohomology above the number of opens.** In the situation of
`AlgebraicGeometry.Scheme.Modules.nonempty_homology_cechModuleComplex_linearEquiv`, with a
nonempty finite cover, the Čech complex `Č(U, ℱ)` is exact in degrees `q < 0` and `q ≥ #ι`: its
cohomology is `H^q(X, ℱ)`, which vanishes for `q ≥ #ι`
(`AlgebraicGeometry.Scheme.Modules.subsingleton_H_of_card_le`). -/
theorem exactAt_cechModuleComplex [IsAffine S] [IsSeparated f] [Fintype ι] [Nonempty ι]
    (hU : ∀ i, IsAffineOpen (U i)) (hU' : iSup U = ⊤)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] (q : ℤ)
    (hq : q < 0 ∨ Fintype.card ι ≤ q) : (cechModuleComplex f ℱ U).ExactAt q := by
  rcases hq with hq | hq
  · exact HomologicalComplex.extend_exactAt _ _ _ fun j hj ↦ by
      change (j : ℤ) = q at hj
      lia
  obtain ⟨q, rfl⟩ : ∃ n : ℕ, q = n := ⟨q.toNat, by lia⟩
  have : IsSeparated (terminal.from X) := by
    rw [← terminal.comp_from f]
    infer_instance
  obtain ⟨e, -⟩ := exists_homology_cechModuleComplex_equiv_H f ℱ U hU hU' q
  have : Subsingleton (ℱ.H q) :=
    subsingleton_H_of_card_le Finset.univ Finset.univ_nonempty U (fun i _ ↦ hU i)
      (by rw [← hU', Finset.sup_univ_eq_iSup]) _
      (cechAcyclicOnAffines_of_isQuasicoherent ℱ) (by simpa using hq)
  have : Subsingleton ((cechModuleComplex f ℱ U).homology q) := e.injective.subsingleton
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact ModuleCat.isZero_of_subsingleton _


/-! ### Flatness of the Čech complex -/

/-- If `ℱ` is flat over an affine base, its sections over an affine open are flat. -/
lemma flat_sectionsModule [IsAffine S] (hℱ : ℱ.IsFlatOver f) {W : X.Opens} (hW : IsAffineOpen W) :
    Module.Flat Γ(S, ⊤) (sectionsModule f ℱ W) :=
  hℱ ⟨⊤, isAffineOpen_top S⟩ ⟨W, hW⟩ (by simp)

/-- **The Čech complex of a module flat over the base is a complex of flat modules**, for a finite
family of opens whose finite intersections are affine. -/
theorem flat_cechModuleComplex_X [IsAffine S] (hℱ : ℱ.IsFlatOver f) [Finite ι]
    (hU : ∀ (k : ℕ) (y : Fin (k + 1) → ι), IsAffineOpen (⨅ l, U (y l))) (n : ℤ) :
    Module.Flat Γ(S, ⊤) ((cechModuleComplex f ℱ U).X n) := by
  by_cases hn : ∃ k : ℕ, (k : ℤ) = n
  · obtain ⟨k, rfl⟩ := hn
    have := Fintype.ofFinite ι
    have (y : Fin (k + 1) → ι) := flat_sectionsModule f ℱ hℱ (hU k y)
    have : Module.Flat Γ(S, ⊤) (∀ y : Fin (k + 1) → ι, sectionsModule f ℱ (⨅ l, U (y l))) :=
      Module.Flat.of_linearEquiv (DFinsupp.linearEquivFunOnFintype (R := Γ(S, ⊤))).symm
    have : Module.Flat Γ(S, ⊤) ((cechModuleComplexNat f ℱ U).X k) := this
    exact Module.Flat.of_linearEquiv
      ((cechModuleComplexNat f ℱ U).extendXIso ComplexShape.embeddingUpNat rfl).toLinearEquiv
  · have hz := (cechModuleComplexNat f ℱ U).isZero_extend_X ComplexShape.embeddingUpNat n
      fun k hk ↦ hn ⟨k, hk⟩
    have : Subsingleton ((cechModuleComplex f ℱ U).X n) :=
      (ModuleCat.subsingleton_of_isZero hz)
    infer_instance

end AlgebraicGeometry.Scheme.Modules
