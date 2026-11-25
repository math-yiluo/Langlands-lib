/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.RelativeGluing
public import Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.SmallAffineZariski
public import WeilConjectures.Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import WeilConjectures.AlgebraicGeometry.QuasiCoherentAffineSectionBaseChange

/-!
# The symmetric algebra of a quasi-coherent sheaf and its relative spectrum

For an `𝒪_X`-module `ℰ`, the presheaf of rings `U ↦ Sym_{Γ(X, U)} Γ(ℰ, U)` with the structure map
`𝒪_X ⟶ Sym^• ℰ` (`AlgebraicGeometry.Scheme.Modules.symPresheaf`,
`AlgebraicGeometry.Scheme.Modules.toSymPresheaf`). If `ℰ` is quasi-coherent, then on the small
affine Zariski site this algebra is quasi-coherent: restriction to a basic open `D(f)` of an
affine open is the localization at `f`, since `Γ(ℰ, D(f)) = Γ(ℰ, U)_f` and the symmetric algebra
commutes with localization (`AlgebraicGeometry.Scheme.Modules.coequifibered_toSymPresheaf`).
Hence the relative spectrum `Spec_X (Sym^• ℰ) ⟶ X` is defined by relative gluing
(`AlgebraicGeometry.Scheme.Modules.symSpec`, `AlgebraicGeometry.Scheme.Modules.symSpecProj`):
this is the vector bundle `E = Spec_Z (Sym^• ℰ)` of `proposition-purity-vector-bundles`.
-/

@[expose] public section

universe u

open CategoryTheory Opposite TensorProduct

namespace SymmetricAlgebra

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] {B : Type*}
  [CommRing B]

/-- Ring homomorphisms out of a symmetric algebra are determined on scalars and generators. -/
lemma ringHom_ext {φ ψ : SymmetricAlgebra R M →+* B}
    (h₁ : ∀ r, φ (algebraMap R _ r) = ψ (algebraMap R _ r)) (h₂ : ∀ m, φ (ι R M m) = ψ (ι R M m)) :
    φ = ψ := by
  refine RingHom.ext fun x ↦ ?_
  induction x using SymmetricAlgebra.induction with
  | algebraMap r => exact h₁ r
  | ι m => exact h₂ m
  | mul a b ha hb => rw [map_mul, map_mul, ha, hb]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

end SymmetricAlgebra

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (F : X.Modules)

/-- The ring map `Sym_{Γ(X, U)} Γ(ℰ, U) ⟶ Sym_{Γ(X, V)} Γ(ℰ, V)` induced by restriction along
`V ⟶ U`. -/
noncomputable def symMap {U V : X.Opens} (e : V ⟶ U) :
    SymmetricAlgebra Γ(X, U) Γ(F, U) →+* SymmetricAlgebra Γ(X, V) Γ(F, V) :=
  letI : Algebra Γ(X, U) Γ(X, V) := (X.presheaf.map e.op).hom.toAlgebra
  letI : Module Γ(X, U) Γ(F, V) := Module.compHom _ (X.presheaf.map e.op).hom
  haveI : IsScalarTower Γ(X, U) Γ(X, V) Γ(F, V) :=
    { smul_assoc := fun r a m ↦ by
        change (X.presheaf.map e.op r * a) • m = X.presheaf.map e.op r • (a • m)
        exact mul_smul _ _ _ }
  (SymmetricAlgebra.mapOfLocalization Γ(X, V)
    { toFun := F.presheaf.map e.op
      map_add' := map_add _
      map_smul' := fun r m ↦ F.map_smul e r m }).toRingHom

@[simp]
lemma symMap_ι {U V : X.Opens} (e : V ⟶ U) (m : Γ(F, U)) :
    F.symMap e (SymmetricAlgebra.ι _ _ m) = SymmetricAlgebra.ι _ _ (F.presheaf.map e.op m) := by
  simp [symMap]

@[simp]
lemma symMap_algebraMap {U V : X.Opens} (e : V ⟶ U) (r : Γ(X, U)) :
    F.symMap e (algebraMap _ _ r) = algebraMap _ _ (X.presheaf.map e.op r) := by
  let : Algebra Γ(X, U) Γ(X, V) := (X.presheaf.map e.op).hom.toAlgebra
  let : Module Γ(X, U) Γ(F, V) := Module.compHom _ (X.presheaf.map e.op).hom
  have : IsScalarTower Γ(X, U) Γ(X, V) Γ(F, V) :=
    { smul_assoc := fun r a m ↦ by
        change (X.presheaf.map e.op r * a) • m = X.presheaf.map e.op r • (a • m)
        exact mul_smul _ _ _ }
  exact AlgHom.commutes (SymmetricAlgebra.mapOfLocalization Γ(X, V)
    { toFun := F.presheaf.map e.op
      map_add' := map_add _
      map_smul' := fun r m ↦ F.map_smul e r m }) r

/-- The presheaf of rings `U ↦ Sym_{Γ(X, U)} Γ(ℰ, U)`. -/
@[simps]
noncomputable def symPresheaf : X.Opensᵒᵖ ⥤ CommRingCat.{u} where
  obj U := CommRingCat.of (SymmetricAlgebra Γ(X, U.unop) Γ(F, U.unop))
  map e := CommRingCat.ofHom (F.symMap e.unop)
  map_id U := by
    ext1
    refine SymmetricAlgebra.ringHom_ext (fun r ↦ ?_) (fun m ↦ ?_)
    · exact (F.symMap_algebraMap _ r).trans (by simp)
    · exact (F.symMap_ι _ m).trans (by simp)
  map_comp e e' := by
    ext1
    refine SymmetricAlgebra.ringHom_ext (fun r ↦ ?_) (fun m ↦ ?_)
    · refine (F.symMap_algebraMap _ r).trans ?_
      change _ = F.symMap e'.unop (F.symMap e.unop _)
      rw [F.symMap_algebraMap, F.symMap_algebraMap]
      simp
    · refine (F.symMap_ι _ m).trans ?_
      change _ = F.symMap e'.unop (F.symMap e.unop _)
      rw [F.symMap_ι, F.symMap_ι]
      simp

/-- The structure map `𝒪_X ⟶ Sym^• ℰ`. -/
@[simps]
noncomputable def toSymPresheaf : X.presheaf ⟶ F.symPresheaf where
  app U := CommRingCat.ofHom
    (algebraMap Γ(X, U.unop) (SymmetricAlgebra Γ(X, U.unop) Γ(F, U.unop)))
  naturality U V e := by
    ext1
    ext r
    exact (F.symMap_algebraMap _ r).symm

/-- **`Sym^• ℰ` is a quasi-coherent algebra** for quasi-coherent `ℰ`: on the affine Zariski site,
restriction of `Sym_{Γ(X, U)} Γ(ℰ, U)` to a basic open `D(f)` is the localization at `f`. -/
theorem coequifibered_toSymPresheaf [F.IsQuasicoherent] :
    (Functor.whiskerLeft (AffineZariskiSite.toOpensFunctor X).op
      F.toSymPresheaf).Coequifibered := by
  rw [AffineZariskiSite.coequifibered_iff_forall_isLocalizationAway]
  intro U f
  let : Algebra Γ(X, U.1) Γ(X, X.basicOpen f) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom.toAlgebra
  let : Module Γ(X, U.1) Γ(F, X.basicOpen f) :=
    Module.compHom _ (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom
  have : IsScalarTower Γ(X, U.1) Γ(X, X.basicOpen f) Γ(F, X.basicOpen f) :=
    { smul_assoc := fun r a m ↦ by
        change (X.presheaf.map (homOfLE (X.basicOpen_le f)).op r * a) • m =
          X.presheaf.map (homOfLE (X.basicOpen_le f)).op r • (a • m)
        exact mul_smul _ _ _ }
  have : IsLocalization (Submonoid.powers f) Γ(X, X.basicOpen f) :=
    U.2.isLocalization_basicOpen f
  have hbc := quasiCoherent_affine_section_baseChange X F (X.affineBasicOpen f) ⟨U.1, U.2⟩
    (X.basicOpen_le f)
  dsimp only [Scheme.affineBasicOpen] at hbc
  obtain ⟨c, hc, hs, ht⟩ := hbc
  let g : Γ(F, U.1) →ₗ[Γ(X, U.1)] Γ(F, X.basicOpen f) :=
    { toFun := F.presheaf.map (homOfLE (X.basicOpen_le f)).op
      map_add' := map_add _
      map_smul' := fun r m ↦ F.map_smul _ r m }
  let d : (Γ(X, X.basicOpen f) ⊗[Γ(X, U.1)] Γ(F, U.1)) →ₗ[
      Γ(X, X.basicOpen f)] Γ(F, X.basicOpen f) :=
    { toFun := fun t ↦ c ((TensorProduct.comm _ _ _) t)
      map_add' := by intro a b; simp
      map_smul' := by
        intro r t
        simpa using hs r ((TensorProduct.comm _ _ _) t) }
  have hd : Function.Bijective d :=
    hc.comp (TensorProduct.comm _ _ _).bijective
  have hg : IsBaseChange Γ(X, X.basicOpen f) g :=
    .of_equiv (LinearEquiv.ofBijective d hd) (fun m ↦ by
      change c ((TensorProduct.comm _ _ _) (1 ⊗ₜ m)) = g m
      simpa [g] using ht m 1)
  have : IsLocalizedModule (Submonoid.powers f) g :=
    (isLocalizedModule_iff_isBaseChange _ Γ(X, X.basicOpen f) g).mpr hg
  have H := SymmetricAlgebra.isLocalization_mapOfLocalization (Submonoid.powers f)
    Γ(X, X.basicOpen f) g
  rw [Algebra.algebraMapSubmonoid, Submonoid.map_powers] at H
  exact H

/-- Blueprint `proposition-purity-vector-bundles`: Vector bundle with zero section

The relative spectrum `Spec_X (Sym^• ℰ)` of the symmetric algebra of a quasi-coherent sheaf,
glued from the affine schemes `Spec (Sym_{Γ(X, U)} Γ(ℰ, U))` over the affine opens `U`. -/
noncomputable def symSpec [F.IsQuasicoherent] : Scheme.{u} :=
  (AffineZariskiSite.relativeGluingData F.coequifibered_toSymPresheaf).glued

/-- The projection `Spec_X (Sym^• ℰ) ⟶ X`. -/
noncomputable abbrev symSpecProj [F.IsQuasicoherent] : F.symSpec ⟶ X :=
  (AffineZariskiSite.relativeGluingData F.coequifibered_toSymPresheaf).toBase

/-- The augmentation `Sym^• ℰ ⟶ 𝒪_X`, killing `ℰ`. -/
@[simps]
noncomputable def symAugmentation : F.symPresheaf ⟶ X.presheaf where
  app U := CommRingCat.ofHom (SymmetricAlgebra.algebraMapInv (R := Γ(X, U.unop))
    (M := Γ(F, U.unop))).toRingHom
  naturality U V e := by
    ext1
    refine SymmetricAlgebra.ringHom_ext (fun r ↦ ?_) (fun m ↦ ?_)
    · change SymmetricAlgebra.algebraMapInv (F.symMap e.unop
          (algebraMap Γ(X, U.unop) (SymmetricAlgebra Γ(X, U.unop) Γ(F, U.unop)) r)) =
        X.presheaf.map e (SymmetricAlgebra.algebraMapInv (R := Γ(X, U.unop)) (M := Γ(F, U.unop))
          (algebraMap Γ(X, U.unop) (SymmetricAlgebra Γ(X, U.unop) Γ(F, U.unop)) r))
      rw [F.symMap_algebraMap]
      simp only [AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]
      rfl
    · change SymmetricAlgebra.algebraMapInv (F.symMap e.unop
          (SymmetricAlgebra.ι Γ(X, U.unop) Γ(F, U.unop) m)) =
        X.presheaf.map e (SymmetricAlgebra.algebraMapInv (R := Γ(X, U.unop)) (M := Γ(F, U.unop))
          (SymmetricAlgebra.ι Γ(X, U.unop) Γ(F, U.unop) m))
      rw [F.symMap_ι, SymmetricAlgebra.algebraMapInv_ι, SymmetricAlgebra.algebraMapInv_ι,
        map_zero]

@[reassoc (attr := simp)]
lemma toSymPresheaf_symAugmentation : F.toSymPresheaf ≫ F.symAugmentation = 𝟙 _ := by
  ext U r
  exact AlgHom.commutes _ r

lemma coequifibered_id_restrict :
    NatTrans.Coequifibered (𝟙 ((AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf)) :=
  NatTrans.Coequifibered.of_isIso _

instance :
    IsIso (AffineZariskiSite.relativeGluingData (coequifibered_id_restrict (X := X))).toBase :=
  AffineZariskiSite.toBase_of_forall _ (.isomorphisms _) fun _ ↦
    (MorphismProperty.isomorphisms.iff _).mpr
      (by rw [NatTrans.id_app, Spec.map_id]; infer_instance)

/-- Blueprint `proposition-purity-vector-bundles`: Vector bundle with zero section

The *zero section* `X ⟶ Spec_X (Sym^• ℰ)`, defined by the augmentation `Sym^• ℰ ⟶ 𝒪_X`. -/
noncomputable def symSpecZeroSection [F.IsQuasicoherent] : X ⟶ F.symSpec :=
  inv (AffineZariskiSite.relativeGluingData (coequifibered_id_restrict (X := X))).toBase ≫
    AffineZariskiSite.relativeGluingMap F.coequifibered_toSymPresheaf coequifibered_id_restrict
      (Functor.whiskerLeft _ F.symAugmentation)

@[reassoc (attr := simp)]
lemma symSpecZeroSection_symSpecProj [F.IsQuasicoherent] :
    F.symSpecZeroSection ≫ F.symSpecProj = 𝟙 X := by
  rw [symSpecZeroSection, symSpecProj, Category.assoc,
    AffineZariskiSite.relativeGluingMap_toBase _ _ _ (by
      rw [← Functor.whiskerLeft_comp, toSymPresheaf_symAugmentation]; rfl),
    IsIso.inv_hom_id]

instance [F.IsQuasicoherent] : IsClosedImmersion F.symSpecZeroSection := by
  have : IsClosedImmersion (F.symSpecZeroSection ≫ F.symSpecProj) := by
    rw [symSpecZeroSection_symSpecProj]; infer_instance
  have : IsAffineHom F.symSpecProj := by unfold symSpecProj; infer_instance
  exact IsClosedImmersion.of_comp _ F.symSpecProj

end AlgebraicGeometry.Scheme.Modules
