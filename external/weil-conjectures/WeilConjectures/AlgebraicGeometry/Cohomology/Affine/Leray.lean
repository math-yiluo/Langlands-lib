/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.CechAcyclic
public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
public import WeilConjectures.Topology.Sheaves.CechCohomology
public import WeilConjectures.Topology.Sheaves.CechComparison

/-!
# Leray's theorem for quasi-coherent sheaves on schemes

Leray's theorem: for a cover by affine opens with affine finite intersections, the Čech cohomology
of a quasi-coherent sheaf is its sheaf cohomology, as modules over the global functions
(`AlgebraicGeometry.Scheme.Modules.nonempty_cechComplex_linearEquiv_H`).
-/

@[expose] public section

universe u

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The action of a global function on cohomology is the map induced by multiplication. -/
lemma H.smul_eq_map (ℱ : X.Modules) (q : ℕ) (r : Γ(X, ⊤)) (x : ℱ.H q) :
    r • x = H.map (ℱ.smulHom r) q x :=
  rfl

/-- The presheaf of abelian groups underlying `ℱ.presheafModuleCat` is that of `ℱ`. -/
noncomputable def presheafModuleCatCompForget₂Iso (ℱ : X.Modules) :
    ℱ.presheafModuleCat ⋙ forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u} ≅
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj ℱ).obj :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun _ ↦ rfl

/-- Multiplication by a global function on `ℱ.presheafModuleCat` is multiplication by it on
the underlying abelian sheaf of `ℱ`. -/
lemma whiskerRight_smul_presheafModuleCat (ℱ : X.Modules) (r : Γ(X, ⊤)) :
    Functor.whiskerRight (r • 𝟙 ℱ.presheafModuleCat) (forget₂ (ModuleCat.{u} Γ(X, ⊤))
      AddCommGrpCat.{u}) ≫ (presheafModuleCatCompForget₂Iso ℱ).hom =
      (presheafModuleCatCompForget₂Iso ℱ).hom ≫
        ((SheafOfModules.toSheaf X.ringCatSheaf).map (ℱ.smulHom r)).hom := by
  ext V x
  rfl

/-- The homology of Mathlib's Čech complex of `ℱ.presheafModuleCat` is the Čech cohomology of the
underlying abelian sheaf of `ℱ`. -/
noncomputable def cechComplexHomologyAddEquiv {ι : Type u} (U : ι → X.Opens) (ℱ : X.Modules)
    (q : ℕ) : ((cechComplexFunctor U).obj ℱ.presheafModuleCat).homology q ≃+
      (TopCat.Sheaf.cechCohomologyFunctor U q).obj
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj ℱ) :=
  (TopCat.Presheaf.cechComplexFunctorHomologyIso U ℱ.presheafModuleCat q ≪≫
    HomologicalComplex.homologyMapIso ((TopCat.Presheaf.cechComplex U).mapIso
      (presheafModuleCatCompForget₂Iso ℱ)) q).addCommGroupIsoToAddEquiv

/-- The identification `cechComplexHomologyAddEquiv` transports multiplication by a global
function to the map induced on Čech cohomology by multiplication on `ℱ`. -/
lemma cechComplexHomologyAddEquiv_smul {ι : Type u} (U : ι → X.Opens) (ℱ : X.Modules)
    (q : ℕ) (r : Γ(X, ⊤)) (x : ((cechComplexFunctor U).obj ℱ.presheafModuleCat).homology q) :
    cechComplexHomologyAddEquiv U ℱ q (r • x) =
      (TopCat.Sheaf.cechCohomologyFunctor U q).map
        ((SheafOfModules.toSheaf X.ringCatSheaf).map (ℱ.smulHom r))
          (cechComplexHomologyAddEquiv U ℱ q x) := by
  have key : HomologicalComplex.homologyMap ((TopCat.Presheaf.cechComplex U).map
      (Functor.whiskerRight (r • 𝟙 ℱ.presheafModuleCat)
        (forget₂ (ModuleCat.{u} Γ(X, ⊤)) AddCommGrpCat.{u}))) q ≫
      HomologicalComplex.homologyMap ((TopCat.Presheaf.cechComplex U).map
        (presheafModuleCatCompForget₂Iso ℱ).hom) q =
      HomologicalComplex.homologyMap ((TopCat.Presheaf.cechComplex U).map
        (presheafModuleCatCompForget₂Iso ℱ).hom) q ≫
      HomologicalComplex.homologyMap ((TopCat.Presheaf.cechComplex U).map
        ((SheafOfModules.toSheaf X.ringCatSheaf).map (ℱ.smulHom r)).hom) q := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
      ← Functor.map_comp, ← Functor.map_comp, whiskerRight_smul_presheafModuleCat]
  change HomologicalComplex.homologyMap ((TopCat.Presheaf.cechComplex U).map
      (presheafModuleCatCompForget₂Iso ℱ).hom) q
      ((TopCat.Presheaf.cechComplexFunctorHomologyIso U ℱ.presheafModuleCat q).hom (r • x)) =
    HomologicalComplex.homologyMap ((TopCat.Presheaf.cechComplex U).map
      ((SheafOfModules.toSheaf X.ringCatSheaf).map (ℱ.smulHom r)).hom) q
      (HomologicalComplex.homologyMap ((TopCat.Presheaf.cechComplex U).map
        (presheafModuleCatCompForget₂Iso ℱ).hom) q
        ((TopCat.Presheaf.cechComplexFunctorHomologyIso U ℱ.presheafModuleCat q).hom x))
  rw [TopCat.Presheaf.cechComplexFunctorHomologyIso_hom_smul]
  exact ConcreteCategory.congr_hom key _

/-- **Leray's theorem for quasi-coherent sheaves.** Let `𝔘 = (U i)` be an open covering of `X`
all of whose nonempty finite intersections `U i₀ ⊓ ⋯ ⊓ U iₙ` are affine. Then for every
quasi-coherent `𝒪_X`-module `ℱ` and every `q` the Čech cohomology of the covering agrees with
the sheaf cohomology, `Ȟ^q(𝔘, ℱ) ≅ H^q(X, ℱ)`, as `Γ(X, ⊤)`-modules.

The left-hand side is the `q`-th cohomology of the Čech complex `cechComplexFunctor U` of the
family `U` with coefficients in the presheaf of `Γ(X, ⊤)`-modules `ℱ.presheafModuleCat`; the
right-hand side carries the `Γ(X, ⊤)`-module structure
`AlgebraicGeometry.Scheme.Modules.moduleH`.

The isomorphism ought to be the edge map of the Čech-to-derived spectral sequence
`CategoryTheory.Sheaf.exists_cechToDerivedSpectralSequence`, which is an isomorphism because
the higher rows of that spectral sequence vanish by `subsingleton_H_succ_of_isAffine`; see the
implementation notes of this module for what is lost by not naming it.

(blueprint: `lem-pc-cech-computes`) -/
@[stacks 01XD]
theorem nonempty_cechComplex_linearEquiv_H {ι : Type u} (U : ι → X.Opens)
    (hU : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (⨅ i ∈ s, U i)) (hU' : iSup U = ⊤)
    (ℱ : X.Modules) [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] (q : ℕ) :
    Nonempty (((cechComplexFunctor U).obj ℱ.presheafModuleCat).homology q ≃ₗ[Γ(X, ⊤)] ℱ.H q) := by
  classical
  have hU₀ (k : ℕ) (y : Fin (k + 1) → ι) : IsAffineOpen (⨅ l, U (y l)) := by
    have h := hU (Finset.univ.image y) (Finset.univ_nonempty.image y)
    convert h using 1
    refine le_antisymm (le_iInf₂ fun i hi ↦ ?_)
      (le_iInf fun l ↦ iInf₂_le (y l) (Finset.mem_image_of_mem y (Finset.mem_univ l)))
    obtain ⟨l, -, rfl⟩ := Finset.mem_image.1 hi
    exact iInf_le _ l
  obtain ⟨e⟩ := TopCat.Sheaf.nonempty_cechCohomologyFunctor_iso_functorH U hU'
    (cechAcyclicOnAffines X) (fun _ h ↦ cechAcyclicOnAffines_under_cokernel h)
    (fun _ hS h k y ↦ surjective_app_of_cechAcyclicOnAffines hS h (hU₀ k y)) q
  let F : (cechAcyclicOnAffines X).FullSubcategory :=
    ⟨(SheafOfModules.toSheaf X.ringCatSheaf).obj ℱ, cechAcyclicOnAffines_of_isQuasicoherent ℱ⟩
  let E : ((cechComplexFunctor U).obj ℱ.presheafModuleCat).homology q ≃+ ℱ.H q :=
    (cechComplexHomologyAddEquiv U ℱ q).trans (e.app F).addCommGroupIsoToAddEquiv
  have hE (r : Γ(X, ⊤)) (x : ((cechComplexFunctor U).obj ℱ.presheafModuleCat).homology q) :
      E (r • x) = H.map (ℱ.smulHom r) q (E x) := by
    have h := ConcreteCategory.congr_hom (e.hom.naturality (ObjectProperty.homMk
      ((SheafOfModules.toSheaf X.ringCatSheaf).map (ℱ.smulHom r)) : F ⟶ F))
        (cechComplexHomologyAddEquiv U ℱ q x)
    refine (congrArg (e.app F).hom (cechComplexHomologyAddEquiv_smul U ℱ q r x)).trans ?_
    exact h
  exact ⟨{ toAddEquiv := E, map_smul' := fun r x ↦ (hE r x).trans (H.smul_eq_map ℱ q r _).symm }⟩

/-- **Leray's theorem for schemes separated over an affine base.** Let `X` be separated over an
affine base `S` and let `𝔘 = (U i)` be a covering of `X` by open affines. Then for every
quasi-coherent `𝒪_X`-module `ℱ` and every `q` we have `Ȟ^q(𝔘, ℱ) ≅ H^q(X, ℱ)` as
`Γ(X, ⊤)`-modules. This is `nonempty_cechComplex_linearEquiv_H`, the finite intersections of
the `U i` being affine because `X` is separated.

Restricting scalars along `f.appTop`, the isomorphism is `Γ(S, 𝒪_S)`-linear, and `k`-linear
when `S = Spec k`.

(blueprint: `lemma-coherent-base-change-invertible-sheaves--1`) -/
theorem nonempty_cechComplex_linearEquiv_H_of_isSeparated {S : Scheme.{u}} (f : X ⟶ S)
    [IsSeparated f] [IsAffine S] {ι : Type u} (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (hU' : iSup U = ⊤) (ℱ : X.Modules)
    [SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) ℱ] (q : ℕ) :
    Nonempty (((cechComplexFunctor U).obj ℱ.presheafModuleCat).homology q ≃ₗ[Γ(X, ⊤)] ℱ.H q) :=
  haveI : IsSeparated (terminal.from X) := by
    rw [← terminal.comp_from f]
    infer_instance
  nonempty_cechComplex_linearEquiv_H U
    (fun s hs ↦ IsAffineOpen.biInf (s : Set ι) s.finite_toSet hs (fun i _ ↦ hU i)) hU' ℱ q

end AlgebraicGeometry.Scheme.Modules
