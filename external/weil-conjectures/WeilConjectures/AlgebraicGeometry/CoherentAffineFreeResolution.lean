/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Coherent
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Homology.QuasiIso
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.RingTheory.FiniteFreeResolution
import WeilConjectures.AlgebraicGeometry.FiniteFreeResolutionSheafification
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel

/-! # Finite free resolutions on affine neighbourhoods

Source: Stacks Project, Coherent Modules, Lemma 01XZ and Algebra, Lemma 00LP
(blueprint: lem-sc-coherent-affine-free-resolution).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- A coherent module on a Noetherian scheme is locally represented by a finite module on an
affine open, and admits there a bounded-above resolution by finite-rank free modules.
Source: Stacks Project, Coherent Modules, Lemma 01XZ and Algebra, Lemma 00LP
(blueprint: lem-sc-coherent-affine-free-resolution).

The bounded-above condition is expressed by vanishing above an integer bound, each finite-free
term by an isomorphism with `SheafOfModules.free`, and the augmentation by `QuasiIso` to the
degree-zero complex.

Proof:
1. Choose an affine open containing `x` from a locally Noetherian affine cover; its ring
   is Noetherian (def-weil-pbc-quasi-compact-scheme, pqf-def-locnoeth).
2. Coherence gives quasi-coherence and finite type (pqf-lem-coherent-ft-locnoeth).
   The affine sections criterion (lem-weil-pbc-quasi-coherent-finite-type-affine) makes
   the module of sections finite. The tilde-Gamma counit
   (lem-weil-pbc-affine-tilde-gamma-adjunction) identifies its tilde with the restriction.
3. Resolve that module by finite free modules
   (lem-weil-pbc-finite-free-resolution-noetherian), apply tilde termwise, and put the
   terms in degrees `-i`. The tilde-stalk localization identification
   (lem-weil-pbc-spec-tilde-stalk-localization) and exactness of localization make the
   augmented complex exact on stalks. Exactness is detected on stalks
   (lem-weil-pbc-module-stalk-exact), so the augmentation is a quasi-isomorphism. -/
theorem coherent_affine_free_resolution
    (X : Scheme.{u}) [IsNoetherian X]
    (F : X.Modules) (hF : RingedSpace.IsCoherent X.toRingedSpace F) (x : X) :
    ∃ (U : X.Opens) (A : Type u) (_ : CommRing A) (_ : IsNoetherianRing A)
      (_ : x ∈ U) (_ : IsAffineOpen U)
      (M : Type u) (_ : AddCommGroup M) (_ : Module A M) (_ : Module.Finite A M)
      (e : U.toScheme ≅ Spec (CommRingCat.of A)),
      Nonempty (F.restrict U.ι ≅ (Scheme.Modules.restrictFunctor e.hom).obj
        (tilde (ModuleCat.of A M))) ∧
      ∃ (E : CochainComplex
          (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ),
        (∃ N : ℤ, ∀ i : ℤ, N < i → IsZero (E.X i)) ∧
        (∀ i : ℤ, ∃ r : ℕ, Nonempty (E.X i ≅ SheafOfModules.free
          (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin r)))) ∧
        ∃ q : E ⟶ (CochainComplex.singleFunctor
          (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) 0).obj (F.over U),
          QuasiIso q := by
  obtain ⟨hq, ht⟩ :=
    (Scheme.Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType X F).mp hF
  have : F.IsQuasicoherent := hq
  have : F.IsFiniteType := ht
  obtain ⟨D, hD⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData F
  obtain ⟨i, hxi⟩ := ((Opens.coversTop_iff _ D.X).mp D.coversTop).exists_mem x
  obtain ⟨U, hU, hxU, hUi⟩ := exists_isAffineOpen_mem_and_subset hxi
  have : IsNoetherianRing Γ(X, U) :=
    IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let W : X.Opens := D.X i
  let f := hU.fromSpec
  let v : Spec Γ(X, U) ⟶ W.toScheme :=
    IsOpenImmersion.lift W.ι f (by
      rw [Scheme.Opens.range_ι]
      exact hU.opensRange_fromSpec.le.trans hUi)
  have hv : v ≫ W.ι = f := IsOpenImmersion.lift_fac _ _ _
  have : IsOpenImmersion (v ≫ W.ι) := by rw [hv]; infer_instance
  have : IsOpenImmersion v := IsOpenImmersion.of_comp v W.ι
  have : PreservesColimitsOfSize.{u, u} (Scheme.Modules.restrictFunctor v) :=
    inferInstance
  let H := (Scheme.Modules.overEquiv (D.X i)).functor ⋙
    Scheme.Modules.restrictFunctor v
  let a₀ : SheafOfModules.overFunctor X.ringCatSheaf (D.X i) ⋙ H ≅
      Scheme.Modules.restrictFunctor f :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (Scheme.Modules.overFunctorEquiv (D.X i)) _ ≪≫
      (Scheme.Modules.restrictFunctorComp v W.ι).symm ≪≫
      Scheme.Modules.restrictFunctorCongr hv
  have := hD.isFiniteType i
  let σ := ((D.generators i).map H (Scheme.Modules.restrictUnitIso v).symm).ofEpi
    (a₀.app F).hom
  let G := F.restrict hU.fromSpec
  let M := moduleSpecΓFunctor.obj G
  have : Module.Finite Γ(X, U) Γ(G, ⊤) :=
    Scheme.Modules.finite_sections_top_of_isIso_fromTildeΓ G σ
  have : Module.Finite Γ(X, U) M :=
    inferInstanceAs (Module.Finite Γ(X, U) Γ(G, ⊤))
  let e := hU.isoSpec
  let a : F.restrict U.ι ≅ (Scheme.Modules.restrictFunctor e.hom).obj G :=
    (Scheme.Modules.restrictFunctorCongr hU.isoSpec_hom_fromSpec.symm).app F ≪≫
      (Scheme.Modules.restrictFunctorComp e.hom hU.fromSpec).app F
  let b : G ≅ tilde M := (asIso G.fromTildeΓ).symm
  let c := a ≪≫ (Scheme.Modules.restrictFunctor e.hom).mapIso b
  refine ⟨U, Γ(X, U), inferInstance, inferInstance, hxU, hU,
    M, inferInstance, inferInstance, inferInstance, e, ⟨c⟩, ?_⟩
  obtain ⟨n, ε, d, hε, h₀, hd⟩ := Module.exists_finite_free_resolution Γ(X, U) M
  obtain ⟨E, hbound, hfree, q, hq⟩ :=
    finite_free_resolution_sheafification X U Γ(X, U) e M n ε d hε h₀ hd
  let t : F.over U ≅ (Scheme.Modules.overEquiv U).inverse.obj
      ((Scheme.Modules.restrictFunctor e.hom).obj (tilde (ModuleCat.of Γ(X, U) M))) :=
    (Scheme.Modules.overEquiv U).unitIso.app (F.over U) ≪≫
      (Scheme.Modules.overEquiv U).inverse.mapIso
        ((Scheme.Modules.overFunctorEquiv U).app F ≪≫ c)
  have : QuasiIso q := hq
  refine ⟨E, hbound, hfree, q ≫ (CochainComplex.singleFunctor _ 0).map t.inv, ?_⟩
  infer_instance

end AlgebraicGeometry
