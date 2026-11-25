/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Preadditive.LeftExact
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import Mathlib.CategoryTheory.Abelian.Projective.Extend
import Mathlib.Algebra.Category.ModuleCat.Projective

/-! # Sheafifying a prescribed finite free resolution

Source: Stacks Project, Algebra, Tag 00LP; Schemes, Tag 01HV;
Modules, Tag 01AG (blueprint: lem-sc-finite-free-resolution-sheafification).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Sheafification of an already specified exact finite free resolution, followed by transport
along an affine chart and the equivalence between open subschemes and the over-site.
No coherence, Noetherian hypothesis, or choice of an affine neighbourhood is required.
Source: Stacks Project, Algebra, Tag 00LP (lemma-resolution-by-finite-free), Schemes,
Tag 01HV (lemma-spec-sheaves), and Modules, Tag 01AG (lemma-abelian)
(blueprint: lem-sc-finite-free-resolution-sheafification).

Proof:
1. Put `A^(n j)` in cochain degree `-j`, zero in every positive degree, and use `d j`
   from degree `-(j+1)` to `-j`. The image-kernel identities imply that consecutive
   differentials compose to zero. The augmentation is `ε` in degree zero and zero
   otherwise; its compatibility follows from `range (d 0) = ker ε`.
2. Apply tilde termwise. Its stalk at a prime is the localization of the given module
   (Tag 01HV). Localization preserves the specified augmented exact sequence, and
   stalks detect exactness (Tag 01AG). Thus this augmentation induces an isomorphism
   on degree-zero homology and both sides have zero homology in every other degree.
3. Pull the sheaf complex back along the chart isomorphism `e`, then apply
   `(Scheme.Modules.overEquiv U).inverse` termwise. These equivalences preserve
   exactness, zero objects and finite direct sums of the unit, so preserve the
   augmentation quasi-isomorphism and the bound zero. The tilde of `A^(n j)` is
   free of rank `n j`: identify finite functions with finitely supported functions
   and use `tildeFinsupp`. Transport the standard basis along `Equiv.ulift` to the
   index type `ULift (Fin (n j))`. The positive-degree zero terms are free of rank
   zero. Commutation with the degree-zero single functor gives the stated target.

The statement concerns only the conversion of explicit algebraic resolution data into
an augmented sheaf complex. For the zero module, the zero ring, or an empty chart the
same construction works; rank zero is allowed in every degree. -/
theorem finite_free_resolution_sheafification
    (X : Scheme.{u}) (U : X.Opens)
    (A : Type u) [CommRing A] (e : U.toScheme ≅ Spec (CommRingCat.of A))
    (M : Type u) [AddCommGroup M] [Module A M]
    (n : ℕ → ℕ) (ε : (Fin (n 0) → A) →ₗ[A] M)
    (d : ∀ j : ℕ, (Fin (n (j + 1)) → A) →ₗ[A] (Fin (n j) → A))
    (hε : Function.Surjective ε) (h₀ : LinearMap.ker ε = LinearMap.range (d 0))
    (hd : ∀ j : ℕ, LinearMap.ker (d j) = LinearMap.range (d (j + 1))) :
    ∃ E : CochainComplex
        (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ,
      (∃ N : ℤ, ∀ i : ℤ, N < i → IsZero (E.X i)) ∧
      (∀ i : ℤ, ∃ r : ℕ, Nonempty (E.X i ≅ SheafOfModules.free
        (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin r)))) ∧
      ∃ q : E ⟶ (CochainComplex.singleFunctor
        (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) 0).obj
          ((Scheme.Modules.overEquiv U).inverse.obj
            ((Scheme.Modules.restrictFunctor e.hom).obj (tilde (ModuleCat.of A M)))),
        QuasiIso q := by
  classical
  let V : ℕ → ModuleCat.{u} A := fun j ↦ ModuleCat.of A (Fin (n j) → A)
  have sq (j : ℕ) : ModuleCat.ofHom (d (j + 1)) ≫ ModuleCat.ofHom (d j) = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change d j (d (j + 1) x) = 0
    apply LinearMap.mem_ker.mp
    rw [hd j]
    exact LinearMap.mem_range.mpr ⟨x, rfl⟩
  let K := ChainComplex.of V (fun j ↦ ModuleCat.ofHom (d j)) sq
  have aug : K.d 1 0 ≫ ModuleCat.ofHom ε = 0 := by
    change ModuleCat.ofHom (d 0) ≫ ModuleCat.ofHom ε = 0
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change ε (d 0 x) = 0
    apply LinearMap.mem_ker.mp
    rw [h₀]
    exact LinearMap.mem_range.mpr ⟨x, rfl⟩
  let π := (ChainComplex.toSingle₀Equiv K (ModuleCat.of A M)).symm
    ⟨ModuleCat.ofHom ε, aug⟩
  have hπ : QuasiIso π := by
    constructor
    intro j
    cases j with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · change (ShortComplex.mk _ _ aug).Exact ∧ Epi (ModuleCat.ofHom ε)
        constructor
        · rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
          simpa [K, ChainComplex.of.d] using h₀.symm
        · exact (ModuleCat.epi_iff_surjective _).mpr hε
      all_goals rfl
    | succ j =>
      rw [quasiIsoAt_iff_exactAt']
      · rw [HomologicalComplex.exactAt_iff' K (j + 2) (j + 1) j (by simp) (by simp)]
        rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
        simpa [K, ChainComplex.of.d, HomologicalComplex.sc',
          HomologicalComplex.shortComplexFunctor'] using
          (hd j).symm
      · apply ChainComplex.exactAt_succ_single_obj
  let R : ProjectiveResolution (ModuleCat.of A M) :=
    { complex := K
      π := π
      projective := fun j ↦ by dsimp [K, V]; infer_instance
      quasiIso := hπ }
  -- Use kernel preservation and the tilde adjunction for exactness, replacing
  -- the stalk-localization argument described in the source proof.
  let T := tilde.functor (CommRingCat.of A)
  let F := Scheme.Modules.restrictFunctor e.hom
  let G := (Scheme.Modules.overEquiv U).inverse
  let : T.IsLeftAdjoint := (tilde.adjunction (R := CommRingCat.of A)).isLeftAdjoint
  let := preservesBinaryBiproducts_of_preservesBinaryCoproducts T
  let : T.Additive := Functor.additive_of_preservesBinaryBiproducts T
  let : F.IsLeftAdjoint := (Scheme.Modules.restrictAdjunction e.hom).isLeftAdjoint
  let : PreservesFiniteLimits F := by
    dsimp [F]
    infer_instance
  let H := (T ⋙ F) ⋙ G
  let tilde_preservesKernel : ∀ {P Q : ModuleCat.{u} A} (f : P ⟶ Q),
      Limits.PreservesLimit (Limits.parallelPair f 0) (tilde.functor (.of A)) := by
    intro P Q f
    let T := tilde.functor (.of A)
    let ff : T.FullyFaithful := tilde.fullyFaithfulFunctor (R := .of A)
    let : T.Full := ff.full
    let : T.Faithful := ff.faithful
    let : T.IsLeftAdjoint := (tilde.adjunction (R := .of A)).isLeftAdjoint
    let := Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts T
    let : T.Additive := Functor.additive_of_preservesBinaryBiproducts T
    have : (T.obj P).IsQuasicoherent := by
      change (tilde.{u} (R := .of A) P).IsQuasicoherent
      infer_instance
    have : (T.obj Q).IsQuasicoherent := by
      change (tilde.{u} (R := .of A) Q).IsQuasicoherent
      infer_instance
    let k := Limits.kernel (T.map f)
    have hk : k.IsQuasicoherent := Scheme.Modules.isQuasicoherent_kernel (T.map f)
    have : IsIso (Scheme.Modules.fromTildeΓ (R := .of A) k) :=
      Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := .of A) k
    let e : T.obj ((moduleSpecΓFunctor (R := .of A)).obj k) ≅ k :=
      asIso (Scheme.Modules.fromTildeΓ (R := .of A) k)
    let t := T.preimage (e.hom ≫ Limits.kernel.ι (T.map f))
    have ht : t ≫ f = 0 := by
      apply T.map_injective
      simp only [Functor.map_comp, Functor.map_preimage, Functor.map_zero,
        Category.assoc, Limits.kernel.condition, Limits.comp_zero, t]
    let c := Limits.KernelFork.ofι t ht
    have hc : Limits.IsLimit (c.map T) := by
      apply Limits.IsLimit.ofIsoLimit (Limits.kernelIsKernel (T.map f))
      exact Limits.Fork.ext e.symm (by simp [c, t, Limits.KernelFork.map])
    have hc' : Limits.IsLimit c :=
      Limits.isLimitOfReflects T ((c.isLimitMapConeEquiv T).symm hc)
    exact Limits.preservesLimit_of_preserves_limit_cone hc'
      ((c.isLimitMapConeEquiv T).symm hc)
  let : ∀ {P Q : ModuleCat.{u} A} (f : P ⟶ Q),
      PreservesLimit (parallelPair f 0) T := fun {_ _} f ↦ tilde_preservesKernel f
  let : PreservesFiniteLimits T := Functor.preservesFiniteLimits_of_preservesKernels T
  let : PreservesFiniteLimits (T ⋙ F) := comp_preservesFiniteLimits _ _
  let : PreservesFiniteLimits H := comp_preservesFiniteLimits _ _
  let : PreservesFiniteColimits (T ⋙ F) := comp_preservesFiniteColimits _ _
  let : PreservesFiniteColimits H := comp_preservesFiniteColimits _ _
  let E := (H.mapHomologicalComplex (ComplexShape.up ℤ)).obj R.cochainComplex
  refine ⟨E, ⟨0, ?_⟩, ?_, ?_⟩
  · intro i hi
    exact H.map_isZero (CochainComplex.isZero_of_isStrictlyLE R.cochainComplex 0 i)
  · intro i
    by_cases hi : i ≤ 0
    · obtain ⟨j, rfl⟩ := Int.exists_eq_neg_ofNat hi
      let b := (Pi.basisFun A (Fin (n j))).reindex Equiv.ulift.symm
      let t := T.mapIso b.repr.toModuleIso ≪≫ tildeFinsupp (ULift.{u} (Fin (n j)))
      let f := (SheafOfModules.mapFreeIso F (ULift.{u} (Fin (n j)))
        (Scheme.Modules.restrictUnitIso e.hom).symm).symm
      let g := (SheafOfModules.mapFreeIso G (ULift.{u} (Fin (n j)))
        (U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf).symm).symm
      exact ⟨n j, ⟨H.mapIso (R.cochainComplexXIso (-j) j) ≪≫
        G.mapIso (F.mapIso t ≪≫ f) ≪≫ g⟩⟩
    · have hz := H.map_isZero
        (CochainComplex.isZero_of_isStrictlyLE R.cochainComplex 0 i)
      have hzero : IsZero (SheafOfModules.free
          (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin 0))) := by
        apply (IsZero.iff_id_eq_zero _).2
        apply Sigma.hom_ext
        intro j
        exact Fin.elim0 j.down
      exact ⟨0, ⟨hz.iso hzero⟩⟩
  · let q := (H.mapHomologicalComplex (ComplexShape.up ℤ)).map R.π' ≫
      (HomologicalComplex.singleMapHomologicalComplex H (ComplexShape.up ℤ) 0).hom.app
        (ModuleCat.of A M)
    exact ⟨q, by dsimp [q]; infer_instance⟩

end AlgebraicGeometry
