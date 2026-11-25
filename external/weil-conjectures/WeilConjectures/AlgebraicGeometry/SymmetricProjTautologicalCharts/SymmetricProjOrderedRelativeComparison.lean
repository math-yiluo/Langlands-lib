/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveBundleQuotientGeometry.ProjectiveBundleQuotientData
import WeilConjectures.AlgebraicGeometry.SymmetricProjTautologicalCharts.AffineFreeComparisonConstructor
import WeilConjectures.AlgebraicGeometry.RelativeProj.Functoriality
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import WeilConjectures.AlgebraicGeometry.RelativeProjectiveSpace.FreeProjectiveBundleBaseChangeSpace
import WeilConjectures.AlgebraicGeometry.Proj.ProjScalarExtensionTwistComparison
import Mathlib.RingTheory.TensorProduct.Maps
import WeilConjectures.AlgebraicGeometry.Modules.HomSection

/-!
# Ordered relative-Proj comparison on polynomial charts

Source: Stacks Project, Constructions, Tags 01OE, 01OB and 01MS.
(blueprint: lem-trf-symmetric-proj-ordered-relative-comparison).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.SymmetricProjTautologicalCharts

attribute [local irreducible] Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj
  Scheme.Modules.tensorPullbackSectionComp Scheme.Modules.tensorPullbackSectionAdjunction
  Scheme.Modules.boundaryPullbackComparison

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

private theorem moduleHom_app_val {S : Scheme.{u}} {M N : S.Modules}
    (f : M ⟶ N) (U : S.Opens) (x : M.val.obj (op U)) :
    f.app U x = f.val.app (op U) x := rfl

private theorem unitSection_comp {S : Scheme.{u}} {F E : S.Modules}
    (a : Scheme.Modules.unit S ⟶ F) (b : F ⟶ E) (U : S.Opens) :
    b.app U (a.val.app (op U) (1 : Γ(S, U))) =
      (a ≫ b).val.app (op U) (1 : Γ(S, U)) := by
  rw [moduleHom_app_val]
  rfl

private theorem unitSection_natural {S : Scheme.{u}} {E : S.Modules}
    (a : Scheme.Modules.unit S ⟶ E) {U V : S.Opens} (h : U ≤ V) :
    E.val.map (homOfLE h).op (a.val.app (op V) (1 : Γ(S, V))) =
      a.val.app (op U) (1 : Γ(S, U)) := by
  have hn := PresheafOfModules.naturality_apply a.val (homOfLE h).op (1 : Γ(S, V))
  have hu : (Scheme.Modules.unit S).val.map (homOfLE h).op (1 : Γ(S, V)) =
      (1 : Γ(S, U)) := (S.presheaf.map (homOfLE h).op).hom.map_one
  rw [hu] at hn
  exact hn.symm

private theorem modulePresheaf_map_id_apply {S : Scheme.{u}} (M : S.Modules)
    (U : S.Opens) (x : Γ(M, U)) : M.presheaf.map (𝟙 (op U)) x = x := by
  rw [CategoryTheory.Functor.map_id]
  rfl

private def orderedFreeSections (S : Scheme.{u}) (r : ℕ) (U : S.Opens) :
    (RelativeProjectiveSpace.freeModule S r).val.obj (op U) ≃ₗ[Γ(S, U)]
      (ULift.{u} (Fin (r + 1)) → Γ(S, U)) where
  toFun x i := (Scheme.Modules.freeπ i).val.app (op U) x
  map_add' x y := by ext i; exact map_add _ _ _
  map_smul' a x := by
    ext i
    exact (Scheme.Modules.freeπ i).val.app (op U) |>.hom.map_smul a x
  invFun c := ∑ i, (SheafOfModules.ιFree (R := S.ringCatSheaf) i).val.app (op U) (c i)
  left_inv x := by
    change ∑ i : ULift.{u} (Fin (r + 1)), (Scheme.Modules.Hom.app
      (Scheme.Modules.freeπ i ≫ SheafOfModules.ιFree i) U) x = x
    rw [← Scheme.Modules.Hom.sum_app_apply, Scheme.Modules.sum_freeπ_ιFree]
    rfl
  right_inv c := by
    ext j
    change (Scheme.Modules.freeπ j).val.app (op U) (∑ i,
      (SheafOfModules.ιFree (R := S.ringCatSheaf) i).val.app (op U) (c i)) = c j
    rw [map_sum, Finset.sum_eq_single j _ (by simp)]
    · have h := congrArg (fun f ↦ f.val.app (op U) (c j))
        (Scheme.Modules.ιFree_freeπ (X := S) j j)
      rw [ite_eq_left rfl] at h
      exact h
    · intro i _ hij
      have h := congrArg (fun f ↦ f.val.app (op U) (c i))
        (Scheme.Modules.ιFree_freeπ (X := S) i j)
      rw [ite_eq_right hij] at h
      exact h

private def orderedSectionEquiv {S : Scheme.{u}} {E F : S.Modules}
    (b : F ≅ E) (U : S.Opens) : F.val.obj (op U) ≃ₗ[Γ(S, U)] E.val.obj (op U) where
  toLinearMap := (b.hom.val.app (op U)).hom
  invFun := b.inv.val.app (op U)
  left_inv x := by
    have h := congrArg (fun f ↦ f.val.app (op U) x) b.hom_inv_id
    exact h
  right_inv x := by
    have h := congrArg (fun f ↦ f.val.app (op U) x) b.inv_hom_id
    exact h

private def orderedBasis {S : Scheme.{u}} {E : S.Modules} {r : ℕ}
    (b : RelativeProjectiveSpace.freeModule S r ≅ E) (U : S.Opens) :
    Module.Basis (ULift.{u} (Fin (r + 1))) Γ(S, U) (E.val.obj (op U)) :=
  ((Pi.basisFun Γ(S, U) (ULift.{u} (Fin (r + 1)))).map
    (orderedFreeSections S r U).symm).map (orderedSectionEquiv b U)

private theorem orderedBasis_apply {S : Scheme.{u}} {E : S.Modules} {r : ℕ}
    (b : RelativeProjectiveSpace.freeModule S r ≅ E) (U : S.Opens)
    (i : ULift.{u} (Fin (r + 1))) :
    orderedBasis b U i = b.hom.app U
      ((SheafOfModules.ιFree (R := S.ringCatSheaf) i).val.app (op U) (1 : Γ(S, U))) := by
  classical
  unfold orderedBasis
  simp only [Module.Basis.map_apply, Pi.basisFun_apply]
  change b.hom.app U (∑ j : ULift.{u} (Fin (r + 1)),
    (SheafOfModules.ιFree (R := S.ringCatSheaf) j).val.app (op U)
      ((Pi.single i 1 : ULift.{u} (Fin (r + 1)) → Γ(S, U)) j)) = _
  congr 1
  simp only [Pi.single_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

private def orderedPolynomial {S : Scheme.{u}} {E : S.Modules} {r : ℕ}
    (b : RelativeProjectiveSpace.freeModule S r ≅ E) (V : S.affineOpens) :
    MvPolynomial (ULift.{u} (Fin (r + 1))) Γ(S, V.1) ≃ₐ[Γ(S, V.1)]
      SymmetricAlgebra Γ(S, V.1) (E.val.obj (op V.1)) :=
  (SymmetricAlgebra.equivMvPolynomial (orderedBasis b V.1)).symm

private theorem orderedPolynomial_X {S : Scheme.{u}} {E : S.Modules} {r : ℕ}
    (b : RelativeProjectiveSpace.freeModule S r ≅ E) (V : S.affineOpens)
    (i : ULift.{u} (Fin (r + 1))) :
    orderedPolynomial b V (MvPolynomial.X i) = SymmetricAlgebra.ι Γ(S, V.1)
      (E.val.obj (op V.1)) (b.hom.app V.1
        ((SheafOfModules.ιFree (R := S.ringCatSheaf) i).val.app (op V.1) (1 : Γ(S, V.1)))) := by
  rw [orderedPolynomial, SymmetricAlgebra.equivMvPolynomial_symm_X, orderedBasis_apply]

private theorem orderedPolynomial_degree {S : Scheme.{u}} {E : S.Modules} {r : ℕ}
    (b : RelativeProjectiveSpace.freeModule S r ≅ E) (V : S.affineOpens) (n : ℕ) :
    (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (r + 1))) Γ(S, V.1) n).map
        (orderedPolynomial b V).toAlgHom.toLinearMap =
      (SymmetricAlgebra.ι Γ(S, V.1) (E.val.obj (op V.1))).range ^ n := by
  rw [← MvPolynomial.homogeneousSubmodule_one_pow, Submodule.map_pow]
  congr 1
  rw [MvPolynomial.homogeneousSubmodule_one_eq_span_X, Submodule.map_span, ← Set.range_comp]
  have h := congrArg (Submodule.map (SymmetricAlgebra.ι Γ(S, V.1)
    (E.val.obj (op V.1)))) (orderedBasis b V.1).span_eq
  rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top] at h
  have heq : (fun i : ULift.{u} (Fin (r + 1)) ↦
      orderedPolynomial b V (MvPolynomial.X i)) =
        (fun i ↦ SymmetricAlgebra.ι Γ(S, V.1) (E.val.obj (op V.1))
          (orderedBasis b V.1 i)) :=
    funext (SymmetricAlgebra.equivMvPolynomial_symm_X (orderedBasis b V.1))
  change Submodule.span Γ(S, V.1) (Set.range
    (fun i ↦ orderedPolynomial b V (MvPolynomial.X i))) = _
  rw [heq]
  exact h

private def orderedGradedPolynomial {S : Scheme.{u}} {E : S.Modules} [E.IsQuasicoherent]
    {r : ℕ} (b : RelativeProjectiveSpace.freeModule S r ≅ E) (V : S.affineOpens) :
    MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (r + 1))) Γ(S, V.1) →+*ᵍ
      (SymmetricAlgebraSheaf.gradedAlgebraData E).grading V where
  toRingHom := (orderedPolynomial b V).toRingHom
  map_mem := by
    intro n p hp
    change orderedPolynomial b V p ∈
      (SymmetricAlgebra.ι Γ(S, V.1) (E.val.obj (op V.1))).range ^ n
    rw [← orderedPolynomial_degree b V n]
    exact ⟨p, hp, rfl⟩

private def projectivePolynomial (S : Scheme.{u}) (r : ℕ) (V : S.affineOpens) :
    MvPolynomial (ULift.{u} (Fin (r + 1))) Γ(S, V.1) ≃ₐ[Γ(S, V.1)]
      (RelativeProjectiveSpace.algebra S r).sections V :=
  (MvPolynomial.renameEquiv Γ(S, V.1) Equiv.ulift).trans
    { (RelativeProjectiveSpace.affinePolynomialEquiv S r V) with
      commutes' := (RelativeProjectiveSpace.existsUnique_affinePolynomialEquiv S r V).exists
        |>.choose_spec.1 }

private theorem projectivePolynomial_degree (S : Scheme.{u}) (r : ℕ) (V : S.affineOpens)
    (n : ℕ) (p : MvPolynomial (ULift.{u} (Fin (r + 1))) Γ(S, V.1)) :
    projectivePolynomial S r V p ∈ (RelativeProjectiveSpace.algebra S r).sectionGrade V n ↔
      p ∈ MvPolynomial.homogeneousSubmodule _ _ n := by
  change RelativeProjectiveSpace.affinePolynomialEquiv S r V (MvPolynomial.rename ULift.down p)
    ∈ (RelativeProjectiveSpace.algebra S r).sectionGrade V n ↔ _
  rw [RelativeProjectiveSpace.affinePolynomial_homogeneous]
  exact MvPolynomial.IsHomogeneous.rename_isHomogeneous_iff Equiv.ulift.injective

private def projectiveGradedPolynomial (S : Scheme.{u}) (r : ℕ) (V : S.affineOpens) :
    MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (r + 1))) Γ(S, V.1) →+*ᵍ
      (RelativeProjectiveSpace.algebra S r).sectionGrade V where
  toRingHom := (projectivePolynomial S r V).toRingHom
  map_mem := fun {n} {p} hp ↦ (projectivePolynomial_degree S r V n p).mpr hp

private theorem orderedPolynomial_restrict {S : Scheme.{u}} {E : S.Modules} {r : ℕ}
    (b : RelativeProjectiveSpace.freeModule S r ≅ E) {U V : S.affineOpens} (h : U ≤ V)
    (p : MvPolynomial (ULift.{u} (Fin (r + 1))) Γ(S, V.1)) :
    SymmetricAlgebraSheaf.restriction E (homOfLE (X := S.Opens) h).op
        (orderedPolynomial b V p) = orderedPolynomial b U
      (MvPolynomial.map (S.presheaf.map (homOfLE (X := S.Opens) h).op).hom p) := by
  have he : (SymmetricAlgebraSheaf.restriction E (homOfLE (X := S.Opens) h).op).comp
      (orderedPolynomial b V).toRingHom = (orderedPolynomial b U).toRingHom.comp
        (MvPolynomial.map (S.presheaf.map (homOfLE (X := S.Opens) h).op).hom) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, MvPolynomial.map_C]
      change SymmetricAlgebraSheaf.restriction E _
        (orderedPolynomial b V (algebraMap _ _ a)) = orderedPolynomial b U (algebraMap _ _ _)
      rw [AlgEquiv.commutes, AlgEquiv.commutes, SymmetricAlgebraSheaf.restriction_algebraMap]
    · intro i
      simp only [RingHom.comp_apply, MvPolynomial.map_X]
      change SymmetricAlgebraSheaf.restriction E _
        (orderedPolynomial b V (MvPolynomial.X i)) =
          orderedPolynomial b U (MvPolynomial.X i)
      rw [orderedPolynomial_X, SymmetricAlgebraSheaf.restriction_ι, orderedPolynomial_X]
      congr 1
      erw [unitSection_comp, unitSection_comp]
      exact unitSection_natural (SheafOfModules.ιFree i ≫ b.hom) h
  exact DFunLike.congr_fun he p

private theorem projectivePolynomial_restrict (S : Scheme.{u}) (r : ℕ)
    {U V : S.affineOpens} (h : U ≤ V)
    (p : MvPolynomial (ULift.{u} (Fin (r + 1))) Γ(S, V.1)) :
    (RelativeProjectiveSpace.algebra S r).restriction h (projectivePolynomial S r V p) =
      projectivePolynomial S r U
        (MvPolynomial.map (S.presheaf.map (homOfLE (X := S.Opens) h).op).hom p) := by
  change (RelativeProjectiveSpace.algebra S r).restriction h
    (RelativeProjectiveSpace.affinePolynomialEquiv S r V (MvPolynomial.rename ULift.down p)) =
      RelativeProjectiveSpace.affinePolynomialEquiv S r U
        (MvPolynomial.rename ULift.down (MvPolynomial.map _ p))
  rw [(RelativeProjectiveSpace.existsUnique_freeProjectiveBundleBaseChangeSpace S r).exists
    |>.choose_spec.2.2.2 V U h]
  congr 1
  exact MvPolynomial.map_rename _ _ _

private theorem orderedPolynomial_mem_iff {S : Scheme.{u}} {E : S.Modules} {r : ℕ}
    (b : RelativeProjectiveSpace.freeModule S r ≅ E) (V : S.affineOpens) (n : ℕ)
    (p : MvPolynomial (ULift.{u} (Fin (r + 1))) Γ(S, V.1)) :
    orderedPolynomial b V p ∈
        (SymmetricAlgebra.ι Γ(S, V.1) (E.val.obj (op V.1))).range ^ n ↔
      p ∈ MvPolynomial.homogeneousSubmodule _ _ n := by
  rw [← orderedPolynomial_degree b V n]
  constructor
  · rintro ⟨q, hq, he⟩
    exact (orderedPolynomial b V).injective he ▸ hq
  · intro hp
    exact ⟨p, hp, rfl⟩

private def orderedAlgebraEquiv {S : Scheme.{u}} {E : S.Modules} {r : ℕ}
    (b : RelativeProjectiveSpace.freeModule S r ≅ E) (V : S.affineOpens) :
    (RelativeProjectiveSpace.algebra S r).sections V ≃ₐ[Γ(S, V.1)]
      SymmetricAlgebra Γ(S, V.1) (E.val.obj (op V.1)) :=
  (projectivePolynomial S r V).symm.trans (orderedPolynomial b V)

private theorem grade_mem_iff_section_mem {S : Scheme.{u}} (A : RelativeProjAlgebra S)
    (V : S.affineOpens) (n : ℕ) (x : A.sections V) :
    x ∈ A.grade V n ↔ x ∈ A.sectionGrade V n := Iff.rfl

private theorem orderedAlgebraEquiv_mem_iff {S : Scheme.{u}} {E : S.Modules} {r : ℕ}
    (b : RelativeProjectiveSpace.freeModule S r ≅ E) (V : S.affineOpens) (n : ℕ)
    (x : (RelativeProjectiveSpace.algebra S r).sections V) :
    orderedAlgebraEquiv b V x ∈
        (SymmetricAlgebra.ι Γ(S, V.1) (E.val.obj (op V.1))).range ^ n ↔
      x ∈ (RelativeProjectiveSpace.algebra S r).grade V n := by
  rw [orderedAlgebraEquiv, AlgEquiv.trans_apply, orderedPolynomial_mem_iff]
  refine (projectivePolynomial_degree S r V n _).symm.trans ?_
  rw [AlgEquiv.apply_symm_apply]
  exact (grade_mem_iff_section_mem (RelativeProjectiveSpace.algebra S r) V n x).symm

private theorem orderedAlgebraEquiv_restrict {S : Scheme.{u}} {E : S.Modules} {r : ℕ}
    (b : RelativeProjectiveSpace.freeModule S r ≅ E) {U V : S.affineOpens} (h : U ≤ V)
    (x : (RelativeProjectiveSpace.algebra S r).sections V) :
    orderedAlgebraEquiv b U ((RelativeProjectiveSpace.algebra S r).restriction h x) =
      SymmetricAlgebraSheaf.restriction E (homOfLE (X := S.Opens) h).op
        (orderedAlgebraEquiv b V x) := by
  obtain ⟨p, rfl⟩ := (projectivePolynomial S r V).surjective x
  rw [projectivePolynomial_restrict, orderedAlgebraEquiv, orderedAlgebraEquiv,
    AlgEquiv.trans_apply, AlgEquiv.trans_apply, AlgEquiv.symm_apply_apply,
    AlgEquiv.symm_apply_apply, orderedPolynomial_restrict]

private def orderedGradedAlgebraIso {S : Scheme.{u}} {E : S.Modules} [E.IsQuasicoherent]
    {r : ℕ} (b : RelativeProjectiveSpace.freeModule S r ≅ E) :
    (RelativeProjectiveSpace.algebra S r).affineData ≅
      SymmetricAlgebraSheaf.gradedAlgebraData E where
  hom :=
    { app V :=
        { toRingHom := (orderedAlgebraEquiv b V).toRingHom
          map_mem := fun {n} {x} hx ↦ (orderedAlgebraEquiv_mem_iff b V n x).mpr hx }
      app_algebraMap V a := (orderedAlgebraEquiv b V).commutes a
      naturality h x := orderedAlgebraEquiv_restrict b h x }
  inv :=
    { app V :=
        { toRingHom := (orderedAlgebraEquiv b V).symm.toRingHom
          map_mem := by
            intro n x hx
            apply (orderedAlgebraEquiv_mem_iff b V n _).mp
            change orderedAlgebraEquiv b V ((orderedAlgebraEquiv b V).symm x) ∈
              (SymmetricAlgebra.ι Γ(S, V.1) (E.val.obj (op V.1))).range ^ n
            rw [AlgEquiv.apply_symm_apply]
            exact hx }
      app_algebraMap V a := (orderedAlgebraEquiv b V).symm.commutes a
      naturality := by
        intro U V h x
        apply (orderedAlgebraEquiv b U).injective
        change orderedAlgebraEquiv b U ((orderedAlgebraEquiv b U).symm
            (SymmetricAlgebraSheaf.restriction E (homOfLE (X := S.Opens) h).op x)) =
          orderedAlgebraEquiv b U ((RelativeProjectiveSpace.algebra S r).restriction h
            ((orderedAlgebraEquiv b V).symm x))
        rw [AlgEquiv.apply_symm_apply, orderedAlgebraEquiv_restrict,
          AlgEquiv.apply_symm_apply] }
  hom_inv_id := by
    ext V x
    exact (orderedAlgebraEquiv b V).symm_apply_apply x
  inv_hom_id := by
    ext V x
    exact (orderedAlgebraEquiv b V).apply_symm_apply x

private def gradedProjIso {R A B σ τ : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]
    (e : A ≃ₐ[R] B) (he : ∀ (n : ℕ) (a : A), e a ∈ ℬ n ↔ a ∈ 𝒜 n) :
    Proj ℬ ≅ Proj 𝒜 := by
  let f : 𝒜 →+*ᵍ ℬ := { e.toRingHom with map_mem := fun {n} {a} ha ↦ (he n a).mpr ha }
  let g : ℬ →+*ᵍ 𝒜 :=
    { e.symm.toRingHom with
      map_mem := fun {n} {b} hb ↦ (he n (e.symm b)).mp (by simpa using hb) }
  refine
    { hom := Proj.map f (GradedRingHom.irrelevant_le_map_of_surjective e.surjective)
      inv := Proj.map g (GradedRingHom.irrelevant_le_map_of_surjective e.symm.surjective)
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · rw [← Proj.map_comp]
    exact (Proj.map_congr (show f.comp g = .id ℬ from
      GradedRingHom.ext fun x ↦ e.apply_symm_apply x) _ (by simp)).trans Proj.map_id
  · rw [← Proj.map_comp]
    exact (Proj.map_congr (show g.comp f = .id 𝒜 from
      GradedRingHom.ext fun x ↦ e.symm_apply_apply x) _ (by simp)).trans Proj.map_id

private theorem gradedProjIso_hom {R A B σ τ : Type u}
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
    (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]
    (e : A ≃ₐ[R] B) (he : ∀ (n : ℕ) (a : A), e a ∈ ℬ n ↔ a ∈ 𝒜 n) :
    (gradedProjIso 𝒜 ℬ e he).hom = Proj.map
      ({ e.toRingHom with map_mem := fun {n} {a} ha ↦ (he n a).mpr ha } : 𝒜 →+*ᵍ ℬ)
      (GradedRingHom.irrelevant_le_map_of_surjective e.surjective) := rfl

private theorem projectiveGradedPolynomial_apply (S : Scheme.{u}) (r : ℕ)
    (V : S.affineOpens) (p : MvPolynomial (ULift.{u} (Fin (r + 1))) Γ(S, V.1)) :
    projectiveGradedPolynomial S r V p = RelativeProjectiveSpace.affinePolynomialEquiv S r V
      (MvPolynomial.rename (fun i : ULift.{u} (Fin (r + 1)) ↦ i.down) p) := rfl

private theorem pullback_unit_morphism_of_section {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M : Y.Modules} {N : X.Modules} (a : Scheme.Modules.unit Y ⟶ M)
    (t : (Scheme.Modules.tensorPullback f).obj M ≅ N)
    (a' : Scheme.Modules.unit X ⟶ N)
    (h : t.hom.app (f ⁻¹ᵁ ⊤)
      (Scheme.Modules.tensorPullbackSection f M ⊤ (a.app ⊤ (1 : Γ(Y, ⊤)))) =
        a'.app (f ⁻¹ᵁ ⊤) (1 : Γ(X, f ⁻¹ᵁ ⊤))) :
    (Scheme.Modules.tensorPullback f).map a ≫ t.hom =
      ((Scheme.Modules.boundaryPullbackComparison f).app (Scheme.Modules.unit Y) ≪≫
        Scheme.Modules.pullbackObjUnitIso f).hom ≫ a' := by
  let adj := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f)
  have hunit : adj.homEquiv _ _
      ((Scheme.Modules.boundaryPullbackComparison f).app (Scheme.Modules.unit Y) ≪≫
        Scheme.Modules.pullbackObjUnitIso f).hom =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom := by
    unfold Scheme.Modules.boundaryPullbackComparison
    dsimp only [Iso.trans_hom, Iso.app_hom]
    rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_leftAdjointUniq_hom_app]
    exact SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
      f.toRingCatSheafHom
  apply (adj.homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right, hunit]
  apply Scheme.Modules.unit_hom_ext
  rw [Adjunction.homEquiv_unit]
  have hn := (Classical.choose_spec (Scheme.Modules.exists_tensorPullbackAdjunction f))
    M (op ⊤) (a.app ⊤ (1 : Γ(Y, ⊤)))
  change (adj.unit.app M).app ⊤ (a.app ⊤ (1 : Γ(Y, ⊤))) =
    Scheme.Modules.tensorPullbackSection f M ⊤ (a.app ⊤ (1 : Γ(Y, ⊤))) at hn
  change t.hom.app (f ⁻¹ᵁ ⊤) ((adj.unit.app M).app ⊤ (a.app ⊤ (1 : Γ(Y, ⊤)))) =
    a'.app (f ⁻¹ᵁ ⊤) (f.app ⊤ (1 : Γ(Y, ⊤)))
  rw [hn]
  have hf : f.app ⊤ (1 : Γ(Y, ⊤)) = (1 : Γ(X, f ⁻¹ᵁ ⊤)) := (f.app ⊤).hom.map_one
  rw [hf]
  exact h

private def coefficientZero {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] : R →+* 𝒜 0 :=
  (GradedRing.projZeroRingHom' 𝒜).comp (algebraMap R A)

private theorem coefficientZero_val {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedAlgebra 𝒜] (r : R) :
    (coefficientZero 𝒜 r : A) = algebraMap R A r := by
  change (DirectSum.decompose 𝒜 (algebraMap R A r) 0 : A) = _
  apply DirectSum.decompose_of_mem_same
  rw [Algebra.algebraMap_eq_smul_one]
  exact (𝒜 0).smul_mem r (SetLike.one_mem_graded 𝒜)

attribute [local irreducible] Proj.twist Proj.unitToTwist Proj.map orderedPolynomial
  RelativeProjectiveSpace.algebra

private theorem orderedPolynomial_twist {S : Scheme.{u}} {E : S.Modules} [E.IsQuasicoherent]
    {r : ℕ} (b : RelativeProjectiveSpace.freeModule S r ≅ E) (V : S.affineOpens)
    (hβ : HomogeneousIdeal.irrelevant ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading V) ≤
      (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule
        (ULift.{u} (Fin (r + 1))) Γ(S, V.1))).map (orderedGradedPolynomial b V)) :
    ∃ t : (Scheme.Modules.tensorPullback (Proj.map (orderedGradedPolynomial b V) hβ)).obj
        (Proj.twist (MvPolynomial.homogeneousSubmodule
          (ULift.{u} (Fin (r + 1))) Γ(S, V.1)) 1) ≅
          Proj.twist ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading V) 1,
      ∀ (s : MvPolynomial (ULift.{u} (Fin (r + 1))) Γ(S, V.1))
        (hs : s ∈ MvPolynomial.homogeneousSubmodule
          (ULift.{u} (Fin (r + 1))) Γ(S, V.1) 1),
        (Scheme.Modules.tensorPullback (Proj.map (orderedGradedPolynomial b V) hβ)).map
          (Proj.unitToTwist hs) ≫ t.hom =
        ((Scheme.Modules.boundaryPullbackComparison
            (Proj.map (orderedGradedPolynomial b V) hβ)).app (Scheme.Modules.unit _) ≪≫
          Scheme.Modules.pullbackObjUnitIso (Proj.map (orderedGradedPolynomial b V) hβ)).hom ≫
            Proj.unitToTwist ((orderedGradedPolynomial b V).map_mem hs) := by
  let P := MvPolynomial (ULift.{u} (Fin (r + 1))) Γ(S, V.1)
  let 𝒜 := MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (r + 1))) Γ(S, V.1)
  let ℬ := (SymmetricAlgebraSheaf.gradedAlgebraData E).grading V
  let β := orderedGradedPolynomial b V
  let e : TensorProduct Γ(S, V.1) Γ(S, V.1) P ≃ₐ[Γ(S, V.1)]
      (SymmetricAlgebraSheaf.gradedAlgebraData E).obj V :=
    (Algebra.TensorProduct.lid Γ(S, V.1) P).trans (orderedPolynomial b V)
  have hgraded (n : ℕ) : ℬ n = Submodule.span Γ(S, V.1) (β '' (𝒜 n : Set P)) := by
    change (SymmetricAlgebra.ι Γ(S, V.1) (E.val.obj (op V.1))).range ^ n =
      Submodule.span Γ(S, V.1) ((orderedPolynomial b V).toAlgHom.toLinearMap '' (𝒜 n : Set P))
    rw [← Submodule.map_span, Submodule.span_eq]
    exact (orderedPolynomial_degree b V n).symm
  obtain ⟨θ, _, _, _, _, hθ, _, _⟩ := Proj.scalarExtension_twist_comparison 𝒜 ℬ
    (coefficientZero 𝒜) (coefficientZero ℬ) (coefficientZero_val 𝒜) (coefficientZero_val ℬ)
    e β (by
      intro a
      change orderedPolynomial b V
        ((Algebra.TensorProduct.lid Γ(S, V.1) P) (TensorProduct.tmul _ (1 : Γ(S, V.1)) a)) =
          orderedPolynomial b V a
      exact congrArg (orderedPolynomial b V)
        ((Algebra.TensorProduct.lid_tmul (1 : Γ(S, V.1)) a).trans (one_smul _ _)))
    hgraded (Proj.map β hβ)
    (fun _ f _ _ ↦ Proj.map_preimage_basicOpen β hβ f)
    (fun _ f hf hn ↦ Proj.awayι_comp_map β hβ hn f hf)
  refine ⟨θ 1, fun s hs ↦ pullback_unit_morphism_of_section _ _ _ _ ?_⟩
  have ht := hθ 1 s hs
  simp only [Proj.scalarExtensionTwistSection, Scheme.Hom.preimage_top,
    homOfLE_refl, op_id] at ht
  exact ht.trans (modulePresheaf_map_id_apply _ _ _)

private def realizationComparison {S : Scheme.{u}} {A : RelativeProjAlgebra S}
    {B : S.GradedAlgebraData} (e : A.affineData ≅ B) : B.relProj ≅ A.realization.proj :=
  Scheme.GradedAlgebraData.relProjIsoOfIso e

private theorem realizationComparison_over {S : Scheme.{u}} {A : RelativeProjAlgebra S}
    {B : S.GradedAlgebraData} (e : A.affineData ≅ B) :
    (realizationComparison e).hom ≫ A.realization.π = B.relProjHom :=
  Scheme.GradedAlgebraData.relProjIsoOfIso_hom_relProjHom e

private theorem relProjIso_chart {S : Scheme.{u}} (A : RelativeProjAlgebra S)
    {B : S.GradedAlgebraData} (e : A.affineData ≅ B) (V : S.affineOpens)
    (h : HomogeneousIdeal.irrelevant (B.grading V) ≤
      (HomogeneousIdeal.irrelevant (A.affineData.grading V)).map (e.hom.app V)) :
    B.relProjι V ≫ (realizationComparison e).hom =
      Proj.map (e.hom.app V) h ≫ A.affineData.relProjι V := by
  change B.relProjι V ≫ Scheme.GradedAlgebraData.relProjMap e.hom _ = _
  exact Scheme.GradedAlgebraData.relProjι_relProjMap _ _ _

attribute [local irreducible] realizationComparison

private theorem realization_restriction_inv_ι {S : Scheme.{u}}
    (A : RelativeProjAlgebra S) (V : S.affineOpens) :
    (A.realization.restrictionIso V).inv ≫ (A.realization.π ⁻¹ᵁ V.1).ι =
      (A.gradeIso V).hom ≫ A.affineData.relProjι V := by
  change ((A.gradeIso V).hom ≫ (A.affineRestrictionIso V).hom) ≫ _ = _
  erw [Category.assoc, A.affineRestrictionIso_hom_ι]

private theorem realizationComparison_chart {S : Scheme.{u}} (A : RelativeProjAlgebra S)
    {B : S.GradedAlgebraData} (e : A.affineData ≅ B) (V : S.affineOpens)
    {P σ : Type u} [CommRing P] [Algebra Γ(S, V.1) P]
    [SetLike σ P] [AddSubgroupClass σ P]
    (D : ℕ → σ) [GradedRing D]
    (eP : P ≃ₐ[Γ(S, V.1)] B.obj V)
    (heP : ∀ (n : ℕ) (p : P), eP p ∈ B.grading V n ↔ p ∈ D n)
    (eQ : P ≃ₐ[Γ(S, V.1)] A.sections V)
    (heQ : ∀ (n : ℕ) (p : P), eQ p ∈ A.sectionGrade V n ↔ p ∈ D n)
    (he : ∀ x : A.sections V, e.hom.app V x = eP (eQ.symm x)) :
    B.relProjι V ≫ (realizationComparison e).hom =
      (gradedProjIso D (B.grading V) eP heP).hom ≫
        (gradedProjIso D (A.sectionGrade V) eQ heQ).inv ≫
          (A.realization.restrictionIso V).inv ≫ (A.realization.π ⁻¹ᵁ V.1).ι := by
  have hsurj : Function.Surjective (e.hom.app V) := by
    intro y
    obtain ⟨p, rfl⟩ := eP.surjective y
    refine ⟨eQ p, ?_⟩
    rw [he, eQ.symm_apply_apply]
  have h := GradedRingHom.irrelevant_le_map_of_surjective hsurj
  rw [relProjIso_chart A e V h, realization_restriction_inv_ι A V]
  simp only [← Category.assoc]
  congr 1
  change Proj.map (e.hom.app V) _ =
    (Proj.map _ _ ≫ Proj.map _ _) ≫ Proj.map _ _
  rw [← Proj.map_comp, ← Proj.map_comp]
  apply Proj.map_congr
  ext x
  exact he x

attribute [local irreducible] gradedProjIso projectivePolynomial

/-- An ordered free presentation `b` identifies the canonical symmetric relative Proj with
relative projective space: the relative-Proj realization of the graded algebra isomorphism
induced by `b` and the standard ordered basis. -/
@[no_expose] def orderedRelativeComparison {S : Scheme.{u}} {E : S.Modules}
    [E.IsQuasicoherent] {r : ℕ} (b : RelativeProjectiveSpace.freeModule S r ≅ E) :
    (SymmetricAlgebraSheaf.gradedAlgebraData E).relProj ≅
      RelativeProjectiveSpace.scheme S r :=
  realizationComparison (orderedGradedAlgebraIso b)

/-- The ordered relative comparison lies over the base. -/
theorem orderedRelativeComparison_hom_π {S : Scheme.{u}} {E : S.Modules}
    [E.IsQuasicoherent] {r : ℕ} (b : RelativeProjectiveSpace.freeModule S r ≅ E) :
    (orderedRelativeComparison b).hom ≫ RelativeProjectiveSpace.π S r =
      (SymmetricAlgebraSheaf.gradedAlgebraData E).relProjHom :=
  realizationComparison_over (orderedGradedAlgebraIso b)

/-- On every affine chart, the ordered relative comparison `orderedRelativeComparison b` is
compatible with the affine polynomial and degree-one twist models.
This assertion does not involve a global tautological quotient or standard projective space.

Source: Stacks Project, Constructions, Tags 01OE (lemma-projective-space-bundle),
01OB (definition-projective-bundle), and 01MS (lemma-when-invertible).
(blueprint: lem-trf-symmetric-proj-ordered-relative-comparison).

Proof: On an affine V, apply the symmetric-algebra universal property to the section
isomorphism induced by b and the standard ordered basis of the free sheaf. The resulting
polynomial isomorphism beta fixes coefficients and sends X_i to iota(b(e_i)). Its inverse
sends a vector to its coordinate linear polynomial. Products of n generators span the
nth symmetric degree, so both maps preserve degree. Naturality of b and of the basis
inclusions shows that these isomorphisms commute with restriction on scalars and vectors.
The defining affinePolynomialEquiv for relative projective space gives gamma, after
reindexing the variables by ULift.down. Compose beta with gamma inverse to identify the
two affine graded algebras, and glue by relative-Proj functoriality. This constructs eRel
over S. On every affine, Proj functoriality gives eC and eR. The realization's
restriction identity and composition of Proj maps give the displayed chart equation.
Surjectivity of beta and gamma supplies their irrelevant-ideal conditions. Apply the
scalar-extension twist comparison with the identity coefficient extension and the
multiplication isomorphism R tensor_R P = P followed by beta. The established equality
of homogeneous pieces supplies its grading hypothesis, and the Proj map supplies its
standard-open formulas. Its degree-one comparison sends the pullback of s/1 to beta(s)/1.
Transpose morphisms by the tensor-pullback adjunction: left-adjoint uniqueness identifies
the boundary unit comparison with the structure-sheaf map. Maps from the structure sheaf
are determined by their value at 1, so the homogeneous-section formula gives exactly the
unitToTwist morphism equality. All formulas hold for r=0, zero coefficient rings and empty
affine charts. No variable is cancelled in the original ring. -/
theorem orderedRelativeComparison_affineFreeComparison {S : Scheme.{u}} {E : S.Modules}
    [E.IsQuasicoherent] {r : ℕ} (b : RelativeProjectiveSpace.freeModule S r ≅ E)
    (V : S.affineOpens) :
    ProjectiveBundleQuotientGeometry.AffineFreeComparison r b (orderedRelativeComparison b) V :=
  let e := orderedGradedAlgebraIso b
  let β := orderedGradedPolynomial b V
  let γ := projectiveGradedPolynomial S r V
  let hβ := GradedRingHom.irrelevant_le_map_of_surjective (f := β)
    (orderedPolynomial b V).surjective
  let hγ := GradedRingHom.irrelevant_le_map_of_surjective (f := γ)
    (projectivePolynomial S r V).surjective
  let eC := gradedProjIso _ ((SymmetricAlgebraSheaf.gradedAlgebraData E).grading V)
    (orderedPolynomial b V) (orderedPolynomial_mem_iff b V)
  let eR := gradedProjIso _ ((RelativeProjectiveSpace.algebra S r).sectionGrade V)
    (projectivePolynomial S r V) (projectivePolynomial_degree S r V)
  have heC : eC.hom = Proj.map β hβ :=
    (gradedProjIso_hom _ _ _ _).trans (Proj.map_congr (by ext p; rfl) _ _)
  have heR : eR.hom = Proj.map γ hγ :=
    (gradedProjIso_hom _ _ _ _).trans (Proj.map_congr (by ext p; rfl) _ _)
  affineFreeComparison_mk b (orderedRelativeComparison b) V β (orderedPolynomial b V).bijective
    (orderedPolynomial b V).commutes (orderedPolynomial_X b V) hβ eC heC
    (by rw [heC]; exact orderedPolynomial_twist b V hβ) γ hγ eR
    (projectiveGradedPolynomial_apply S r V) heR
    (realizationComparison_chart (RelativeProjectiveSpace.algebra S r) e V _
      (orderedPolynomial b V) (orderedPolynomial_mem_iff b V)
      (projectivePolynomial S r V) (projectivePolynomial_degree S r V)
      (fun _ ↦ rfl))

end

end AlgebraicGeometry.SymmetricProjTautologicalCharts
