/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SymmetricAlgebraSheaf.CanonicalSymmetricGradedAlgebra
public import WeilConjectures.AlgebraicGeometry.Tensor.TensorPullbackSectionAdjunction
public import WeilConjectures.AlgebraicGeometry.RelativeProj.BaseChange
import WeilConjectures.AlgebraicGeometry.ModulePullbackAffineSections
import WeilConjectures.AlgebraicGeometry.SymmetricAlgebraSheaf.SymmetricAlgebraAffineSectionComparison
import WeilConjectures.RingTheory.SymmetricAlgebraBaseChange
import Mathlib.RingTheory.GradedAlgebra.TensorProduct

/-! # Normalized pullback data for symmetric graded algebras

Source: Stacks Project, Modules, lemma-pullback-tensor-algebra;
Constructions, Tag 01OB; Algebra, lemma-tensor-algebra-localization (general base change).
(blueprint: lem-trf-symmetric-algebra-normalized-pullback-data).
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Opposite
open scoped AlgebraicGeometry TensorProduct

namespace AlgebraicGeometry.SymmetricAlgebraSheaf

-- Match the finite-limit instance used by the normalized quotient definitions.
attribute [local instance 2000] CategoryTheory.Abelian.hasFiniteLimits

attribute [local irreducible] Scheme.Modules.tensorPullback Scheme.Modules.tensorPullbackObj
  Scheme.Modules.tensorPullbackSectionAdjunction

private noncomputable def unitSection {X S : Scheme.{u}} (g : X ⟶ S) (E : S.Modules)
    {U : S.affineOpens} {W : X.affineOpens} (h : W.1 ≤ g ⁻¹ᵁ U.1)
    (m : E.val.obj (op U.1)) : ((Scheme.Modules.tensorPullback g).obj E).val.obj (op W.1) :=
  ((Scheme.Modules.tensorPullback g).obj E).presheaf.map (homOfLE h).op
    (((Scheme.Modules.tensorPullbackSectionAdjunction g).unit.app E).app U.1 m)

private theorem unitSection_eq {X S : Scheme.{u}} (g : X ⟶ S) (E : S.Modules)
    {U : S.affineOpens} {W : X.affineOpens} (h : W.1 ≤ g ⁻¹ᵁ U.1)
    (m : E.val.obj (op U.1)) : unitSection g E h m =
      ((Scheme.Modules.tensorPullback g).obj E).presheaf.map (homOfLE h).op
        (Scheme.Modules.tensorPullbackSection g E U.1 m) := by
  unfold unitSection
  congr 1
  simpa only [Scheme.Modules.tensorPullbackSectionAdjunction] using
    (Classical.choose_spec
      (Scheme.Modules.existsUnique_tensorPullbackSectionAdjunction g)).1 E U.1 m

private theorem unitSection_add {X S : Scheme.{u}} (g : X ⟶ S) (E : S.Modules)
    {U : S.affineOpens} {W : X.affineOpens} (h : W.1 ≤ g ⁻¹ᵁ U.1)
    (m n : E.val.obj (op U.1)) :
    unitSection g E h (m + n) = unitSection g E h m + unitSection g E h n := by
  simp only [unitSection, map_add]

private theorem unitSection_smul {X S : Scheme.{u}} (g : X ⟶ S) (E : S.Modules)
    {U : S.affineOpens} {W : X.affineOpens} (h : W.1 ≤ g ⁻¹ᵁ U.1)
    (r : Γ(S, U.1)) (m : E.val.obj (op U.1)) :
    unitSection g E h (r • m) = g.appLE U.1 W.1 h r • unitSection g E h m := by
  unfold unitSection
  rw [Scheme.Modules.Hom.app_smul]
  change ((Scheme.Modules.tensorPullback g).obj E).val.map (homOfLE h).op
      ((g.app U.1).hom r • _) = _
  rw [PresheafOfModules.map_smul]
  rfl

private noncomputable def pullbackRingMap {X S : Scheme.{u}} (g : X ⟶ S) (E : S.Modules)
    {U : S.affineOpens} {W : X.affineOpens} (h : W.1 ≤ g ⁻¹ᵁ U.1) :
    sections E (op U.1) →+* sections ((Scheme.Modules.tensorPullback g).obj E) (op W.1) := by
  let R := Γ(S, U.1)
  let B := sections ((Scheme.Modules.tensorPullback g).obj E) (op W.1)
  let : Algebra R B := ((algebraMap Γ(X, W.1) B).comp (g.appLE U.1 W.1 h).hom).toAlgebra
  let f : E.val.obj (op U.1) →ₗ[R] B :=
    { toFun := fun m ↦ SymmetricAlgebra.ι Γ(X, W.1) _ (unitSection g E h m)
      map_add' := by intro m n; rw [unitSection_add, map_add]
      map_smul' := by
        intro r m
        rw [unitSection_smul, map_smul]
        rfl }
  exact (SymmetricAlgebra.lift f).toRingHom

private theorem pullbackRingMap_ι {X S : Scheme.{u}} (g : X ⟶ S) (E : S.Modules)
    {U : S.affineOpens} {W : X.affineOpens} (h : W.1 ≤ g ⁻¹ᵁ U.1)
    (m : E.val.obj (op U.1)) :
    pullbackRingMap g E h (SymmetricAlgebra.ι Γ(S, U.1) _ m) =
      SymmetricAlgebra.ι Γ(X, W.1) _ (unitSection g E h m) := by
  let B := sections ((Scheme.Modules.tensorPullback g).obj E) (op W.1)
  let : Algebra Γ(S, U.1) B :=
    ((algebraMap Γ(X, W.1) B).comp (g.appLE U.1 W.1 h).hom).toAlgebra
  unfold pullbackRingMap
  exact SymmetricAlgebra.lift_ι_apply _ _

private theorem pullbackRingMap_algebraMap {X S : Scheme.{u}} (g : X ⟶ S) (E : S.Modules)
    {U : S.affineOpens} {W : X.affineOpens} (h : W.1 ≤ g ⁻¹ᵁ U.1)
    (r : Γ(S, U.1)) :
    pullbackRingMap g E h (algebraMap Γ(S, U.1) _ r) =
      algebraMap Γ(X, W.1) _ (g.appLE U.1 W.1 h r) := by
  let B := sections ((Scheme.Modules.tensorPullback g).obj E) (op W.1)
  let : Algebra Γ(S, U.1) B :=
    ((algebraMap Γ(X, W.1) B).comp (g.appLE U.1 W.1 h).hom).toAlgebra
  unfold pullbackRingMap
  exact AlgHom.commutes _ _

private theorem pullbackRingMap_mem {X S : Scheme.{u}} (g : X ⟶ S) (E : S.Modules)
    {U : S.affineOpens} {W : X.affineOpens} (h : W.1 ≤ g ⁻¹ᵁ U.1) (n : ℕ)
    (a : sections E (op U.1))
    (ha : a ∈ (SymmetricAlgebra.ι Γ(S, U.1) (E.val.obj (op U.1))).range ^ n) :
    pullbackRingMap g E h a ∈
      (SymmetricAlgebra.ι Γ(X, W.1)
        (((Scheme.Modules.tensorPullback g).obj E).val.obj (op W.1))).range ^ n := by
  induction ha using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    rw [pullbackRingMap_algebraMap]
    exact Submodule.algebraMap_mem _
  | add x y i hx hy ihx ihy =>
    rw [map_add]
    exact add_mem ihx ihy
  | mem_mul m hm i x hx ih =>
    obtain ⟨m, rfl⟩ := hm
    rw [map_mul, pullbackRingMap_ι, pow_succ']
    exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ _) ih

private noncomputable def pullbackGradedMap {X S : Scheme.{u}} (g : X ⟶ S)
    (E : S.Modules) [E.IsQuasicoherent]
    [((Scheme.Modules.tensorPullback g).obj E).IsQuasicoherent]
    {U : S.affineOpens} {W : X.affineOpens} (h : W.1 ≤ g ⁻¹ᵁ U.1) :
    (gradedAlgebraData E).grading U →+*ᵍ
      (gradedAlgebraData ((Scheme.Modules.tensorPullback g).obj E)).grading W where
  toRingHom := pullbackRingMap g E h
  map_mem := fun {n} {a} ha ↦ pullbackRingMap_mem g E h n a ha

private theorem exists_unitSectionEquiv {X S : Scheme.{u}} (g : X ⟶ S)
    (E : S.Modules) [E.IsQuasicoherent]
    {U : S.affineOpens} {W : X.affineOpens} (h : W.1 ≤ g ⁻¹ᵁ U.1) :
    letI : Algebra Γ(S, U.1) Γ(X, W.1) := (g.appLE U.1 W.1 h).hom.toAlgebra
    ∃ e : Γ(X, W.1) ⊗[Γ(S, U.1)] Γ(E, U.1) ≃ₗ[Γ(X, W.1)]
        ((Scheme.Modules.tensorPullback g).obj E).val.obj (op W.1),
      ∀ (r : Γ(X, W.1)) (m : Γ(E, U.1)),
        e (r ⊗ₜ[Γ(S, U.1)] m) = r • unitSection g E h m := by
  classical
  let : Algebra Γ(S, U.1) Γ(X, W.1) := (g.appLE U.1 W.1 h).hom.toAlgebra
  let : ∀ F : S.Modules,
      Module Γ(S, U.1) Γ((Scheme.Modules.tensorPullback g).obj F, W.1) :=
    fun F ↦ Module.compHom _ (g.appLE U.1 W.1 h).hom
  obtain ⟨c, hc, hs, ht, _⟩ := Scheme.Modules.exists_tensorPullback_affine_sections g U W h
  let d : Γ(X, W.1) ⊗[Γ(S, U.1)] Γ(E, U.1) →ₗ[Γ(X, W.1)]
      ((Scheme.Modules.tensorPullback g).obj E).val.obj (op W.1) :=
    { toFun := fun t ↦ c E inferInstance
        (TensorProduct.comm Γ(S, U.1) Γ(X, W.1) (Γ(E, U.1)) t)
      map_add' := by intro x y; simp
      map_smul' := by
        intro r t
        simpa only [TensorProduct.comm_symm, TensorProduct.comm_comm, RingHom.id_apply]
          using hs E inferInstance r
            (TensorProduct.comm Γ(S, U.1) Γ(X, W.1) (Γ(E, U.1)) t) }
  refine ⟨LinearEquiv.ofBijective d ((hc E inferInstance).comp
    (TensorProduct.comm Γ(S, U.1) Γ(X, W.1) (Γ(E, U.1))).bijective), ?_⟩
  intro r m
  change c E inferInstance (m ⊗ₜ[Γ(S, U.1)] r) = _
  rw [ht, unitSection_eq]
  congr 2
  exact Classical.choose_spec (Scheme.Modules.exists_tensorPullbackAdjunction g) E (op U.1) m

private theorem graded_bijective_degree
    {R T A B : Type u} [CommRing R] [CommRing T] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra T B]
    {D : ℕ → Submodule R A} {D' : ℕ → Submodule T B}
    [GradedAlgebra D] [GradedAlgebra D']
    (f : D →+*ᵍ D') (hf : Function.Bijective f) (n : ℕ) :
    Function.Bijective (f.gradedAddHom n) := by
  classical
  constructor
  · intro a b hab
    exact Subtype.ext (hf.injective (congrArg Subtype.val hab))
  · intro b
    obtain ⟨a, ha⟩ := hf.surjective b
    refine ⟨DirectSum.decompose D a n, ?_⟩
    apply Subtype.ext
    change f (DirectSum.decompose D a n) = (b : B)
    rw [f.map_directSumDecompose, ha, DirectSum.decompose_of_mem_same D' b.property]

private theorem pullbackGradedMap_isBaseChange {X S : Scheme.{u}} (g : X ⟶ S)
    (E : S.Modules) [E.IsQuasicoherent]
    [((Scheme.Modules.tensorPullback g).obj E).IsQuasicoherent]
    {U : S.affineOpens} {W : X.affineOpens} (h : W.1 ≤ g ⁻¹ᵁ U.1) :
    (pullbackGradedMap g E h).IsGradedBaseChangeAlong (g.appLE U.1 W.1 h).hom := by
  classical
  let R := Γ(S, U.1)
  let T := Γ(X, W.1)
  let M := Γ(E, U.1)
  let N := Γ((Scheme.Modules.tensorPullback g).obj E, W.1)
  let A := (gradedAlgebraData E).obj U
  let B := (gradedAlgebraData ((Scheme.Modules.tensorPullback g).obj E)).obj W
  let D : ℕ → Submodule R A := (gradedAlgebraData E).grading U
  let D' : ℕ → Submodule T B :=
    (gradedAlgebraData ((Scheme.Modules.tensorPullback g).obj E)).grading W
  let : Algebra R T := (g.appLE U.1 W.1 h).hom.toAlgebra
  let : Algebra R B := ((algebraMap T B).comp (g.appLE U.1 W.1 h).hom).toAlgebra
  have : IsScalarTower R T B := .of_algebraMap_eq' rfl
  let f : D →ₐᵍ[R] (fun n ↦ (D' n).restrictScalars R) :=
    { toRingHom := pullbackRingMap g E h
      commutes' := pullbackRingMap_algebraMap g E h
      map_mem := fun {n} {a} ha ↦ pullbackRingMap_mem g E h n a ha }
  let Φ := GradedAlgHom.liftEquiv D D' f
  obtain ⟨e, he⟩ := exists_unitSectionEquiv g E h
  let β : A →ₐ[R] SymmetricAlgebra T (T ⊗[R] M) :=
    SymmetricAlgebra.lift
      (((SymmetricAlgebra.ι T _).restrictScalars R).comp (TensorProduct.mk R T M 1))
  have hβ (m : M) : β (SymmetricAlgebra.ι R M m) =
      SymmetricAlgebra.ι T _ (1 ⊗ₜ[R] m) := SymmetricAlgebra.lift_ι_apply _ _
  let k := AlgEquiv.ofBijective (AlgHom.liftEquiv R T A _ β)
    (SymmetricAlgebra.baseChange_bijective β hβ)
  let q : SymmetricAlgebra T (T ⊗[R] M) ≃ₐ[T] B := symmetricCongr e
  have hq (a : A) : q (β a) = pullbackRingMap g E h a := by
    induction a using SymmetricAlgebra.induction with
    | algebraMap r =>
      calc
        q (β (algebraMap R A r)) = q (algebraMap R _ r) :=
          congrArg q (β.commutes r)
        _ = algebraMap T B (g.appLE U.1 W.1 h r) := q.commutes _
        _ = pullbackRingMap g E h (algebraMap R A r) :=
          (pullbackRingMap_algebraMap g E h r).symm
    | ι m =>
      calc
        q (β (SymmetricAlgebra.ι R M m)) =
            q (SymmetricAlgebra.ι T _ (1 ⊗ₜ[R] m)) := congrArg q (hβ m)
        _ = SymmetricAlgebra.ι T N (e (1 ⊗ₜ[R] m)) := symmetricCongr_ι e _
        _ = SymmetricAlgebra.ι T N (unitSection g E h m) :=
          congrArg (SymmetricAlgebra.ι T N) ((he 1 m).trans (one_smul T _))
        _ = pullbackRingMap g E h (SymmetricAlgebra.ι R M m) :=
          (pullbackRingMap_ι g E h m).symm
    | mul a b ha hb => simp_all only [map_mul]
    | add a b ha hb => simp_all only [map_add]
  have hΦ : Function.Bijective Φ := by
    have heq : (fun t ↦ (k.trans q) t) = Φ := by
      funext t
      induction t using TensorProduct.inductionOn with
      | tmul r a =>
        change q (AlgHom.liftEquiv R T A _ β (r ⊗ₜ[R] a)) = Φ (r ⊗ₜ[R] a)
        rw [AlgHom.liftEquiv_tmul, map_smul, hq, GradedAlgHom.liftEquiv_tmul]
        rfl
      | add t t' ht ht' => simp_all only [map_add]
    rw [← heq]
    exact (k.trans q).bijective
  refine ⟨pullbackRingMap_algebraMap g E h, fun n ↦ ?_⟩
  let l : (D n).baseChange T →ₗ[T] D' n :=
    (Φ.toAlgHom.toLinearMap.domRestrict ((D n).baseChange T)).codRestrict
      (D' n) (fun a ↦ Φ.map_mem a.property)
  have hl : Function.Bijective l := graded_bijective_degree Φ.toGradedRingHom hΦ n
  let e₁ := LinearEquiv.ofBijective ((D n).toBaseChange T)
    (DirectSum.toBaseChange_bijective D n)
  let e₂ := LinearEquiv.ofBijective l hl
  apply IsBaseChange.of_equiv (e₁.trans e₂)
  intro a
  apply Subtype.ext
  change Φ (1 ⊗ₜ[R] (a : A)) = pullbackRingMap g E h (a : A)
  rw [GradedAlgHom.liftEquiv_tmul, one_smul]
  rfl

private theorem unitSection_res_map {X S : Scheme.{u}} (g : X ⟶ S) (E : S.Modules)
    {U : S.affineOpens} {W W' : X.affineOpens} (h' : W' ≤ W)
    (h : W.1 ≤ g ⁻¹ᵁ U.1) (m : E.val.obj (op U.1)) :
    ((Scheme.Modules.tensorPullback g).obj E).val.map (homOfLE (X := X.Opens) h').op
      (unitSection g E h m) =
        unitSection g E (W := W') ((show W'.1 ≤ W.1 from h').trans h) m := by
  exact (((Scheme.Modules.tensorPullback g).obj E).val.map_comp_apply
    (homOfLE h).op (homOfLE (X := X.Opens) h').op _).symm

private theorem unitSection_map_res {X S : Scheme.{u}} (g : X ⟶ S) (E : S.Modules)
    {U V : S.affineOpens} {W : X.affineOpens} (h : W.1 ≤ g ⁻¹ᵁ U.1)
    (hUV : U ≤ V) (m : E.val.obj (op V.1)) :
    unitSection g E h (E.val.map (homOfLE (X := S.Opens) hUV).op m) =
      unitSection g E (U := V) (h.trans (g.preimage_mono hUV)) m := by
  unfold unitSection
  have hn := PresheafOfModules.naturality_apply
    ((Scheme.Modules.tensorPullbackSectionAdjunction g).unit.app E).val
    (homOfLE (X := S.Opens) hUV).op m
  change ((Scheme.Modules.tensorPullbackSectionAdjunction g).unit.app E).app U.1
      (E.val.map (homOfLE (X := S.Opens) hUV).op m) =
    ((Scheme.Modules.tensorPullback g).obj E).val.map
      (homOfLE (g.preimage_mono hUV)).op
        (((Scheme.Modules.tensorPullbackSectionAdjunction g).unit.app E).app V.1 m) at hn
  rw [hn]
  exact (((Scheme.Modules.tensorPullback g).obj E).val.map_comp_apply
    (homOfLE (g.preimage_mono hUV)).op (homOfLE h).op _).symm

/-- Canonical coefficientwise pullback data for the symmetric graded algebra, with its
specified degree-one generator formula.

Source: Stacks Project, Modules, lemma-pullback-tensor-algebra;
Constructions, Tag 01OB; Algebra, lemma-tensor-algebra-localization (general base change).
(blueprint: lem-trf-symmetric-algebra-normalized-pullback-data).

Proof: send a scalar by the scheme structure map and send iota(m) to the inclusion
of the restricted section 1 tensor m. The symmetric universal property constructs
this ring map. Products of n degree-one generators show that it preserves degree n.
Affine pullback sections identify the target module with scalar extension of the
source module. Symmetric algebra base change therefore makes the corresponding
scalar extension map bijective. Its grading and the direct-sum decomposition give
bijectivity in each degree. Naturality of the pullback unit and restriction gives
compatibility on affine refinements in both variables. These identities hold on
scalars and on degree-one generators and extend by symmetric-algebra induction.
This argument applies to every base morphism and includes zero rings and modules. -/
theorem exists_normalized_pullbackData {X S : Scheme.{u}} (g : X ⟶ S)
    (E : S.Modules) [E.IsQuasicoherent]
    [((Scheme.Modules.tensorPullback g).obj E).IsQuasicoherent] :
    ∃ b : Scheme.GradedAlgebraData.PullbackData g (gradedAlgebraData E)
        (gradedAlgebraData ((Scheme.Modules.tensorPullback g).obj E)),
      ∀ (U : S.affineOpens) (W : X.affineOpens) (h : W.1 ≤ g ⁻¹ᵁ U.1)
        (m : E.val.obj (op U.1)),
        b.map h (SymmetricAlgebra.ι Γ(S, U.1) _ m) =
          SymmetricAlgebra.ι Γ(X, W.1) _
            (((Scheme.Modules.tensorPullback g).obj E).presheaf.map (homOfLE h).op
              (Scheme.Modules.tensorPullbackSection g E U.1 m)) := by
  let b : Scheme.GradedAlgebraData.PullbackData g (gradedAlgebraData E)
      (gradedAlgebraData ((Scheme.Modules.tensorPullback g).obj E)) :=
    { map := fun h ↦ pullbackGradedMap g E h
      isGradedBaseChangeAlong := fun h ↦ pullbackGradedMap_isBaseChange g E h
      res_map := by
        intro U' V' U h' h a
        induction a using SymmetricAlgebra.induction with
        | algebraMap r =>
          change restriction _ _ (pullbackRingMap g E h (algebraMap _ _ r)) =
            pullbackRingMap g E _ (algebraMap _ _ r)
          rw [pullbackRingMap_algebraMap, restriction_algebraMap,
            pullbackRingMap_algebraMap]
          congr 1
          exact congrArg (fun f ↦ f r)
            (g.appLE_map h (homOfLE (X := X.Opens) h').op)
        | ι m =>
          change restriction _ _ (pullbackRingMap g E h (SymmetricAlgebra.ι _ _ m)) =
            pullbackRingMap g E _ (SymmetricAlgebra.ι _ _ m)
          rw [pullbackRingMap_ι, restriction_ι, pullbackRingMap_ι, unitSection_res_map]
        | mul a b ha hb => simp_all only [map_mul]
        | add a b ha hb => simp_all only [map_add]
      map_res := by
        intro U' U V h hUV a
        induction a using SymmetricAlgebra.induction with
        | algebraMap r =>
          change pullbackRingMap g E h (restriction E _ (algebraMap _ _ r)) =
            pullbackRingMap g E _ (algebraMap _ _ r)
          rw [restriction_algebraMap, pullbackRingMap_algebraMap, pullbackRingMap_algebraMap]
          congr 1
          exact congrArg (fun f ↦ f r)
            (g.map_appLE h (homOfLE (X := S.Opens) hUV).op)
        | ι m =>
          change pullbackRingMap g E h (restriction E _ (SymmetricAlgebra.ι _ _ m)) =
            pullbackRingMap g E _ (SymmetricAlgebra.ι _ _ m)
          rw [restriction_ι, pullbackRingMap_ι, pullbackRingMap_ι, unitSection_map_res]
        | mul a b ha hb => simp_all only [map_mul]
        | add a b ha hb => simp_all only [map_add] }
  refine ⟨b, ?_⟩
  intro U W h m
  change pullbackRingMap g E h (SymmetricAlgebra.ι _ _ m) = _
  rw [pullbackRingMap_ι, unitSection_eq]
  rfl

end AlgebraicGeometry.SymmetricAlgebraSheaf
