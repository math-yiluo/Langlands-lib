/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.AlgebraicGeometry.AdicCoefficientDatum
import Mathlib.Algebra.Category.ModuleCat.Products
import WeilConjectures.AlgebraicGeometry.CompletedConstantAlgebraFlatQuotients
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Module.Projective
import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.CategoryTheory.Sites.Abelian

/-!
# Completed constant sheaves and finite reduction

Source: Stacks Project, Modules on Sites, Tags 093J--093M;
Cohomology on Sites, Tags 06YN and 06YU
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped ChangeOfRings

namespace AlgebraicGeometry.Scheme.CompletedConstantReduction

open AdicCoefficients

/-- The base map is uniquely fixed by all quotient projections. Source: Stacks Tag 093M
(auxiliary; not a blueprint node).
Proof: apply the limit universal property to the quotient maps. Their compatibility follows
on representatives from the quotient factor formula, and constant sheafification preserves it.
The limit universal property also gives uniqueness. -/
theorem base_exists (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (I : Ideal A) :
    ∃! φ : adicLisseConstantRing T A ⟶ adicLisseCompletedRing T I,
      ∀ n : ℕ, φ ≫ limit.π (adicLisseRingSystem T I) (op n) =
        (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
          (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))) := by
  let c : Cone (adicLisseRingSystem T I) :=
    { pt := adicLisseConstantRing T A
      π := NatTrans.ofOpSequence
        (fun n ↦ (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
          (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))) (by
            intro n
            simp only [Functor.const_obj_map, adicLisseRingSystem,
              Functor.ofOpSequence_map_homOfLE_succ, ← Functor.map_comp]
            congr 1) }
  refine ⟨limit.lift _ c, ?_, ?_⟩
  · intro n
    exact limit.lift_π c (op n)
  · intro φ hφ
    apply limit.hom_ext
    intro n
    exact (hφ n.unop).trans (limit.lift_π c n).symm

/-- The canonical constant-to-completed coefficient homomorphism. Source: Stacks Tag 093M
(auxiliary; not a blueprint node). -/
def base (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (I : Ideal A) :
    adicLisseConstantRing T A ⟶ adicLisseCompletedRing T I :=
  (base_exists T I).choose

/-- The quotient sheaf, retaining its action by the completed ring through its projection.
Source: Stacks Tags 093M and 06YU
(auxiliary; not a blueprint node). -/
def residue (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (I : Ideal A) (n : ℕ) :
    SheafOfModules.{u + 1} ((adicLisseForget T).obj (adicLisseCompletedRing T I)) :=
  (SheafOfModules.restrictScalars ((adicLisseForget T).map
    (limit.π (adicLisseRingSystem T I) (op n)))).obj
      (SheafOfModules.unit ((adicLisseForget T).obj
        (adicLisseConstantRing T (A ⧸ I ^ (n + 1)))))

section

private local instance completedConstantReductionRestrictedModule (T : Scheme.{u})
    {A : Sheaf (ProEt.topology T) CommRingCat.{u + 1}}
    (M : SheafOfModules.{u + 1} ((adicLisseForget T).obj A))
    {X Y : T.ProEtᵒᵖ} (i : X ⟶ Y) :
    Module (A.obj.obj Y)
      ((ModuleCat.restrictScalars (((adicLisseForget T).obj A).obj.map i).hom).obj
        (M.val.obj Y)) :=
  inferInstanceAs (Module (A.obj.obj Y) (M.val.obj Y))

private theorem tensorRestriction_tmul
    (T : Scheme.{u})
    {A S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (c : A ⟶ S) (M : SheafOfModules.{u + 1}
      ((adicLisseForget T).obj A))
    {X Y : T.ProEtᵒᵖ} (i : X ⟶ Y) (s : S.obj.obj X) (m : M.val.obj X) :
    (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} c M).map i
      (s ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m) =
      S.obj.map i s ⊗ₜ[A.obj.obj Y, (c.hom.app Y).hom] M.val.map i m :=
  Classical.choose_spec (SheafOfModules.exists_changeOfRingsMap.{u, u + 1, u + 1} c M i) s m

end

private noncomputable def tensorToRestriction
    (T : Scheme.{u})
    {A S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (c : A ⟶ S)
    (M : SheafOfModules.{u + 1} ((adicLisseForget T).obj A)) (H : SheafOfModules.{u + 1}
      ((adicLisseForget T).obj S))
    (f : SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} c M ⟶ H.val) : M ⟶
      (SheafOfModules.restrictScalars ((adicLisseForget T).map c)).obj H where
  val :=
    { app := fun W ↦ ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.toRestrictScalars.{u + 1, u + 1,
      u + 1}
        (c.hom.app W).hom (f.app W)
      naturality := by
        intro X Y i
        ext m
        change f.app Y ((1 : S.obj.obj Y) ⊗ₜ[A.obj.obj Y, (c.hom.app Y).hom]
          M.val.map i m) = H.val.map i (f.app X
            ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m))
        have h := PresheafOfModules.naturality_apply f i
          ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m)
        rw [tensorRestriction_tmul T, map_one] at h
        exact h }

private noncomputable def restrictionToTensor
    (T : Scheme.{u})
    {A S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (c : A ⟶ S)
    (M : SheafOfModules.{u + 1} ((adicLisseForget T).obj A)) (H : SheafOfModules.{u + 1}
      ((adicLisseForget T).obj S))
    (g : M ⟶ (SheafOfModules.restrictScalars ((adicLisseForget T).map c)).obj H) :
      SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} c M ⟶ H.val where
  app W := ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars.{u + 1, u + 1, u + 1}
    (c.hom.app W).hom (g.val.app W)
  naturality := by
    intro X Y i
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    have h := PresheafOfModules.naturality_apply g.val i m
    change ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars.{u + 1, u + 1, u + 1}
      (c.hom.app Y).hom (g.val.app Y)
        ((SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} c M).map i
          ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m)) =
      H.val.map i (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars.{u + 1, u + 1, u
        + 1}
        (c.hom.app X).hom (g.val.app X)
          ((1 : S.obj.obj X) ⊗ₜ[A.obj.obj X, (c.hom.app X).hom] m))
    rw [tensorRestriction_tmul T, map_one]
    have atOne (W : T.ProEtᵒᵖ) (n : M.val.obj W) :
        ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars.{u + 1, u + 1, u + 1}
          (c.hom.app W).hom (g.val.app W)
            ((1 : S.obj.obj W) ⊗ₜ[A.obj.obj W, (c.hom.app W).hom] n) = g.val.app W n := by
      exact congrArg (fun f : M.val.obj W ⟶
        (ModuleCat.restrictScalars (c.hom.app W).hom).obj (H.val.obj W) ↦ f n)
        ((ModuleCat.ExtendRestrictScalarsAdj.homEquiv.{u + 1, u + 1, u + 1} (c.hom.app
          W).hom).apply_symm_apply
          (g.val.app W))
    rw [atOne, atOne]
    exact h

private noncomputable def tensorPresheafHomEquiv
    (T : Scheme.{u})
    {A S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (c : A ⟶ S)
    (M : SheafOfModules.{u + 1} ((adicLisseForget T).obj A)) (H : SheafOfModules.{u + 1}
      ((adicLisseForget T).obj S)) :
    (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} c M ⟶ H.val) ≃
      (M ⟶ (SheafOfModules.restrictScalars ((adicLisseForget T).map c)).obj H) where
  toFun := tensorToRestriction T c M H
  invFun := restrictionToTensor T c M H
  left_inv f := by
    ext W : 1
    exact (ModuleCat.ExtendRestrictScalarsAdj.homEquiv.{u + 1, u + 1, u + 1} (c.hom.app
      W).hom).symm_apply_apply
      (f.app W)
  right_inv g := by
    apply SheafOfModules.hom_ext
    ext W : 1
    exact (ModuleCat.ExtendRestrictScalarsAdj.homEquiv.{u + 1, u + 1, u + 1} (c.hom.app
      W).hom).apply_symm_apply
      (g.val.app W)

private noncomputable def tensorHomEquiv
    (T : Scheme.{u})
    {A S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (c : A ⟶ S)
    (M : SheafOfModules.{u + 1} ((adicLisseForget T).obj A)) (H : SheafOfModules.{u + 1}
      ((adicLisseForget T).obj S)) :
    (SheafOfModules.changeOfRings.{u, u + 1, u + 1} c M ⟶ H) ≃ (M ⟶
      (SheafOfModules.restrictScalars ((adicLisseForget T).map c)).obj H) :=
  ((PresheafOfModules.sheafificationAdjunction.{u + 1} (𝟙 ((adicLisseForget T).obj
    S).obj)).homEquiv _ _).trans
    (tensorPresheafHomEquiv T c M H)

private theorem tensorHomEquiv_tmul (T : Scheme.{u})
    {R S : Sheaf (ProEt.topology T) CommRingCat.{u + 1}} (φ : R ⟶ S)
    (M : SheafOfModules.{u + 1} ((adicLisseForget T).obj R))
    (H : SheafOfModules.{u + 1} ((adicLisseForget T).obj S))
    (f : SheafOfModules.changeOfRings.{u, u + 1, u + 1} φ M ⟶ H)
    (U : T.ProEtᵒᵖ) (s : S.obj.obj U) (m : M.val.obj U) :
    f.val.app U ((toSheafify (ProEt.topology T)
      (SheafOfModules.changeOfRingsPresheaf.{u, u + 1, u + 1} φ M).presheaf).app U
        (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] m)) =
      s • (@id (H.val.obj U) ((tensorHomEquiv T φ M H f).val.app U m)) := by
  let k := PresheafOfModules.sheafificationHomEquiv.{u + 1}
    (𝟙 ((adicLisseForget T).obj S).obj) f
  change k.app U (s ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] m) =
    s • k.app U ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] m)
  let k' : (ModuleCat.extendScalars (φ.hom.app U).hom).obj (M.val.obj U) ⟶
      H.val.obj U := k.app U
  have hh := k'.hom.map_smul s
    ((1 : S.obj.obj U) ⊗ₜ[R.obj.obj U, (φ.hom.app U).hom] m)
  rw [ModuleCat.ExtendScalars.smul_tmul, mul_one] at hh
  exact hh

/-- The reduction map is uniquely determined on local tensor generators by projection
and multiplication. Source: Stacks Tag 093M
(auxiliary; not a blueprint node).
Proof: multiplication after the nth projection is balanced over the constant base ring.
It commutes with restriction, and therefore descends through module sheafification.
Constant module sections and local pure tensors generate the source, proving uniqueness. -/
theorem reduction_exists (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (I : Ideal A) (n : ℕ) :
    ∃! r : (completedAdicChange T (base T I)).obj
        ((adicLisseConstantModules T A).obj (ModuleCat.of A (A ⧸ I ^ (n + 1)))) ⟶
          residue T I n,
      ∀ (U : T.ProEtᵒᵖ) (b : (adicLisseCompletedRing T I).obj.obj U)
        (x : A ⧸ I ^ (n + 1)),
        r.val.app U (tensorSection T (base T I) _ U b
          ((toSheafify (ProEt.topology T)
            ((Functor.const T.ProEtᵒᵖ).obj
              (AddCommGrpCat.of (ModuleCat.of A (A ⧸ I ^ (n + 1)))))).app U x)) =
            @id ((adicLisseConstantRing T (A ⧸ I ^ (n + 1))).obj.obj U)
              ((limit.π (adicLisseRingSystem T I) (op n)).hom.app U b) *
              @id ((adicLisseConstantRing T (A ⧸ I ^ (n + 1))).obj.obj U)
                ((adicLisseConstantUnit T (A ⧸ I ^ (n + 1))).app U x) := by
  let Q := A ⧸ I ^ (n + 1)
  let M := (adicLisseConstantModules T A).obj (ModuleCat.of A Q)
  let N := (SheafOfModules.restrictScalars ((adicLisseForget T).map (base T I))).obj
    (residue T I n)
  let P : PresheafOfModules.{u + 1}
      ((Functor.const T.ProEtᵒᵖ).obj (RingCat.of A)) :=
    (siteConstantModulePresheaf (C := Discrete (ULift.{u + 1} Unit)) A ⋙
    PresheafOfModules.pushforward₀
      ((Functor.const T.ProEt).obj (Discrete.mk (ULift.up ())))
      ((Functor.const (Discrete (ULift.{u + 1} Unit))ᵒᵖ).obj (RingCat.of A))).obj
        (ModuleCat.of A Q)
  let g₀ : P ⟶
      (PresheafOfModules.restrictScalars (adicLisseConstantUnit T A)).obj N.val :=
    { app := fun U ↦ ModuleCat.ofHom
        (Y := ((PresheafOfModules.restrictScalars (adicLisseConstantUnit T A)).obj N.val).obj U)
        { toFun := fun (x : Q) ↦ (adicLisseConstantUnit T Q).app U x
          map_add' := fun (x y : Q) ↦ map_add ((adicLisseConstantUnit T Q).app U).hom x y
          map_smul' := by
            intro a x
            have hb : base T I ≫ limit.π (adicLisseRingSystem T I) (op n) =
                (constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
                  (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))) :=
              (base_exists T I).choose_spec.1 n
            change (adicLisseConstantUnit T Q).app U (a • x) =
              @id ((adicLisseConstantRing T Q).obj.obj U)
                ((limit.π (adicLisseRingSystem T I) (op n)).hom.app U
                  ((base T I).hom.app U ((adicLisseConstantUnit T A).app U a))) *
                    @id ((adicLisseConstantRing T Q).obj.obj U)
                      ((adicLisseConstantUnit T Q).app U x)
            have h := congrArg (fun k ↦ (k.hom.app U) ((adicLisseConstantUnit T A).app U a)) hb
            change (limit.π (adicLisseRingSystem T I) (op n)).hom.app U
                ((base T I).hom.app U ((adicLisseConstantUnit T A).app U a)) = _ at h
            dsimp only [id_eq]
            rw [h]
            have hn := toSheafify_naturality (ProEt.topology T)
              ((Functor.const T.ProEtᵒᵖ).map
                (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1)))))
            have hn' := congrArg (fun k ↦ (k.app U).hom (show A from a)) hn
            change (adicLisseConstantUnit T Q).app U
                ((Ideal.Quotient.mk (I ^ (n + 1))) a) =
              ((constantSheaf (ProEt.topology T) CommRingCat.{u + 1}).map
                (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (n + 1))))).hom.app U
                  ((adicLisseConstantUnit T A).app U a) at hn'
            erw [← hn']
            change (adicLisseConstantUnit T Q).app U
                ((show A from a) • (show Q from x)) = _
            change (adicLisseConstantUnit T Q).app U
                ((Ideal.Quotient.mk (I ^ (n + 1))) a * (show Q from x)) = _
            exact
              (map_mul ((adicLisseConstantUnit T Q).app U).hom
                ((Ideal.Quotient.mk (I ^ (n + 1))) a) (show Q from x)) }
      naturality := by
        intro U V f
        ext x
        change (adicLisseConstantUnit T Q).app V (show Q from x) =
          (adicLisseRing T Q).obj.map f ((adicLisseConstantUnit T Q).app U x)
        exact ConcreteCategory.congr_hom
          ((adicLisseConstantUnit T Q).naturality f) x }
  let g : M ⟶ N := (PresheafOfModules.sheafificationHomEquiv.{u + 1}
    (adicLisseConstantUnit T A) (P := P) (F := N)).symm g₀
  let h := (completedAdicChangeData T (base T I)).choose_spec.choose M
  let r₀ := (tensorHomEquiv T (base T I) M (residue T I n)).symm g
  let r := eqToHom h ≫ r₀
  have hc : eqToHom h.symm ≫ r = r₀ := by simp [r]
  refine ⟨r, ?_, ?_⟩
  · intro U b x
    change (eqToHom h.symm ≫ r).val.app U
      ((toSheafify (ProEt.topology T)
        (SheafOfModules.changeOfRingsPresheaf (base T I) M).presheaf).app U
          (b ⊗ₜ[(adicLisseConstantRing T A).obj.obj U, ((base T I).hom.app U).hom]
            ((toSheafify (ProEt.topology T) P.presheaf).app U x))) = _
    rw [hc]
    refine (tensorHomEquiv_tmul T (base T I) M (residue T I n) r₀ U b
      ((toSheafify (ProEt.topology T) P.presheaf).app U x)).trans ?_
    have he : tensorHomEquiv T (base T I) M (residue T I n) r₀ = g :=
      (tensorHomEquiv T (base T I) M (residue T I n)).apply_symm_apply g
    rw [he]
    have hg₀ : PresheafOfModules.sheafificationHomEquiv.{u + 1}
        (adicLisseConstantUnit T A) g = g₀ :=
      (PresheafOfModules.sheafificationHomEquiv.{u + 1}
        (adicLisseConstantUnit T A) (P := P) (F := N)).apply_symm_apply g₀
    have hg := congrArg (fun (k : P ⟶
      (PresheafOfModules.restrictScalars (adicLisseConstantUnit T A)).obj N.val) ↦
        (k.app U).hom x) hg₀
    change g.val.app U ((toSheafify (ProEt.topology T) P.presheaf).app U x) =
      (adicLisseConstantUnit T Q).app U x at hg
    rw [hg]
    rfl
  · intro s hs
    apply (cancel_epi (eqToHom h.symm)).mp
    rw [hc]
    apply (tensorHomEquiv T (base T I) M (residue T I n)).injective
    have he : tensorHomEquiv T (base T I) M (residue T I n) r₀ = g :=
      (tensorHomEquiv T (base T I) M (residue T I n)).apply_symm_apply g
    refine Eq.trans ?_ he.symm
    apply (PresheafOfModules.sheafificationHomEquiv.{u + 1}
      (adicLisseConstantUnit T A) (P := P) (F := N)).injective
    have hg : PresheafOfModules.sheafificationHomEquiv.{u + 1}
        (adicLisseConstantUnit T A) g = g₀ :=
      (PresheafOfModules.sheafificationHomEquiv.{u + 1}
        (adicLisseConstantUnit T A) (P := P) (F := N)).apply_symm_apply g₀
    refine Eq.trans ?_ hg.symm
    ext U x
    have ht := tensorHomEquiv_tmul T (base T I) M (residue T I n)
      (eqToHom h.symm ≫ s) U 1
      ((toSheafify (ProEt.topology T) P.presheaf).app U x)
    have hx := hs U 1 (show Q from x)
    simp only [one_smul] at ht
    change (tensorHomEquiv T (base T I) M (residue T I n)
      (eqToHom h.symm ≫ s)).val.app U
        ((toSheafify (ProEt.topology T) P.presheaf).app U x) =
          (adicLisseConstantUnit T Q).app U x
    refine ht.symm.trans ?_
    change s.val.app U (tensorSection T (base T I) M U 1
      ((toSheafify (ProEt.topology T) P.presheaf).app U x)) = _
    simp only [map_one, id_eq, one_mul] at hx
    convert hx using 1
    rfl

/-- The ordinary canonical reduction map, fixed by its formula in `reduction_exists`.
Source: Stacks Tag 093M (auxiliary; not a blueprint node). -/
def reduction (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (I : Ideal A) (n : ℕ) := (reduction_exists T I n).choose

/-- The actual canonical reduction on a complex mapping to the constant quotient.
Source: Stacks Tags 06YY and 093M
(auxiliary; not a blueprint node). -/
def reductionComplex (T : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (I : Ideal A) (n : ℕ)
    (P : CochainComplex
      (SheafOfModules.{u + 1} ((adicLisseForget T).obj (adicLisseConstantRing T A))) ℤ)
    (f : P ⟶ (CochainComplex.singleFunctor _ 0).obj
      ((adicLisseConstantModules T A).obj (ModuleCat.of A (A ⧸ I ^ (n + 1))))) :=
  ((completedAdicChange T (base T I)).mapHomologicalComplex (.up ℤ)).map f ≫
    ((completedAdicChange T (base T I)).mapCochainComplexSingleFunctor 0).hom.app _ ≫
      (CochainComplex.singleFunctor _ 0).map (reduction T I n)

/-- Constant module sheafification is additive. Source: Stacks Tag 093J
(auxiliary; not a blueprint node).
Proof: the constant presheaf functor and associated-module-sheafification functor are additive,
and so is their composite defining `adicLisseConstantModules`. -/
theorem constant_additive (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    (adicLisseConstantModules T A).Additive := by
  constructor
  intro M N f g
  apply (SheafOfModules.toSheaf _).map_injective
  change (presheafToSheaf (ProEt.topology T) AddCommGrpCat.{u + 1}).map
    ((Functor.const T.ProEtᵒᵖ).map
      ((forget₂ (ModuleCat A) AddCommGrpCat).map (f + g))) = _
  rw [Functor.map_add, Functor.map_add, Functor.map_add]
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem constant_exact (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    PreservesFiniteLimits (adicLisseConstantModules T A) ∧
      PreservesFiniteColimits (adicLisseConstantModules T A) := by
  let P : ModuleCat.{u + 1} A ⥤
      PresheafOfModules.{u + 1} ((Functor.const T.ProEtᵒᵖ).obj (RingCat.of A)) :=
    siteConstantModulePresheaf (C := Discrete (ULift.{u + 1} Unit)) A ⋙
      PresheafOfModules.pushforward₀
        ((Functor.const T.ProEt).obj (Discrete.mk (ULift.up ())))
        ((Functor.const (Discrete (ULift.{u + 1} Unit))ᵒᵖ).obj (RingCat.of A))
  have : PreservesFiniteLimits P := by
    constructor
    intro K _ _
    constructor
    intro F
    constructor
    intro c hc
    exact ⟨PresheafOfModules.evaluationJointlyReflectsLimits _ _ (fun X ↦ hc)⟩
  have : PreservesFiniteColimits P := by
    constructor
    intro K _ _
    constructor
    intro F
    constructor
    intro c hc
    exact ⟨PresheafOfModules.evaluationJointlyReflectsColimits _ _ (fun X ↦ hc)⟩
  exact ⟨comp_preservesFiniteLimits P
    (PresheafOfModules.sheafification (adicLisseConstantUnit T A)),
    comp_preservesFiniteColimits P
      (PresheafOfModules.sheafification (adicLisseConstantUnit T A))⟩

/-- The termwise constant module sheaf of a complex. Source: Stacks Tag 093J
(auxiliary; not a blueprint node). -/
def constantComplex (T : Scheme.{u}) (A : Type (u + 1)) [CommRing A] :
    CochainComplex (ModuleCat.{u + 1} A) ℤ ⥤
      CochainComplex
        (SheafOfModules.{u + 1} ((adicLisseForget T).obj (adicLisseConstantRing T A))) ℤ :=
  letI := constant_additive T A
  (adicLisseConstantModules T A).mapHomologicalComplex (.up ℤ)

end AlgebraicGeometry.Scheme.CompletedConstantReduction
