/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import WeilConjectures.Algebra.Homology.KFlat
import WeilConjectures.AlgebraicGeometry.Modules.AffineTildeTensor
import WeilConjectures.AlgebraicGeometry.Modules.PullbackMonoidal
import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.Functor
import WeilConjectures.AlgebraicGeometry.Modules.RestrictionTensorComparison

/-! # Total tensor complexes through the canonical affine chart

Source: Stacks Project, Tag 08DX(2), the underived total-complex comparison.
(blueprint: lem-pc-affine-chart-total-tensor).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

noncomputable local instance chartTotalTensor (X : Scheme.{u}) :
    MonoidalCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.monoidalCategory X.sheaf

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private noncomputable def tildeTensorHom (R : CommRingCat.{u}) (M N : ModuleCat.{u} R) :
    tilde (M ⊗ N) ⟶ tilde M ⊗ tilde N :=
  (affine_tilde_tensor R M N).choose_spec.2.2.choose

private instance tildeTensorHom_isIso (R : CommRingCat.{u}) (M N : ModuleCat.{u} R) :
    IsIso (tildeTensorHom R M N) :=
  (affine_tilde_tensor R M N).choose_spec.2.2.choose_spec.2.1

private noncomputable def tildeTensorNatIso (R : CommRingCat.{u}) :
    (Functor.postcompose₂.obj (tilde.functor R)).obj (curriedTensor (ModuleCat.{u} R)) ≅
      (((Functor.whiskeringLeft₂ _).obj (tilde.functor R)).obj (tilde.functor R)).obj
        (curriedTensor (Spec R).Modules) :=
  NatIso.ofComponents (fun M ↦
    NatIso.ofComponents (fun N ↦ asIso (tildeTensorHom R M N)) (fun {N N'} g ↦ by
      apply ((tilde.adjunction (R := R)).homEquiv (M ⊗ N) _).injective
      apply ModuleCat.hom_ext
      apply TensorProduct.ext'
      intro m n
      change (tildeTensorHom R M N').app ⊤
          ((tilde.map (M ◁ g)).app ⊤ (tilde.toOpen (M ⊗ N) ⊤ (m ⊗ₜ[R] n))) =
        (tilde M ◁ tilde.map g).app ⊤
          ((tildeTensorHom R M N).app ⊤ (tilde.toOpen (M ⊗ N) ⊤ (m ⊗ₜ[R] n)))
      have ht := congrArg (fun k ↦ k (m ⊗ₜ[R] n)) (tilde.toOpen_map_app (M ◁ g) ⊤)
      change (tilde.map (M ◁ g)).app ⊤ (tilde.toOpen (M ⊗ N) ⊤ (m ⊗ₜ[R] n)) =
        tilde.toOpen (M ⊗ N') ⊤ (m ⊗ₜ[R] g n) at ht
      rw [ht, show (tildeTensorHom R M N').app ⊤
          (tilde.toOpen (M ⊗ N') ⊤ (m ⊗ₜ[R] g n)) =
          Scheme.Modules.tmulSection (tilde.toOpen M ⊤ m) (tilde.toOpen N' ⊤ (g n)) from
        ((affine_tilde_tensor R M N').choose_spec.2.2.choose_spec.1 _).trans
          ((affine_tilde_tensor R M N').choose_spec.1 m (g n)),
        show (tildeTensorHom R M N).app ⊤
          (tilde.toOpen (M ⊗ N) ⊤ (m ⊗ₜ[R] n)) =
          Scheme.Modules.tmulSection (tilde.toOpen M ⊤ m) (tilde.toOpen N ⊤ n) from
        ((affine_tilde_tensor R M N).choose_spec.2.2.choose_spec.1 _).trans
          ((affine_tilde_tensor R M N).choose_spec.1 m n),
        Scheme.Modules.whiskerLeft_app_tmulSection]
      congr 1
      exact (congrArg (fun k ↦ k n) (tilde.toOpen_map_app g ⊤)).symm)
    )
    (fun {M M'} f ↦ by
      ext N : 2
      apply ((tilde.adjunction (R := R)).homEquiv (M ⊗ N) _).injective
      apply ModuleCat.hom_ext
      apply TensorProduct.ext'
      intro m n
      change (tildeTensorHom R M' N).app ⊤
          ((tilde.map (f ▷ N)).app ⊤ (tilde.toOpen (M ⊗ N) ⊤ (m ⊗ₜ[R] n))) =
        (tilde.map f ▷ tilde N).app ⊤
          ((tildeTensorHom R M N).app ⊤ (tilde.toOpen (M ⊗ N) ⊤ (m ⊗ₜ[R] n)))
      have ht := congrArg (fun k ↦ k (m ⊗ₜ[R] n)) (tilde.toOpen_map_app (f ▷ N) ⊤)
      change (tilde.map (f ▷ N)).app ⊤ (tilde.toOpen (M ⊗ N) ⊤ (m ⊗ₜ[R] n)) =
        tilde.toOpen (M' ⊗ N) ⊤ (f m ⊗ₜ[R] n) at ht
      rw [ht, show (tildeTensorHom R M' N).app ⊤
          (tilde.toOpen (M' ⊗ N) ⊤ (f m ⊗ₜ[R] n)) =
          Scheme.Modules.tmulSection (tilde.toOpen M' ⊤ (f m)) (tilde.toOpen N ⊤ n) from
        ((affine_tilde_tensor R M' N).choose_spec.2.2.choose_spec.1 _).trans
          ((affine_tilde_tensor R M' N).choose_spec.1 (f m) n),
        show (tildeTensorHom R M N).app ⊤
          (tilde.toOpen (M ⊗ N) ⊤ (m ⊗ₜ[R] n)) =
          Scheme.Modules.tmulSection (tilde.toOpen M ⊤ m) (tilde.toOpen N ⊤ n) from
        ((affine_tilde_tensor R M N).choose_spec.2.2.choose_spec.1 _).trans
          ((affine_tilde_tensor R M N).choose_spec.1 m n),
        Scheme.Modules.whiskerRight_app_tmulSection]
      congr 1
      exact (congrArg (fun k ↦ k m) (tilde.toOpen_map_app f ⊤)).symm)
/-- Associated sheaf followed by canonical chart restriction commutes with total tensor.
Source: Stacks Project, Tag 08DX, lemma-quasi-coherence-tensor-product, proof of (2),
and Tag 01I8 for the underived associated-sheaf tensor identification.
(blueprint: lem-pc-affine-chart-total-tensor).

Proof: let C be tilde followed by restriction along X.toSpecΓ. The affine associated-
sheaf tensor comparison identifies C(U tensor V) with C(U) tensor C(V). Its defining
formula on pure tensors proves naturality in U and V; restriction has the same
naturality by its defining formula on restricted sections. The affine tilde functor
is a left adjoint, and open restriction preserves colimits, so C preserves the
coproduct indexed by all pairs (p,q) with p+q=n in each integer degree n. Combine the
tensor comparisons on these summands with the coproduct comparison. Naturality
identifies the first differentials and the signed second differentials. This gives
mutually inverse chain maps between C(Tot(P tensor N)) and Tot(C(P) tensor C(N)).
Take the inverse comparison to obtain the displayed orientation. This construction
uses no K-flatness, no localization, and no finiteness assumption; it also applies
to zero rings, zero complexes and an empty affine scheme. -/
theorem affineChart_totalTensor_iso (X : Scheme.{u}) [IsAffine X]
    (P N : CochainComplex (ModuleCat.{u} Γ(X, ⊤)) ℤ) :
    letI : Functor.PreservesZeroMorphisms
        (curriedTensor (SheafOfModules.{u} (moduleRings X.toRingedSpace))) :=
      SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
    letI : ∀ F : SheafOfModules.{u} (moduleRings X.toRingedSpace),
        ((curriedTensor _).obj F).PreservesZeroMorphisms :=
      SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf
    let T := @Functor.mapHomologicalComplex _ _ _ _ _ _ _
      (@id (ModuleCat.{u} Γ(X, ⊤) ⥤
        SheafOfModules.{u} (moduleRings (Spec Γ(X, ⊤)).toRingedSpace))
        (tilde.functor Γ(X, ⊤))) ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)
    let R := (Scheme.Modules.restrictFunctor X.toSpecΓ).mapHomologicalComplex (.up ℤ)
    Nonempty
      (CochainComplex.mapBifunctor (R.obj (T.obj P)) (R.obj (T.obj N))
        (curriedTensor (SheafOfModules.{u} (moduleRings X.toRingedSpace))) ≅
      R.obj (T.obj (CochainComplex.mapBifunctor P N
        (curriedTensor (ModuleCat.{u} Γ(X, ⊤)))))) := by
  let : (curriedTensor X.Modules).PreservesZeroMorphisms :=
    SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf
  let : ∀ F : X.Modules, ((curriedTensor _).obj F).PreservesZeroMorphisms :=
    SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf
  let : (curriedTensor (Spec Γ(X, ⊤)).Modules).PreservesZeroMorphisms :=
    SheafOfModules.preservesZeroMorphisms_curriedTensor (Spec Γ(X, ⊤)).sheaf
  let : ∀ F : (Spec Γ(X, ⊤)).Modules,
      ((curriedTensor _).obj F).PreservesZeroMorphisms :=
    SheafOfModules.preservesZeroMorphisms_curriedTensor_obj (Spec Γ(X, ⊤)).sheaf
  let S : ModuleCat.{u} Γ(X, ⊤) ⥤ (Spec Γ(X, ⊤)).Modules :=
    tilde.functor Γ(X, ⊤)
  let : S.IsLeftAdjoint := (tilde.adjunction (R := Γ(X, ⊤))).isLeftAdjoint
  let : S.Additive := by
    have := Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts S
    exact Functor.additive_of_preservesBinaryBiproducts S
  let U := Scheme.Modules.restrictFunctor X.toSpecΓ
  let : U.Monoidal := Functor.Monoidal.transport
    (Scheme.Modules.restrictFunctorIsoPullback X.toSpecΓ).symm
  let : U.Additive := by
    have := Limits.preservesBinaryBiproducts_of_preservesBinaryCoproducts U
    exact Functor.additive_of_preservesBinaryBiproducts U
  let eS := asIso (HomologicalComplex.mapBifunctorComparison
    (G₁ := S) (G₂ := S) (G := S)
    (tildeTensorNatIso Γ(X, ⊤)).hom (.up ℤ) P N)
  let eU := asIso (HomologicalComplex.mapBifunctorComparison
    (G₁ := U) (G₂ := U) (G := U)
    (Functor.OplaxMonoidal.δNatTrans U) (.up ℤ)
    ((S.mapHomologicalComplex (.up ℤ)).obj P)
    ((S.mapHomologicalComplex (.up ℤ)).obj N))
  exact ⟨eU.symm ≪≫ (U.mapHomologicalComplex (.up ℤ)).mapIso eS.symm⟩

end AlgebraicGeometry
