/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel
public import WeilConjectures.Algebra.Homology.RingTensorCohomology
public import Mathlib.RingTheory.Localization.Basic
import WeilConjectures.Algebra.Homology.FirstLocalizationCohomologyBaseChange

/-! # The characterized first-factor localization morphism

Source: Stacks Project, More on Algebra, Tag 06Y6; perfect.tex, Tag 0DJ8.
(blueprint: lem-pc-first-localization-map).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory
open scoped TensorProduct ChangeOfRings

attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace RingTensorCohomology

variable (R A Aq : Type u) [CommRing R] [CommRing A] [CommRing Aq]
  [Algebra R A] [Algebra A Aq] [Algebra R Aq] [IsScalarTower R A Aq]

/-- The localization unit on the underlying R-complex. It sends x to 1 tensor x.
Source: Stacks Project, Tag 06Y6 (blueprint: lem-pc-first-localization-map). -/
noncomputable def firstLocalizationUnit
    (Q : CochainComplex (ModuleCat.{u} A) ℤ) :
    (restrict R A).obj Q ⟶ (restrict R Aq).obj ((extend A Aq).obj Q) where
  f j := (ModuleCat.restrictScalars (algebraMap R A)).map
    ((ModuleCat.extendRestrictScalarsAdj (algebraMap A Aq)).unit.app (Q.X j)) ≫
    (ModuleCat.restrictScalarsComp'App (algebraMap R A) (algebraMap A Aq)
      (algebraMap R Aq) (IsScalarTower.algebraMap_eq R A Aq)
      (((extend A Aq).obj Q).X j)).inv
  comm' j k hjk := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (ModuleCat.extendScalars (algebraMap A Aq)).map (Q.d j k)
        ((1 : Aq) ⊗ₜ[A,algebraMap A Aq] x) =
      (1 : Aq) ⊗ₜ[A,algebraMap A Aq] (Q.d j k x)
    rw [ModuleCat.ExtendScalars.map_tmul]

variable (B D : Type u) [CommRing B] [CommRing D] [Algebra R B]
  [Algebra (A ⊗[R] B) D] [Algebra (Aq ⊗[R] B) D]
  [HasDerivedCategory.{w} (ModuleCat.{u} R)]
  [HasDerivedCategory.{w} (ModuleCat.{u} B)]

/-- Apply derived tensor and cohomology to the first-factor unit, using the unique
counit-compatible comparison of derived functors.
Source: Stacks Project, Tag 06Y6 (blueprint: lem-pc-first-localization-map). -/
noncomputable def firstLocalizationCohomologyMap
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
    (K : ModuleCat.BaseDerivedTensorCohomologyModel R Aq B ((extend A Aq).obj Q) D)
    (i : ℤ) :
    (ModuleCat.restrictScalars.{u}
      (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).obj
        (L.cohomology i) ⟶
    (ModuleCat.restrictScalars.{u}
      (Algebra.TensorProduct.includeRight : B →ₐ[R] Aq ⊗[R] B).toRingHom).obj
        (K.cohomology i) := by
  let _ := L.universal
  let _ := K.universal
  let ζ := Functor.leftDerivedNatIso L.derived K.derived L.counit K.counit
    (HomotopyCategory.quasiIso (ModuleCat.{u} R) (.up ℤ)) (Iso.refl _)
  exact (L.cohomologyIso i).hom ≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
      (L.derived.map (DerivedCategory.Qh.map
        ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).map
          (firstLocalizationUnit R A Aq Q))) ≫
        ζ.hom.app (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).obj
            ((restrict R Aq).obj ((extend A Aq).obj Q))))) ≫
    (K.cohomologyIso i).inv

/-- The generator formula fixes the localization morphism uniquely.
Source: Stacks Project, Tag 06Y6 (blueprint: lem-pc-first-localization-map). -/
def IsFirstLocalizationMap
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
    (K : ModuleCat.BaseDerivedTensorCohomologyModel R Aq B ((extend A Aq).obj Q) D)
    (i : ℤ)
    (e : (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).obj (L.cohomology i) ⟶
      (ModuleCat.extendScalars (algebraMap (Aq ⊗[R] B) D)).obj (K.cohomology i)) : Prop :=
  ∀ x : L.cohomology i,
    e ((1 : D) ⊗ₜ[A ⊗[R] B,algebraMap (A ⊗[R] B) D] x) =
      (1 : D) ⊗ₜ[Aq ⊗[R] B,algebraMap (Aq ⊗[R] B) D]
        (firstLocalizationCohomologyMap R A Aq B D Q L K i x)

/-- Equality on the scalar-extension generators proves uniqueness; in particular the
existence theorem below determines data, rather than an arbitrary witness.
Source: Stacks Project, Tag 06Y6 (blueprint: lem-pc-first-localization-map). -/
theorem IsFirstLocalizationMap.ext
    {Q : CochainComplex (ModuleCat.{u} A) ℤ}
    {L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D}
    {K : ModuleCat.BaseDerivedTensorCohomologyModel R Aq B ((extend A Aq).obj Q) D}
    {i : ℤ}
    {e e' : (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).obj (L.cohomology i) ⟶
      (ModuleCat.extendScalars (algebraMap (Aq ⊗[R] B) D)).obj (K.cohomology i)}
    (he : IsFirstLocalizationMap R A Aq B D Q L K i e)
    (he' : IsFirstLocalizationMap R A Aq B D Q L K i e') : e = e' := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro x
  exact (he x).trans (he' x).symm

variable [Algebra A D] [Algebra B D] [Algebra Aq D]
  [tAD : IsScalarTower A (A ⊗[R] B) D] [tBD : IsScalarTower B (A ⊗[R] B) D]
  [tAqD : IsScalarTower Aq (Aq ⊗[R] B) D] [tBqD : IsScalarTower B (Aq ⊗[R] B) D]
  [tAAqD : IsScalarTower A Aq D]

private theorem extendScalars_eqToIso_one_tmul
    {E F : Type u} [CommRing E] [CommRing F] (f g : E →+* F) (h : f = g)
    (M : ModuleCat.{u} E) (x : M) :
    (eqToIso (congrArg (fun k : E →+* F ↦ (ModuleCat.extendScalars k).obj M) h)).hom
        ((1 : F) ⊗ₜ[E,f] x) = (1 : F) ⊗ₜ[E,g] x := by
  subst g
  rfl

include tAD tBD tAqD tBqD tAAqD in
/-- The canonical derived localization map becomes invertible after extension to D.
Source: Stacks Project, Tag 0DJ8, affine localization identity; Tag 06Y6.
(blueprint: lem-pc-first-localization-map).

Proof: resolve B[0] over R by a K-flat complex F. Tensoring Q with F computes the
base-derived tensor, with commuting A and B actions. Exact localization in the
A-variable commutes with total direct sums and differentials, and hence with
cohomology. It identifies the cohomology for Aq tensor_A Q with localization of
the cohomology for Q. On cohomology the localization unit is the map constructed
above: compare the balanced model with each given model using the unique
counit-compatible derived-functor isomorphism and cohomologyIso_smul. Thus its
extension to D is the tensor associativity isomorphism, since every s in S is
already a unit in D. This supplies e and its generator formula; that formula
determines e uniquely by IsFirstLocalizationMap.ext. No flatness of D, A over R,
or Q over R is used. Identity localization gives the model comparison; if S
contains zero then Aq and D are zero, so the isomorphism is between zero modules. -/
theorem exists_firstLocalization_iso (S : Submonoid A) [IsLocalization S Aq] (i : ℤ)
    (Q : CochainComplex (ModuleCat.{u} A) ℤ)
    (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
    (K : ModuleCat.BaseDerivedTensorCohomologyModel R Aq B ((extend A Aq).obj Q) D)
    : ∃ e : (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).obj (L.cohomology i) ≅
      (ModuleCat.extendScalars (algebraMap (Aq ⊗[R] B) D)).obj (K.cohomology i),
      IsFirstLocalizationMap R A Aq B D Q L K i e.hom := by
  let φ := (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R A Aq)
    (AlgHom.id R B)).toRingHom
  have hφ : (algebraMap (Aq ⊗[R] B) D).comp φ = algebraMap (A ⊗[R] B) D := by
    apply RingHom.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul a b =>
      change algebraMap (Aq ⊗[R] B) D
          (algebraMap A Aq a ⊗ₜ[R] b) = algebraMap (A ⊗[R] B) D (a ⊗ₜ[R] b)
      have hleft (a : A) : algebraMap (A ⊗[R] B) D (a ⊗ₜ[R] (1 : B)) =
          algebraMap A D a := (IsScalarTower.algebraMap_apply A (A ⊗[R] B) D a).symm
      have hleftq (a : Aq) : algebraMap (Aq ⊗[R] B) D (a ⊗ₜ[R] (1 : B)) =
          algebraMap Aq D a := (IsScalarTower.algebraMap_apply Aq (Aq ⊗[R] B) D a).symm
      have hright (b : B) : algebraMap (A ⊗[R] B) D ((1 : A) ⊗ₜ[R] b) =
          algebraMap B D b := (IsScalarTower.algebraMap_apply B (A ⊗[R] B) D b).symm
      have hrightq (b : B) : algebraMap (Aq ⊗[R] B) D ((1 : Aq) ⊗ₜ[R] b) =
          algebraMap B D b := (IsScalarTower.algebraMap_apply B (Aq ⊗[R] B) D b).symm
      have hsplit (a : A) (b : B) : a ⊗ₜ[R] b =
          (a ⊗ₜ[R] (1 : B)) * ((1 : A) ⊗ₜ[R] b) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      have hsplitq (a : Aq) (b : B) : a ⊗ₜ[R] b =
          (a ⊗ₜ[R] (1 : B)) * ((1 : Aq) ⊗ₜ[R] b) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [hsplitq, hsplit, map_mul, map_mul, hleftq, hrightq, hleft, hright,
        ← IsScalarTower.algebraMap_apply A Aq D]
    | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
  obtain ⟨e₀, he₀⟩ := exists_firstLocalization_cohomology_baseChange R A Aq B D S i
    Q L K (firstLocalizationUnit R A Aq Q) (by intros; rfl)
  let E := ModuleCat.extendScalars (algebraMap (Aq ⊗[R] B) D)
  let ι := (ModuleCat.extendScalarsComp φ (algebraMap (Aq ⊗[R] B) D)).app
    (L.cohomology i)
  have heq : (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).obj
      (L.cohomology i) =
      (ModuleCat.extendScalars ((algebraMap (Aq ⊗[R] B) D).comp φ)).obj
        (L.cohomology i) := congrArg (fun k : A ⊗[R] B →+* D ↦
        (ModuleCat.extendScalars k).obj (L.cohomology i)) hφ.symm
  refine ⟨eqToIso heq ≪≫ ι ≪≫ E.mapIso e₀, ?_⟩
  intro x
  change E.map e₀.hom (ι.hom ((eqToIso heq).hom
    ((1 : D) ⊗ₜ[A ⊗[R] B,algebraMap (A ⊗[R] B) D] x))) = _
  have hgen : (eqToIso heq).hom
      ((1 : D) ⊗ₜ[A ⊗[R] B,algebraMap (A ⊗[R] B) D] x) =
      (1 : D) ⊗ₜ[A ⊗[R] B,(algebraMap (Aq ⊗[R] B) D).comp φ] x :=
    extendScalars_eqToIso_one_tmul _ _ hφ.symm (L.cohomology i) x
  rw [hgen]
  have hι : ι.hom
      ((1 : D) ⊗ₜ[A ⊗[R] B,(algebraMap (Aq ⊗[R] B) D).comp φ] x) =
      (1 : D) ⊗ₜ[Aq ⊗[R] B,algebraMap (Aq ⊗[R] B) D]
        ((1 : Aq ⊗[R] B) ⊗ₜ[A ⊗[R] B,φ] x) :=
    ModuleCat.extendScalarsComp_hom_app_one_tmul φ (algebraMap (Aq ⊗[R] B) D)
      (L.cohomology i) x
  rw [hι]
  have hmap := ModuleCat.ExtendScalars.map_tmul (algebraMap (Aq ⊗[R] B) D)
    e₀.hom (1 : D) ((1 : Aq ⊗[R] B) ⊗ₜ[A ⊗[R] B,φ] x)
  change E.map e₀.hom
      ((1 : D) ⊗ₜ[Aq ⊗[R] B,algebraMap (Aq ⊗[R] B) D]
        ((1 : Aq ⊗[R] B) ⊗ₜ[A ⊗[R] B,φ] x)) = _
  exact hmap.trans (congrArg
    (fun y ↦ (1 : D) ⊗ₜ[Aq ⊗[R] B,algebraMap (Aq ⊗[R] B) D] y) (he₀ x))

end RingTensorCohomology
