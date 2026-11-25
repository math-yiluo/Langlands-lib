/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModel


public import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModelExtension
public import WeilConjectures.Algebra.Homology.RingTensorCohomology
public import Mathlib.RingTheory.Localization.Basic
import WeilConjectures.Algebra.Homology.BaseDerivedTensorCohomologyModelMap
import WeilConjectures.Algebra.Homology.DerivedTensorSecondLocalizationModels
import WeilConjectures.Algebra.Homology.DerivedTensorBaseLocalizationModels
/-! # Localizing the base and second factor of a derived tensor

Source: Stacks Project, perfect.tex, Tag 0DJ8, localization of the base and
second coefficient ring; More on Algebra, Tag 06Y6.
(blueprint: lem-pc-derived-tensor-base-second-localization-models).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory
open scoped TensorProduct ChangeOfRings

attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace RingTensorCohomology

/-- Changing equal scalar maps gives the identity on pure tensors. -/
private noncomputable def equalScalarComplexIso
    (S T : Type u) [CommRing S] [CommRing T] (f g : S →+* T) (h : f = g)
    (Q : CochainComplex (ModuleCat.{u} S) ℤ) :
    ((ModuleCat.extendScalars f).mapHomologicalComplex (.up ℤ)).obj Q ≅
      ((ModuleCat.extendScalars g).mapHomologicalComplex (.up ℤ)).obj Q :=
  eqToIso (congrArg
    (fun k : S →+* T ↦ ((ModuleCat.extendScalars k).mapHomologicalComplex (.up ℤ)).obj Q) h)

private theorem equalScalarComplexIso_tmul
    (S T : Type u) [CommRing S] [CommRing T] (f g : S →+* T) (h : f = g)
    (Q : CochainComplex (ModuleCat.{u} S) ℤ) (j : ℤ) (d : T) (x : Q.X j) :
    (equalScalarComplexIso S T f g h Q).hom.f j (d ⊗ₜ[S, f] x) = d ⊗ₜ[S, g] x := by
  subst g
  rfl

private theorem equalScalarComplexIso_inv_tmul
    (S T : Type u) [CommRing S] [CommRing T] (f g : S →+* T) (h : f = g)
    (Q : CochainComplex (ModuleCat.{u} S) ℤ) (j : ℤ) (d : T) (x : Q.X j) :
    (equalScalarComplexIso S T f g h Q).inv.f j (d ⊗ₜ[S, g] x) = d ⊗ₜ[S, f] x := by
  subst g
  rfl

variable (R A B Rp Bp D : Type u)
  [CommRing R] [CommRing A] [CommRing B] [CommRing Rp] [CommRing Bp] [CommRing D]
  [Algebra R A] [Algebra R B] [Algebra R Rp] [Algebra B Bp]
  [Algebra R Bp] [Algebra Rp A] [Algebra Rp Bp]
  [tRpA : IsScalarTower R Rp A]
  [tRB : IsScalarTower R B Bp] [tRpB : IsScalarTower R Rp Bp]
  [Algebra (A ⊗[R] B) D] [Algebra (A ⊗[Rp] Bp) D]
  [Algebra A D] [Algebra B D] [Algebra Bp D]
  [tAD : IsScalarTower A (A ⊗[R] B) D]
  [tBD : IsScalarTower B (A ⊗[R] B) D]
  [tApD : IsScalarTower A (A ⊗[Rp] Bp) D]
  [tBpD : IsScalarTower Bp (A ⊗[Rp] Bp) D]
  [tBBpD : IsScalarTower B Bp D]
  [HasDerivedCategory.{w} (ModuleCat.{u} R)]
  [HasDerivedCategory.{w} (ModuleCat.{u} B)]
  [HasDerivedCategory.{w} (ModuleCat.{u} Rp)]
  [HasDerivedCategory.{w} (ModuleCat.{u} Bp)]

include tRpA tRB tRpB tAD tBD tApD tBpD tBBpD in
/-- Change a localized base and localize the second algebra, keeping Q fixed.
Source: Stacks Project, perfect.tex, Tag 0DJ8, second localization identity.
(blueprint: lem-pc-derived-tensor-base-second-localization-models).

Proof: let F -> B[0] be a K-flat R-resolution. As Q is an Rp-complex after
restriction from A, the tensor-localization formula identifies Q tensor_R F
with Q tensor_Rp (Rp tensor_R F), termwise and naturally in Q. Localization is
exact and preserves K-flatness, so Rp tensor_R F resolves Rp tensor_R B.
The map Rp tensor_R B -> Bp is a flat localization: it is the base change of
B -> Bp, and Rp tensor_R Bp = Bp because the R-elements in S are already
units in Bp. Flat second-factor base change identifies the cohomology after
extension to Bp with H(Q tensor-derived_Rp Bp). Both coefficient actions agree,
so this is linear over A tensor_Rp Bp. Tensor associativity followed by
extension to D gives the claimed isomorphism. The maps induced by F -> B[0]
and its localization are the comparison maps; their square commutes on pure
tensors d tensor x. Chain maps give naturality. Unique counit-compatible
identifications of derived functors transport this construction to arbitrary
models; cohomologyIso_smul identifies the A-action, and faithful restriction
of scalars identifies the characterized g and h. Tau is uniquely fixed by its
pure-tensor formula, so the comparison clause holds for every such tau.
The argument applies to unbounded Q and does not require Q to be R-K-flat. -/
theorem derivedTensor_base_second_localization_models
    (S : Submonoid R) [IsLocalization S Rp]
    (T : Submonoid B) [IsLocalization T Bp] (i : ℤ) :
    ∃ e : ∀ (Q : CochainComplex (ModuleCat.{u} A) ℤ)
        (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
        (K : ModuleCat.BaseDerivedTensorCohomologyModel Rp A Bp Q D),
        (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).obj
            (L.cohomology i) ≅
          (ModuleCat.extendScalars (algebraMap (A ⊗[Rp] Bp) D)).obj
            (K.cohomology i),
      (∀ (Q : CochainComplex (ModuleCat.{u} A) ℤ)
          (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
          (K : ModuleCat.BaseDerivedTensorCohomologyModel Rp A Bp Q D)
          (τ : ((ModuleCat.extendScalars ((algebraMap (A ⊗[R] B) D).comp
              (algebraMap A (A ⊗[R] B)))).mapHomologicalComplex (.up ℤ)).obj Q ≅
            ((ModuleCat.extendScalars ((algebraMap (A ⊗[Rp] Bp) D).comp
              (algebraMap A (A ⊗[Rp] Bp)))).mapHomologicalComplex (.up ℤ)).obj Q),
          (∀ (j : ℤ) (d : D) (x : Q.X j),
            τ.hom.f j (d ⊗ₜ[A, (algebraMap (A ⊗[R] B) D).comp
              (algebraMap A (A ⊗[R] B))] x) =
              d ⊗ₜ[A, (algebraMap (A ⊗[Rp] Bp) D).comp
                (algebraMap A (A ⊗[Rp] Bp))] x) →
          L.localizedComparison i ≫ HomologicalComplex.homologyMap τ.hom i =
            (e Q L K).hom ≫ K.localizedComparison i) ∧
      (∀ (Q Q' : CochainComplex (ModuleCat.{u} A) ℤ) (f : Q ⟶ Q')
          (L : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q D)
          (K : ModuleCat.BaseDerivedTensorCohomologyModel Rp A Bp Q D)
          (L' : ModuleCat.BaseDerivedTensorCohomologyModel R A B Q' D)
          (K' : ModuleCat.BaseDerivedTensorCohomologyModel Rp A Bp Q' D)
          (δ : L.derived ⟶ L'.derived) (ε : K.derived ⟶ K'.derived)
          (g : L.cohomology i ⟶ L'.cohomology i)
          (h : K.cohomology i ⟶ K'.cohomology i),
        Functor.whiskerLeft (DerivedCategory.Qh (C := ModuleCat.{u} R)) δ ≫
            L'.counit = L.counit →
        (ModuleCat.restrictScalars.{u}
          (Algebra.TensorProduct.includeRight : B →ₐ[R] A ⊗[R] B).toRingHom).map g ≫
              (L'.cohomologyIso i).hom =
          (L.cohomologyIso i).hom ≫
            (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
              (L.derived.map (DerivedCategory.Qh.map
                ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).map
                  ((restrict R A).map f)))) ≫
            (DerivedCategory.homologyFunctor (ModuleCat.{u} B) i).map
              (δ.app (DerivedCategory.Qh.obj
                ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).obj
                  ((restrict R A).obj Q')))) →
        Functor.whiskerLeft (DerivedCategory.Qh (C := ModuleCat.{u} Rp)) ε ≫
            K'.counit = K.counit →
        (ModuleCat.restrictScalars.{u}
          (Algebra.TensorProduct.includeRight : Bp →ₐ[Rp] A ⊗[Rp] Bp).toRingHom).map h ≫
              (K'.cohomologyIso i).hom =
          (K.cohomologyIso i).hom ≫
            (DerivedCategory.homologyFunctor (ModuleCat.{u} Bp) i).map
              (K.derived.map (DerivedCategory.Qh.map
                ((HomotopyCategory.quotient (ModuleCat.{u} Rp) (.up ℤ)).map
                  ((restrict Rp A).map f)))) ≫
            (DerivedCategory.homologyFunctor (ModuleCat.{u} Bp) i).map
              (ε.app (DerivedCategory.Qh.obj
                ((HomotopyCategory.quotient (ModuleCat.{u} Rp) (.up ℤ)).obj
                  ((restrict Rp A).obj Q')))) →
        (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).map g ≫
            (e Q' L' K').hom =
          (e Q L K).hom ≫
            (ModuleCat.extendScalars (algebraMap (A ⊗[Rp] Bp) D)).map h) := by
  classical
  let : Algebra R D :=
    ((algebraMap (A ⊗[R] B) D).comp (algebraMap R (A ⊗[R] B))).toAlgebra
  let : IsScalarTower R (A ⊗[R] B) D :=
    IsScalarTower.of_algebraMap_eq' rfl
  let : IsScalarTower R A D := IsScalarTower.of_algebraMap_eq' (by
    rw [IsScalarTower.algebraMap_eq R (A ⊗[R] B) D,
      IsScalarTower.algebraMap_eq R A (A ⊗[R] B),
      IsScalarTower.algebraMap_eq A (A ⊗[R] B) D]
    rfl)
  let : IsScalarTower R B D := IsScalarTower.of_algebraMap_eq' (by
    rw [IsScalarTower.algebraMap_eq R (A ⊗[R] B) D,
      IsScalarTower.algebraMap_eq R B (A ⊗[R] B),
      IsScalarTower.algebraMap_eq B (A ⊗[R] B) D]
    rfl)
  let : IsScalarTower R Bp D := IsScalarTower.of_algebraMap_eq' (by
    rw [IsScalarTower.algebraMap_eq R B D, IsScalarTower.algebraMap_eq B Bp D,
      IsScalarTower.algebraMap_eq R B Bp]
    rfl)
  let φ : (A ⊗[R] Bp) →ₐ[R] D := Algebra.TensorProduct.lift
    (IsScalarTower.toAlgHom R A D) (IsScalarTower.toAlgHom R Bp D)
      (fun _ _ ↦ Commute.all _ _)
  let : Algebra (A ⊗[R] Bp) D := φ.toRingHom.toAlgebra
  let : IsScalarTower A (A ⊗[R] Bp) D :=
    IsScalarTower.of_algebraMap_eq' (by
      ext x
      change algebraMap A D x = φ (x ⊗ₜ[R] (1 : Bp))
      simp [φ])
  let : IsScalarTower Bp (A ⊗[R] Bp) D :=
    IsScalarTower.of_algebraMap_eq' (by
      ext x
      change algebraMap Bp D x = φ ((1 : A) ⊗ₜ[R] x)
      simp [φ])
  obtain ⟨e₁, c₁, n₁⟩ := derivedTensor_second_localization_models R A B Bp D T i
  obtain ⟨e₂, c₂, n₂⟩ := derivedTensor_base_localization_models R A Bp Rp D S i
  let U : ∀ Q : CochainComplex (ModuleCat.{u} A) ℤ,
      ModuleCat.BaseDerivedTensorCohomologyModel R A Bp Q D :=
    fun Q ↦ Classical.choice
      (ModuleCat.nonempty_baseDerivedTensorCohomologyModel R A Bp Q D)
  refine ⟨fun Q L K ↦ e₁ Q L (U Q) ≪≫ e₂ Q (U Q) K, ?_, ?_⟩
  · intro Q L K τ hτ
    let f₀ := (algebraMap (A ⊗[R] B) D).comp (algebraMap A (A ⊗[R] B))
    let f₁ := (algebraMap (A ⊗[R] Bp) D).comp (algebraMap A (A ⊗[R] Bp))
    have hf : f₀ = f₁ := by
      dsimp [f₀, f₁]
      rw [← IsScalarTower.algebraMap_eq A (A ⊗[R] B) D,
        ← IsScalarTower.algebraMap_eq A (A ⊗[R] Bp) D]
    let τ₀ := equalScalarComplexIso A D f₀ f₁ hf Q
    let τ₂ := τ₀.symm ≪≫ τ
    have hc₁ := c₁ Q L (U Q) τ₀ (by
      intro j d x
      exact equalScalarComplexIso_tmul A D f₀ f₁ hf Q j d x)
    have hc₂ := c₂ Q (U Q) K τ₂ (by
      intro j d x
      change τ.hom.f j (τ₀.inv.f j _) = _
      rw [equalScalarComplexIso_inv_tmul, hτ])
    have hcomp : τ₀.hom ≫ τ₂.hom = τ.hom := by simp [τ₂]
    change L.localizedComparison i ≫ HomologicalComplex.homologyMap τ.hom i =
      (e₁ Q L (U Q)).hom ≫ (e₂ Q (U Q) K).hom ≫ K.localizedComparison i
    rw [← hcomp, HomologicalComplex.homologyMap_comp, ← Category.assoc, hc₁,
      Category.assoc]
    exact congrArg (fun k ↦ (e₁ Q L (U Q)).hom ≫ k) hc₂
  · intro Q Q' f L K L' K' δ ε g h hδ hg hε hh
    obtain ⟨δ₀, g₀, hδ₀, hg₀⟩ := exists_baseDerivedTensorCohomologyModelMap
      R A Bp D Q Q' f (U Q) (U Q') i
    have hn₁ := n₁ Q Q' f L (U Q) L' (U Q') δ δ₀ g g₀ hδ hg hδ₀ hg₀
    have hn₂ := n₂ Q Q' f (U Q) K (U Q') K' δ₀ ε g₀ h hδ₀ hg₀ hε hh
    change (ModuleCat.extendScalars (algebraMap (A ⊗[R] B) D)).map g ≫
        ((e₁ Q' L' (U Q')).hom ≫ (e₂ Q' (U Q') K').hom) =
      ((e₁ Q L (U Q)).hom ≫ (e₂ Q (U Q) K).hom) ≫
        (ModuleCat.extendScalars (algebraMap (A ⊗[Rp] Bp) D)).map h
    rw [← Category.assoc, hn₁, Category.assoc, hn₂, Category.assoc]

end RingTensorCohomology
