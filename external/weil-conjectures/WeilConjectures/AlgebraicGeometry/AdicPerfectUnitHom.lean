/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Homology.AdicShortComplexCohomologyML
public import WeilConjectures.AlgebraicGeometry.AdicPerfectModuleFunctors
import WeilConjectures.AlgebraicGeometry.AdicPerfectQuotientSectionAdjunction
import WeilConjectures.Mathlib.CategoryTheory.Sites.Abelian

/-! # The unit case of the ordinary quotient Hom comparison

Source: Stacks Project, Tags 093T and 09C6.
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.ConstantCompletion
namespace AlgebraicGeometry.Scheme

attribute [local irreducible] derivedExtension extend change

private def homEvaluation {A : Type w} [CommRing A]
    (M N : ModuleCat.{w} A) (m : M) : ModuleCat.of A (M →ₗ[A] N) ⟶ N :=
  ModuleCat.ofHom ((LinearMap.applyₗ : M →ₗ[A] (M →ₗ[A] N) →ₗ[A] N) m)

private def sectionsEvaluation {A : Type w} [CommRing A]
    (H : ModuleCat.{w} A ⥤ ModuleCat.{w} A) [H.Additive] [H.Linear A]
    (M N : ModuleCat.{w} A) (x : H.obj (ModuleCat.of A (M →ₗ[A] N))) :
    M ⟶ H.obj N :=
  ModuleCat.ofHom
    { toFun := fun m ↦ H.map (homEvaluation M N m) x
      map_add' := fun m m' ↦ by
        have h : homEvaluation M N (m + m') =
            homEvaluation M N m + homEvaluation M N m' := by ext f; exact f.map_add _ _
        rw [h, H.map_add]
        rfl
      map_smul' := fun r m ↦ by
        have h : homEvaluation M N (r • m) = r • homEvaluation M N m := by
          ext f
          exact f.map_smul _ _
        rw [h, H.map_smul]
        rfl }

private def sectionsEvaluationAdd {A : Type w} [CommRing A]
    (H : ModuleCat.{w} A ⥤ ModuleCat.{w} A) [H.Additive] [H.Linear A]
    (M N : ModuleCat.{w} A) :
    H.obj (ModuleCat.of A (M →ₗ[A] N)) →+ (M ⟶ H.obj N) where
  toFun := sectionsEvaluation H M N
  map_zero' := by ext m; exact map_zero (H.map (homEvaluation M N m)).hom
  map_add' x y := by ext m; exact map_add (H.map (homEvaluation M N m)).hom x y

private def adjointHomComparison {A : Type w} [CommRing A]
    {D : Type*} [Category* D] [Preadditive D]
    (H : ModuleCat.{w} A ⥤ ModuleCat.{w} A) [H.Additive] [H.Linear A]
    (F : ModuleCat.{w} A ⥤ D) [F.Additive] (R : D ⥤ ModuleCat.{w} A)
    (adj : F ⊣ R) (e : H ≅ F ⋙ R) (M N : ModuleCat.{w} A) :
    H.obj (ModuleCat.of A (M →ₗ[A] N)) →+ (F.obj M ⟶ F.obj N) :=
  (adj.homAddEquiv M (F.obj N)).symm.toAddMonoidHom.comp
    ((Preadditive.rightComp M (e.hom.app N)).comp (sectionsEvaluationAdd H M N))

private theorem sectionsEvaluation_naturality {A : Type w} [CommRing A]
    (H : ModuleCat.{w} A ⥤ ModuleCat.{w} A) [H.Additive] [H.Linear A]
    (M M' N N' : ModuleCat.{w} A) (a : M' ⟶ M) (b : N ⟶ N')
    (x : H.obj (ModuleCat.of A (M →ₗ[A] N))) :
    sectionsEvaluation H M' N'
        (H.map (ModuleCat.ofHom
          ((LinearMap.llcomp A M' N N' b.hom).comp (LinearMap.lcomp A N a.hom))) x) =
      a ≫ sectionsEvaluation H M N x ≫ H.map b := by
  ext m
  change H.map (homEvaluation M' N' m)
    (H.map (ModuleCat.ofHom
      ((LinearMap.llcomp A M' N N' b.hom).comp (LinearMap.lcomp A N a.hom))) x) =
      H.map b (H.map (homEvaluation M N (a m)) x)
  rw [← ModuleCat.comp_apply, ← H.map_comp, ← ModuleCat.comp_apply, ← H.map_comp]
  rfl

private theorem adjointHomComparison_naturality {A : Type w} [CommRing A]
    {D : Type*} [Category* D] [Preadditive D]
    (H : ModuleCat.{w} A ⥤ ModuleCat.{w} A) [H.Additive] [H.Linear A]
    (F : ModuleCat.{w} A ⥤ D) [F.Additive] (R : D ⥤ ModuleCat.{w} A)
    (adj : F ⊣ R) (e : H ≅ F ⋙ R)
    (M M' N N' : ModuleCat.{w} A) (a : M' ⟶ M) (b : N ⟶ N')
    (x : H.obj (ModuleCat.of A (M →ₗ[A] N))) :
    adjointHomComparison H F R adj e M' N'
        (H.map (ModuleCat.ofHom
          ((LinearMap.llcomp A M' N N' b.hom).comp (LinearMap.lcomp A N a.hom))) x) =
      F.map a ≫ adjointHomComparison H F R adj e M N x ≫ F.map b := by
  apply (adj.homEquiv _ _).injective
  change adj.homEquiv _ _ ((adj.homEquiv _ _).symm _) = _
  rw [Equiv.apply_symm_apply, adj.homEquiv_naturality_left,
    adj.homEquiv_naturality_right]
  change _ = a ≫ adj.homEquiv _ _ ((adj.homEquiv _ _).symm _) ≫ _
  rw [Equiv.apply_symm_apply]
  change sectionsEvaluation H M' N' _ ≫ e.hom.app N' =
    a ≫ (sectionsEvaluation H M N x ≫ e.hom.app N) ≫ R.map (F.map b)
  rw [sectionsEvaluation_naturality, Category.assoc, Category.assoc,
    e.hom.naturality b]
  rfl

private theorem sectionsEvaluation_bijective {A : Type w} [CommRing A]
    (H : ModuleCat.{w} A ⥤ ModuleCat.{w} A) [H.Additive] [H.Linear A]
    (N : ModuleCat.{w} A) :
    Function.Bijective (sectionsEvaluationAdd H (ModuleCat.of A A) N) := by
  let i : ModuleCat.of A (A →ₗ[A] N) ≅ N :=
    (LinearMap.ringLmapEquivSelf A A N).toModuleIso
  have hi : homEvaluation (ModuleCat.of A A) N 1 = i.hom := rfl
  have he : Function.Bijective (H.map i.hom) :=
    ConcreteCategory.bijective_of_isIso (H.map i.hom)
  constructor
  · intro x y h
    apply he.1
    have hh := congrArg (fun f : ModuleCat.of A A ⟶ H.obj N ↦ f 1) h
    change H.map (homEvaluation _ _ 1) x = H.map (homEvaluation _ _ 1) y at hh
    rwa [hi] at hh
  · intro f
    obtain ⟨x, hx⟩ := he.2 (f 1)
    refine ⟨x, ?_⟩
    apply ModuleCat.hom_ext
    apply (LinearMap.ringLmapEquivSelf A A (H.obj N)).injective
    exact hx

private theorem adjointHomComparison_bijective {A : Type w} [CommRing A]
    {D : Type*} [Category* D] [Preadditive D]
    (H : ModuleCat.{w} A ⥤ ModuleCat.{w} A) [H.Additive] [H.Linear A]
    (F : ModuleCat.{w} A ⥤ D) [F.Additive] (R : D ⥤ ModuleCat.{w} A)
    (adj : F ⊣ R) (e : H ≅ F ⋙ R) (N : ModuleCat.{w} A) :
    Function.Bijective (adjointHomComparison H F R adj e (ModuleCat.of A A) N) := by
  have hp : Function.Bijective
      (fun f : ModuleCat.of A A ⟶ H.obj N ↦ f ≫ e.hom.app N) :=
    (Iso.homCongr (Iso.refl (ModuleCat.of A A)) (e.app N)).bijective
  exact (adj.homAddEquiv (ModuleCat.of A A) (F.obj N)).symm.bijective.comp
    (hp.comp (sectionsEvaluation_bijective H N))

private theorem sectionsEvaluation_transition {A : Type w} [CommRing A]
    (H₁ H₀ : ModuleCat.{w} A ⥤ ModuleCat.{w} A)
    [H₁.Additive] [H₁.Linear A] [H₀.Additive] [H₀.Linear A]
    (δ : H₁ ⟶ H₀) (M N : ModuleCat.{w} A)
    (x : H₁.obj (ModuleCat.of A (M →ₗ[A] N))) :
    sectionsEvaluation H₀ M N (δ.app _ x) =
      sectionsEvaluation H₁ M N x ≫ δ.app N := by
  ext m
  exact (ConcreteCategory.congr_hom (δ.naturality (homEvaluation M N m)) x).symm

private theorem successor_mate {A : Type w} [CommRing A]
    {D₁ D₀ : Type*} [Category* D₁] [Category* D₀]
    (F₁ : ModuleCat.{w} A ⥤ D₁) (R₁ : D₁ ⥤ ModuleCat.{w} A)
    (F₀ : ModuleCat.{w} A ⥤ D₀) (R₀ : D₀ ⥤ ModuleCat.{w} A)
    (a₁ : F₁ ⊣ R₁) (a₀ : F₀ ⊣ R₀) (T : D₁ ⥤ D₀)
    (θ : F₁ ⋙ T ≅ F₀) (κ : R₁ ⟶ T ⋙ R₀)
    (hunit : ∀ M, a₀.unit.app M =
      a₁.unit.app M ≫ κ.app (F₁.obj M) ≫ R₀.map (θ.hom.app M))
    (M N : ModuleCat.{w} A) (f : F₁.obj M ⟶ F₁.obj N) :
    a₀.homEquiv M (F₀.obj N)
        (θ.inv.app M ≫ T.map f ≫ θ.hom.app N) =
      a₁.homEquiv M (F₁.obj N) f ≫ κ.app (F₁.obj N) ≫ R₀.map (θ.hom.app N) := by
  rw [a₀.homEquiv_unit, hunit]
  simp only [Functor.map_comp, Functor.comp_obj, Category.assoc]
  rw [← R₀.map_comp_assoc, θ.hom_inv_id_app]
  erw [R₀.map_id]
  rw [Category.id_comp]
  change a₁.unit.app M ≫ κ.app (F₁.obj M) ≫
    (T ⋙ R₀).map f ≫ R₀.map (θ.hom.app N) = _
  rw [← κ.naturality_assoc]
  rw [a₁.homEquiv_unit, Category.assoc]

private theorem adjointHomComparison_transition {A : Type w} [CommRing A]
    {D₁ D₀ : Type*} [Category* D₁] [Category* D₀] [Preadditive D₁] [Preadditive D₀]
    (H₁ H₀ : ModuleCat.{w} A ⥤ ModuleCat.{w} A)
    [H₁.Additive] [H₁.Linear A] [H₀.Additive] [H₀.Linear A]
    (F₁ : ModuleCat.{w} A ⥤ D₁) [F₁.Additive] (R₁ : D₁ ⥤ ModuleCat.{w} A)
    (F₀ : ModuleCat.{w} A ⥤ D₀) [F₀.Additive] (R₀ : D₀ ⥤ ModuleCat.{w} A)
    (a₁ : F₁ ⊣ R₁) (a₀ : F₀ ⊣ R₀) (e₁ : H₁ ≅ F₁ ⋙ R₁) (e₀ : H₀ ≅ F₀ ⋙ R₀)
    (T : D₁ ⥤ D₀) (θ : F₁ ⋙ T ≅ F₀) (κ : R₁ ⟶ T ⋙ R₀)
    (δ : H₁ ⟶ H₀)
    (hunit : ∀ M, a₀.unit.app M =
      a₁.unit.app M ≫ κ.app (F₁.obj M) ≫ R₀.map (θ.hom.app M))
    (hδ : ∀ N, δ.app N ≫ e₀.hom.app N =
      e₁.hom.app N ≫ κ.app (F₁.obj N) ≫ R₀.map (θ.hom.app N))
    (M N : ModuleCat.{w} A) (x : H₁.obj (ModuleCat.of A (M →ₗ[A] N))) :
    adjointHomComparison H₀ F₀ R₀ a₀ e₀ M N (δ.app _ x) =
      θ.inv.app M ≫ T.map (adjointHomComparison H₁ F₁ R₁ a₁ e₁ M N x) ≫ θ.hom.app N := by
  apply (a₀.homEquiv _ _).injective
  rw [successor_mate F₁ R₁ F₀ R₀ a₁ a₀ T θ κ hunit]
  change a₀.homEquiv _ _ ((a₀.homEquiv _ _).symm _) =
    a₁.homEquiv _ _ ((a₁.homEquiv _ _).symm _) ≫ _
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  change sectionsEvaluation H₀ M N (δ.app _ x) ≫ e₀.hom.app N =
    (sectionsEvaluation H₁ M N x ≫ e₁.hom.app N) ≫ _
  rw [sectionsEvaluation_transition, Category.assoc, hδ, Category.assoc]

private theorem adic_sections_linear {A : Type w} [CommRing A]
    {C : Type w} [SmallCategory C] (T : GrothendieckTopology C) (V : C) :
    (AdicCohomology.sections (R := A) T V).Linear A := by
  constructor
  intro M N f r
  change ((constantSheaf T (ModuleCat.{w} A)).map (r • f)).hom.app (op V) = _
  rw [Functor.map_smul]
  rfl

private theorem adic_quotient_linear {A : Type w} [CommRing A]
    (J : Ideal A) (n : ℕ) : (AdicCohomology.quotient J n).Linear A := by
  constructor
  intro M N f r
  ext x
  exact Submodule.Quotient.induction_on _ x (fun _ ↦ rfl)

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall in
/-- The natural ordinary quotient Hom comparison, with its rank-one computation.
Source: Stacks Project, Modules on Sites, Tag 093T; proetale.tex, Tag 09C6,
quotient total-Hom calculation; More on Algebra, Tag 0A8H.
(auxiliary; not a blueprint node).

Proof: use the scalar section adjunction of
adicPerfectQuotientSectionAdjunction. Write H_n for quotient followed by constant
A-module sections, retaining its A-action, F_n for quotient realization, R_n for
its right adjoint, and e_n : H_n = F_n R_n for the section identification.
The functor H_n is A-linear: constant sheafification is A-linear and the algebraic
quotient preserves scalar multiples of maps. For x in H_n(Hom_A(M,N)), evaluation
at m in M gives H_n(ev_m)(x). This is linear in m and additive in x. Postcompose
with e_n(N) and transpose through F_n left adjoint to R_n to define t_n(M,N).
Evaluation commutes with arbitrary pre- and postcomposition; naturality of e_n
and of the adjunction then proves the stated two-variable naturality.

When M=A, evaluation at 1 identifies Hom_A(A,N) with N. Every functor preserves
this isomorphism, and linear maps from A are determined by their value at 1.
Hence x maps bijectively to the linear map a maps to H_n(ev_a)(x). Postcomposition
with e_n(N) and adjunction are bijections, proving the required rank-one claim.
For a successor, naturality of the quotient transition with evaluation identifies
the two evaluation maps after the section transition. Transpose the conjugated
morphism through the lower adjunction. Its transpose is the upper transpose
followed by kappa and R_n of the balancing map: expand homEquiv using the unit,
use the unit compatibility, cancel the inverse balancing maps, and use naturality
of kappa. The section-transition compatibility now proves the successor identity.
The geometric scalar normalization is the remaining separate theorem; no
finite-projective hypothesis or internal-Hom isomorphism is used here. -/
theorem adicPerfectUnitHom (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A)
    (U : coefficientProEtaleSiteModel.{u, v} X) :
    let G := AdicCohomology.sections
      ((coefficientProEtaleModelTopology.{u, v} X).over U) (Over.mk (𝟙 U)) ⋙
        forget₂ (ModuleCat A) AddCommGrpCat
    let H := fun n : ℕ ↦ AdicCohomology.quotient J (n + 1) ⋙ G
    let F := fun n : ℕ ↦ adicPerfectQuotientFunctor X J U n
    ∃ t : ∀ (n : ℕ) (M N : ModuleCat.{max v (u + 1)} A),
        (H n).obj (ModuleCat.of A (M →ₗ[A] N)) →+ ((F n).obj M ⟶ (F n).obj N),
      (∀ (n : ℕ) (N : ModuleCat.{max v (u + 1)} A),
        Function.Bijective (t n (ModuleCat.of A A) N)) ∧
      (∀ (n : ℕ) (M M' N N' : ModuleCat.{max v (u + 1)} A)
        (a : M' ⟶ M) (b : N ⟶ N') (x : (H n).obj (ModuleCat.of A (M →ₗ[A] N))),
        t n M' N' ((H n).map (ModuleCat.ofHom
          ((LinearMap.llcomp A M' N N' b.hom).comp (LinearMap.lcomp A N a.hom))) x) =
          (F n).map a ≫ t n M N x ≫ (F n).map b) ∧
      (∀ (n : ℕ) (M N : ModuleCat.{max v (u + 1)} A)
        (x : (H (n + 1)).obj (ModuleCat.of A (M →ₗ[A] N))),
        t n M N (G.map ((AdicCohomology.transition J
          (Nat.add_le_add_right (Nat.le_succ n) 1)).app
            (ModuleCat.of A (M →ₗ[A] N))) x) =
          ((adicPerfectQuotientModuleStep X J U n).app M).inv ≫
            (change (adicPerfectQuotientScalarStep X J U n)).map (t (n + 1) M N x) ≫
              ((adicPerfectQuotientModuleStep X J U n).app N).hom) := by
  let Gₘ := AdicCohomology.sections (R := A)
    ((coefficientProEtaleModelTopology.{u, v} X).over U) (Over.mk (𝟙 U))
  let Hₘ := fun n : ℕ ↦ AdicCohomology.quotient J (n + 1) ⋙ Gₘ
  let F := fun n : ℕ ↦ adicPerfectQuotientFunctor X J U n
  have : Gₘ.Linear A := adic_sections_linear (A := A) _ _
  have (n : ℕ) : (AdicCohomology.quotient J (n + 1)).Linear A :=
    adic_quotient_linear J (n + 1)
  have (n : ℕ) : (Hₘ n).Linear A := inferInstanceAs
    ((AdicCohomology.quotient J (n + 1) ⋙ Gₘ).Linear A)
  obtain ⟨R, a, e, κ, hunit, hδ⟩ := adicPerfectQuotientSectionAdjunction X J U
  refine ⟨fun n M N ↦ adjointHomComparison (Hₘ n) (F n) (R n) (a n) (e n) M N,
    ?_, ?_, ?_⟩
  · intro n N
    exact adjointHomComparison_bijective (Hₘ n) (F n) (R n) (a n) (e n) N
  · intro n M M' N N' f g x
    exact adjointHomComparison_naturality (Hₘ n) (F n) (R n) (a n) (e n)
      M M' N N' f g x
  · intro n M N x
    exact adjointHomComparison_transition (Hₘ (n + 1)) (Hₘ n)
      (F (n + 1)) (R (n + 1)) (F n) (R n) (a (n + 1)) (a n) (e (n + 1)) (e n)
      (change (adicPerfectQuotientScalarStep X J U n))
      (adicPerfectQuotientModuleStep X J U n) (κ n)
      (Functor.whiskerRight
        (AdicCohomology.transition J (Nat.add_le_add_right (Nat.le_succ n) 1)) Gₘ)
      (hunit n) (hδ n) M N x

end AlgebraicGeometry.Scheme
