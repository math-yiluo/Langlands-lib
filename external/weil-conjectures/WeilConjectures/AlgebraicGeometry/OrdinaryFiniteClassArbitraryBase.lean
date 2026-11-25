/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Kummer
import WeilConjectures.AlgebraicGeometry.EtaleModuleInjectiveForgetAcyclic
import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBoundaryComparison

/-! # The normalized class comparison over an arbitrary scheme

The arbitrary-scheme acyclicity theorem removes the quasi-compactness and
quasi-separatedness assumptions in the usual dimension-shifting argument.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Etale

-- Match the proposition arguments of the cached degree-zero and class constructions.
set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

/-- Constants adjunction followed by evaluation of an A-linear map at one. -/
private noncomputable def constantModuleHomEquiv (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (ordinaryFiniteConstant A T ⟶ F) ≃
      F.obj.obj (op (Scheme.Etale.mk (𝟙 T))) := by
  let adj := constantSheafAdj T.smallEtaleTopology (ModuleCat.{u + 1} A)
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T)
  refine (adj.homEquiv _ _).trans {
    toFun := fun f ↦ f.hom 1
    invFun := fun x ↦ ModuleCat.ofHom ((LinearMap.id : A →ₗ[A] A).smulRight x)
    left_inv := ?_
    right_inv := ?_
  }
  · intro f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro a
    change a • f.hom 1 = f.hom a
    simpa using (f.hom.map_smul a (1 : A)).symm
  · intro x
    simp

/-- Integral constant maps identify with sections by evaluation at one. -/
private noncomputable def constantAbelianHomEquiv (T : Scheme.{u})
    (F : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    ((constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ F) ≃
        F.obj.obj (op (Scheme.Etale.mk (𝟙 T))) :=
  ((constantSheafAdj T.smallEtaleTopology AddCommGrpCat.{u + 1}
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T)).homEquiv _ _).trans
    (AddCommGrpCat.uliftZMultiplesAddEquiv
      (F.obj.obj (op (Scheme.Etale.mk (𝟙 T))))).toEquiv

set_option backward.isDefEq.respectTransparency false in
/-- The specified integral generator corepresents global sections of module sheaves. -/
private theorem integralGenerator_bijective (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    Function.Bijective (fun f : ordinaryFiniteConstant A T ⟶ F ↦
      ordinaryFiniteIntegralGenerator A T ≫ (moduleAbelianForget A T).map f) := by
  let e := constantAbelianHomEquiv T ((moduleAbelianForget A T).obj F)
  have h : e ∘ (fun f : ordinaryFiniteConstant A T ⟶ F ↦
      ordinaryFiniteIntegralGenerator A T ≫ (moduleAbelianForget A T).map f) =
      constantModuleHomEquiv A T F := by
    funext f
    dsimp only [Function.comp_apply, e, constantAbelianHomEquiv, Equiv.trans_apply,
      AddEquiv.toEquiv_eq_coe]
    rw [Adjunction.homEquiv_naturality_right]
    simp only [ordinaryFiniteIntegralGenerator, Equiv.apply_symm_apply]
    simp only [AddEquiv.coe_toEquiv]
    erw [AddCommGrpCat.uliftZMultiplesAddEquiv_eq]
    change _ = ((constantSheafAdj T.smallEtaleTopology (ModuleCat.{u + 1} A)
      (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T)).homEquiv _ _ f).hom 1
    erw [AlgebraicGeometry.constantSheafAdj_homEquiv_eq]
    simp [AddEquiv.ulift]
    rfl
  have hcomp : Function.Bijective (e ∘ (fun f : ordinaryFiniteConstant A T ⟶ F ↦
      ordinaryFiniteIntegralGenerator A T ≫ (moduleAbelianForget A T).map f)) :=
    h ▸ (constantModuleHomEquiv A T F).bijective
  exact Function.Bijective.of_comp_left hcomp e.injective

attribute [local instance] Abelian.Ext.subsingleton_of_injective in
private theorem bijective_extToSheafHOf_arbitraryBase
    (Λ : Type (u + 1)) [CommRing Λ] {X : Scheme.{u}}
    {A : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (ι : (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ (forget₂Sheaf Λ X).obj A)
    (hι : ∀ N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ),
      Function.Bijective (fun f : A ⟶ N ↦ ι ≫ (forget₂Sheaf Λ X).map f)) (n : ℕ)
    (N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Function.Bijective (extToSheafHOf Λ ι N n) := by
  induction n generalizing N with
  | zero =>
    have hc : (extToSheafHOf Λ ι N 0) ∘ Abelian.Ext.mk₀ =
        Abelian.Ext.mk₀ ∘ (fun f : A ⟶ N ↦ ι ≫ (forget₂Sheaf Λ X).map f) := by
      funext f
      simp only [Function.comp_apply, extToSheafHOf_apply, Abelian.Ext.mapExactFunctor_mk₀,
        Abelian.Ext.mk₀_comp_mk₀]
    refine (Function.Bijective.of_comp_iff _ (Abelian.Ext.mk₀_bijective _ _)).1 ?_
    rw [hc]
    exact (Abelian.Ext.mk₀_bijective _ _).comp (hι N)
  | succ n ih =>
    let I : InjectivePresentation N := Classical.arbitrary _
    have := I.injective
    let T := ShortComplex.mk I.f (cokernel.π I.f) (cokernel.condition I.f)
    have hT : T.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
    have hS : (T.map (forget₂Sheaf Λ X)).ShortExact := hT.map_of_exact _
    have hz := Scheme.isZero_rightDerived_globalSections_forget_of_injective X Λ I.J n
    let hterminal := MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale X
    let e := NatIso.rightDerived
      (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1} hterminal)
      (n + 1)
    have hz' : IsZero (((Sheaf.sectionsFunctorAt.{u + 1} X.smallEtaleTopology
        (Scheme.Etale.mk (𝟙 X))).rightDerived (n + 1)).obj
          ((forget₂Sheaf Λ X).obj I.J)) := hz.of_iso (e.app _).symm
    have hI := (Sheaf.subsingleton_H_iff_isZero_rightDerived.{u + 1}
      X.smallEtaleTopology hterminal (n + 1) ((forget₂Sheaf Λ X).obj I.J)).2 hz'
    exact AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact
      ((Abelian.Ext.mk₀ T.g).postcomp _ (add_zero n)) (hT.extClass.postcomp _ rfl)
      ((Abelian.Ext.mk₀ ((forget₂Sheaf Λ X).map T.g)).postcomp _ (add_zero n))
      (hS.extClass.postcomp _ rfl)
      (extToSheafHOf Λ ι I.J n) (extToSheafHOf Λ ι T.X₃ n)
      (extToSheafHOf Λ ι N (n + 1))
      (AddMonoidHom.ext fun x ↦ (extToSheafHOf_comp_mk₀ Λ ι T.g n x).symm)
      (AddMonoidHom.ext fun y ↦ (extToSheafHOf_comp_extClass Λ ι hT n y).symm)
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Abelian.Ext.covariant_sequence_exact₃' _ hT n (n + 1) rfl))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Abelian.Ext.covariant_sequence_exact₃' _ hS n (n + 1) rfl))
      (ih I.J).2 (ih T.X₃)
      (fun x ↦ Abelian.Ext.covariant_sequence_exact₁ _ hT x
        (Abelian.Ext.eq_zero_of_injective _) rfl)
      (fun y ↦ Abelian.Ext.covariant_sequence_exact₁ _ hS y (@Subsingleton.elim _ hI _ _) rfl)

/-- The specified class map is bijective over every base scheme.
Source: Stacks Project, Tag 03FD, and the normalized constants adjunction.
(auxiliary; not a blueprint node).

Proof: the constant free rank-one module represents sections, by evaluation at
one; the chosen integral generator realizes exactly this identification. In
degree zero the Ext/cohomology comparison is therefore bijective. Embed a
module sheaf into an injective and take its cokernel. The underlying abelian
sheaf of the injective has zero higher global-section cohomology over an
arbitrary scheme, by Tag 03FD. The two long exact sequences, naturality of the
comparison, and induction identify the cokernels in every successive degree.
The normalized comparison thus is bijective in all degrees. Finally apply the
Ext/derived-morphism equivalence, which is itself bijective. The argument also
applies to the empty scheme and to the zero coefficient ring. -/
theorem ordinaryFiniteClass_bijective_arbitraryBase (A : Type (u + 1)) [CommRing A]
    (T : Scheme.{u}) (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) (n : ℕ) :
    Function.Bijective (ordinaryFiniteClass A T F n) := by
  have h := bijective_extToSheafHOf_arbitraryBase A (ordinaryFiniteIntegralGenerator A T)
    (integralGenerator_bijective A T) n F
  unfold ordinaryFiniteClass
  exact h.comp
    (ordinaryFiniteExtHomEquiv A T (ordinaryFiniteConstant A T) F n).symm.bijective

end AlgebraicGeometry.Etale
