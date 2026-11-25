/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClassGenerator

/-!
# Kummer classes with coefficients and the classical Kummer boundary

For a sheaf `A` of `Λ`-modules on `X_ét` with a class `ι : ℤ_X ⟶ A` through which `A` corepresents
the global sections, `Extⁿ(A, N) ⟶ Hⁿ(X, N)` (apply the forgetful functor, precompose with `ι`)
is bijective on a quasi-compact quasi-separated scheme
(`AlgebraicGeometry.Etale.bijective_extToSheafHOf`). For `A = Λ ⊗ ℤ_X` and its unit class this
identifies the Kummer class `κ(u)` with coefficients in `Λ` with the image of the classical
Kummer boundary `δ(u) ∈ H¹(X, μₙ)` under `μₙ ⟶ μₙ ⊗ Λ`
(`AlgebraicGeometry.Etale.kummerClassOf_eq_extToSheafHOf_symm`).
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

section Comparison

variable {X : Scheme.{u}} {A : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
  (ι : (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
    (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶ (forget₂Sheaf Λ X).obj A)

/-- The comparison `Extⁿ(A, N) ⟶ Hⁿ(X, N)` along a class `ι ∈ H⁰(X, A)`: apply the exact
forgetful functor and precompose with `ι`. -/
noncomputable def extToSheafHOf (N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (n : ℕ) :
    Abelian.Ext.{u + 1} A N n →+ Sheaf.H ((forget₂Sheaf Λ X).obj N) n :=
  ((Abelian.Ext.mk₀ ι).precomp _ (zero_add n)).comp ((forget₂Sheaf Λ X).mapExtAddHom _ N n)

lemma extToSheafHOf_apply (N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (n : ℕ)
    (x : Abelian.Ext.{u + 1} A N n) :
    extToSheafHOf Λ ι N n x =
      (Abelian.Ext.mk₀ ι).comp (x.mapExactFunctor (forget₂Sheaf Λ X)) (zero_add n) :=
  rfl

lemma extToSheafHOf_comp_mk₀ {N N' : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)}
    (g : N ⟶ N') (n : ℕ) (x : Abelian.Ext.{u + 1} A N n) :
    extToSheafHOf Λ ι N' n (x.comp (Abelian.Ext.mk₀ g) (add_zero n)) =
      Sheaf.H.map ((forget₂Sheaf Λ X).map g) n (extToSheafHOf Λ ι N n x) := by
  rw [extToSheafHOf_apply, extToSheafHOf_apply, Sheaf.H.map_apply,
    Abelian.Ext.mapExactFunctor_comp, Abelian.Ext.mapExactFunctor_mk₀]
  exact (Abelian.Ext.comp_assoc _ _ _ (zero_add n) (add_zero n) (by omega)).symm

lemma extToSheafHOf_comp_extClass
    {S : ShortComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))} (hS : S.ShortExact)
    (n : ℕ) (y : Abelian.Ext.{u + 1} A S.X₃ n) :
    extToSheafHOf Λ ι S.X₁ (n + 1) (y.comp hS.extClass rfl) =
      (extToSheafHOf Λ ι S.X₃ n y).comp (hS.map_of_exact (forget₂Sheaf Λ X)).extClass rfl := by
  rw [extToSheafHOf_apply, extToSheafHOf_apply, Abelian.Ext.mapExactFunctor_comp,
    Abelian.Ext.mapExactFunctor_extClass]
  exact (Abelian.Ext.comp_assoc _ _ _ (zero_add n) rfl (by omega)).symm

attribute [local instance] Abelian.Ext.subsingleton_of_injective in
/-- On a quasi-compact quasi-separated scheme, `Extⁿ(A, N) ⟶ Hⁿ(X, N)` is bijective as soon as
`A` corepresents the sections over `X` through `ι`: both sides are universal δ-functors which
agree in degree zero. -/
theorem bijective_extToSheafHOf [CompactSpace X] [QuasiSeparatedSpace X]
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
    have hI := subsingleton_H_forget₂_succ_of_injective Λ X I.J n
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

end Comparison

section Kummer

variable (X : Scheme.{u})

/-- The class `ℤ_X ⟶ Λ ⊗ ℤ_X` of the unit section, the class through which
`Λ ⊗ ℤ_X = Λ_X` corepresents global sections. -/
noncomputable def unitIntToExtendScalars :
    (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} ℤ)) ⟶
      (forget₂Sheaf Λ X).obj ((extendScalars Λ X).obj X.constantSheafInt) :=
  (X.constantSheafULiftIntIso).hom ≫ (extendScalarsAdjunction Λ X).unit.app _

lemma bijective_unitIntToExtendScalars_comp
    (N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Function.Bijective (fun f : (extendScalars Λ X).obj X.constantSheafInt ⟶ N ↦
      unitIntToExtendScalars Λ X ≫ (forget₂Sheaf Λ X).map f) := by
  have h : (fun f : (extendScalars Λ X).obj X.constantSheafInt ⟶ N ↦
      unitIntToExtendScalars Λ X ≫ (forget₂Sheaf Λ X).map f) =
      (fun g ↦ (X.constantSheafULiftIntIso).hom ≫ g) ∘
        (extendScalarsAdjunction Λ X).homEquiv _ _ := by
    funext f
    simp only [Function.comp_apply, Adjunction.homEquiv_unit, unitIntToExtendScalars,
      Category.assoc]
    rfl
  rw [h]
  refine Function.Bijective.comp ⟨fun a b hab ↦ (cancel_epi _).1 hab, fun g ↦
    ⟨(X.constantSheafULiftIntIso).inv ≫ g, by simp⟩⟩ (Equiv.bijective _)

variable [HasInvertibleExponent Λ X] [NeZero (ringChar Λ)]

omit [NeZero (ringChar Λ)] in
/-- The comparison of `Ext¹(Λ ⊗ ℤ, μₙ ⊗ Λ)` with `H¹(X, μₙ ⊗ Λ)` sends the class of the Kummer
sequence of `u`, with coefficients extended to `Λ`, to the image of the Kummer class
`δ(u) ∈ H¹(X, μₙ)` under `μₙ ⟶ μₙ ⊗ Λ`. -/
lemma extToSheafHOf_kummerExtClass (u : Γ(X, ⊤)ˣ) :
    extToSheafHOf Λ (unitIntToExtendScalars Λ X) _ 1
        (shortExact_kummerSequence_pullback_map_extendScalars Λ (Scheme.unitToGmSheaf u)
          (fun x ↦ projective_sheafFiber_constantSheafInt (X.uliftPointSmallEtale x))).extClass =
      Sheaf.H.map ((extendScalarsAdjunction Λ X).unit.app (X.rootsOfUnitySheaf (ringChar Λ))) 1
        (X.kummerδ₀ (ringChar Λ) (isUnit_ringChar_of_hasInvertibleExponent X)
          (Additive.ofMul u)) := by
  let adj := extendScalarsAdjunction Λ X
  let φ := Scheme.unitToGmSheaf u
  have hT := shortExact_kummerSequence_pullback_map_extendScalars Λ φ
    (fun x ↦ projective_sheafFiber_constantSheafInt (X.uliftPointSmallEtale x))
  set S := (X.kummerSequence (ringChar Λ)).pullback φ with hSdef
  set T := S.map (extendScalars Λ X) with hTdef
  have hK := X.kummerSequence_shortExact (ringChar Λ)
    (isUnit_ringChar_of_hasInvertibleExponent (Λ := Λ) X)
  have hS : S.ShortExact := hK.pullback φ
  have hTf := hT.map_of_exact (forget₂Sheaf Λ X)
  have h1 : X.kummerδ₀ (ringChar Λ) (isUnit_ringChar_of_hasInvertibleExponent X)
      (Additive.ofMul u) =
        (Abelian.Ext.mk₀ (X.constantSheafULiftIntIso).hom).comp hS.extClass (zero_add 1) := by
    have hn := hS.extClass_naturality hK ((X.kummerSequence (ringChar Λ)).pullbackHom φ)
    rw [Scheme.kummerδ₀_eq_comp_extClass, ← Abelian.Ext.mk₀_comp_mk₀_assoc]
    congr 1
    exact hn.symm.trans (Abelian.Ext.comp_mk₀_id _)
  let m : S ⟶ T.map (forget₂Sheaf Λ X) :=
    { τ₁ := adj.unit.app S.X₁
      τ₂ := adj.unit.app S.X₂
      τ₃ := adj.unit.app S.X₃
      comm₁₂ := (adj.unit.naturality S.f).symm
      comm₂₃ := (adj.unit.naturality S.g).symm }
  have h2 := hS.extClass_naturality hTf m
  rw [Sheaf.H.map_apply, h1, Abelian.Ext.comp_assoc _ _ _ (zero_add 1) (add_zero 1) (by omega)]
  erw [h2]
  refine Eq.trans ?_ (Abelian.Ext.mk₀_comp_mk₀_assoc _ _ _).symm
  rw [extToSheafHOf_apply, Abelian.Ext.mapExactFunctor_extClass]
  rfl

/-- **The Kummer class with coefficients is the image of the classical Kummer class.** On a
quasi-compact quasi-separated scheme `X`, `κ(u) : Λ_X ⟶ Λ_X(1)[1]` corresponds, under
`Ext¹(Λ_X, μₙ ⊗ Λ) ≅ H¹(X, μₙ ⊗ Λ)`, to the image of `δ(u) ∈ H¹(X, μₙ)` under the coefficient
extension `μₙ ⟶ μₙ ⊗ Λ`. -/
theorem kummerClassOf_eq_extToSheafHOf_symm [CompactSpace X] [QuasiSeparatedSpace X]
    (u : Γ(X, ⊤)ˣ) :
    kummerClassOf X Λ u = (constantComplexIsoSingleFunctorExtendScalarsInt X Λ).hom ≫
      Abelian.Ext.homAddEquiv ((AddEquiv.ofBijective _ (bijective_extToSheafHOf Λ
        (unitIntToExtendScalars Λ X) (bijective_unitIntToExtendScalars_comp Λ X) 1 _)).symm
          (Sheaf.H.map ((extendScalarsAdjunction Λ X).unit.app
            (X.rootsOfUnitySheaf (ringChar Λ))) 1
              (X.kummerδ₀ (ringChar Λ) (isUnit_ringChar_of_hasInvertibleExponent X)
                (Additive.ofMul u)))) ≫
      (tateTwistObjectOneIso X Λ).inv⟦(1 : ℤ)⟧' := by
  rw [← extToSheafHOf_kummerExtClass]
  erw [(AddEquiv.ofBijective _ _).symm_apply_apply]
  rw [kummerClassOf, kummerδ, ← ShortComplex.ShortExact.extClass_hom]
  rfl

end Kummer

end AlgebraicGeometry.Etale
