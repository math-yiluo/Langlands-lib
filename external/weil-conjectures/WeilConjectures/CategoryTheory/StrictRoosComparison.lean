/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.CategoryTheory.Adjunction.Evaluation
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.Algebra.Homology.KInjectiveProductsTermwise
public import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
public import WeilConjectures.CategoryTheory.RingedStrictTowerHomotopyLimit
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.StrictRoosDerivation
import WeilConjectures.CategoryTheory.StrictRoosNormalization

/-!
# Natural strict Roos comparison with total derived inverse limit

Source: Stacks Project, Cohomology on Sites, Tag 0941, lemma-derived-limit-is-ok,
and the strict-cone naturality and augmentation refinement of its proof
(auxiliary; not a blueprint node).

The complex functor `F` has exactly the displayed shifted-cone objects. The coordinates
`χ` are the canonical shift/cone coordinates, and determine its maps. This spells out
Mathlib's constructions directly; no downstream comparison theorem or its helper
module is imported. `κ` is one fixed descent isomorphism, natural on complexes.
The unit of total derived limit is written using the ordinary limit in complexes;
limits of complexes are termwise, so this is the ordinary unbounded derived functor
of inverse limit, with its canonical termwise-limit presentation.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe uC vC r w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

/-- The strict Roos product cone descends, naturally and with its canonical normalization,
to total derived inverse limit. All occurrences of the comparison use the same `κ` and `ρ`.
For every resolution with injective tower terms, `εI` is exactly the localized inclusion,
and `dI` is exactly the derived-limit identification determined by the unit and `q`.
The equations pin the chain evaluation `a`, the derived evaluation `e`, the augmentation
`b` and its ordinary-limit lift `λ`. The last clause gives the canonical transport between
any two resolutions along a comparison map compatible up to homotopy.

Source: Stacks Project, Tag 0941, lemma-derived-limit-is-ok, proof, with the strict-cone
naturality and augmentation refinement in the blueprint
(auxiliary; not a blueprint node).

Proof plan, following the eight steps of the node:
1. Take the shifted cone of `1-s` on the termwise product. Strict maps act by the product
   map on both coordinates, and a homotopy H acts by (-H,H) in the signed coordinates.
2. Exact countable products preserve quasi-isomorphisms. The cone triangle and
   two-out-of-three show that F inverts quasi-isomorphisms after Q, giving CF and κ.
3. Identify strict module towers with modules on the small tower site. Functorial
   K-injective resolutions with injective tower terms exist by
   prop-pur-kinjective-resolutions-exist. The total-derived-limit dependency identifies
   their termwise limits with RF via its unit η.
4. For an injective tower, each transition splits by the finite-prefix lifting argument.
   Recursively solve y_n-t_n y_(n+1)=x_n using those splittings. Thus 1-s is split epic
   in each degree and its kernel is the ordinary inverse limit.
5. Include that kernel into the cone as (0,z). The quotient has differential
   (-dy-w,dw), contracted by (y,w)↦(0,-y), so the inclusion is a quasi-isomorphism.
   The complex-SES triangle and triangle-morphism isomorphism lemma give εI. Define
   the comparison by Q(F(q)) followed by εI inverse and dI. Its coordinate identities
   give both evaluation equations.
6. Functorial resolutions give F(I(f))ηI=ηJ lim(I(f)). Cancel the inclusions and use
   the derived-limit map computation to obtain strict-map naturality. Localization
   extends this equality to all derived morphisms, giving the natural isomorphism ρ.
7. K-injective comparison gives a:I→J with aq homotopic to q', unique up to homotopy.
   It is a homotopy equivalence. Termwise limit preserves these homotopies; naturality
   of η gives Q(lim a)dJ=dI. The formula for the same fixed ρ holds for every q,
   so both its normalization and evaluations are independent of the resolution.
8. Strict compatibility of γ gives (1-s)γ=0, hence b=(0,γ) is a chain map. The family
   q_nγ_n defines λ by the limit universal property. The coordinate identity
   F(q)b=ηI λ gives Q(b)κρ=Q(λ)dI. The formula for every resolution, together with
   the transport in step 7, proves independence of the augmentation assertion. -/
theorem strictRoosComparison
    {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max uC vC r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC r}]
    (R : Sheaf J RingCat.{max uC vC r})
    (_hcomm : ∀ (U : Cᵒᵖ) (a b : R.obj.obj U), a * b = b * a)
    [HasDerivedCategory.{w} (ringedSiteModules.{max uC vC r} R)]
    [HasDerivedCategory.{w}
      (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R)]
    [HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{max uC vC r} R)]
    (RF : DerivedCategory.{w}
      (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ⥤
        DerivedCategory.{w} (ringedSiteModules.{max uC vC r} R))
    (η : HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
      (lim : (ℕᵒᵖ ⥤ CochainComplex (ringedSiteModules.{max uC vC r} R) ℤ) ⥤ CochainComplex
        (ringedSiteModules.{max uC vC r} R) ℤ) ⋙
        DerivedCategory.Q.{w} ⟶ DerivedCategory.Q.{w} ⋙ RF)
    (_hRF : RF.IsRightDerivedFunctor η
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) (ComplexShape.up ℤ))) :
    ∃ (F : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ ⥤ CochainComplex
      (ringedSiteModules.{max uC vC r} R) ℤ)
      (hobj : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ), F.obj X =
        (CochainComplex.mappingCone (towerTransitionEndomorphism
          (K := fun n : ℕ ↦ X.asFunctor.obj (op n))
          (fun n : ℕ ↦ X.asFunctor.map (homOfLE (Nat.le_succ n)).op)))⟦(-1 : ℤ)⟧)
      (χ : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ) (p : ℤ), (F.obj X).X
        (p + 1) ≅
        (∏ᶜ (fun n : ℕ ↦ X.asFunctor.obj (op n))).X p ⊞
          (∏ᶜ (fun n : ℕ ↦ X.asFunctor.obj (op n))).X (p + 1))
      (CF : DerivedCategory.{w} (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ⥤ DerivedCategory.{w}
        (ringedSiteModules.{max uC vC r} R))
      (κ : F ⋙ DerivedCategory.Q.{w} ≅ DerivedCategory.Q.{w} ⋙ CF)
      (ρ : CF ≅ RF)
      (a : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ) (n : ℕ), F.obj X ⟶
        X.asFunctor.obj (op n))
      (e : ∀ (X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ) (n : ℕ), RF.obj
        (DerivedCategory.Q.obj X) ⟶
        DerivedCategory.Q.obj (X.asFunctor.obj (op n))),
      (∀ (X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ) (p : ℤ), χ X p =
        eqToIso (congrArg (fun K : CochainComplex (ringedSiteModules.{max uC vC r} R) ℤ ↦ K.X (p +
          1)) (hobj X)) ≪≫
          (CochainComplex.mappingCone (towerTransitionEndomorphism
          (K := fun n : ℕ ↦ X.asFunctor.obj (op n))
            (fun n : ℕ ↦ X.asFunctor.map (homOfLE (Nat.le_succ n)).op))).shiftFunctorObjXIso
              (-1) (p + 1) p (add_neg_cancel_right p 1).symm ≪≫
          HomologicalComplex.homotopyCofiber.XIsoBiprod (towerTransitionEndomorphism
          (K := fun n : ℕ ↦ X.asFunctor.obj (op n))
            (fun n : ℕ ↦ X.asFunctor.map (homOfLE (Nat.le_succ n)).op))
              p (p + 1) rfl ≪≫ biprod.braiding _ _) ∧
      (∀ {X Y : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ} (f : X ⟶ Y) (p : ℤ),
        (F.map f).f (p + 1) ≫ (χ Y p).hom = (χ X p).hom ≫
          biprod.map
            ((Limits.Pi.map (fun n : ℕ ↦
              (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).app
                (op n))).f p)
            ((Limits.Pi.map (fun n : ℕ ↦
              (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).app
                (op n))).f (p + 1))) ∧
      (∀ (X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ) (n : ℕ) (p : ℤ), (a X n).f
        (p + 1) =
        (χ X p).hom ≫ biprod.snd ≫
          (Pi.π (fun k : ℕ ↦ X.asFunctor.obj (op k)) n).f (p + 1)) ∧
      (∀ (X : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ) (n : ℕ), κ.hom.app X ≫
        ρ.hom.app (DerivedCategory.Q.obj X) ≫ e X n =
        DerivedCategory.Q.map (a X n)) ∧
      (∀ {X Y : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ} (f : X ⟶ Y),
        DerivedCategory.Q.map (F.map f) ≫ κ.hom.app Y ≫
            ρ.hom.app (DerivedCategory.Q.obj Y) =
          κ.hom.app X ≫ ρ.hom.app (DerivedCategory.Q.obj X) ≫
            RF.map (DerivedCategory.Q.map f)) ∧
      (∀ (X I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ)
        (q : X ⟶ I) [QuasiIso q] [I.IsKInjective]
        (_hIinj : ∀ p : ℤ, Injective (I.X p)),
        ∃ (ι : limit I.asFunctor ⟶ F.obj I)
          (εI : DerivedCategory.Q.{w}.obj (limit I.asFunctor) ≅
            DerivedCategory.Q.obj (F.obj I))
          (dI : DerivedCategory.Q.{w}.obj (limit I.asFunctor) ≅
            RF.obj (DerivedCategory.Q.obj X)),
          (∀ p : ℤ, ι.f (p + 1) ≫ (χ I p).hom =
            biprod.lift 0
              ((Pi.lift (fun n : ℕ ↦ limit.π I.asFunctor (op n))).f (p + 1))) ∧
          QuasiIso (F.map q) ∧ QuasiIso ι ∧
          εI.hom = DerivedCategory.Q.map ι ∧
          dI.hom ≫ RF.map (DerivedCategory.Q.map q) = η.app I ∧
          κ.hom.app X ≫ ρ.hom.app (DerivedCategory.Q.obj X) =
            DerivedCategory.Q.map (F.map q) ≫ εI.inv ≫ dI.hom ∧
          (∀ n : ℕ, ∃ υ : DerivedCategory.Q.{w}.obj (X.asFunctor.obj (op n)) ≅
              DerivedCategory.Q.obj (I.asFunctor.obj (op n)),
            υ.hom = DerivedCategory.Q.map
              ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map q).app (op n)) ∧
            dI.hom ≫ e X n =
              DerivedCategory.Q.map (limit.π I.asFunctor (op n)) ≫ υ.inv) ∧
          (∀ (P : CochainComplex (ringedSiteModules.{max uC vC r} R) ℤ)
            (γ : ∀ n : ℕ, P ⟶ X.asFunctor.obj (op n))
            (_hγ : ∀ n : ℕ, γ (n + 1) ≫
              X.asFunctor.map (homOfLE (Nat.le_succ n)).op = γ n),
            ∃ (b : P ⟶ F.obj X) (lam : P ⟶ limit I.asFunctor),
              (∀ p : ℤ, b.f (p + 1) ≫ (χ X p).hom =
                biprod.lift 0 ((Pi.lift γ).f (p + 1))) ∧
              (∀ n : ℕ, lam ≫ limit.π I.asFunctor (op n) = γ n ≫
                (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map q).app (op n)) ∧
              DerivedCategory.Q.map b ≫ κ.hom.app X ≫
                  ρ.hom.app (DerivedCategory.Q.obj X) =
                DerivedCategory.Q.map lam ≫ dI.hom) ∧
          (∀ (J' : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ)
            (q' : X ⟶ J') [QuasiIso q'] [J'.IsKInjective]
            (_hJinj : ∀ p : ℤ, Injective (J'.X p))
            (dJ : DerivedCategory.Q.{w}.obj (limit J'.asFunctor) ≅
              RF.obj (DerivedCategory.Q.obj X))
            (_hdJ : dJ.hom ≫ RF.map (DerivedCategory.Q.map q') = η.app J')
            (v : I ⟶ J') (_hv : Nonempty (Homotopy (q ≫ v) q')),
            DerivedCategory.Q.map
                (lim.map (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map v)) ≫
              dJ.hom = dI.hom)) := by
  obtain ⟨CF, κ, hCF, hι⟩ :=
    strictRoosDerivation.{uC, vC, r, w} J R _hcomm
  obtain ⟨ρ, e, he, hr⟩ :=
    strictRoosNormalization.{uC, vC, r, w} J R _hcomm RF η _hRF CF κ hCF hι
  refine ⟨roosF, (fun _ ↦ rfl), roosχ, CF, κ, ρ, roosEval, e,
    (fun _ _ ↦ ?_), roosF_map_χ, roosEval_f, he, ?_, hr⟩
  · simp [roosχ]
  · intro X Y f
    have hκ := κ.hom.naturality f
    have hρ := ρ.hom.naturality (DerivedCategory.Q.map f)
    dsimp only [Functor.comp_map] at hκ hρ
    rw [← Category.assoc, hκ, Category.assoc, hρ]

end CategoryTheory
