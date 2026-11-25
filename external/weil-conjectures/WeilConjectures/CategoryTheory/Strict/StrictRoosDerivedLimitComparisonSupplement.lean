/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
import WeilConjectures.CategoryTheory.StrictRoosComparison
import WeilConjectures.CategoryTheory.Ringed.RingedStrictTowerHomotopyLimitOfUniverses
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
import WeilConjectures.CategoryTheory.StrictRoosDerivation
import WeilConjectures.CategoryTheory.StrictRoosModel
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import Mathlib.CategoryTheory.Whiskering
import Mathlib.Algebra.Homology.Functor
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import WeilConjectures.Algebra.Homology.RoosComplex
import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Generator.Basic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Sites.LocallyBijective
import WeilConjectures.CategoryTheory.Sites.RGammaDerivedLimit
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.CategoryTheory.Adjunction.Evaluation
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.FunctorCategory
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.CategoryTheory.StrictRoosNormalization
import Mathlib.CategoryTheory.Generator.Presheaf
import Mathlib.Algebra.Homology.DerivedCategory.KInjective

/-!
# The strict Roos comparison and its evaluation maps

Source: Stacks Project, Derived Categories, Tags 07KC and 08TC, and Cohomology on Sites,
Tags 0940 and 0941; the explicit comparison and evaluation square in the DAG proof
(blueprint: lem-sf-strict-roos-derived-limit-comparison).

The helper definitions spell out the products, transition endomorphism and signed cone
already introduced by this statement. The comparison maps are uniquely specified by
coordinates, rather than chosen as arbitrary isomorphisms of derived-limit triangles.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v w uC vC r

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

variable {A : Type u} [Category.{v} A] [Abelian A] [HasCountableProducts A]

/-- The termwise product of the evaluated strict tower complexes. Index `n` means the
paper's positive index `n+1`. Source: Stacks 07KC and 08TC
(blueprint: lem-sf-strict-roos-derived-limit-comparison). -/
def strictRoosProduct (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) : CochainComplex A ℤ :=
  ∏ᶜ (fun n : ℕ ↦ X.asFunctor.obj (op n))

/-- The existing transition endomorphism, applied in the category of complexes.
Source: Stacks 08TC (blueprint: lem-sf-strict-roos-derived-limit-comparison). -/
def strictRoosEndomorphism (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    strictRoosProduct X ⟶ strictRoosProduct X :=
  towerTransitionEndomorphism
    (fun n ↦ X.asFunctor.map (homOfLE (Nat.le_succ n)).op)

/-- The actual shifted mapping cone of `1-s`. In the coordinate order `(y,x)`, its
 differential is `(-dy-(1-s)x,dx)`. Source: Stacks 07KC and 08TC
(blueprint: lem-sf-strict-roos-derived-limit-comparison). -/
def strictRoosComplex (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) : CochainComplex A ℤ :=
  (CochainComplex.mappingCone (strictRoosEndomorphism X))⟦(-1 : ℤ)⟧

/-- The degree `p+1` coordinates `(y,x)`, interchanging Mathlib's source-first cone
summands. All transports are the canonical shift and cone isomorphisms.
Source: Stacks 08TC and the displayed differential of the node
(blueprint: lem-sf-strict-roos-derived-limit-comparison). -/
def strictRoosCoordinates (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) :
    (strictRoosComplex X).X (p + 1) ≅
      (strictRoosProduct X).X p ⊞ (strictRoosProduct X).X (p + 1) :=
  (CochainComplex.mappingCone (strictRoosEndomorphism X)).shiftFunctorObjXIso
      (-1) (p + 1) p (by omega) ≪≫
    HomologicalComplex.homotopyCofiber.XIsoBiprod (strictRoosEndomorphism X)
      p (p + 1) rfl ≪≫
    biprod.braiding _ _

/-- The product map induced by a strict map of tower complexes, on both cone coordinates.
Source: Stacks 07KC and the strict naturality square of the DAG proof
(blueprint: lem-sf-strict-roos-derived-limit-comparison). -/
def strictRoosProductMap {X I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ} (f : X ⟶ I) :
    strictRoosProduct X ⟶ strictRoosProduct I :=
  Limits.Pi.map (fun n ↦
    (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f).app (op n))

set_option backward.isDefEq.respectTransparency false in
private def strictTowerLimitIso [HasLimitsOfShape ℕᵒᵖ A] :
    HomologicalComplex.complexOfFunctorsToFunctorToComplex ⋙
      (lim : (ℕᵒᵖ ⥤ CochainComplex A ℤ) ⥤ CochainComplex A ℤ) ≅
        (lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ) :=
  NatIso.ofComponents (fun X ↦
    limit.isoLimitCone ⟨HomologicalComplex.coneOfHasLimitEval X.asFunctor,
      HomologicalComplex.isLimitConeOfHasLimitEval X.asFunctor⟩) (by
    intro X Y f
    apply (HomologicalComplex.isLimitConeOfHasLimitEval Y.asFunctor).hom_ext
    intro n
    ext p
    have hπ (Z : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
        (limit.isoLimitCone ⟨HomologicalComplex.coneOfHasLimitEval Z.asFunctor,
          HomologicalComplex.isLimitConeOfHasLimitEval Z.asFunctor⟩).hom.f p ≫
            limit.π (Z.X p) n = (limit.π Z.asFunctor n).f p := by
      simpa only [HomologicalComplex.comp_f,
        HomologicalComplex.coneOfHasLimitEval_π_app_f, HomologicalComplex.asFunctor,
        HomologicalComplex.eval, Functor.comp] using
        congrArg (fun f ↦ HomologicalComplex.Hom.f f p)
          (limit.isoLimitCone_hom_π
            ⟨HomologicalComplex.coneOfHasLimitEval Z.asFunctor,
              HomologicalComplex.isLimitConeOfHasLimitEval Z.asFunctor⟩ n)
    have hm := congrArg (fun f ↦ HomologicalComplex.Hom.f f p)
      (limMap_π (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f) n)
    dsimp at hπ hm ⊢
    simp only [HomologicalComplex.coneOfHasLimitEval_π_app_f,
      HomologicalComplex.asFunctor, HomologicalComplex.eval, Functor.comp] at hπ hm ⊢
    calc
      _ = (limMap (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f)).f p ≫
          (limit.π Y.asFunctor n).f p := by
        rw [Category.assoc, hπ Y]
        rfl
      _ = (limit.π X.asFunctor n).f p ≫ (f.f p).app n := hm
      _ = _ := by
        rw [Category.assoc]
        change _ = _ ≫ limMap (f.f p) ≫ limit.π (Y.X p) n
        rw [limMap_π, ← Category.assoc, hπ X]
        rfl)

set_option backward.isDefEq.respectTransparency false in
/-- Both arrows of the prescribed strict Roos zigzag are quasi-isomorphisms, for an
arbitrary K-injective tower resolution, and its resulting isomorphism respects every
evaluation. `ε` is the image of the inclusion `η`; `θ` is precisely `Roos(u)` followed
by its inverse. `υ` is the image of the evaluated resolution, so its inverse gives
exactly the specified evaluation on the total derived limit, represented by `lim I`.

The sectionwise commutativity binder is the commutative-ring-sheaf hypothesis. The
module universe contains both site universes, without equating them. The sheafification
instances and the derived-category instance only supply the standard category structures.

Source: Stacks 07KC, 08TC, 0940 and 0941; explicit arbitrary-K-injective extension and
evaluation square in the node's proof
(blueprint: lem-sf-strict-roos-derived-limit-comparison).

Proof plan:
1. Exact countable products preserve quasi-isomorphisms (Stacks 07KC). Naturality of
   towerTransitionEndomorphism makes the two product maps commute with `1-s`; the
   induced cone map is `ρ` with the displayed coordinates. Thus `ρ` is a quasi-isomorphism,
   as also follows from the functor clause of lem-weil-strict-roos-comparison.
   Evaluation is exact by lem-weil-tower-category-levelwise-abelian.
2. The tower category is Grothendieck by lem-weil-pbc-small-module-diagrams-grothendieck.
   Apply lem-pur-kinjective-degreewise-existence to resolve I by a K-injective J with
   injective terms. The map I to J is a homotopy equivalence by
   lem-weil-pbc-kinjective-hom-derived. The injective-term normalization of
   lem-weil-strict-roos-comparison makes the inclusion lim J to Roos(J) a quasi-isomorphism.
3. Termwise limit preserves the homotopies of this equivalence. The coordinate identity
   Roos(v) η_I = η_J lim(v) and two-out-of-three on cohomology make the prescribed η_I
   a quasi-isomorphism, without requiring I to have injective terms.
4. lem-weil-pbc-ringed-strict-tower-homotopy-limit identifies lim I with total derived
   inverse limit. Set θ = Roos(u) η_I inverse. The chain projections a_n satisfy
   a_n^I η_I = pr_n and a_n^I Roos(u) = u_n a_n^X. Inverting the evaluated resolution
   gives e_n θ = a_n^X, for the actual zigzag. -/
theorem strictRoosDerivedLimitComparison
    {C : Type uC} [Category.{vC} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max uC vC r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max uC vC r}]
    (R : Sheaf J RingCat.{max uC vC r})
    (_hcomm : ∀ (U : Cᵒᵖ) (a b : R.obj.obj U), a * b = b * a)
    [HasDerivedCategory.{w} (ringedSiteModules.{max uC vC r} R)]
    [HasExactLimitsOfShape (Discrete ℕ) (ringedSiteModules.{max uC vC r} R)]
    (X I : CochainComplex (ℕᵒᵖ ⥤ ringedSiteModules.{max uC vC r} R) ℤ)
    (u : X ⟶ I) [QuasiIso u] [I.IsKInjective] :
    ∃ (ρ : strictRoosComplex X ⟶ strictRoosComplex I)
      (η : limit I.asFunctor ⟶ strictRoosComplex I)
      (a : ∀ n : ℕ, strictRoosComplex X ⟶ X.asFunctor.obj (op n)),
      (∀ p : ℤ, ρ.f (p + 1) ≫ (strictRoosCoordinates I p).hom =
        (strictRoosCoordinates X p).hom ≫
          biprod.map ((strictRoosProductMap u).f p) ((strictRoosProductMap u).f (p + 1))) ∧
      (∀ p : ℤ, η.f (p + 1) ≫ (strictRoosCoordinates I p).hom =
        biprod.lift 0 ((Pi.lift (fun n : ℕ ↦ limit.π I.asFunctor (op n))).f (p + 1))) ∧
      (∀ (n : ℕ) (p : ℤ), (a n).f (p + 1) =
        (strictRoosCoordinates X p).hom ≫ biprod.snd ≫
          (Pi.π (fun k : ℕ ↦ X.asFunctor.obj (op k)) n).f (p + 1)) ∧
      QuasiIso ρ ∧ QuasiIso η ∧
      ∃ (ε : DerivedCategory.Q.{w}.obj (limit I.asFunctor) ≅
          DerivedCategory.Q.{w}.obj (strictRoosComplex I))
        (θ : DerivedCategory.Q.{w}.obj (strictRoosComplex X) ≅
          DerivedCategory.Q.{w}.obj (limit I.asFunctor)),
        ε.hom = DerivedCategory.Q.{w}.map η ∧
        θ.hom = DerivedCategory.Q.{w}.map ρ ≫ ε.inv ∧
        ∀ n : ℕ, ∃ υ : DerivedCategory.Q.{w}.obj (X.asFunctor.obj (op n)) ≅
            DerivedCategory.Q.{w}.obj (I.asFunctor.obj (op n)),
          υ.hom = DerivedCategory.Q.{w}.map
            ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map u).app (op n)) ∧
          θ.hom ≫ DerivedCategory.Q.{w}.map (limit.π I.asFunctor (op n)) ≫ υ.inv =
            DerivedCategory.Q.{w}.map (a n) := by
  let Qw := DerivedCategory.Q.{w} (C := ringedSiteModules.{max uC vC r} R)
  let A := ringedSiteModules.{max uC vC r} R
  let := HasDerivedCategory.standard A
  let := HasDerivedCategory.standard (ℕᵒᵖ ⥤ A)
  obtain ⟨RF, δ, hRF, _⟩ :=
    ringedStrictTowerHomotopyLimitOfUniverses.{max uC vC r + 1, uC, vC, r} J R _hcomm
  let δ' := (Functor.isoWhiskerRight (strictTowerLimitIso (A := A))
    DerivedCategory.Q).hom ≫ δ
  have hRF' : RF.IsRightDerivedFunctor δ'
      (HomologicalComplex.quasiIso (ℕᵒᵖ ⥤ A) (.up ℤ)) := by
    apply (Functor.isRightDerivedFunctor_iff_isLeftKanExtension _ _ _).2
    apply (Functor.isLeftKanExtension_iff_of_iso₂ δ' δ
      (Functor.isoWhiskerRight (strictTowerLimitIso (A := A)) DerivedCategory.Q)
      (Iso.refl RF) (by simp [δ'])).2
    exact (Functor.isRightDerivedFunctor_iff_isLeftKanExtension _ _ _).1 hRF
  obtain ⟨F, hobj, χ, CF, κ, c, a, e, hχ, hmap, ha, he, hnat, hnorm⟩ :=
    strictRoosComparison.{uC, vC, r, max uC vC r + 1} J R _hcomm RF δ' hRF'
  let : IsGrothendieckAbelian.{max uC vC r} A :=
    SheafOfModules.isGrothendieckAbelianOfUniverses.{uC, vC, max uC vC r, 0} J R
  let : HasFilteredColimitsOfSize.{max uC vC r, max uC vC r} (ℕᵒᵖ ⥤ A) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  let : AB5OfSize.{max uC vC r, max uC vC r} (ℕᵒᵖ ⥤ A) :=
    ⟨fun _ _ _ ↦ inferInstance⟩
  let : IsGrothendieckAbelian.{max uC vC r} (ℕᵒᵖ ⥤ A) := {}
  let K := (CochainComplex.kInjectiveResolutionFunctor.{max uC vC r} (ℕᵒᵖ ⥤ A)).obj I
  let v : I ⟶ K := (CochainComplex.toKInjectiveResolution.{max uC vC r} (ℕᵒᵖ ⥤ A)).app I
  have hv : QuasiIso v :=
    (CochainComplex.monoQuasiIso_toKInjectiveResolution_app.{max uC vC r} _ I).2
  obtain ⟨ι, εK, dK, hι, _, hιqi, hεK, hdK, hcK, heK, haug, htransport⟩ :=
    hnorm I K v (fun p ↦ inferInstance)
  obtain ⟨b, lam, hb, hlam, hblam⟩ :=
    haug (limit I.asFunctor) (fun n ↦ limit.π I.asFunctor (op n)) (fun n ↦ by
      exact limit.w I.asFunctor (homOfLE (Nat.le_succ n)).op)
  clear hnorm htransport hι hιqi hεK hdK hcK heK haug
  have hlam' : lam = limMap
      (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map v) := by
    apply limit.hom_ext
    intro n
    exact (hlam n.unop).trans
      (limMap_π (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map v) n).symm
  have hlimqi : QuasiIso lam := by
    obtain ⟨hvEquiv, hve⟩ := (CochainComplex.IsKInjective.quasiIso_iff v).1 hv
    let : (lim : (ℕᵒᵖ ⥤ A) ⥤ A).Additive :=
      Functor.additive_of_preserves_binary_products _
    let eL := (lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomotopyEquiv hvEquiv
    have heL : QuasiIso ((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex
        (.up ℤ) |>.map v) := by
      rw [← hve]
      exact eL.quasiIso_hom
    rw [hlam']
    have hn := (strictTowerLimitIso (A := A)).hom.naturality v
    have heq : limMap (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map v) =
        (strictTowerLimitIso (A := A)).hom.app I ≫
          ((lim : (ℕᵒᵖ ⥤ A) ⥤ A).mapHomologicalComplex (.up ℤ)).map v ≫
            (strictTowerLimitIso (A := A)).inv.app K := by
      simpa only [Functor.comp_map, lim, Category.assoc,
        Iso.hom_inv_id_app, Category.comp_id] using
        (congrArg (fun f ↦ f ≫ (strictTowerLimitIso (A := A)).inv.app K) hn)
    rw [heq]
    infer_instance
  have hbqi : QuasiIso b := by
    apply (DerivedCategory.isIso_Q_map_iff_quasiIso A b).1
    have hi : IsIso (DerivedCategory.Q.map b ≫ κ.hom.app I ≫
        c.hom.app (DerivedCategory.Q.obj I)) := by
      rw [hblam]
      infer_instance
    exact (isIso_comp_right_iff _ (κ.hom.app I ≫ c.hom.app _)).1 hi
  have hFqi : QuasiIso (F.map u) := by
    apply (DerivedCategory.isIso_Q_map_iff_quasiIso A (F.map u)).1
    have hi : IsIso (DerivedCategory.Q.map (F.map u) ≫ κ.hom.app I ≫
        c.hom.app (DerivedCategory.Q.obj I)) := by
      rw [hnat u]
      infer_instance
    exact (isIso_comp_right_iff _ (κ.hom.app I ≫ c.hom.app _)).1 hi
  let φ (T : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) : F.obj T ≅ strictRoosComplex T :=
    eqToIso (hobj T)
  have hφ (T : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (p : ℤ) :
      (φ T).hom.f (p + 1) ≫ (strictRoosCoordinates T p).hom = (χ T p).hom := by
    rw [hχ]
    dsimp only [φ, strictRoosCoordinates, strictRoosComplex, strictRoosEndomorphism,
      strictRoosProduct]
    simp only [Iso.trans_hom, eqToIso.hom, HomologicalComplex.eqToHom_f]
  let ρ : strictRoosComplex X ⟶ strictRoosComplex I :=
    (φ X).inv ≫ F.map u ≫ (φ I).hom
  let η : limit I.asFunctor ⟶ strictRoosComplex I := b ≫ (φ I).hom
  let aX (n : ℕ) : strictRoosComplex X ⟶ X.asFunctor.obj (op n) :=
    (φ X).inv ≫ a X n
  have hρ (p : ℤ) : ρ.f (p + 1) ≫ (strictRoosCoordinates I p).hom =
      (strictRoosCoordinates X p).hom ≫
        biprod.map ((strictRoosProductMap u).f p) ((strictRoosProductMap u).f (p + 1)) := by
    dsimp [ρ]
    simp only [Category.assoc, hφ]
    rw [hmap]
    rw [← hφ]
    simp [strictRoosProductMap, strictRoosProduct]
    rfl
  have hη (p : ℤ) : η.f (p + 1) ≫ (strictRoosCoordinates I p).hom =
      biprod.lift 0 ((Pi.lift (fun n : ℕ ↦ limit.π I.asFunctor (op n))).f (p + 1)) := by
    simpa only [η, HomologicalComplex.comp_f, Category.assoc, hφ,
      strictRoosProduct] using hb p
  have haX (n : ℕ) (p : ℤ) : (aX n).f (p + 1) =
      (strictRoosCoordinates X p).hom ≫ biprod.snd ≫
        (Pi.π (fun k : ℕ ↦ X.asFunctor.obj (op k)) n).f (p + 1) := by
    change (φ X).inv.f (p + 1) ≫ (a X n).f (p + 1) = _
    rw [ha X n p, ← hφ X p]
    have hcancel : (φ X).inv.f (p + 1) ≫ (φ X).hom.f (p + 1) = 𝟙 _ := by
      exact congrArg (fun f ↦ HomologicalComplex.Hom.f f (p + 1)) (φ X).inv_hom_id
    dsimp only [strictRoosProduct]
    simp only [← Category.assoc, hcancel, Category.id_comp]
  have hρqi : QuasiIso ρ := by dsimp [ρ]; infer_instance
  have hηqi : QuasiIso η := by dsimp [η]; infer_instance
  let aI (n : ℕ) : strictRoosComplex I ⟶ I.asFunctor.obj (op n) :=
    (φ I).inv ≫ a I n
  have haI (n : ℕ) (p : ℤ) : (aI n).f (p + 1) =
      (strictRoosCoordinates I p).hom ≫ biprod.snd ≫
        (Pi.π (fun k : ℕ ↦ I.asFunctor.obj (op k)) n).f (p + 1) := by
    change (φ I).inv.f (p + 1) ≫ (a I n).f (p + 1) = _
    rw [ha I n p, ← hφ I p]
    have hcancel : (φ I).inv.f (p + 1) ≫ (φ I).hom.f (p + 1) = 𝟙 _ := by
      exact congrArg (fun f ↦ HomologicalComplex.Hom.f f (p + 1)) (φ I).inv_hom_id
    dsimp only [strictRoosProduct]
    simp only [← Category.assoc, hcancel, Category.id_comp]
  have hηa (n : ℕ) : η ≫ aI n = limit.π I.asFunctor (op n) := by
    apply HomologicalComplex.Hom.ext
    funext k
    obtain ⟨p, rfl⟩ : ∃ p : ℤ, k = p + 1 := ⟨k - 1, by omega⟩
    simp only [HomologicalComplex.comp_f, haI, ← Category.assoc, hη]
    have hprod := congrArg (fun f ↦ HomologicalComplex.Hom.f f (p + 1))
      (Pi.lift_comp_π (fun n : ℕ ↦ limit.π I.asFunctor (op n)) n)
    simpa only [strictRoosProduct, HomologicalComplex.comp_f, biprod.lift_snd,
      Category.assoc, biprod.lift_snd_assoc] using hprod
  have hρa (n : ℕ) : ρ ≫ aI n = aX n ≫
      (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map u).app (op n) := by
    apply HomologicalComplex.Hom.ext
    funext k
    obtain ⟨p, rfl⟩ : ∃ p : ℤ, k = p + 1 := ⟨k - 1, by omega⟩
    simp only [HomologicalComplex.comp_f, haI, haX]
    have hprod := congrArg (fun f ↦ HomologicalComplex.Hom.f f (p + 1))
      (Pi.map_π (fun n : ℕ ↦
        (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map u).app (op n)) n)
    change (strictRoosProductMap u).f (p + 1) ≫
      (Pi.π (fun k : ℕ ↦ I.asFunctor.obj (op k)) n).f (p + 1) =
      (Pi.π (fun k : ℕ ↦ X.asFunctor.obj (op k)) n).f (p + 1) ≫
        ((HomologicalComplex.complexOfFunctorsToFunctorToComplex.map u).app (op n)).f
          (p + 1) at hprod
    calc
      _ = (ρ.f (p + 1) ≫ (strictRoosCoordinates I p).hom) ≫ biprod.snd ≫
          (Pi.π (fun k : ℕ ↦ I.asFunctor.obj (op k)) n).f (p + 1) := by
        simp only [Category.assoc]
      _ = _ := by
        rw [hρ]
        dsimp only [strictRoosProduct, strictRoosProductMap] at hprod ⊢
        simp only [Category.assoc, biprod.map_snd_assoc, hprod]
  let ε : Qw.obj (limit I.asFunctor) ≅
      Qw.obj (strictRoosComplex I) :=
    asIso (Qw.map η)
  let θ : Qw.obj (strictRoosComplex X) ≅
      Qw.obj (limit I.asFunctor) :=
    asIso (Qw.map ρ) ≪≫ ε.symm
  refine ⟨ρ, η, aX, hρ, hη, haX, hρqi, hηqi, ε, θ, rfl, rfl, ?_⟩
  intro n
  let un := (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map u).app (op n)
  have hun : QuasiIso un :=
    (HomologicalComplex.quasiIso_iff_evaluation u).1 inferInstance (op n)
  let υ : Qw.obj (X.asFunctor.obj (op n)) ≅
      Qw.obj (I.asFunctor.obj (op n)) :=
    asIso (Qw.map un)
  refine ⟨υ, rfl, ?_⟩
  change (Qw.map ρ ≫ ε.inv) ≫
    Qw.map (limit.π I.asFunctor (op n)) ≫ υ.inv = _
  let Q := Qw
  have hεa : ε.hom ≫ Q.map (aI n) = Q.map (limit.π I.asFunctor (op n)) := by
    exact (Q.map_comp η (aI n)).symm.trans (congrArg Q.map (hηa n))
  have hρa' : Q.map ρ ≫ Q.map (aI n) = Q.map (aX n) ≫ Q.map un := by
    exact (Q.map_comp ρ (aI n)).symm.trans
      ((congrArg Q.map (hρa n)).trans (Q.map_comp (aX n) un))
  change (Q.map ρ ≫ ε.inv) ≫ Q.map (limit.π I.asFunctor (op n)) ≫ υ.inv = _
  rw [← hεa]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Category.assoc, hρa']
  change (Q.map (aX n) ≫ υ.hom) ≫ υ.inv = _
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rfl

end CategoryTheory
