/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerP1.TowerP1LevelWords
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteRootSiteComparison
import all WeilConjectures.AlgebraicGeometry.Finite.FiniteRootSiteComparison
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteTateLineUniversal

/-! # Intrinsic realization of the finite root tensor

Source: Stacks Project, Tags 03CY and 03EK; diagonal-tower trace (1).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry.ProEtale.SpTowerP1
open SpTowerClasses
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private abbrev IntrinsicModules (T : Scheme.{u}) (A : Type u) [CommRing A] :=
  SheafOfModules.{u + 1} ((sheafCompose (Scheme.ProEt.topology T)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj (Scheme.proEtaleConstantRing T A))

private def fixedRestriction (T : Scheme.{u}) (A : Type u) [CommRing A]
    (N : IntrinsicModules T A) :
    Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A)) := by
  let P := (PresheafOfModules.restrictScalars
    (finiteCoefficientIntrinsicScalarMap T A)).obj N.val
  let F : T.ProEtᵒᵖ ⥤ ModuleCat.{u + 1} (ULift.{u + 1} A) :=
    { obj := P.obj
      map := P.map
      map_id U := by ext x; exact ConcreteCategory.congr_hom (P.presheaf.map_id U) x
      map_comp f g := by
        ext x
        exact ConcreteCategory.congr_hom (P.presheaf.map_comp f g) x }
  exact ⟨F, Presheaf.isSheaf_of_isSheaf_comp (Scheme.ProEt.topology T) F
    (forget₂ (ModuleCat.{u + 1} (ULift.{u + 1} A)) AddCommGrpCat.{u + 1}) N.isSheaf⟩

private def fixedRestrictionHomEquiv (T : Scheme.{u}) (A : Type u) [CommRing A]
    (M : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A)))
    (N : IntrinsicModules T A) :
    ((finiteCoefficientModulePresheaf T.ProEt (ULift.{u + 1} A)).obj M.obj ⟶
      (PresheafOfModules.restrictScalars
        (finiteCoefficientIntrinsicScalarMap T A)).obj N.val) ≃
      (M ⟶ fixedRestriction T A N) where
  toFun f := ⟨{
    app := f.app
    naturality := by
      intro U V g
      ext x
      exact ConcreteCategory.congr_hom (f.naturality g) x }⟩
  invFun f := {
    app := f.hom.app
    naturality := by
      intro U V g
      ext x
      exact ConcreteCategory.congr_hom (f.hom.naturality g) x }
  left_inv f := by ext U x; rfl
  right_inv f := by ext U x; rfl

private def realizationHomEquiv (T : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
    (M : Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} A)))
    (N : IntrinsicModules T A) :
    ((Scheme.sfIntrinsicModuleEquivalence T A).functor.obj M ⟶ N) ≃
      (M ⟶ fixedRestriction T A N) :=
  ((PresheafOfModules.sheafificationAdjunction
    (finiteCoefficientIntrinsicScalarMap T A)).homEquiv _ N).trans
      (fixedRestrictionHomEquiv T A M N)

private def rootHomEquiv (n : ℕ) [Finite (SpTowerShriek.R l E n)]
    (T : Scheme.{u}) (N : IntrinsicModules T (SpTowerShriek.R l E n)) :
    ((realization l E n T).obj
      (Scheme.finiteRootProTensor (levelRing l E n) (l ^ (n + 1))
        (pow_pos (Fact.out : l.Prime).pos _) (levelAnnihilates l E n) T) ⟶ N) ≃
      (Scheme.proEtaleRootsOfUnitySheaf T (l ^ (n + 1)) ⟶
        (SheafOfModules.toSheaf _).obj N) :=
  (realizationHomEquiv T (SpTowerShriek.R l E n) _ N).trans
    (Scheme.proLineHomEquiv T (l ^ (n + 1))
      (pow_pos (Fact.out : l.Prime).pos _) (levelRing l E n)
      (levelAnnihilates l E n) (fixedRestriction T (SpTowerShriek.R l E n) N))

private theorem rootHomEquiv_apply (n : ℕ) [Finite (SpTowerShriek.R l E n)]
    (T : Scheme.{u}) (N : IntrinsicModules T (SpTowerShriek.R l E n))
    (f : (realization l E n T).obj
      (Scheme.finiteRootProTensor (levelRing l E n) (l ^ (n + 1))
        (pow_pos (Fact.out : l.Prime).pos _) (levelAnnihilates l E n) T) ⟶ N)
    (W : T.ProEtᵒᵖ)
    (z : (Scheme.proEtaleRootsOfUnitySheaf T (l ^ (n + 1))).obj.obj W) :
    (rootHomEquiv l E n T N f).hom.app W z =
      f.val.app W (Scheme.sfIntrinsicRealizationUnit T (SpTowerShriek.R l E n) _ W
        (Scheme.finiteRootProGenerator (levelRing l E n) (l ^ (n + 1))
          (pow_pos (Fact.out : l.Prime).pos _) (levelAnnihilates l E n) T W 1 z)) := by
  exact Scheme.proLineHomEquiv_generator T (l ^ (n + 1))
    (pow_pos (Fact.out : l.Prime).pos _) (levelRing l E n)
    (levelAnnihilates l E n) (fixedRestriction T (SpTowerShriek.R l E n) N)
    (realizationHomEquiv T (SpTowerShriek.R l E n) _ N f) W z

private theorem rootHomEquiv_comp (n : ℕ) [Finite (SpTowerShriek.R l E n)]
    (T : Scheme.{u})
    {N N' : IntrinsicModules T (SpTowerShriek.R l E n)}
    (f : (realization l E n T).obj
      (Scheme.finiteRootProTensor (levelRing l E n) (l ^ (n + 1))
        (pow_pos (Fact.out : l.Prime).pos _) (levelAnnihilates l E n) T) ⟶ N)
    (g : N ⟶ N') :
    rootHomEquiv l E n T N' (f ≫ g) =
      rootHomEquiv l E n T N f ≫ (SheafOfModules.toSheaf _).map g := by
  ext W z
  change (rootHomEquiv l E n T N' (f ≫ g)).hom.app W z =
    g.val.app W ((rootHomEquiv l E n T N f).hom.app W z)
  rw [rootHomEquiv_apply, rootHomEquiv_apply]
  rfl

private theorem rootHomEquiv_tensor (n : ℕ) [Finite (SpTowerShriek.R l E n)]
    (T : Scheme.{u}) (N : IntrinsicModules T (SpTowerShriek.R l E n))
    (f : (realization l E n T).obj
      (Scheme.finiteRootProTensor (levelRing l E n) (l ^ (n + 1))
        (pow_pos (Fact.out : l.Prime).pos _) (levelAnnihilates l E n) T) ⟶ N)
    (W : T.ProEtᵒᵖ) (a : levelRing l E n)
    (z : (Scheme.proEtaleRootsOfUnitySheaf T (l ^ (n + 1))).obj.obj W) :
    f.val.app W (Scheme.sfIntrinsicRealizationUnit T (SpTowerShriek.R l E n) _ W
        (Scheme.finiteRootProGenerator (levelRing l E n) (l ^ (n + 1))
          (pow_pos (Fact.out : l.Prime).pos _) (levelAnnihilates l E n) T W a z)) =
      (finiteCoefficientIntrinsicScalarMap T (SpTowerShriek.R l E n)).app W a •
        (show N.val.obj W from (rootHomEquiv l E n T N f).hom.app W z) := by
  let M := Scheme.finiteRootProTensor (levelRing l E n) (l ^ (n + 1))
    (pow_pos (Fact.out : l.Prime).pos _) (levelAnnihilates l E n) T
  have hg : Scheme.finiteRootProGenerator (levelRing l E n) (l ^ (n + 1))
      (pow_pos (Fact.out : l.Prime).pos _) (levelAnnihilates l E n) T W a z =
    a • Scheme.finiteRootProGenerator (levelRing l E n) (l ^ (n + 1))
      (pow_pos (Fact.out : l.Prime).pos _) (levelAnnihilates l E n) T W 1 z := by
    exact Scheme.proGenerator_smul T (l ^ (n + 1))
      (pow_pos (Fact.out : l.Prime).pos _) (levelRing l E n) (levelAnnihilates l E n) W a z
  rw [rootHomEquiv_apply, hg]
  let η := (PresheafOfModules.sheafificationAdjunction
    (finiteCoefficientIntrinsicScalarMap T (SpTowerShriek.R l E n))).unit.app
      ((finiteCoefficientModulePresheaf T.ProEt (levelRing l E n)).obj M.obj)
  change (f.val.app W).hom ((η.app W).hom (a • _)) = _
  rw [map_smul]
  exact (f.val.app W).hom.map_smul _ _

/-- Associated-module realization identifies the two sheafified presentations of
scalar extension of the finite roots, with every pure tensor fixed.

Source: Stacks Tags 03CY and 03EK; diagonal-tower trace (1), the root-to-tensor
part of coefficient identification.
(blueprint: lem-sfb-finite-p1-intrinsic-root-tensor).

Proof: apply the module sheafification adjunction defining realization. The
fixed-scalar tensor sheaf represents balanced maps from the finite roots module
and the coefficient ring. The intrinsic tensor sheaf defining finiteLine has
the same universal property by finiteTateLine_universal. Restriction of scalars
along constant sections identifies the balancing maps: the two maps from
ZMod(l^(n+1)) are equal because this ring is initial among rings annihilated by
that exponent. Locally every section of the constant coefficient sheaf comes
from a constant, so fixed-scalar linearity extends uniquely to linearity over
the sheaf of rings. Sheafification gives maps in both directions. They carry
each pure tensor to itself; these tensors locally generate, so both composites
are identities and the comparison is unique. The displayed scalar-section
formula is the sheafification unit formula for these tensor maps. The argument
also applies to the empty scheme, the zero ring, and n=0. -/
theorem finiteP1_intrinsic_root_tensor (n : ℕ) [Finite (SpTowerShriek.R l E n)]
    (T : Scheme.{u}) :
    ∃! e : (realization l E n T).obj
        (Scheme.finiteRootProTensor (levelRing l E n) (l ^ (n + 1))
          (pow_pos (Fact.out : l.Prime).pos _) (levelAnnihilates l E n) T) ≅
      finiteLine l E T n,
      ∀ (W : T.ProEtᵒᵖ) (a : levelRing l E n)
        (z : (Scheme.proEtaleRootsOfUnitySheaf T (l ^ (n + 1))).obj.obj W),
        e.hom.val.app W
          (Scheme.sfIntrinsicRealizationUnit T (SpTowerShriek.R l E n) _ W
            (Scheme.finiteRootProGenerator (levelRing l E n) (l ^ (n + 1))
              (pow_pos (Fact.out : l.Prime).pos _) (levelAnnihilates l E n) T W a z)) =
          Scheme.tateFiniteTensor T l (levelRing l E n) n (finiteScalar l E n) W.unop
            ((toSheafify (Scheme.ProEt.topology T)
              ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (levelRing l E n)))).app W a) z := by
  let U := (realization l E n T).obj
    (Scheme.finiteRootProTensor (levelRing l E n) (l ^ (n + 1))
      (pow_pos (Fact.out : l.Prime).pos _) (levelAnnihilates l E n) T)
  let V := finiteLine l E T n
  let Φ := rootHomEquiv l E n T
  obtain ⟨Ψ, hcomp, hpure⟩ := finiteTateLine_universal T l (levelRing l E n) n
    (finiteScalar l E n)
  let f : U ⟶ V := (Φ V).symm (Ψ V (𝟙 V))
  let g : V ⟶ U := (Ψ U).symm (Φ U (𝟙 U))
  have hf : Φ V f = Ψ V (𝟙 V) := (Φ V).apply_symm_apply _
  have hg : Ψ U g = Φ U (𝟙 U) := (Ψ U).apply_symm_apply _
  have hfg : f ≫ g = 𝟙 U := by
    apply (Φ U).injective
    rw [show Φ U (f ≫ g) = Φ V f ≫ (SheafOfModules.toSheaf _).map g from
      rootHomEquiv_comp l E n T f g, hf, ← hcomp]
    exact (congrArg (Ψ U) (Category.id_comp g)).trans hg
  have hgf : g ≫ f = 𝟙 V := by
    apply (Ψ V).injective
    rw [hcomp, hg, ← rootHomEquiv_comp]
    exact (congrArg (Φ V) (Category.id_comp f)).trans hf
  let e : U ≅ V := ⟨f, g, hfg, hgf⟩
  have he (W : T.ProEtᵒᵖ) (a : levelRing l E n)
      (z : (Scheme.proEtaleRootsOfUnitySheaf T (l ^ (n + 1))).obj.obj W) :
      e.hom.val.app W
        (Scheme.sfIntrinsicRealizationUnit T (SpTowerShriek.R l E n) _ W
          (Scheme.finiteRootProGenerator (levelRing l E n) (l ^ (n + 1))
            (pow_pos (Fact.out : l.Prime).pos _) (levelAnnihilates l E n) T W a z)) =
        Scheme.tateFiniteTensor T l (levelRing l E n) n (finiteScalar l E n) W.unop
          ((toSheafify (Scheme.ProEt.topology T)
            ((Functor.const T.ProEtᵒᵖ).obj (CommRingCat.of (levelRing l E n)))).app W a) z := by
    rw [show e.hom = f from rfl, rootHomEquiv_tensor]
    change _ • (show V.val.obj W from (Φ V f).hom.app W z) = _
    rw [hf]
    exact hpure V (𝟙 V) W _ z
  refine ⟨e, he, ?_⟩
  intro e' he'
  apply Iso.ext
  apply (Φ V).injective
  ext W z
  rw [rootHomEquiv_apply, rootHomEquiv_apply, he', he]

end AlgebraicGeometry.ProEtale.SpTowerP1
