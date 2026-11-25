/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.OpenTensorNormalizationData
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.Algebra.Homology.CochainTensorModelRigidity
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Localization.Construction
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Whiskering
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.RingTheory.Flat.CategoryTheory
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Localization.Prod
import Mathlib.Algebra.Homology.BifunctorFlip
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorHomotopy
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import Mathlib.CategoryTheory.Localization.CalculusOfFractions
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses

/-! Extension of the finite restriction square from resolving representatives.
(blueprint: lem-sf-finite-base-change-restriction-localization)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open AlgebraicGeometry.Scheme.ProjectionRestriction
namespace SheafOfModules.OpenTensorNormalization

set_option synthInstance.maxSize 4096
set_option maxRecDepth 2048

private theorem resolving_of_iso {X : Scheme.{u}}
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
    {P Q : CochainComplex (Mod R) ℤ} (a : P ≅ Q) (hQ : resolving R Q) :
    resolving R P := by
  let := SheafOfModules.monoidalCategory R
  constructor
  · intro F hF
    exact HomologicalComplex.Acyclic.of_iso (hQ.1 F hF)
      ((total R).mapIso (Iso.prod (Iso.refl F) a.symm))
  · intro n
    have hcat : exactFunctor _ _ (tensorRight (Q.X n)) :=
      (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R (Q.X n)) (hQ.2 n)
    have hcat' : exactFunctor _ _ (tensorRight (P.X n)) :=
      (exactFunctor _ _).prop_of_iso
        ((curriedTensor (Mod R)).flip.mapIso
          ((HomologicalComplex.eval _ _ n).mapIso a.symm)) hcat
    exact (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso R (P.X n)).symm hcat'

private theorem natTrans_app_eq_of_iso
    {C D : Type*} [Category* C] [Category* D] {F G : C ⥤ D}
    (a b : F ⟶ G) {X Y : C} (i : X ≅ Y) (h : a.app X = b.app X) :
    a.app Y = b.app Y := by
  apply (cancel_epi (F.map i.hom)).1
  rw [a.naturality, b.naturality, h]

private theorem finite_representatives_ext
    {A : Type (u + 1)} [CommRing A] {X : Scheme.{u}}
    {R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}}
    {i : (Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of A) ⟶ R.obj}
    (e : FiniteRealization A X R i)
    {E : Type*} [Category* E] {F G : FiniteD A X ⥤ E}
    (a b : F ⟶ G)
    (h : ∀ (P : CochainComplex (FiniteModules A X) ℤ),
      resolving R ((finiteComplexRealization e).obj P) →
      a.app (DerivedCategory.Q.obj P) = b.app (DerivedCategory.Q.obj P)) : a = b := by
  let eC := e.equivalence.mapHomologicalComplex (.up ℤ)
  let eD := e.equivalence.mapDerivedCategory
  let π := CategoryTheory.Prod.fst (DerivedCategory (Mod R)) (DerivedCategory (Mod R))
  have heq : Functor.whiskerLeft (π ⋙ eD.inverse) a =
      Functor.whiskerLeft (π ⋙ eD.inverse) b := by
    obtain ⟨_, _, _, hdesc⟩ := cochain_tensor_model_rigidity (ProEt.topology X) R
    apply (hdesc E inferInstance _ _).1
    apply NatTrans.ext
    funext Z
    let P := eC.inverse.obj Z.1.obj
    have hp : resolving R ((finiteComplexRealization e).obj P) :=
      resolving_of_iso R (eC.counitIso.app Z.1.obj) Z.1.property
    let p : DerivedCategory.Q.obj P ≅ eD.inverse.obj (DerivedCategory.Q.obj Z.1.obj) :=
      eD.unitIso.app _ ≪≫ eD.inverse.mapIso
        (e.equivalence.functor.mapDerivedCategoryFactors.app P ≪≫
          DerivedCategory.Q.mapIso (eC.counitIso.app Z.1.obj))
    exact natTrans_app_eq_of_iso a b p (h P hp)
  apply NatTrans.ext
  funext M
  exact natTrans_app_eq_of_iso a b (eD.unitIso.app M).symm
    (congrArg (fun t ↦ t.app (eD.functor.obj M, eD.functor.obj M)) heq)

/-- Equality on resolving representatives extends to every object of the
unbounded derived category.  This is the localization and naturality step in
lem-sf-finite-base-change-restriction-coherence.

Source: Stacks 06YS (K-flat resolutions on a ringed site) and the equivalence
clause of lem-weil-pbc-site-derived-tensor-descent; the localization step of
`fix-prop-coherence.proof.md`.
Proof: by the resolving-localization equivalence there are a flat-term K-flat
ringed complex `R` and an isomorphism `Q R ≅ e.realizeX.derived.obj M`.  The
ordinary realization equivalence and its inverse are exact; applied termwise and
localized they give inverse derived equivalences.  Put `P` the termwise inverse
realization of `R`; the termwise counit gives `finiteComplexRealization P ≅ R`,
so it is resolving (flatness and K-flatness are invariant under isomorphism of
complexes), and `Q P ≅ M`.  Both displayed composites are components at `M` of
composites of natural transformations between the same two functors of `M`,
so naturality carries the equality `hrep P` across `Q P ≅ M`.
(blueprint: lem-sf-finite-base-change-restriction-localization) -/
theorem finite_base_change_restriction_of_representatives
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U' U X' X : Scheme.{u}} (gU : U' ⟶ U) (j' : U' ⟶ X')
    (j : U ⟶ X) (g : X' ⟶ X) (sq : OpenImmersionSquare gU j' j g)
    [IsOpenImmersion j] [IsOpenImmersion j']
    {t : SiteSquare (finiteInput A gU j' j g sq)}
    (o : Operations (finiteInput A gU j' j g sq) t)
    (e : FiniteComparisons A o)
    (hrep : ∀ (P : CochainComplex (FiniteModules A X) ℤ),
      resolving (finiteInput A gU j' j g sq).R
        ((finiteComplexRealization e.realizeX).obj P) →
      let r := Functor.isoWhiskerRight
        (ProEtale.upperStar (ModuleCat.{u + 1} A) j).leftDerivedFunctorIsoMapDerivedCategory.symm
        e.realizeU.derived ≪≫ e.openPull
      let M := DerivedCategory.Q.obj P
      e.pullU.hom.app ((finitePull A j).obj M) ≫
          o.gUPull.derived.map (r.hom.app M) ≫
          o.theta.inv.app (e.realizeX.derived.obj M) =
        e.realizeU'.derived.map
            ((Functor.mapDerivedCategorySquareIso
              (ProEtale.upperStarCompIso (ModuleCat.{u + 1} A) sq.toCommSq.w)).hom.app M) ≫
          e.openPull'.hom.app ((finitePull A g).obj M) ≫
          o.opens.jStar'.map (e.pull.hom.app M)) :
    let r := Functor.isoWhiskerRight
      (ProEtale.upperStar (ModuleCat.{u + 1} A) j).leftDerivedFunctorIsoMapDerivedCategory.symm
      e.realizeU.derived ≪≫ e.openPull
    ∀ M : FiniteD A X,
      e.pullU.hom.app ((finitePull A j).obj M) ≫
          o.gUPull.derived.map (r.hom.app M) ≫ o.theta.inv.app (e.realizeX.derived.obj M) =
        e.realizeU'.derived.map
            ((Functor.mapDerivedCategorySquareIso
              (ProEtale.upperStarCompIso (ModuleCat.{u + 1} A) sq.toCommSq.w)).hom.app M) ≫
          e.openPull'.hom.app ((finitePull A g).obj M) ≫
          o.opens.jStar'.map (e.pull.hom.app M) := by
  dsimp only
  let r := Functor.isoWhiskerRight
    (ProEtale.upperStar (ModuleCat.{u + 1} A) j).leftDerivedFunctorIsoMapDerivedCategory.symm
    e.realizeU.derived ≪≫ e.openPull
  let F := finitePull A j ⋙ finitePull A gU ⋙ e.realizeU'.derived
  let G := e.realizeX.derived ⋙ o.gPull.derived ⋙ o.opens.jStar'
  let a : F ⟶ G :=
    Functor.whiskerLeft (finitePull A j) e.pullU.hom ≫
      Functor.whiskerRight r.hom o.gUPull.derived ≫
      Functor.whiskerLeft e.realizeX.derived o.theta.inv
  let c := Functor.mapDerivedCategorySquareIso
    (ProEtale.upperStarCompIso (ModuleCat.{u + 1} A) sq.toCommSq.w)
  let b : F ⟶ G :=
    Functor.whiskerRight c.hom e.realizeU'.derived ≫
      Functor.whiskerLeft (finitePull A g) e.openPull'.hom ≫
      Functor.whiskerRight e.pull.hom o.opens.jStar'
  have hab : a = b := by
    apply finite_representatives_ext e.realizeX a b
    intro P hp
    exact hrep P hp
  intro M
  exact congrArg (fun t ↦ t.app M) hab

end SheafOfModules.OpenTensorNormalization
