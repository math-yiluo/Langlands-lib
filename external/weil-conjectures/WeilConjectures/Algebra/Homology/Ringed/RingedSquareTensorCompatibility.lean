/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.Ringed.RingedTensorSquarePresentation
import WeilConjectures.Algebra.Homology.Ringed.RingedSquareOrdinaryTensorCompatibility
import WeilConjectures.Algebra.Homology.Ringed.RingedTensorEdgeRepresentativeEquation
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Homology.CanonicalTensorPullbackOfUniverses.DerivedPullbackRepresentativeComputationSupplement
import WeilConjectures.Algebra.Homology.KFlatTotalTensorModel.KFlatTotalTensorModelSupplement

/-!
# Tensor compatibility of a ringed square on flat K-flat representatives

Source: Stacks Project, Cohomology on Sites, Tags 07A4, 0D6D and 0E48
(blueprint: lem-weil-pbc-ringed-square-tensor-compatibility).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048

universe u w

open CategoryTheory

namespace SheafOfModules

variable {Y X Y' X' : RingedTensorCorner.{u, w}}
  {f : RingedTensorEdge Y X} {g : RingedTensorEdge Y Y'}
  {h : RingedTensorEdge X X'} {k : RingedTensorEdge Y' X'}

private abbrev Modules (A : RingedTensorCorner.{u, w}) :=
  SheafOfModules.{u}
    ((sheafCompose A.topology (forget₂ CommRingCat.{u} RingCat.{u})).obj A.ring)

private abbrev Complexes (A : RingedTensorCorner.{u, w}) := CochainComplex (Modules A) ℤ

private abbrev Good {A : RingedTensorCorner.{u, w}} (P : Complexes A) : Prop :=
  P.IsAcyclicTensorKFlat ∧ ∀ n : ℤ, (P.X n).IsFlat

private noncomputable abbrev totalTensor (A : RingedTensorCorner.{u, w}) :=
  Functor.uncurry.obj ((@MonoidalCategory.curriedTensor (Modules A) _
    (monoidalCategory A.ring)).map₂HomologicalComplex (.up ℤ) (.up ℤ) (.up ℤ))

private noncomputable abbrev pull {A B : RingedTensorCorner.{u, w}}
    (e : RingedTensorEdge A B) := e.pullback.mapHomologicalComplex (.up ℤ)

private noncomputable abbrev comparison {A B : RingedTensorCorner.{u, w}}
    (e : RingedTensorEdge A B) (P : Complexes A) :=
  derivedPullbackComplexComparison e.pullback e.left e.epsilon P

private noncomputable abbrev delta {A B : RingedTensorCorner.{u, w}}
    (e : RingedTensorEdge A B) (P Q : Complexes A) :
    (pull e).obj ((totalTensor A).obj (P, Q)) ⟶
      (totalTensor B).obj ((pull e).obj P, (pull e).obj Q) :=
  (e.ordinaryTensor.totalIso A.ring B.ring e.inverseRing e.inverse e.algebraic e.ringMap
    e.pullback e.object_eq e.pushforward e.moduleAdjunction P Q).inv

private theorem pull_good {A B : RingedTensorCorner.{u, w}}
    (e : RingedTensorEdge A B) {P : Complexes A} (hp : Good P) :
    Good ((pull e).obj P) := by
  have hp' : ∀ n, IsFlatOnSite (J := A.topology) (R := A.ring) (P.X n) := fun n ↦
    (exactFunctor _ _).prop_of_iso (siteSheafTensorRightIso A.ring _).symm (hp.2 n)
  obtain ⟨hk, hf⟩ := isKFlat_ringedToposPullback e.inverse e.direct e.adjunction
    e.algebraic e.ringMap e.pullback e.object_eq e.map_eq P hp.1 hp'
  exact ⟨hk, fun n ↦ (exactFunctor _ _).prop_of_iso
    (siteSheafTensorRightIso B.ring _) (hf n)⟩

private theorem total_good {A : RingedTensorCorner.{u, w}}
    {P Q : Complexes A} (hp : Good P) (hq : Good Q) :
    Good ((totalTensor A).obj (P, Q)) := by
  have ht := KFlatTotalTensorModel.kFlat_total_tensor_model A.ring P Q hp.1 hq.1
    (fun n ↦ (exactFunctor _ _).prop_of_iso
      (siteSheafTensorRightIso A.ring _).symm (hp.2 n))
    (fun n ↦ (exactFunctor _ _).prop_of_iso
      (siteSheafTensorRightIso A.ring _).symm (hq.2 n))
  exact ⟨ht.1, fun n ↦ (exactFunctor _ _).prop_of_iso
    (siteSheafTensorRightIso A.ring _) (ht.2.1 n)⟩

private theorem comparison_isIso {A B : RingedTensorCorner.{u, w}}
    (e : RingedTensorEdge A B) {P : Complexes A} (hp : Good P) :
    IsIso (comparison e P) := by
  exact (CanonicalTensorPullbackOfUniverses.derivedPullback_kflat_tensor_computation
    e.inverse e.direct e.adjunction
    e.algebraic e.ringMap e.pullback e.object_eq e.map_eq e.left e.epsilon e.isLeftDerived).1
    P hp.1 (fun n ↦ (exactFunctor _ _).prop_of_iso
      (siteSheafTensorRightIso A.ring _).symm (hp.2 n))

-- Elaborate the uniquely characterized comparison with both tensor models fixed.
private theorem edge_equation {A B : RingedTensorCorner.{u, w}}
    (e : RingedTensorEdge A B) (a : RingedTensorModel A) (b : RingedTensorModel B)
    (P Q : Complexes A) (hp : Good P) (hq : Good Q) :
    e.left.map (a.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩)) ≫
      (e.tensorComparison a b).hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ≫
      B.tensor.map (CategoryTheory.Prod.mkHom (comparison e P) (comparison e Q)) =
    comparison e ((totalTensor A).obj (P, Q)) ≫ DerivedCategory.Q.map (delta e P Q) ≫
      b.representative.hom.app
        (⟨(pull e).obj P, pull_good e hp⟩, ⟨(pull e).obj Q, pull_good e hq⟩) := by
  exact ringedTensorEdgeRepresentativeEquation e a b P Q hp hq
    (pull_good e hp) (pull_good e hq)

attribute [local irreducible] monoidalCategory CanonicalRingedTensorComparison.totalIso
  RingedTensorEdge.tensorComparison ringedTopoiCanonicalDerivedTensorComparison
  derivedPullbackComplexComparison

private theorem comparison_naturality {A B : RingedTensorCorner.{u, w}}
    (e : RingedTensorEdge A B) {P Q : Complexes A} (a : P ⟶ Q) :
    e.left.map (DerivedCategory.Q.map a) ≫ comparison e Q =
      comparison e P ≫ DerivedCategory.Q.map ((pull e).map a) := by
  let eps : DerivedCategory.Q ⋙ e.left ⟶ pull e ⋙ DerivedCategory.Q :=
    Functor.whiskerRight (DerivedCategory.quotientCompQhIso (Modules A)).inv e.left ≫
      Functor.whiskerLeft (HomotopyCategory.quotient (Modules A) (.up ℤ)) e.epsilon ≫
      Functor.whiskerRight (e.pullback.mapHomotopyCategoryFactors (.up ℤ)).hom
        DerivedCategory.Qh ≫
      Functor.whiskerLeft (pull e) (DerivedCategory.quotientCompQhIso (Modules B)).hom
  simpa only [eps, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.comp_map, comparison,
    derivedPullbackComplexComparison, Category.assoc] using eps.naturality a

private theorem tensor_map_comp {A B : Type*} [Category A] [Category B]
    (T : A × A ⥤ B) {P₁ P₂ P₃ Q₁ Q₂ Q₃ : A}
    (a : P₁ ⟶ P₂) (b : Q₁ ⟶ Q₂) (c : P₂ ⟶ P₃) (d : Q₂ ⟶ Q₃) :
    T.map (CategoryTheory.Prod.mkHom (a ≫ c) (b ≫ d)) =
      T.map (CategoryTheory.Prod.mkHom a b) ≫ T.map (CategoryTheory.Prod.mkHom c d) :=
  T.map_comp (CategoryTheory.Prod.mkHom a b) (CategoryTheory.Prod.mkHom c d)

private theorem tensor_map_square {A B : Type*} [Category A] [Category B]
    (T : A × A ⥤ B) {P₁ P₂ P₃ P₄ Q₁ Q₂ Q₃ Q₄ : A}
    {a : P₁ ⟶ P₂} {b : Q₁ ⟶ Q₂} {c : P₂ ⟶ P₄} {d : Q₂ ⟶ Q₄}
    {e : P₁ ⟶ P₃} {f : Q₁ ⟶ Q₃} {g : P₃ ⟶ P₄} {h : Q₃ ⟶ Q₄}
    (hp : a ≫ c = e ≫ g) (hq : b ≫ d = f ≫ h) :
    T.map (CategoryTheory.Prod.mkHom a b) ≫ T.map (CategoryTheory.Prod.mkHom c d) =
      T.map (CategoryTheory.Prod.mkHom e f) ≫ T.map (CategoryTheory.Prod.mkHom g h) := by
  rw [← tensor_map_comp, hp, hq, tensor_map_comp]

-- Perform the diagram chase before specializing to derived categories and total complexes.
private theorem tensor_square_of_comparison {C : Type*} [Category C]
    {R₁ R₂ A₁ A₂ B₁ B₂ D₁ D₂ E₁ E₂ F₁ F₂ : C}
    (r₁ : R₁ ⟶ A₁) (r₂ : R₂ ⟶ A₂) (θr : R₁ ⟶ R₂) (θ : A₁ ⟶ A₂)
    (t₁ : A₁ ⟶ B₁) (t₂ : A₂ ⟶ B₂) (θt : B₁ ⟶ B₂)
    (z₁ : B₁ ⟶ F₁) (z₂ : B₂ ⟶ F₂) (θz : F₁ ⟶ F₂)
    (c₁ : R₁ ⟶ D₁) (c₂ : R₂ ⟶ D₂) (θc : D₁ ⟶ D₂)
    (d₁ : D₁ ⟶ E₁) (d₂ : D₂ ⟶ E₂) (θd : E₁ ⟶ E₂)
    (r₁' : E₁ ⟶ F₁) (r₂' : E₂ ⟶ F₂)
    (hn : r₁ ≫ θ = θr ≫ r₂)
    (he₁ : r₁ ≫ t₁ ≫ z₁ = c₁ ≫ d₁ ≫ r₁')
    (he₂ : r₂ ≫ t₂ ≫ z₂ = c₂ ≫ d₂ ≫ r₂')
    (hc : θr ≫ c₂ = c₁ ≫ θc) (hd : θc ≫ d₂ = d₁ ≫ θd)
    (hr : θd ≫ r₂' = r₁' ≫ θz) (hz : θt ≫ z₂ = z₁ ≫ θz) :
    r₁ ≫ (θ ≫ t₂) ≫ z₂ = r₁ ≫ (t₁ ≫ θt) ≫ z₂ := by
  simp only [Category.assoc]
  rw [reassoc_of% hn, he₂, reassoc_of% hc, reassoc_of% hd, hr,
    ← reassoc_of% he₁, hz]

-- Keep the four representative identifications explicit during composition.
private theorem two_edges_equation {A B C : RingedTensorCorner.{u, w}}
    (e : RingedTensorEdge A B) (d : RingedTensorEdge B C)
    (a : RingedTensorModel A) (b : RingedTensorModel B) (c : RingedTensorModel C)
    (P Q : Complexes A) (hp : Good P) (hq : Good Q) :
    d.left.map (e.left.map (a.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩))) ≫
      d.left.map ((e.tensorComparison a b).hom.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
      (d.tensorComparison b c).hom.app
        (e.left.obj (DerivedCategory.Q.obj P), e.left.obj (DerivedCategory.Q.obj Q)) ≫
      C.tensor.map (CategoryTheory.Prod.mkHom
        (d.left.map (comparison e P) ≫ comparison d ((pull e).obj P))
        (d.left.map (comparison e Q) ≫ comparison d ((pull e).obj Q))) =
    d.left.map (comparison e ((totalTensor A).obj (P, Q))) ≫
      comparison d ((pull e).obj ((totalTensor A).obj (P, Q))) ≫
      DerivedCategory.Q.map ((pull d).map (delta e P Q) ≫
        delta d ((pull e).obj P) ((pull e).obj Q)) ≫
      c.representative.hom.app
        (⟨(pull d).obj ((pull e).obj P), pull_good d (pull_good e hp)⟩,
          ⟨(pull d).obj ((pull e).obj Q), pull_good d (pull_good e hq)⟩) := by
  have hn := (d.tensorComparison b c).hom.naturality
    (CategoryTheory.Prod.mkHom (comparison e P) (comparison e Q))
  dsimp only [Functor.comp_map, Functor.prod_map] at hn
  conv_lhs =>
    arg 2
    arg 2
    arg 2
    rw [tensor_map_comp]
  conv_lhs =>
    arg 2
    arg 2
    rw [← reassoc_of% hn]
  have he := congrArg (fun a ↦ d.left.map a) (edge_equation e a b P Q hp hq)
  simp only [Functor.map_comp] at he
  rewrite [reassoc_of% he]
  simp only [Functor.map_comp, Category.assoc]
  conv_lhs =>
    arg 2
    arg 2
    rw [edge_equation d b c ((pull e).obj P) ((pull e).obj Q)
      (pull_good e hp) (pull_good e hq)]
  conv_lhs =>
    arg 2
    rw [reassoc_of% (comparison_naturality d (delta e P Q))]

-- Elaborate the four derived functors and their representative comparisons together.
/-- The representative characterization of the derived square is compatible with
canonical tensor comparisons on flat K-flat complexes.

Proof: write each module pullback as inverse image followed by scalar extension.
Its canonical tensor map sends s tensor (v tensor w) to
(s tensor v) tensor (1 tensor w). The insertion equation for the square fixes its
module comparison on 1 tensor (1 tensor v). By linearity and balancing it therefore
commutes with the tensor map: both orders split the same two factors and multiply
the same nested scalars. This checks equality on pure tensors, which locally generate the
sheafified scalar extensions and their tensor products, and hence proves equality of module
sheaf maps. Apply this equality in each bidegree of the total tensor complex.
The maps preserve both degrees, so there is no interchange sign. Pullback preserves
flat K-flat complexes. Their total tensor is K-flat: reassociate its tensor with
an acyclic test complex and apply K-flatness of the two factors successively.
Its terms are flat: tensoring with a tensor product is the composition of the two
exact tensor functors, and each total degree is a direct sum of such flat products;
these sums are flat by exactness of direct sums and preservation of sums by tensor.
For the derived transport, write T for the ordinary total tensor, r_A(P,Q) for
the model identification Q(T(P,Q)) ≅ A.tensor(Q(P),Q(Q)), C_e for the edge complex
comparison, and d_e for the inverse of ordinaryTensor.totalIso. The defining
representative equation for the edge tensor comparison is
  e.left.map(r_A) ; t_e ; B.tensor.map(C_e(P),C_e(Q))
    = C_e(T(P,Q)) ; Q.map(d_e) ; r_B(e*P,e*Q).
Precompose the desired identity with (g.left ⋙ k.left).map(r_Y(P,Q).hom).
Postcompose it with X'.tensor applied to the pair
  h.left.map(C_f(P)) ; C_h(f*P), h.left.map(C_f(Q)) ; C_h(f*Q).
These maps are isomorphisms on flat K-flat representatives, so cancellation is valid.
Naturality of theta for r_Y, naturality of the edge tensor comparisons, and the
four edge representative equations reduce the left side to the composite through
C_h(f*T(P,Q)). Apply the assumed equation for theta at T(P,Q). On the right side,
apply the assumed equations at P and Q, followed by the representative equations
for g and k. Naturality of C_h and C_k for d_f and d_g, and naturality of r_X',
reduce the remaining equality to Q applied to
  gamma_T ; h*(d_f) ; d_h = k*(d_g) ; d_k ; T(gamma_P,gamma_Q),
where gamma is the termwise module square. This is exactly the total-complex
identity already established on pure tensors. Functoriality of Q proves the
conjugated equality; cancellation proves the asserted derived equality.
This is only the representative calculation: extension to arbitrary derived objects
and the mate argument are separate steps.
Source: Stacks, Cohomology on Sites, Tags 07A4 (pullback and tensor),
0D6D (composition), and 0E48 (compatibility; verification omitted there)
(blueprint: lem-weil-pbc-ringed-square-tensor-compatibility). -/
theorem ringedSquareTensorCompatibility
    (s : RingedTensorSquare Y X Y' X' f g h k)
    (aY : RingedTensorModel Y) (aX : RingedTensorModel X)
    (aY' : RingedTensorModel Y') (aX' : RingedTensorModel X')
    (theta : g.left ⋙ k.left ≅ f.left ⋙ h.left)
    (htheta : ∀ (P : CochainComplex (SheafOfModules.{u}
        ((sheafCompose Y.topology (forget₂ CommRingCat.{u} RingCat.{u})).obj Y.ring)) ℤ),
      P.IsAcyclicTensorKFlat → (∀ n : ℤ, (P.X n).IsFlat) →
      theta.hom.app (DerivedCategory.Q.obj P) ≫
        h.left.map (derivedPullbackComplexComparison f.pullback f.left f.epsilon P) ≫
        derivedPullbackComplexComparison h.pullback h.left h.epsilon
          ((f.pullback.mapHomologicalComplex (.up ℤ)).obj P) =
      k.left.map (derivedPullbackComplexComparison g.pullback g.left g.epsilon P) ≫
        derivedPullbackComplexComparison k.pullback k.left k.epsilon
          ((g.pullback.mapHomologicalComplex (.up ℤ)).obj P) ≫
        DerivedCategory.Q.map
          ((NatIso.mapHomologicalComplex s.modules (.up ℤ)).hom.app P))
    (P Q : CochainComplex (SheafOfModules.{u}
      ((sheafCompose Y.topology (forget₂ CommRingCat.{u} RingCat.{u})).obj Y.ring)) ℤ)
    (hP : P.IsAcyclicTensorKFlat) (hPf : ∀ n : ℤ, (P.X n).IsFlat)
    (hQ : Q.IsAcyclicTensorKFlat) (hQf : ∀ n : ℤ, (Q.X n).IsFlat) :
    theta.hom.app (Y.tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
      h.left.map ((f.tensorComparison aY aX).hom.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
      (h.tensorComparison aX aX').hom.app
        (f.left.obj (DerivedCategory.Q.obj P), f.left.obj (DerivedCategory.Q.obj Q)) =
    k.left.map ((g.tensorComparison aY aY').hom.app
        (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
      (k.tensorComparison aY' aX').hom.app
        (g.left.obj (DerivedCategory.Q.obj P), g.left.obj (DerivedCategory.Q.obj Q)) ≫
      X'.tensor.map (CategoryTheory.Prod.mkHom
        (theta.hom.app (DerivedCategory.Q.obj P))
        (theta.hom.app (DerivedCategory.Q.obj Q))) := by
  let hp : Good P := ⟨hP, hPf⟩
  let hq : Good Q := ⟨hQ, hQf⟩
  let r : DerivedCategory.Q.obj ((totalTensor Y).obj (P, Q)) ⟶
      Y.tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) :=
    aY.representative.hom.app (⟨P, hp⟩, ⟨Q, hq⟩)
  let γ : pull g ⋙ pull k ⟶ pull f ⋙ pull h :=
    (NatIso.mapHomologicalComplex s.modules (.up ℤ)).hom
  have hfP := comparison_isIso f hp
  have hfQ := comparison_isIso f hq
  have hhP := comparison_isIso h (pull_good f hp)
  have hhQ := comparison_isIso h (pull_good f hq)
  let zP := h.left.map (comparison f P) ≫ comparison h ((pull f).obj P)
  let zQ := h.left.map (comparison f Q) ≫ comparison h ((pull f).obj Q)
  have hzP : IsIso zP := by dsimp only [zP]; infer_instance
  have hzQ : IsIso zQ := by dsimp only [zQ]; infer_instance
  have hr : IsIso r := by dsimp only [r]; infer_instance
  have hpair : IsIso (CategoryTheory.Prod.mkHom zP zQ) :=
    ⟨⟨CategoryTheory.Prod.mkHom (inv zP) (inv zQ), by ext <;> simp, by ext <;> simp⟩⟩
  apply (cancel_epi ((g.left ⋙ k.left).map r)).1
  apply (cancel_mono (X'.tensor.map (CategoryTheory.Prod.mkHom zP zQ))).1
  have hn := theta.hom.naturality r
  dsimp only [Functor.comp_map] at hn
  have heF := two_edges_equation f h aY aX aX' P Q hp hq
  have heG := two_edges_equation g k aY aY' aX' P Q hp hq
  have hsP : theta.hom.app (DerivedCategory.Q.obj P) ≫ zP =
      (k.left.map (comparison g P) ≫ comparison k ((pull g).obj P)) ≫
        DerivedCategory.Q.map (γ.app P) := by
    simpa only [zP, Category.assoc] using htheta P hP hPf
  have hsQ : theta.hom.app (DerivedCategory.Q.obj Q) ≫ zQ =
      (k.left.map (comparison g Q) ≫ comparison k ((pull g).obj Q)) ≫
        DerivedCategory.Q.map (γ.app Q) := by
    simpa only [zQ, Category.assoc] using htheta Q hQ hQf
  have ht := total_good hp hq
  have hsT := htheta ((totalTensor Y).obj (P, Q)) ht.1 ht.2
  have ho := congrArg (fun a ↦ DerivedCategory.Q.map a)
    (ringedSquareOrdinaryTensorCompatibility s P Q)
  simp only [Functor.map_comp] at ho
  have hrep : DerivedCategory.Q.map ((totalTensor X').map
      (CategoryTheory.Prod.mkHom (γ.app P) (γ.app Q))) ≫
      aX'.representative.hom.app
        (⟨(pull h).obj ((pull f).obj P), pull_good h (pull_good f hp)⟩,
          ⟨(pull h).obj ((pull f).obj Q), pull_good h (pull_good f hq)⟩) =
    aX'.representative.hom.app
        (⟨(pull k).obj ((pull g).obj P), pull_good k (pull_good g hp)⟩,
          ⟨(pull k).obj ((pull g).obj Q), pull_good k (pull_good g hq)⟩) ≫
      X'.tensor.map (CategoryTheory.Prod.mkHom
        (DerivedCategory.Q.map (γ.app P)) (DerivedCategory.Q.map (γ.app Q))) := by
    exact aX'.representative.hom.naturality
      (CategoryTheory.Prod.mkHom
        (ObjectProperty.homMk
          (X := ⟨(pull k).obj ((pull g).obj P), pull_good k (pull_good g hp)⟩)
          (Y := ⟨(pull h).obj ((pull f).obj P), pull_good h (pull_good f hp)⟩) (γ.app P))
        (ObjectProperty.homMk
          (X := ⟨(pull k).obj ((pull g).obj Q), pull_good k (pull_good g hq)⟩)
          (Y := ⟨(pull h).obj ((pull f).obj Q), pull_good h (pull_good f hq)⟩) (γ.app Q)))
  have chase := tensor_square_of_comparison
    (r₁ := k.left.map (g.left.map r))
    (r₂ := h.left.map (f.left.map r))
    (θr := theta.hom.app (DerivedCategory.Q.obj ((totalTensor Y).obj (P, Q))))
    (θ := theta.hom.app (Y.tensor.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)))
    (t₁ := k.left.map ((g.tensorComparison aY aY').hom.app
      (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
      (k.tensorComparison aY' aX').hom.app
        (g.left.obj (DerivedCategory.Q.obj P), g.left.obj (DerivedCategory.Q.obj Q)))
    (t₂ := h.left.map ((f.tensorComparison aY aX).hom.app
      (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q)) ≫
      (h.tensorComparison aX aX').hom.app
        (f.left.obj (DerivedCategory.Q.obj P), f.left.obj (DerivedCategory.Q.obj Q)))
    (θt := X'.tensor.map (CategoryTheory.Prod.mkHom
      (theta.hom.app (DerivedCategory.Q.obj P)) (theta.hom.app (DerivedCategory.Q.obj Q))))
    (z₁ := X'.tensor.map (CategoryTheory.Prod.mkHom
      (k.left.map (comparison g P) ≫ comparison k ((pull g).obj P))
      (k.left.map (comparison g Q) ≫ comparison k ((pull g).obj Q))))
    (z₂ := X'.tensor.map (CategoryTheory.Prod.mkHom zP zQ))
    (θz := X'.tensor.map (CategoryTheory.Prod.mkHom
      (DerivedCategory.Q.map (γ.app P)) (DerivedCategory.Q.map (γ.app Q))))
    (c₁ := k.left.map (comparison g ((totalTensor Y).obj (P, Q))) ≫
      comparison k ((pull g).obj ((totalTensor Y).obj (P, Q))))
    (c₂ := h.left.map (comparison f ((totalTensor Y).obj (P, Q))) ≫
      comparison h ((pull f).obj ((totalTensor Y).obj (P, Q))))
    (θc := DerivedCategory.Q.map (γ.app ((totalTensor Y).obj (P, Q))))
    (d₁ := DerivedCategory.Q.map ((pull k).map (delta g P Q) ≫
      delta k ((pull g).obj P) ((pull g).obj Q)))
    (d₂ := DerivedCategory.Q.map ((pull h).map (delta f P Q) ≫
      delta h ((pull f).obj P) ((pull f).obj Q)))
    (θd := DerivedCategory.Q.map ((totalTensor X').map
      (CategoryTheory.Prod.mkHom (γ.app P) (γ.app Q))))
    (r₁' := aX'.representative.hom.app
      (⟨(pull k).obj ((pull g).obj P), pull_good k (pull_good g hp)⟩,
        ⟨(pull k).obj ((pull g).obj Q), pull_good k (pull_good g hq)⟩))
    (r₂' := aX'.representative.hom.app
      (⟨(pull h).obj ((pull f).obj P), pull_good h (pull_good f hp)⟩,
        ⟨(pull h).obj ((pull f).obj Q), pull_good h (pull_good f hq)⟩))
    hn (by simpa only [Category.assoc] using heG)
    (by simpa only [Category.assoc] using heF)
    (by simpa only [Category.assoc] using hsT)
    (by simpa only [Functor.map_comp, Category.assoc] using ho)
    hrep (tensor_map_square X'.tensor hsP hsQ)
  simpa only [Functor.comp_map, Category.assoc] using chase

end SheafOfModules
