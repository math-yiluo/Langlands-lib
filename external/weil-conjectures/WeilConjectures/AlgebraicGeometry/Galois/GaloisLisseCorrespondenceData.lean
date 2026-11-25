/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.LisseModuleSheaves
public import WeilConjectures.AlgebraicGeometry.Lisse.LisseAdicFiberFunctors
public import WeilConjectures.RepresentationTheory.PoincareDuality.LAdic
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.LocallyConstantEquivalenceExtension
public import WeilConjectures.AlgebraicGeometry.GaloisCategories
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Restriction
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsorDescent
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.FiniteStalksComparison
public import WeilConjectures.AlgebraicGeometry.Sites.InverseImageRepresentable
public import WeilConjectures.AlgebraicGeometry.HenselianFiniteEtale
public import WeilConjectures.CategoryTheory.SetFunctorAut.AutProfinite
public import Mathlib.GroupTheory.Index
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.RepresentationTheory.Rep.Basic
public import WeilConjectures.AlgebraicGeometry.Lisse.LisseTensorScalarExtension

/-!
# Data of the Galois correspondence for lisse sheaves

Source: Stacks Project, Tag 0DV5; the blueprint, `chap-Verdier-and-Poincare-duality`,
`lemma-perfect-complexes-geometric-point` (blueprint: def-pod-galois-correspondence-data-e4);
Deligne, Weil II (1.1.1), (1.1.6).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory
open AlgebraicGeometry Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme

attribute [local irreducible] lisseRationalFiberFunctor

/-- The invertible linear action of a representation. Source: Stacks 0DV5 (3),
Weil II (1.1.6) (blueprint: def-pod-galois-correspondence-data-e4). -/
noncomputable def galoisRepLinearAction (R : Type (u + 1)) [CommRing R]
    {G : Type u} [Group G] (X : Rep.{u + 1} R G) : G →* (X.V ≃ₗ[R] X.V) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv R X.V).toMonoidHom.comp
    (Representation.asGroupHom (k := R) (G := G) (V := X.V) X.ρ)

/-- Finite representations with open stabilizers (discrete continuity), including
noncommutative finite coefficient rings. Source: Stacks 0DV5 (3)
(blueprint: def-pod-galois-correspondence-data-e4). -/
@[reducible] def galoisFiniteRepresentations (R : Type (u + 1)) [Ring R]
    (G : Type u) [Group G] [TopologicalSpace G] :=
  ObjectProperty.FullSubcategory
    (fun X : Rep.{u + 1} R G ↦ Finite X.V ∧ ∀ x : X.V, IsOpen {g : G | X.ρ g x = x})

/-- Continuous integral representations, transported along the specified profinite model.
Source: Weil II (1.1.6) (blueprint: def-pod-galois-correspondence-data-e4). -/
@[reducible] noncomputable def galoisIntegralRepresentations (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {G : Type u} [Group G] [TopologicalSpace G] (P : ProfiniteGrp.{u}) (δ : G ≃ₜ* P) :=
  ObjectProperty.FullSubcategory
    (fun X : Rep.{u + 1} (Padic.coefficientExtensionIntegers l E) G ↦
      Representation.IsContinuousIntegral l E P X.V
        ((galoisRepLinearAction _ X).comp δ.symm.toMonoidHom))

/-- Continuous finite-extension representations over the same profinite model.
Source: Weil II (1.1.6) (blueprint: def-pod-galois-correspondence-data-e4). -/
@[reducible] noncomputable def galoisCoefficientRepresentations (l : ℕ) [Fact l.Prime]
    (E : Type (u + 1)) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {G : Type u} [Group G] [TopologicalSpace G] (P : ProfiniteGrp.{u}) (δ : G ≃ₜ* P) :=
  ObjectProperty.FullSubcategory
    (fun X : Rep.{u + 1} E G ↦ Representation.IsContinuousCoefficient l E P X.V
      ((galoisRepLinearAction E X).comp δ.symm.toMonoidHom))

/-- Algebraic l-adic representations over the same profinite model.
Source: Weil II (1.1.6) (blueprint: def-pod-galois-correspondence-data-e4). -/
@[reducible] noncomputable def galoisAdicRepresentations (l : ℕ) [Fact l.Prime]
    (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]
    {G : Type u} [Group G] [TopologicalSpace G] (P : ProfiniteGrp.{u}) (δ : G ≃ₜ* P) :=
  ObjectProperty.FullSubcategory
    (fun X : Rep.{u + 1} Q G ↦ Representation.IsLAdic l Q P X.V
      ((galoisRepLinearAction Q X).comp δ.symm.toMonoidHom))

/-- The underlying sheaf of sets of a module sheaf. Its FLC witness is supplied in
`galoisUnderlyingFLC`. Source: Stacks 0DV5 (3)
(blueprint: def-pod-galois-correspondence-data-e4). -/
noncomputable def galoisUnderlyingSetSheaf {Y : Scheme.{u}}
    (R : Type (u + 1)) [Ring R] (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) :=
  (sheafCompose Y.smallEtaleTopology (CategoryTheory.forget (ModuleCat.{u + 1} R))).obj F

/-- The underlying set sheaf bundled with its specified FLC witness.
Source: Stacks 0DV5 (3) (blueprint: def-pod-galois-correspondence-data-e4). -/
noncomputable def galoisUnderlyingFLC {Y : Scheme.{u}}
    (R : Type (u + 1)) [Ring R] (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))
    (h : IsLisseEtaleSheafOfSets (galoisUnderlyingSetSheaf R F)) : Y.FLC :=
  ⟨galoisUnderlyingSetSheaf R F, h⟩

/-- Diagonal action on the tensor product of the underlying representation modules.
Source: Weil II (1.1.6) (blueprint: def-pod-galois-correspondence-data-e4). -/
noncomputable def galoisTensorAction (R : Type (u + 1)) [CommRing R]
    {G : Type u} [Group G] (X Z : Rep.{u + 1} R G) :=
  Representation.tensorDiagonal R G X.V Z.V
    (galoisRepLinearAction R X) (galoisRepLinearAction R Z)

/-- Scalar-extension action on the underlying representation module (`1 ⊗ σ`).
Source: Weil II (1.1.6) (blueprint: def-pod-galois-correspondence-data-e4). -/
noncomputable def galoisScalarAction (E L : Type (u + 1)) [Field E] [Field L] [Algebra E L]
    {G : Type u} [Group G] (X : Rep.{u + 1} E G) :=
  Representation.coefficientScalarExtension E L G X.V (galoisRepLinearAction E X)

set_option genSizeOfSpec false in
set_option genInjectivity false in
/-- The shared group, equivalence and fibre-comparison data of part (1).
Source: Stacks 0DV5 (3) (blueprint: def-pod-galois-correspondence-data-e4). -/
structure GaloisLisseFiniteData
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (G : Type u) [Group G] [TopologicalSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)] where
  γ : G ≃ₜ* Aut (ObjectProperty.ι (IsLisseEtaleSheafOfSets (T := Y)) ⋙
    (pointSmallEtale y).sheafFiber (A := Type (u + 1)))
  Φ : Y.FiniteEtale ≌ Y.FLC
  η : Φ.functor ⋙ ObjectProperty.ι _ ⋙ (pointSmallEtale y).sheafFiber (A := Type (u + 1)) ≅
    FiniteEtale.fiber y ⋙ CategoryTheory.forget FintypeCat.{u} ⋙ uliftFunctor.{u + 1, u}
  e : ∀ (Λ : Type (u + 1)) [Ring Λ] [Finite Λ], LisseModuleSheafCategory Y Λ ≌
    galoisFiniteRepresentations Λ G
  τ : ∀ (Λ : Type (u + 1)) [Ring Λ] [Finite Λ], (e Λ).functor ⋙ ObjectProperty.ι _ ⋙ forget₂ (Rep.{u
    + 1} Λ G) (ModuleCat.{u + 1} Λ) ≅ ObjectProperty.ι _ ⋙ (pointSmallEtale y).sheafFiber (A :=
    ModuleCat.{u + 1} Λ)

/-- Clause `yonedaComparison` of the finite correspondence.
Source: Stacks 0DV5 (3), Weil II (1.1.1), (1.1.6)
(blueprint: def-pod-galois-correspondence-data-e4). -/
def galoisYonedaComparison
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (G : Type u) [Group G] [TopologicalSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    (d : GaloisLisseFiniteData y G) : Prop :=
  Nonempty (d.Φ.functor ⋙ ObjectProperty.ι _ ≅ ObjectProperty.ι _ ⋙
    Y.smallEtaleTopology.uliftYoneda.{u + 1})

/-- Clause `finiteEtaleAction` of the finite correspondence.
Source: Stacks 0DV5 (3), Weil II (1.1.1), (1.1.6)
(blueprint: def-pod-galois-correspondence-data-e4). -/
def galoisFiniteEtaleAction
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (G : Type u) [Group G] [TopologicalSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    (d : GaloisLisseFiniteData y G) : Prop :=
  ∀ (P : Y.FiniteEtale) (g : G) (z : ((pointSmallEtale y).sheafFiber (A := Type (u + 1))).obj
    (d.Φ.functor.obj P).obj), d.η.hom.app P ((d.γ g).asIso.hom.app (d.Φ.functor.obj P) z) = ⟨g •
    (d.η.hom.app P z).down⟩

/-- Clause `finiteAbelian` of the finite correspondence.
Source: Stacks 0DV5 (3), Weil II (1.1.1), (1.1.6)
(blueprint: def-pod-galois-correspondence-data-e4). -/
def galoisFiniteAbelian
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (G : Type u) [Group G] [TopologicalSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    (_d : GaloisLisseFiniteData y G) : Prop :=
  ∀ (Λ : Type (u + 1)) [Ring Λ] [Finite Λ], Nonempty (Abelian (LisseModuleSheafCategory Y Λ))

/-- Clause `finiteKernels` of the finite correspondence.
Source: Stacks 0DV5 (3), Weil II (1.1.1), (1.1.6)
(blueprint: def-pod-galois-correspondence-data-e4). -/
def galoisFiniteKernels
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (G : Type u) [Group G] [TopologicalSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    (_d : GaloisLisseFiniteData y G) : Prop :=
  ∀ (Λ : Type (u + 1)) [Ring Λ] [Finite Λ], ObjectProperty.IsClosedUnderKernels (IsLisseModuleSheaf
    (Y := Y) (Λ := Λ))

/-- Clause `finiteCokernels` of the finite correspondence.
Source: Stacks 0DV5 (3), Weil II (1.1.1), (1.1.6)
(blueprint: def-pod-galois-correspondence-data-e4). -/
def galoisFiniteCokernels
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (G : Type u) [Group G] [TopologicalSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    (_d : GaloisLisseFiniteData y G) : Prop :=
  ∀ (Λ : Type (u + 1)) [Ring Λ] [Finite Λ], ObjectProperty.IsClosedUnderCokernels
    (IsLisseModuleSheaf (Y := Y) (Λ := Λ))

/-- Clause `finiteLimits` of the finite correspondence.
Source: Stacks 0DV5 (3), Weil II (1.1.1), (1.1.6)
(blueprint: def-pod-galois-correspondence-data-e4). -/
def galoisFiniteLimits
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (G : Type u) [Group G] [TopologicalSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    (d : GaloisLisseFiniteData y G) : Prop :=
  ∀ (Λ : Type (u + 1)) [Ring Λ] [Finite Λ], PreservesFiniteLimits (d.e Λ).functor

/-- Clause `finiteColimits` of the finite correspondence.
Source: Stacks 0DV5 (3), Weil II (1.1.1), (1.1.6)
(blueprint: def-pod-galois-correspondence-data-e4). -/
def galoisFiniteColimits
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (G : Type u) [Group G] [TopologicalSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    (d : GaloisLisseFiniteData y G) : Prop :=
  ∀ (Λ : Type (u + 1)) [Ring Λ] [Finite Λ], PreservesFiniteColimits (d.e Λ).functor

/-- Clause `finiteUnit` of the finite correspondence.
Source: Stacks 0DV5 (3), Weil II (1.1.1), (1.1.6)
(blueprint: def-pod-galois-correspondence-data-e4). -/
def galoisFiniteUnit
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (G : Type u) [Group G] [TopologicalSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    (d : GaloisLisseFiniteData y G) : Prop :=
  ∀ (Λ : Type (u + 1)) [Ring Λ] [Finite Λ], (∃ C : LisseModuleSheafCategory Y Λ, C.obj =
    (constantSheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ) ∧ Nonempty
    (((d.e Λ).functor.obj C).obj ≅ Rep.trivial Λ G Λ))

/-- Clause `finiteEvaluationAction` of the finite correspondence.
Source: Stacks 0DV5 (3), Weil II (1.1.1), (1.1.6)
(blueprint: def-pod-galois-correspondence-data-e4). -/
def galoisFiniteEvaluationAction
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (G : Type u) [Group G] [TopologicalSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    (d : GaloisLisseFiniteData y G) : Prop :=
  ∀ (Λ : Type (u + 1)) [Ring Λ] [Finite Λ], ∀ F : LisseModuleSheafCategory Y Λ, ∃ h :
    IsLisseEtaleSheafOfSets (galoisUnderlyingSetSheaf Λ F.obj), ∃ κ :
    (((pointSmallEtale y).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj F.obj) ≃ (((pointSmallEtale
    y).sheafFiber (A := Type (u + 1))).obj (galoisUnderlyingSetSheaf Λ F.obj)), (∀ (U : Y.Etale) (x
    : (pointSmallEtale y).fiber.obj U) (s : F.obj.obj.obj (op U)), κ ((pointSmallEtale
    y).toPresheafFiber U x F.obj.obj s) = (pointSmallEtale y).toPresheafFiber U x
    (galoisUnderlyingSetSheaf Λ F.obj).obj s) ∧ ∀ (g : G) (z : ((d.e Λ).functor.obj F).obj.V), κ
    ((d.τ Λ).hom.app F (((d.e Λ).functor.obj F).obj.ρ g z)) = (d.γ g).asIso.hom.app
    (galoisUnderlyingFLC Λ F.obj h) (κ ((d.τ Λ).hom.app F z))

/-- Clause `finiteTensor` of the finite correspondence.
Source: Stacks 0DV5 (3), Weil II (1.1.1), (1.1.6)
(blueprint: def-pod-galois-correspondence-data-e4). -/
def galoisFiniteTensor
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (G : Type u) [Group G] [TopologicalSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    (d : GaloisLisseFiniteData y G) : Prop :=
  ∀ (R : Type (u + 1)) [CommRing R] [Finite R], ∃ (m : MonoidalCategory (LisseModuleSheafCategory Y
    R)) (b : @BraidedCategory (LisseModuleSheafCategory Y R) _ m), Nonempty (@Functor.Braided
    (LisseModuleSheafCategory Y R) _ m b (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R)) _
    (Sheaf.monoidalCategory Y.smallEtaleTopology (ModuleCat.{u + 1} R)) (Sheaf.braidedCategory
    Y.smallEtaleTopology (ModuleCat.{u + 1} R)) (ObjectProperty.ι _)) ∧ Nonempty (@Functor.Braided
    (LisseModuleSheafCategory Y R) _ m b (Rep.{u + 1} R G) _ _ _ ((d.e R).functor ⋙ ObjectProperty.ι
    _)) ∧ ∃ F : LisseModuleSheafCategory Y R, F.obj = (constantSheaf Y.smallEtaleTopology
    (ModuleCat.{u + 1} R)).obj (ModuleCat.of R R) ∧ Nonempty (((d.e R).functor.obj F).obj ≅
    Rep.trivial R G R)

/-- Clause `finiteScalarExtension` of the finite correspondence.
Source: Stacks 0DV5 (3), Weil II (1.1.1), (1.1.6)
(blueprint: def-pod-galois-correspondence-data-e4). -/
def galoisFiniteScalarExtension
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (G : Type u) [Group G] [TopologicalSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    (d : GaloisLisseFiniteData y G) : Prop :=
  ∃ (B : ∀ (R S : Type (u + 1)) [Ring R] [Finite R] [Ring S] [Finite S], (R →+* S) →
    (LisseModuleSheafCategory Y R ⥤ LisseModuleSheafCategory Y S)) (α : ∀ (R S : Type (u + 1)) [Ring
    R] [Finite R] [Ring S] [Finite S] (f : R →+* S), B R S f ⋙ ObjectProperty.ι _ ≅ ObjectProperty.ι
    _ ⋙ Sheaf.ringExtendScalars.{u + 1, u + 1} Y.smallEtaleTopology f) (β : ∀ (R S : Type (u + 1))
    [Ring R] [Finite R] [Ring S] [Finite S] (f : R →+* S), B R S f ⋙ (d.e S).functor ⋙
    ObjectProperty.ι _ ≅ (d.e R).functor ⋙ ObjectProperty.ι _ ⋙ (Rep.repIsoAction R G).functor ⋙
    (ModuleCat.ringExtendScalars.{u + 1, u + 1} f).mapAction G ⋙ (Rep.repIsoAction S G).inverse), ∀
    (R S T : Type (u + 1)) [Ring R] [Finite R] [Ring S] [Finite S] [Ring T] [Finite T] (f : R →+* S)
    (g : S →+* T), ∃ c : B R S f ⋙ B S T g ≅ B R T (g.comp f), (∀ (F : LisseModuleSheafCategory Y R)
    (z : ((d.e T).functor.obj ((B S T g).obj ((B R S f).obj F))).obj.V), ((β R T (g.comp f)).hom.app
    F).hom (((d.e T).functor.map (c.hom.app F)).hom.hom z) = (ModuleCat.ringExtensionComp.{u + 1, u
    + 1} f g).hom.app (ModuleCat.of R ((d.e R).functor.obj F).obj.V)
    ((ModuleCat.ringExtendScalars.{u + 1, u + 1} g).map ((forget₂ (Rep.{u + 1} S G) (ModuleCat.{u +
    1} S)).map ((β R S f).hom.app F)) (((β S T g).hom.app ((B R S f).obj F)).hom z))) ∧ ∀ (F :
    LisseModuleSheafCategory Y R) (U : Y.Etale) (a : S) (b : T) (z : F.obj.obj.obj (op U)), ((α R T
    (g.comp f)).hom.app F).hom.app (op U) ((c.hom.app F).hom.hom.app (op U) (((α S T g).inv.app ((B
    R S f).obj F)).hom.app (op U) (((toSheafification Y.smallEtaleTopology (ModuleCat.{u + 1}
    T)).app (((B R S f).obj F).obj.obj ⋙ ModuleCat.ringExtendScalars.{u + 1, u + 1} g)).app (op U)
    (ModuleCat.ringExtensionTmul.{u + 1, u + 1} g _ b (((α R S f).inv.app F).hom.app (op U)
    (((toSheafification Y.smallEtaleTopology (ModuleCat.{u + 1} S)).app (F.obj.obj ⋙
    ModuleCat.ringExtendScalars.{u + 1, u + 1} f)).app (op U) (ModuleCat.ringExtensionTmul.{u + 1, u
    + 1} f _ a z))))))) = ((toSheafification Y.smallEtaleTopology (ModuleCat.{u + 1} T)).app
    (F.obj.obj ⋙ ModuleCat.ringExtendScalars.{u + 1, u + 1} (g.comp f))).app (op U)
    (ModuleCat.ringExtensionTmul.{u + 1, u + 1} (g.comp f) _ (b * g a) z)

attribute [local irreducible] galoisYonedaComparison
  galoisFiniteEtaleAction galoisFiniteAbelian galoisFiniteKernels galoisFiniteCokernels
  galoisFiniteLimits galoisFiniteColimits galoisFiniteUnit galoisFiniteEvaluationAction
  galoisFiniteTensor galoisFiniteScalarExtension

set_option genSizeOfSpec false in
set_option genInjectivity false in
/-- The simultaneous finite-coefficient correspondence and all clauses of part (1).
Source: Stacks 0DV5 (3) (blueprint: def-pod-galois-correspondence-data-e4). -/
structure GaloisLisseFiniteCorrespondence
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (G : Type u) [Group G] [TopologicalSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    extends GaloisLisseFiniteData y G where
  yonedaComparison : galoisYonedaComparison y G toGaloisLisseFiniteData
  finiteEtaleAction : galoisFiniteEtaleAction y G toGaloisLisseFiniteData
  finiteAbelian : galoisFiniteAbelian y G toGaloisLisseFiniteData
  finiteKernels : galoisFiniteKernels y G toGaloisLisseFiniteData
  finiteCokernels : galoisFiniteCokernels y G toGaloisLisseFiniteData
  finiteLimits : galoisFiniteLimits y G toGaloisLisseFiniteData
  finiteColimits : galoisFiniteColimits y G toGaloisLisseFiniteData
  finiteUnit : galoisFiniteUnit y G toGaloisLisseFiniteData
  finiteEvaluationAction : galoisFiniteEvaluationAction y G toGaloisLisseFiniteData
  finiteTensor : galoisFiniteTensor y G toGaloisLisseFiniteData
  finiteScalarExtension : galoisFiniteScalarExtension y G toGaloisLisseFiniteData

set_option genSizeOfSpec false in
set_option genInjectivity false in
/-- The profinite model, three equivalences and fibre comparisons of part (2).
Source: Weil II (0.1), (1.1.1), (1.1.6)
(blueprint: def-pod-galois-correspondence-data-e4). -/
structure GaloisLisseAdicData
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (G : Type u) [Group G] [TopologicalSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    (c : GaloisLisseFiniteCorrespondence y G)
    (l : ℕ) [Fact l.Prime] [IsNoetherian Y] [Y.IsSeparated]
    [∀ x : Y, Invertible (l : Y.residueField x)]
    (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q] where
  P : ProfiniteGrp.{u}
  δ : G ≃ₜ* P
  eI : ∀ E : Padic.FiniteCoefficientFields l Q, LisseIntegralSheaf l E.val Y ≌
    galoisIntegralRepresentations l E.val P δ
  eR : ∀ E : Padic.FiniteCoefficientFields l Q, LisseRationalSheaf l E.val Y ≌
    galoisCoefficientRepresentations l E.val P δ
  eA : LisseAlgebraicSheaf l Y Q ≌ galoisAdicRepresentations l Q P δ
  τI : ∀ E : Padic.FiniteCoefficientFields l Q, (eI E).functor ⋙ ObjectProperty.ι _ ⋙ forget₂
    (Rep.{u + 1} (Padic.coefficientExtensionIntegers l E.val) G) (ModuleCat.{u + 1}
    (Padic.coefficientExtensionIntegers l E.val)) ≅ lisseIntegralFiberFunctor l E.val Y y
  τR : ∀ E : Padic.FiniteCoefficientFields l Q, (eR E).functor ⋙ ObjectProperty.ι _ ⋙ forget₂
    (Rep.{u + 1} E.val G) (ModuleCat.{u + 1} E.val) ≅ lisseRationalFiberFunctor l E.val Y y
  τA : eA.functor ⋙ ObjectProperty.ι _ ⋙ forget₂ (Rep.{u + 1} Q G) (ModuleCat.{u + 1} Q) ≅
    lisseAlgebraicFiberFunctor l Y y Q

/-- Clause `rationalSheavesAbelian` of the adic correspondence.
Source: Stacks 0DV5 (3), Weil II (1.1.1), (1.1.6)
(blueprint: def-pod-galois-correspondence-data-e4). -/
def galoisRationalSheavesAbelian
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (G : Type u) [Group G] [TopologicalSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    (c : GaloisLisseFiniteCorrespondence y G)
    (l : ℕ) [Fact l.Prime] [IsNoetherian Y] [Y.IsSeparated]
    [∀ x : Y, Invertible (l : Y.residueField x)]
    (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]
    (_d : GaloisLisseAdicData y G c l Q) : Prop :=
  ∀ E : Padic.FiniteCoefficientFields l Q, Nonempty (Abelian (LisseRationalSheaf l E.val Y))

/-- Clause `rationalRepresentationsAbelian` of the adic correspondence.
Source: Stacks 0DV5 (3), Weil II (1.1.1), (1.1.6)
(blueprint: def-pod-galois-correspondence-data-e4). -/
def galoisRationalRepresentationsAbelian
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (G : Type u) [Group G] [TopologicalSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    (c : GaloisLisseFiniteCorrespondence y G)
    (l : ℕ) [Fact l.Prime] [IsNoetherian Y] [Y.IsSeparated]
    [∀ x : Y, Invertible (l : Y.residueField x)]
    (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]
    (d : GaloisLisseAdicData y G c l Q) : Prop :=
  ∀ E : Padic.FiniteCoefficientFields l Q, Nonempty (Abelian (galoisCoefficientRepresentations l
    E.val d.P d.δ))

/-- Clause `rationalFiniteLimits` of the adic correspondence.
Source: Stacks 0DV5 (3), Weil II (1.1.1), (1.1.6)
(blueprint: def-pod-galois-correspondence-data-e4). -/
def galoisRationalFiniteLimits
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (G : Type u) [Group G] [TopologicalSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    (c : GaloisLisseFiniteCorrespondence y G)
    (l : ℕ) [Fact l.Prime] [IsNoetherian Y] [Y.IsSeparated]
    [∀ x : Y, Invertible (l : Y.residueField x)]
    (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]
    (d : GaloisLisseAdicData y G c l Q) : Prop :=
  ∀ E : Padic.FiniteCoefficientFields l Q, PreservesFiniteLimits (d.eR E).functor

/-- Clause `rationalFiniteColimits` of the adic correspondence.
Source: Stacks 0DV5 (3), Weil II (1.1.1), (1.1.6)
(blueprint: def-pod-galois-correspondence-data-e4). -/
def galoisRationalFiniteColimits
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (G : Type u) [Group G] [TopologicalSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    (c : GaloisLisseFiniteCorrespondence y G)
    (l : ℕ) [Fact l.Prime] [IsNoetherian Y] [Y.IsSeparated]
    [∀ x : Y, Invertible (l : Y.residueField x)]
    (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]
    (d : GaloisLisseAdicData y G c l Q) : Prop :=
  ∀ E : Padic.FiniteCoefficientFields l Q, PreservesFiniteColimits (d.eR E).functor

/-- Clause `algebraicSheavesAbelian` of the adic correspondence.
Source: Stacks 0DV5 (3), Weil II (1.1.1), (1.1.6)
(blueprint: def-pod-galois-correspondence-data-e4). -/
def galoisAlgebraicSheavesAbelian
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (G : Type u) [Group G] [TopologicalSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    (c : GaloisLisseFiniteCorrespondence y G)
    (l : ℕ) [Fact l.Prime] [IsNoetherian Y] [Y.IsSeparated]
    [∀ x : Y, Invertible (l : Y.residueField x)]
    (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]
    (_d : GaloisLisseAdicData y G c l Q) : Prop :=
  Nonempty (Abelian (LisseAlgebraicSheaf l Y Q))

/-- Clause `algebraicRepresentationsAbelian` of the adic correspondence.
Source: Stacks 0DV5 (3), Weil II (1.1.1), (1.1.6)
(blueprint: def-pod-galois-correspondence-data-e4). -/
def galoisAlgebraicRepresentationsAbelian
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (G : Type u) [Group G] [TopologicalSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    (c : GaloisLisseFiniteCorrespondence y G)
    (l : ℕ) [Fact l.Prime] [IsNoetherian Y] [Y.IsSeparated]
    [∀ x : Y, Invertible (l : Y.residueField x)]
    (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]
    (d : GaloisLisseAdicData y G c l Q) : Prop :=
  Nonempty (Abelian (galoisAdicRepresentations l Q d.P d.δ))

/-- Clause `algebraicFiniteLimits` of the adic correspondence.
Source: Stacks 0DV5 (3), Weil II (1.1.1), (1.1.6)
(blueprint: def-pod-galois-correspondence-data-e4). -/
def galoisAlgebraicFiniteLimits
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (G : Type u) [Group G] [TopologicalSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    (c : GaloisLisseFiniteCorrespondence y G)
    (l : ℕ) [Fact l.Prime] [IsNoetherian Y] [Y.IsSeparated]
    [∀ x : Y, Invertible (l : Y.residueField x)]
    (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]
    (d : GaloisLisseAdicData y G c l Q) : Prop :=
  PreservesFiniteLimits d.eA.functor

/-- Clause `algebraicFiniteColimits` of the adic correspondence.
Source: Stacks 0DV5 (3), Weil II (1.1.1), (1.1.6)
(blueprint: def-pod-galois-correspondence-data-e4). -/
def galoisAlgebraicFiniteColimits
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (G : Type u) [Group G] [TopologicalSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    (c : GaloisLisseFiniteCorrespondence y G)
    (l : ℕ) [Fact l.Prime] [IsNoetherian Y] [Y.IsSeparated]
    [∀ x : Y, Invertible (l : Y.residueField x)]
    (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]
    (d : GaloisLisseAdicData y G c l Q) : Prop :=
  PreservesFiniteColimits d.eA.functor

/-- Clause `integralEvaluationAction` of the adic correspondence.
Source: Stacks 0DV5 (3), Weil II (1.1.1), (1.1.6)
(blueprint: def-pod-galois-correspondence-data-e4). -/
def galoisIntegralEvaluationAction
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (G : Type u) [Group G] [TopologicalSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    (c : GaloisLisseFiniteCorrespondence y G)
    (l : ℕ) [Fact l.Prime] [IsNoetherian Y] [Y.IsSeparated]
    [∀ x : Y, Invertible (l : Y.residueField x)]
    (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]
    (d : GaloisLisseAdicData y G c l Q) : Prop :=
  ∀ (E : Padic.FiniteCoefficientFields l Q) (F : LisseIntegralSheaf l E.val Y) (n : ℕ), ∃ h :
    IsLisseEtaleSheafOfSets (galoisUnderlyingSetSheaf
    (Padic.coefficientExtensionIntegers l E.val) (F.obj.obj (op n))), ∃ κ : (((pointSmallEtale
    y).ulift.{u + 1}.sheafFiber (A := ModuleCat.{u + 1} (Padic.coefficientExtensionIntegers l
    E.val))).obj (F.obj.obj (op n))) ≃ (((pointSmallEtale y).sheafFiber (A := Type (u + 1))).obj
    (galoisUnderlyingSetSheaf (Padic.coefficientExtensionIntegers l E.val) (F.obj.obj (op n)))), (∀
    (U : Y.Etale) (x : (pointSmallEtale y).fiber.obj U) (z : (F.obj.obj (op n)).obj.obj (op U)), κ
    ((pointSmallEtale y).ulift.{u + 1}.toPresheafFiber U ⟨x⟩ (F.obj.obj (op n)).obj z) =
    (pointSmallEtale y).toPresheafFiber U x (galoisUnderlyingSetSheaf
    (Padic.coefficientExtensionIntegers l E.val) (F.obj.obj (op n))).obj z) ∧ ∀ (g : G) (z : ((d.eI
    E).functor.obj F).obj.V), κ (limit.π (F.obj ⋙ (pointSmallEtale y).ulift.{u + 1}.sheafFiber) (op
    n) ((d.τI E).hom.app F (((d.eI E).functor.obj F).obj.ρ g z))) = (c.γ g).asIso.hom.app
    (galoisUnderlyingFLC (Padic.coefficientExtensionIntegers l E.val) (F.obj.obj (op n)) h) (κ
    (limit.π (F.obj ⋙ (pointSmallEtale y).ulift.{u + 1}.sheafFiber) (op n) ((d.τI E).hom.app F z)))

/-- Clause `rationalEvaluationAction` of the adic correspondence.
Source: Stacks 0DV5 (3), Weil II (1.1.1), (1.1.6)
(blueprint: def-pod-galois-correspondence-data-e4). -/
def galoisRationalEvaluationAction
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (G : Type u) [Group G] [TopologicalSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    (c : GaloisLisseFiniteCorrespondence y G)
    (l : ℕ) [Fact l.Prime] [IsNoetherian Y] [Y.IsSeparated]
    [∀ x : Y, Invertible (l : Y.residueField x)]
    (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]
    (d : GaloisLisseAdicData y G c l Q) : Prop :=
  ∀ (E : Padic.FiniteCoefficientFields l Q) (F : LisseRationalSheaf l E.val Y) (g : G) (a : E.val)
    (z : ((d.eI E).functor.obj F.integral).obj.V), eqToHom (lisseRationalFiberFunctor_obj l E.val Y
    y F) ((d.τR E).hom.app F (((d.eR E).functor.obj F).obj.ρ g ((d.τR E).inv.app F (eqToHom
    (lisseRationalFiberFunctor_obj l E.val Y y F).symm (TensorProduct.tmul _ a ((d.τI E).hom.app
    F.integral z)))))) = TensorProduct.tmul _ a ((d.τI E).hom.app F.integral (((d.eI E).functor.obj
    F.integral).obj.ρ g z))

/-- Clause `integralMonoidal` of the adic correspondence.
Source: Stacks 0DV5 (3), Weil II (1.1.1), (1.1.6)
(blueprint: def-pod-galois-correspondence-data-e4). -/
def galoisIntegralMonoidal
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (G : Type u) [Group G] [TopologicalSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    (c : GaloisLisseFiniteCorrespondence y G)
    (l : ℕ) [Fact l.Prime] [IsNoetherian Y] [Y.IsSeparated]
    [∀ x : Y, Invertible (l : Y.residueField x)]
    (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]
    (d : GaloisLisseAdicData y G c l Q) : Prop :=
  ∀ E : Padic.FiniteCoefficientFields l Q, ∃ m : MonoidalCategory (LisseIntegralSheaf l E.val Y),
    m.toMonoidalCategoryStruct.tensorObj = lisseIntegralTensor l E.val Y ∧
    @MonoidalCategoryStruct.tensorUnit (LisseIntegralSheaf l E.val Y) _ m.toMonoidalCategoryStruct =
    lisseIntegralUnit l E.val Y ∧ Nonempty (@Functor.Monoidal (LisseIntegralSheaf l E.val Y) _ m
    (Rep.{u + 1} (Padic.coefficientExtensionIntegers l E.val) G) _ _ ((d.eI E).functor ⋙
    ObjectProperty.ι _))

/-- Clause `rationalMonoidal` of the adic correspondence.
Source: Stacks 0DV5 (3), Weil II (1.1.1), (1.1.6)
(blueprint: def-pod-galois-correspondence-data-e4). -/
def galoisRationalMonoidal
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (G : Type u) [Group G] [TopologicalSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    (c : GaloisLisseFiniteCorrespondence y G)
    (l : ℕ) [Fact l.Prime] [IsNoetherian Y] [Y.IsSeparated]
    [∀ x : Y, Invertible (l : Y.residueField x)]
    (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]
    (d : GaloisLisseAdicData y G c l Q) : Prop :=
  ∀ E : Padic.FiniteCoefficientFields l Q, ∃ m : MonoidalCategory (LisseRationalSheaf l E.val Y),
    m.toMonoidalCategoryStruct.tensorObj = lisseRationalTensor l E.val Y ∧
    @MonoidalCategoryStruct.tensorUnit (LisseRationalSheaf l E.val Y) _ m.toMonoidalCategoryStruct =
    lisseRationalUnit l E.val Y ∧ Nonempty (@Functor.Monoidal (LisseRationalSheaf l E.val Y) _ m
    (Rep.{u + 1} E.val G) _ _ ((d.eR E).functor ⋙ ObjectProperty.ι _))

/-- Clause `algebraicMonoidal` of the adic correspondence.
Source: Stacks 0DV5 (3), Weil II (1.1.1), (1.1.6)
(blueprint: def-pod-galois-correspondence-data-e4). -/
def galoisAlgebraicMonoidal
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (G : Type u) [Group G] [TopologicalSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    (c : GaloisLisseFiniteCorrespondence y G)
    (l : ℕ) [Fact l.Prime] [IsNoetherian Y] [Y.IsSeparated]
    [∀ x : Y, Invertible (l : Y.residueField x)]
    (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]
    (d : GaloisLisseAdicData y G c l Q) : Prop :=
  ∃ m : MonoidalCategory (LisseAlgebraicSheaf l Y Q), m.toMonoidalCategoryStruct.tensorObj =
    lisseAlgebraicTensor l Y Q ∧ @MonoidalCategoryStruct.tensorUnit (LisseAlgebraicSheaf l Y Q) _
    m.toMonoidalCategoryStruct = lisseAlgebraicUnit l Y Q ∧ Nonempty (@Functor.Monoidal
    (LisseAlgebraicSheaf l Y Q) _ m (Rep.{u + 1} Q G) _ _ (d.eA.functor ⋙ ObjectProperty.ι _))

/-- Clause `integralTensor` of the adic correspondence.
Source: Stacks 0DV5 (3), Weil II (1.1.1), (1.1.6)
(blueprint: def-pod-galois-correspondence-data-e4). -/
def galoisIntegralTensor
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (G : Type u) [Group G] [TopologicalSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    (c : GaloisLisseFiniteCorrespondence y G)
    (l : ℕ) [Fact l.Prime] [IsNoetherian Y] [Y.IsSeparated]
    [∀ x : Y, Invertible (l : Y.residueField x)]
    (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]
    (d : GaloisLisseAdicData y G c l Q) : Prop :=
  ∀ E : Padic.FiniteCoefficientFields l Q, (∀ F H : LisseIntegralSheaf l E.val Y, ∃ c : (((d.eI
    E).functor.obj F).obj.V ⊗[(Padic.coefficientExtensionIntegers l E.val)] ((d.eI E).functor.obj
    H).obj.V) ≃ₗ[(Padic.coefficientExtensionIntegers l E.val)] ((d.eI E).functor.obj
    (lisseIntegralTensor l E.val Y F H)).obj.V, ∀ (g : G) (z : ((d.eI E).functor.obj F).obj.V
    ⊗[(Padic.coefficientExtensionIntegers l E.val)] ((d.eI E).functor.obj H).obj.V), c
    (galoisTensorAction (Padic.coefficientExtensionIntegers l E.val) ((d.eI E).functor.obj F).obj
    ((d.eI E).functor.obj H).obj g z) = ((d.eI E).functor.obj (lisseIntegralTensor l E.val Y F
    H)).obj.ρ g (c z))

/-- Clause `integralUnit` of the adic correspondence.
Source: Stacks 0DV5 (3), Weil II (1.1.1), (1.1.6)
(blueprint: def-pod-galois-correspondence-data-e4). -/
def galoisIntegralUnit
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (G : Type u) [Group G] [TopologicalSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    (c : GaloisLisseFiniteCorrespondence y G)
    (l : ℕ) [Fact l.Prime] [IsNoetherian Y] [Y.IsSeparated]
    [∀ x : Y, Invertible (l : Y.residueField x)]
    (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]
    (d : GaloisLisseAdicData y G c l Q) : Prop :=
  ∀ E : Padic.FiniteCoefficientFields l Q, Nonempty (((d.eI E).functor.obj (lisseIntegralUnit l
    E.val Y)).obj ≅ Rep.trivial (Padic.coefficientExtensionIntegers l E.val) G
    (Padic.coefficientExtensionIntegers l E.val))

/-- Clause `rationalTensor` of the adic correspondence.
Source: Stacks 0DV5 (3), Weil II (1.1.1), (1.1.6)
(blueprint: def-pod-galois-correspondence-data-e4). -/
def galoisRationalTensor
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (G : Type u) [Group G] [TopologicalSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    (c : GaloisLisseFiniteCorrespondence y G)
    (l : ℕ) [Fact l.Prime] [IsNoetherian Y] [Y.IsSeparated]
    [∀ x : Y, Invertible (l : Y.residueField x)]
    (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]
    (d : GaloisLisseAdicData y G c l Q) : Prop :=
  ∀ E : Padic.FiniteCoefficientFields l Q, (∀ F H : LisseRationalSheaf l E.val Y, ∃ c : (((d.eR
    E).functor.obj F).obj.V ⊗[E.val] ((d.eR E).functor.obj H).obj.V) ≃ₗ[E.val] ((d.eR E).functor.obj
    (lisseRationalTensor l E.val Y F H)).obj.V, ∀ (g : G) (z : ((d.eR E).functor.obj F).obj.V
    ⊗[E.val] ((d.eR E).functor.obj H).obj.V), c (galoisTensorAction E.val ((d.eR E).functor.obj
    F).obj ((d.eR E).functor.obj H).obj g z) = ((d.eR E).functor.obj (lisseRationalTensor l E.val Y
    F H)).obj.ρ g (c z))

/-- Clause `rationalUnit` of the adic correspondence.
Source: Stacks 0DV5 (3), Weil II (1.1.1), (1.1.6)
(blueprint: def-pod-galois-correspondence-data-e4). -/
def galoisRationalUnit
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (G : Type u) [Group G] [TopologicalSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    (c : GaloisLisseFiniteCorrespondence y G)
    (l : ℕ) [Fact l.Prime] [IsNoetherian Y] [Y.IsSeparated]
    [∀ x : Y, Invertible (l : Y.residueField x)]
    (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]
    (d : GaloisLisseAdicData y G c l Q) : Prop :=
  ∀ E : Padic.FiniteCoefficientFields l Q, Nonempty (((d.eR E).functor.obj (lisseRationalUnit l
    E.val Y)).obj ≅ Rep.trivial E.val G E.val)

/-- Clause `algebraicTensor` of the adic correspondence.
Source: Stacks 0DV5 (3), Weil II (1.1.1), (1.1.6)
(blueprint: def-pod-galois-correspondence-data-e4). -/
def galoisAlgebraicTensor
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (G : Type u) [Group G] [TopologicalSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    (c : GaloisLisseFiniteCorrespondence y G)
    (l : ℕ) [Fact l.Prime] [IsNoetherian Y] [Y.IsSeparated]
    [∀ x : Y, Invertible (l : Y.residueField x)]
    (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]
    (d : GaloisLisseAdicData y G c l Q) : Prop :=
  (∀ F H : LisseAlgebraicSheaf l Y Q, ∃ c : ((d.eA.functor.obj F).obj.V ⊗[Q] (d.eA.functor.obj
    H).obj.V) ≃ₗ[Q] (d.eA.functor.obj (lisseAlgebraicTensor l Y Q F H)).obj.V, ∀ (g : G) (z :
    (d.eA.functor.obj F).obj.V ⊗[Q] (d.eA.functor.obj H).obj.V), c (galoisTensorAction Q
    (d.eA.functor.obj F).obj (d.eA.functor.obj H).obj g z) = (d.eA.functor.obj (lisseAlgebraicTensor
    l Y Q F H)).obj.ρ g (c z))

/-- Clause `algebraicUnit` of the adic correspondence.
Source: Stacks 0DV5 (3), Weil II (1.1.1), (1.1.6)
(blueprint: def-pod-galois-correspondence-data-e4). -/
def galoisAlgebraicUnit
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (G : Type u) [Group G] [TopologicalSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    (c : GaloisLisseFiniteCorrespondence y G)
    (l : ℕ) [Fact l.Prime] [IsNoetherian Y] [Y.IsSeparated]
    [∀ x : Y, Invertible (l : Y.residueField x)]
    (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]
    (d : GaloisLisseAdicData y G c l Q) : Prop :=
  Nonempty ((d.eA.functor.obj (lisseAlgebraicUnit l Y Q)).obj ≅ Rep.trivial Q G Q)

/-- Clause `algebraicModelScalarExtension` of the adic correspondence.
Source: Stacks 0DV5 (3), Weil II (1.1.1), (1.1.6)
(blueprint: def-pod-galois-correspondence-data-e4). -/
def galoisAlgebraicModelScalarExtension
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (G : Type u) [Group G] [TopologicalSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    (c : GaloisLisseFiniteCorrespondence y G)
    (l : ℕ) [Fact l.Prime] [IsNoetherian Y] [Y.IsSeparated]
    [∀ x : Y, Invertible (l : Y.residueField x)]
    (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]
    (d : GaloisLisseAdicData y G c l Q) : Prop :=
  ∀ (E : Padic.FiniteCoefficientFields l Q) (F : LisseRationalSheaf l E.val Y), ∃ c : (Q ⊗[E.val]
    ((d.eR E).functor.obj F).obj.V) ≃ₗ[Q] (d.eA.functor.obj (lisseAlgebraicOfModel l Y Q E
    F)).obj.V, (∀ (g : G) (z : Q ⊗[E.val] ((d.eR E).functor.obj F).obj.V), c (galoisScalarAction
    E.val Q ((d.eR E).functor.obj F).obj g z) = (d.eA.functor.obj (lisseAlgebraicOfModel l Y Q E
    F)).obj.ρ g (c z)) ∧ ∀ (a : Q) (z : ((d.eR E).functor.obj F).obj.V), eqToHom
    (lisseAlgebraicFiber_ofModel l Y y Q E F) (eqToHom (lisseAlgebraicFiberFunctor_obj l Y y Q
    (lisseAlgebraicOfModel l Y Q E F)) (d.τA.hom.app _ (c (TensorProduct.tmul _ a z)))) =
    TensorProduct.tmul _ a (eqToHom (lisseRationalFiberFunctor_obj l E.val Y y F) ((d.τR E).hom.app
    F z))

/-- Clause `integralScalarExtension` of the adic correspondence.
Source: Stacks 0DV5 (3), Weil II (1.1.1), (1.1.6)
(blueprint: def-pod-galois-correspondence-data-e4). -/
def galoisIntegralScalarExtension
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (G : Type u) [Group G] [TopologicalSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    (c : GaloisLisseFiniteCorrespondence y G)
    (l : ℕ) [Fact l.Prime] [IsNoetherian Y] [Y.IsSeparated]
    [∀ x : Y, Invertible (l : Y.residueField x)]
    (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]
    (d : GaloisLisseAdicData y G c l Q) : Prop :=
  ∀ (E L : Padic.FiniteCoefficientFields l Q) (h : E ≤ L), Nonempty (lisseIntegralScalarExtension l
    E.val Y L.val (IntermediateField.inclusion h) ⋙ (d.eI L).functor ⋙ ObjectProperty.ι _ ≅ (d.eI
    E).functor ⋙ ObjectProperty.ι _ ⋙ (Rep.repIsoAction (Padic.coefficientExtensionIntegers l E.val)
    G).functor ⋙ (ModuleCat.ringExtendScalars.{u + 1, u + 1} (lisseIntegerInclusion l E.val L.val
    (IntermediateField.inclusion h))).mapAction G ⋙ (Rep.repIsoAction
    (Padic.coefficientExtensionIntegers l L.val) G).inverse)

/-- Clause `rationalScalarExtension` of the adic correspondence.
Source: Stacks 0DV5 (3), Weil II (1.1.1), (1.1.6)
(blueprint: def-pod-galois-correspondence-data-e4). -/
def galoisRationalScalarExtension
    {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (y : Spec (.of Ω) ⟶ Y) (G : Type u) [Group G] [TopologicalSpace G]
    [∀ P, MulAction G ((FiniteEtale.fiber y).obj P)]
    (c : GaloisLisseFiniteCorrespondence y G)
    (l : ℕ) [Fact l.Prime] [IsNoetherian Y] [Y.IsSeparated]
    [∀ x : Y, Invertible (l : Y.residueField x)]
    (Q : Type (u + 1)) [Field Q] [Algebra ℚ_[l] Q] [IsAlgClosure ℚ_[l] Q]
    (d : GaloisLisseAdicData y G c l Q) : Prop :=
  ∀ (E L : Padic.FiniteCoefficientFields l Q) (h : E ≤ L) [_aEL : Algebra E.val L.val] (_haEL :
    algebraMap E.val L.val = (IntermediateField.inclusion h).toRingHom), ∃ c : ∀ F :
    LisseRationalSheaf l E.val Y, (L.val ⊗[E.val] ((d.eR E).functor.obj F).obj.V) ≃ₗ[L.val] ((d.eR
    L).functor.obj ((lisseRationalScalarExtension l E.val Y L.val (IntermediateField.inclusion
    h)).obj F)).obj.V, (∀ (F : LisseRationalSheaf l E.val Y) (g : G) (z : L.val ⊗[E.val] ((d.eR
    E).functor.obj F).obj.V), c F (galoisScalarAction E.val L.val ((d.eR E).functor.obj F).obj g z)
    = ((d.eR L).functor.obj ((lisseRationalScalarExtension l E.val Y L.val
    (IntermediateField.inclusion h)).obj F)).obj.ρ g (c F z)) ∧ ∀ (F H : LisseRationalSheaf l E.val
    Y) (f : F ⟶ H) (z : L.val ⊗[E.val] ((d.eR E).functor.obj F).obj.V), c H (LinearMap.baseChange
    L.val (((d.eR E).functor.map f).hom.hom.toLinearMap) z) = ((d.eR L).functor.map
    ((lisseRationalScalarExtension l E.val Y L.val (IntermediateField.inclusion h)).map f)).hom.hom
    (c F z)

attribute [local irreducible] galoisRationalSheavesAbelian
  galoisRationalRepresentationsAbelian galoisRationalFiniteLimits galoisRationalFiniteColimits
  galoisAlgebraicSheavesAbelian galoisAlgebraicRepresentationsAbelian
  galoisAlgebraicFiniteLimits galoisAlgebraicFiniteColimits galoisIntegralEvaluationAction
  galoisRationalEvaluationAction galoisIntegralMonoidal galoisRationalMonoidal
  galoisAlgebraicMonoidal galoisIntegralTensor galoisIntegralUnit galoisRationalTensor
  galoisRationalUnit galoisAlgebraicTensor galoisAlgebraicUnit
  galoisAlgebraicModelScalarExtension galoisIntegralScalarExtension
  galoisRationalScalarExtension

end AlgebraicGeometry.Scheme
