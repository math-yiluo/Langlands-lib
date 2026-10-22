import Langlands.Geometry.EtaleGodement
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.Homotopy

/-!
# Exactness of the constructed Godement resolution

The coaugmentation chain map is constructed below, with its degree-zero
formula and naturality proved. Exactness of the augmented resolution and of
its term functors are separate Prop-valued definitions, not assumed data.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Cohomology.CokernelComplex

universe u v

variable {A : Type u} [Category.{v} A] [Abelian A]
variable (T : A ⥤ A) (η : 𝟭 A ⟶ T)

/-- The constructed coaugmentation, now as a map of cochain complexes. -/
def augmentationMap (M : A) :
    (CochainComplex.single₀ A).obj M ⟶ complex T η M :=
  (CochainComplex.fromSingle₀Equiv _ M).symm
    ⟨augmentation T η M, augmentation_d T η M⟩

@[simp]
theorem augmentationMap_f_zero (M : A) :
    (augmentationMap T η M).f 0 = η.app M := by
  exact CochainComplex.fromSingle₀Equiv_symm_apply_f_zero
    (augmentation T η M) (augmentation_d T η M)

/-- The chain map is natural in the resolved object. -/
@[reassoc]
theorem augmentationMap_naturality {M N : A} (f : M ⟶ N) :
    (CochainComplex.single₀ A).map f ≫ augmentationMap T η N =
      augmentationMap T η M ≫ (functor T η).map f := by
  apply (CochainComplex.fromSingle₀Equiv _ M).injective
  apply Subtype.ext
  change ((CochainComplex.single₀ A).map f ≫ augmentationMap T η N).f 0 =
    (augmentationMap T η M ≫ (functor T η).map f).f 0
  simp only [HomologicalComplex.comp_f, CochainComplex.single₀_map_f_zero,
    augmentationMap_f_zero]
  exact η.naturality f

/-- The augmentation as an actual natural transformation of complex functors. -/
def augmentationNat : CochainComplex.single₀ A ⟶ functor T η where
  app := augmentationMap T η
  naturality _ _ f := augmentationMap_naturality T η f

end Langlands.Cohomology.CokernelComplex

namespace Langlands.Cohomology

universe u v

/-- Monicity of the coaugmentation suffices for the actual cokernel complex
to resolve its input. Exactness of the endofunctor is not required here. -/
def CokernelResolutionStatement : Prop :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A]
    (T : A ⥤ A) (η : 𝟭 A ⟶ T),
    (∀ M : A, Mono (η.app M)) →
    ∀ M : A, QuasiIso (CokernelComplex.augmentationMap T η M)

/-- An exact additive endofunctor with monic coaugmentation produces exact
residual and term functors at every stage of the cokernel construction. -/
def CokernelResolutionFunctorExactnessStatement : Prop :=
  ∀ (A : Type u) [Category.{v} A] [Abelian A]
    (T : A ⥤ A) [T.Additive] [PreservesFiniteLimits T]
    [PreservesFiniteColimits T] (η : 𝟭 A ⟶ T),
    (∀ M : A, Mono (η.app M)) →
    ∀ n : ℕ,
      (CokernelComplex.residual T η n).Additive ∧
      PreservesFiniteLimits (CokernelComplex.residual T η n) ∧
      PreservesFiniteColimits (CokernelComplex.residual T η n) ∧
      (CokernelComplex.term T η n).Additive ∧
      PreservesFiniteLimits (CokernelComplex.term T η n) ∧
      PreservesFiniteColimits (CokernelComplex.term T η n)

end Langlands.Cohomology

namespace Langlands.Sheaf.Godement

universe u v w wI uA vA uR

section FiberRetraction

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable {I : Type wI} (points : I → GrothendieckTopology.Point.{w} J)
variable (A : Type uA) [Category.{vA} A]
variable [HasProducts.{w} A] [HasProducts.{wI} A] [HasColimitsOfSize.{w, w} A]

/-- Projection to a chosen point followed by the adjunction counit. -/
def fiberRetraction (F : CategoryTheory.Sheaf J A) (i : I) :
    (points i).sheafFiber.obj ((zeroFunctor points A).obj F) ⟶
      (points i).sheafFiber.obj F :=
  (points i).sheafFiber.map ((Pi.π (fun j => pointFunctor points A j) i).app F) ≫
    (points i).skyscraperSheafAdjunction.counit.app ((points i).sheafFiber.obj F)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The adjunction identity proves that this is a retraction on the fiber. -/
@[reassoc (attr := simp)]
theorem fiber_coaugmentation_retraction (F : CategoryTheory.Sheaf J A) (i : I) :
    (points i).sheafFiber.map ((coaugmentation points A).app F) ≫
      fiberRetraction points A F i = 𝟙 _ := by
  unfold fiberRetraction
  rw [← Category.assoc, ← Functor.map_comp]
  have hπ := NatTrans.congr_app (coaugmentation_π points A i) F
  rw [NatTrans.comp_app] at hπ
  rw [hπ]
  exact (points i).skyscraperSheafAdjunction.left_triangle_components F

end FiberRetraction

/-- Jointly faithful point fibers make the constructed Godement augmentation
a quasi-isomorphism. No exactness of the degree-zero functor is assumed. -/
def ResolutionStatement : Prop :=
  ∀ (C : Type u) [Category.{v} C] (J : GrothendieckTopology C)
    (I : Type wI) (points : I → GrothendieckTopology.Point.{w} J)
    (A : Type uA) [Category.{vA} A] [Abelian A]
    [HasProducts.{w} A] [HasProducts.{wI} A]
    [HasColimitsOfSize.{w, w} A] [HasSheafify J A],
    JointlyFaithful (fun i => (points i).sheafFiber (A := A)) →
    ∀ F : CategoryTheory.Sheaf J A,
      QuasiIso
        (Cohomology.CokernelComplex.augmentationMap
          (zeroFunctor points A) (coaugmentation points A) F)

/-- For module coefficients the actual product-of-skyscrapers functor is
additive and exact. This target does not assume a conservative point family. -/
def ModuleZeroFunctorExactnessStatement : Prop :=
  ∀ (C : Type u) [Category.{v} C] [LocallySmall.{w} C] (J : GrothendieckTopology C)
    (I : Type w) (points : I → GrothendieckTopology.Point.{w} J)
    (R : Type uR) [Ring R] [HasSheafify J (ModuleCat.{w} R)],
      (zeroFunctor points (ModuleCat.{w} R)).Additive ∧
      PreservesFiniteLimits (zeroFunctor points (ModuleCat.{w} R)) ∧
      PreservesFiniteColimits (zeroFunctor points (ModuleCat.{w} R))

/-- With jointly faithful point fibers, every residual and term functor in
the module-valued Godement construction is additive and exact. -/
def ModuleTermFunctorExactnessStatement : Prop :=
  ∀ (C : Type u) [Category.{v} C] [LocallySmall.{w} C] (J : GrothendieckTopology C)
    (I : Type w) (points : I → GrothendieckTopology.Point.{w} J)
    (R : Type uR) [Ring R] [HasSheafify J (ModuleCat.{w} R)],
    JointlyFaithful (fun i => (points i).sheafFiber (A := ModuleCat.{w} R)) →
    ∀ n : ℕ,
      let T := zeroFunctor points (ModuleCat.{w} R)
      let η := coaugmentation points (ModuleCat.{w} R)
      (Cohomology.CokernelComplex.residual T η n).Additive ∧
      PreservesFiniteLimits (Cohomology.CokernelComplex.residual T η n) ∧
      PreservesFiniteColimits (Cohomology.CokernelComplex.residual T η n) ∧
      (Cohomology.CokernelComplex.term T η n).Additive ∧
      PreservesFiniteLimits (Cohomology.CokernelComplex.term T η n) ∧
      PreservesFiniteColimits (Cohomology.CokernelComplex.term T η n)

/-- On each chosen point fiber the constructed augmentation has a chain
retraction with the specified counit formula, and a contracting homotopy. -/
def ModuleFiberSplitResolutionStatement : Prop :=
  ∀ (C : Type u) [Category.{v} C] [LocallySmall.{w} C] (J : GrothendieckTopology C)
    (I : Type w) (points : I → GrothendieckTopology.Point.{w} J)
    (R : Type uR) [Ring R] [HasSheafify J (ModuleCat.{w} R)]
    (F : CategoryTheory.Sheaf J (ModuleCat.{w} R)) (i : I),
    let Φ := (points i).sheafFiber (A := ModuleCat.{w} R)
    let Φc := Φ.mapHomologicalComplex (ComplexShape.up ℕ)
    let K := Φc.obj (complex points (ModuleCat.{w} R) F)
    let S := Φc.obj ((CochainComplex.single₀ _).obj F)
    let a := Φc.map (Cohomology.CokernelComplex.augmentationMap
      (zeroFunctor points (ModuleCat.{w} R))
      (coaugmentation points (ModuleCat.{w} R)) F)
    ∃ r : K ⟶ S,
      r.f 0 = fiberRetraction points (ModuleCat.{w} R) F i ∧
      a ≫ r = 𝟙 S ∧ Nonempty (Homotopy (r ≫ a) (𝟙 K))

end Langlands.Sheaf.Godement

namespace Langlands.Geometry.EtaleGodement

universe u

/-- The geometric points of an actual scheme give an exact augmented
Godement resolution and exact term functors for its module-valued etale sheaves. -/
def ResolutionExactnessStatement : Prop :=
  ∀ (X : AlgebraicGeometry.Scheme.{u}) (R : Type u) [CommRing R],
    (∀ F : EtaleSheaf X R,
      QuasiIso
        (Cohomology.CokernelComplex.augmentationMap
          (zeroFunctor X R) (coaugmentation X R) F)) ∧
    ∀ n : ℕ,
      (Cohomology.CokernelComplex.term
        (zeroFunctor X R) (coaugmentation X R) n).Additive ∧
      PreservesFiniteLimits (Cohomology.CokernelComplex.term
        (zeroFunctor X R) (coaugmentation X R) n) ∧
      PreservesFiniteColimits (Cohomology.CokernelComplex.term
        (zeroFunctor X R) (coaugmentation X R) n)

end Langlands.Geometry.EtaleGodement

namespace Langlands.Cohomology

universe u v w wI uA vA uR

/-- A coherent family for the actual augmented cokernel and Godement
constructions. Every conjunct remains a separate theorem obligation. -/
def GodementExactnessStatements : Prop :=
  CokernelResolutionStatement.{uA, vA} ∧
  CokernelResolutionFunctorExactnessStatement.{uA, vA} ∧
  Sheaf.Godement.ResolutionStatement.{u, v, w, wI, uA, vA} ∧
  Sheaf.Godement.ModuleZeroFunctorExactnessStatement.{u, v, w, uR} ∧
  Sheaf.Godement.ModuleTermFunctorExactnessStatement.{u, v, w, uR} ∧
  Sheaf.Godement.ModuleFiberSplitResolutionStatement.{u, v, w, uR} ∧
  Geometry.EtaleGodement.ResolutionExactnessStatement.{u}

end Langlands.Cohomology
