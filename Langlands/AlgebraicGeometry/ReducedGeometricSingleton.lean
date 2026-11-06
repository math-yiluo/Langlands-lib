import Langlands.AlgebraicGeometry.ReducedGeometricSingletonStatement
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-! # Effective descent for a reduced geometric singleton -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- A reduced nonempty singleton of locally finite type over an algebraically closed
field has an isomorphic structure morphism. -/
theorem algClosedReducedSingleton_isIso
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of Ω))
    [LocallyOfFiniteType f] [AlgebraicGeometry.IsReduced X]
    [Nonempty X] [Subsingleton X] : IsIso f := by
  have : IrreducibleSpace X :=
    { toPreirreducibleSpace := inferInstance, toNonempty := inferInstance }
  let : IsIntegral X := isIntegral_of_irreducibleSpace_of_isReduced X
  let : Field Γ(X, ⊤) := (isField_of_isIntegral_of_subsingleton X).toField
  let g : CommRingCat.of Ω ⟶ Γ(X, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv ≫ f.appTop
  have heq : X.isoSpec.hom ≫ Spec.map g = f := by
    dsimp only [g]
    rw [Spec.map_comp, Scheme.isoSpec_hom_naturality_assoc,
      ← Scheme.isoSpec_Spec_inv]
    simp
  have hft : g.hom.FiniteType :=
    (HasRingHomProperty.appTop (P := @LocallyOfFiniteType) f inferInstance).comp
      (RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso
          (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv).2)
  algebraize [g.hom]
  have : Algebra.FiniteType Ω Γ(X, ⊤) := hft
  have : Module.Finite Ω Γ(X, ⊤) :=
    finite_of_finite_type_of_isJacobsonRing Ω Γ(X, ⊤)
  have hg : IsIso g :=
    (ConcreteCategory.isIso_iff_bijective _).mpr
      (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := Ω))
  rw [← heq]
  infer_instance

/-- Isomorphism of the actual geometric singleton descends along a field extension. -/
theorem reducedGeometricSingleton_isIso
    (K Ω : Type u) [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosed Ω]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType f]
    [AlgebraicGeometry.IsReduced
      (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K Ω))))]
    [Nonempty
      (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) : Scheme.{u})]
    [Subsingleton
      (pullback f (Spec.map (CommRingCat.ofHom (algebraMap K Ω))) : Scheme.{u})] :
    IsIso f := by
  let q := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
  have : Flat q := by
    apply (HasRingHomProperty.Spec_iff (P := @Flat)).mpr
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  have : Surjective q := inferInstance
  have : QuasiCompact q := inferInstance
  have hbase : IsIso (pullback.snd f q) :=
    algClosedReducedSingleton_isIso Ω _ (pullback.snd f q)
  exact MorphismProperty.of_pullback_snd_of_descendsAlong
    (P := MorphismProperty.isomorphisms Scheme.{u})
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (g := q)
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hbase

/-- Exact-target wrapper for the independently published proposition. -/
theorem reducedGeometricSingleton : ReducedGeometricSingletonStatement.{u} := by
  intro K Ω _ _ _ _ X f hf
  dsimp only
  intro hred hne hone
  exact @reducedGeometricSingleton_isIso K Ω _ _ _ _ X f hf hred hne hone

end Langlands.AlgebraicGeometry
