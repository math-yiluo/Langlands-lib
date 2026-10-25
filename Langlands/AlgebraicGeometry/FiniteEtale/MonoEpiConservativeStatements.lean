import Langlands.AlgebraicGeometry.FiniteEtale.StructuralStatements

open CategoryTheory CategoryTheory.Limits

universe u

namespace Langlands.AlgebraicGeometry.FiniteEtale

open _root_.AlgebraicGeometry

/-- Every monomorphism of finite étale covers exhibits its source as a direct
summand of its target. -/
def GeometricMonomorphismComplements {S : Scheme.{u}} [ConnectedSpace S]
    [IsLocallyNoetherian S] {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) (hfin : ∀ Y : Cover S, Finite (Fiber s Y)) : Prop :=
  ∀ {X Y : Cover S} (i : X ⟶ Y) [Mono i],
    ∃ (Z : Cover S) (v : Z ⟶ Y), Nonempty (IsColimit (BinaryCofan.mk i v))

/-- The actual geometric fibre functor preserves categorical epimorphisms. -/
def GeometricEpimorphismPreservation {S : Scheme.{u}} [ConnectedSpace S]
    [IsLocallyNoetherian S] {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) (hfin : ∀ Y : Cover S, Finite (Fiber s Y)) : Prop :=
  Functor.PreservesEpimorphisms (fiberFunctor s hfin)

/-- The actual geometric fibre functor reflects isomorphisms. -/
def GeometricFiberConservative {S : Scheme.{u}} [ConnectedSpace S]
    [IsLocallyNoetherian S] {Ω : Type u} [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ S) (hfin : ∀ Y : Cover S, Finite (Fiber s Y)) : Prop :=
  (fiberFunctor s hfin).ReflectsIsomorphisms

end Langlands.AlgebraicGeometry.FiniteEtale
