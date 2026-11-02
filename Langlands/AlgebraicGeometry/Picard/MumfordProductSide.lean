import Langlands.AlgebraicGeometry.Picard.MumfordProductEulerCharacteristic
import Langlands.AlgebraicGeometry.Picard.MumfordSecondProjectionSupport

/-! # The product side of the Mumford-bundle computation on `A ×_K A` -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules
open Langlands.AlgebraicGeometry.Modules Langlands.AlgebraicGeometry.Modules.DerivedSections

/-- Anchor proposition of this module (internal). On the self-product `A ×_K A` of an abelian
scheme over a field, with addition `m` and projections `p₁, p₂`:
(1) for line bundles `L, M` with finite cohomology, `m^* L ⊗ p₁^* M` has finite cohomology and
`χ(m^* L ⊗ p₁^* M) = χ(L) χ(M)`; (2) the same for `m^* L ⊗ p₂^* M`; (3) given the theorem of the
square, over an algebraically closed field, for `H` ample and `N` a tensor inverse of `H`, every
higher direct image of `m^* H ⊗ p₁^* N` along `p₂` has finite closed support. -/
def MumfordProductSideStatement : Prop :=
  (∀ (K : Type u) [Field K] (A : AbelianScheme (Spec (CommRingCat.of K)))
    (L M : LineBundle A.X.left)
    (hL : HasFiniteCohomology A.X.hom L.obj) (hM : HasFiniteCohomology A.X.hom M.obj),
    HasFiniteCohomology (mumfordProduct A).hom
        (tensorObj ((Scheme.Modules.pullback (mumfordAddition A)).obj L.obj)
          ((Scheme.Modules.pullback (pullback.fst A.X.hom A.X.hom)).obj M.obj)) ∧
      ∀ hQ : HasFiniteCohomology (mumfordProduct A).hom
          (tensorObj ((Scheme.Modules.pullback (mumfordAddition A)).obj L.obj)
            ((Scheme.Modules.pullback (pullback.fst A.X.hom A.X.hom)).obj M.obj)),
        eulerCharacteristic (mumfordProduct A).hom
            (tensorObj ((Scheme.Modules.pullback (mumfordAddition A)).obj L.obj)
              ((Scheme.Modules.pullback (pullback.fst A.X.hom A.X.hom)).obj M.obj)) hQ =
          eulerCharacteristic A.X.hom L.obj hL * eulerCharacteristic A.X.hom M.obj hM) ∧
  (∀ (K : Type u) [Field K] (A : AbelianScheme (Spec (CommRingCat.of K)))
    (L M : LineBundle A.X.left)
    (hL : HasFiniteCohomology A.X.hom L.obj) (hM : HasFiniteCohomology A.X.hom M.obj),
    HasFiniteCohomology (mumfordProduct A).hom
        (tensorObj ((Scheme.Modules.pullback (mumfordAddition A)).obj L.obj)
          ((Scheme.Modules.pullback (pullback.snd A.X.hom A.X.hom)).obj M.obj)) ∧
      ∀ hQ : HasFiniteCohomology (mumfordProduct A).hom
          (tensorObj ((Scheme.Modules.pullback (mumfordAddition A)).obj L.obj)
            ((Scheme.Modules.pullback (pullback.snd A.X.hom A.X.hom)).obj M.obj)),
        eulerCharacteristic (mumfordProduct A).hom
            (tensorObj ((Scheme.Modules.pullback (mumfordAddition A)).obj L.obj)
              ((Scheme.Modules.pullback (pullback.snd A.X.hom A.X.hom)).obj M.obj)) hQ =
          eulerCharacteristic A.X.hom L.obj hL * eulerCharacteristic A.X.hom M.obj hM) ∧
  (Langlands.GroupScheme.FieldTheoremOfTheSquareStatement.{u} →
    ∀ (K : Type u) [Field K] [IsAlgClosed K] (A : AbelianScheme (Spec (CommRingCat.of K)))
      (H N : LineBundle A.X.left), H.IsAmple →
      Nonempty (tensorObj H.obj N.obj ≅ structureSheaf A.X.left) →
      ∀ n : ℕ, HasFiniteClosedSupport
        ((higherDirectImage (pullback.snd A.X.hom A.X.hom) n).obj
          (tensorObj ((Scheme.Modules.pullback (mumfordAddition A)).obj H.obj)
            ((Scheme.Modules.pullback (pullback.fst A.X.hom A.X.hom)).obj N.obj))))

/-- The anchor proposition holds. -/
theorem mumfordProductSide : MumfordProductSideStatement.{u} :=
  ⟨fun _ _ A L M hL hM => ⟨hasFiniteCohomology_mumfordAddition_tensor_fst A L M hL hM,
      eulerCharacteristic_mumfordAddition_tensor_fst A L M hL hM⟩,
    fun _ _ A L M hL hM => ⟨hasFiniteCohomology_mumfordAddition_tensor_snd A L M hL hM,
      eulerCharacteristic_mumfordAddition_tensor_snd A L M hL hM⟩,
    fun square _ _ _ A H N hH ⟨evaluation⟩ n =>
      hasFiniteClosedSupport_higherDirectImage_mumfordAddition_tensor_fst A square H N hH
        evaluation n⟩

end Langlands.AbelianScheme
