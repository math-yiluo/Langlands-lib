import Langlands.AlgebraicGeometry.LangWeil.FiniteAlgebraPointBound
import Mathlib.AlgebraicGeometry.AffineSpace

/-! # Uniform point bounds for finite morphisms and points of affine space -/

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.LangWeil

set_option backward.isDefEq.respectTransparency.types false in
/-- Over an affine target, a finite morphism has uniformly bounded field-valued fibres. -/
theorem exists_uniform_card_finiteMorphism_le {X Y : Scheme.{u}} [IsAffine Y]
    (f : X ⟶ Y) [IsFinite f] :
    ∃ N : ℕ, ∀ (K : Type u) [Field K] (s : Spec (.of K) ⟶ Y),
      Finite {x : Spec (.of K) ⟶ X // x ≫ f = s} ∧
      Nat.card {x : Spec (.of K) ⟶ X // x ≫ f = s} ≤ N := by
  have : IsAffine X := isAffine_of_isAffineHom f
  let : Algebra Γ(Y, ⊤) Γ(X, ⊤) := f.appTop.hom.toAlgebra
  have : Module.Finite Γ(Y, ⊤) Γ(X, ⊤) := f.finite_appTop
  obtain ⟨N, hN⟩ := exists_uniform_card_algHom_le Γ(Y, ⊤) Γ(X, ⊤)
  refine ⟨N, ?_⟩
  intro K _ s
  let s' : Γ(Y, ⊤) ⟶ CommRingCat.of K :=
    s.appTop ≫ (Scheme.ΓSpecIso (.of K)).hom
  let : Algebra Γ(Y, ⊤) K := s'.hom.toAlgebra
  let ev : {x : Spec (.of K) ⟶ X // x ≫ f = s} → (Γ(X, ⊤) →ₐ[Γ(Y, ⊤)] K) :=
    fun x =>
      { toRingHom := (x.1.appTop ≫ (Scheme.ΓSpecIso (.of K)).hom).hom
        commutes' := fun r => by
          have hx : f.appTop ≫ x.1.appTop ≫ (Scheme.ΓSpecIso (.of K)).hom = s' := by
            rw [← Category.assoc, ← Scheme.Hom.comp_appTop, x.2]
          exact congrArg (fun z : Γ(Y, ⊤) ⟶ CommRingCat.of K => z.hom r) hx }
  have hev : Function.Injective ev := by
    intro x y h
    apply Subtype.ext
    apply ext_of_isAffine
    apply (cancel_mono (Scheme.ΓSpecIso (.of K)).hom).mp
    ext r
    exact DFunLike.congr_fun h r
  obtain ⟨hfin, hcard⟩ := hN K
  let := hfin
  exact ⟨Finite.of_injective ev hev,
    (Nat.card_le_card_of_injective ev hev).trans hcard⟩

/-- Points of relative affine space above a fixed field-valued base point are its
coordinate vectors. -/
noncomputable def affineSpacePointEquiv (T : Scheme.{u}) (n : Type u)
    (K : Type u) [Field K] (s : Spec (.of K) ⟶ T) :
    {a : Spec (.of K) ⟶ AffineSpace n T // a ≫ (AffineSpace n T ↘ T) = s} ≃
      (n → Γ(Spec (.of K), ⊤)) where
  toFun a i := a.1.appTop (AffineSpace.coord T i)
  invFun v := ⟨AffineSpace.homOfVector s v, AffineSpace.homOfVector_over s v⟩
  left_inv a := by
    apply Subtype.ext
    apply AffineSpace.hom_ext
    · exact (AffineSpace.homOfVector_over _ _).trans a.2.symm
    · intro i
      exact AffineSpace.homOfVector_appTop_coord _ _ _
  right_inv v := by
    funext i
    exact AffineSpace.homOfVector_appTop_coord _ _ _

/-- Relative affine `d`-space has exactly `q^d` points above a fixed point over a
finite field of cardinality `q`. -/
theorem card_affineSpace_fibrePoints (T : Scheme.{u}) (d : ℕ)
    (K : Type u) [Field K] [Finite K] (s : Spec (.of K) ⟶ T) :
    Finite {a : Spec (.of K) ⟶ AffineSpace (ULift.{u} (Fin d)) T //
      a ≫ (AffineSpace (ULift.{u} (Fin d)) T ↘ T) = s} ∧
    Nat.card {a : Spec (.of K) ⟶ AffineSpace (ULift.{u} (Fin d)) T //
      a ≫ (AffineSpace (ULift.{u} (Fin d)) T ↘ T) = s} = Nat.card K ^ d := by
  let e := affineSpacePointEquiv T (ULift.{u} (Fin d)) K s
  let r := (Scheme.ΓSpecIso (.of K)).commRingCatIsoToRingEquiv.toEquiv
  have : Finite Γ(Spec (.of K), ⊤) := Finite.of_equiv K r.symm
  refine ⟨Finite.of_equiv _ e.symm, ?_⟩
  rw [Nat.card_congr e, Nat.card_fun, Nat.card_congr r]
  simp

end Langlands.AlgebraicGeometry.LangWeil
