import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! # Compatible norms on affine opens along a finite field-extension base change -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- For a scheme `X` over a field `K` and a finite field extension `L / K`, with
`π : X_L ⟶ X` the first projection of the actual pullback
`X_L = X ×_{Spec K} Spec L`, there is a family of multiplicative norm maps
`Γ(X_L, π⁻¹ U) → Γ(X, U)`, one for every affine open `U` of `X`, which commutes
with restriction along every inclusion of affine opens, raises functions pulled
back from `X` to the power `[L : K]`, and whose basic open is the set of points
of `U` whose whole fibre lies in the basic open of the function.
This proposition is a statement target, not a proof. -/
def FiniteFieldExtensionAffineNormStatement : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of K)),
    ∃ Nm : ∀ U : X.affineOpens,
        Γ(pullback p (Spec.map (CommRingCat.ofHom (algebraMap K L))),
          pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap K L))) ⁻¹ᵁ
            (U : X.Opens)) →*
          Γ(X, (U : X.Opens)),
      (∀ (U V : X.affineOpens) (hUV : (U : X.Opens) ≤ (V : X.Opens))
          (f : Γ(pullback p (Spec.map (CommRingCat.ofHom (algebraMap K L))),
            pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap K L))) ⁻¹ᵁ
              (V : X.Opens))),
        X.presheaf.map (homOfLE hUV).op (Nm V f) =
          Nm U ((pullback p (Spec.map (CommRingCat.ofHom (algebraMap K L)))).presheaf.map
            (homOfLE (Scheme.Hom.preimage_mono
              (pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap K L)))) hUV)).op f)) ∧
      (∀ (U : X.affineOpens) (g : Γ(X, (U : X.Opens))),
        Nm U ((pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap K L)))).app
            (U : X.Opens) g) =
          g ^ Module.finrank K L) ∧
      (∀ (U : X.affineOpens)
          (f : Γ(pullback p (Spec.map (CommRingCat.ofHom (algebraMap K L))),
            pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap K L))) ⁻¹ᵁ
              (U : X.Opens))),
        (X.basicOpen (Nm U f) : Set X) =
          {x : X | x ∈ (U : X.Opens) ∧
            ∀ y : (pullback p (Spec.map (CommRingCat.ofHom (algebraMap K L))) : Scheme.{u}),
            (pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap K L)))).base y = x →
              y ∈ (pullback p (Spec.map (CommRingCat.ofHom (algebraMap K L)))).basicOpen f})

end Langlands.AlgebraicGeometry.Picard
