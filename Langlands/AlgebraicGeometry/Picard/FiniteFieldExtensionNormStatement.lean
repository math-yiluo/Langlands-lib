import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! # Norms of functions along the base change of a finite field extension -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- For a scheme `X` over a field `K` and a finite field extension `L / K`, with
`π : X_L ⟶ X` the first projection of the actual pullback
`X_L = X ×_{Spec K} Spec L`, there is a family of multiplicative norm maps
`Γ(X_L, π⁻¹ U) → Γ(X, U)`, one for every open `U` of `X`, which commutes with
restriction, raises functions pulled back from `X` to the power `[L : K]`, and
whose basic open is the set of points of `U` whose whole fibre lies in the basic
open of the function.
This proposition is a statement target, not a proof. -/
def FiniteFieldExtensionNormStatement : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of K)),
    ∃ Nm : ∀ U : X.Opens,
        Γ(pullback p (Spec.map (CommRingCat.ofHom (algebraMap K L))),
          pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap K L))) ⁻¹ᵁ U) →*
          Γ(X, U),
      (∀ (U V : X.Opens) (hUV : U ≤ V)
          (f : Γ(pullback p (Spec.map (CommRingCat.ofHom (algebraMap K L))),
            pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap K L))) ⁻¹ᵁ V)),
        X.presheaf.map (homOfLE hUV).op (Nm V f) =
          Nm U ((pullback p (Spec.map (CommRingCat.ofHom (algebraMap K L)))).presheaf.map
            (homOfLE (Scheme.Hom.preimage_mono
              (pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap K L)))) hUV)).op f)) ∧
      (∀ (U : X.Opens) (g : Γ(X, U)),
        Nm U ((pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap K L)))).app U g) =
          g ^ Module.finrank K L) ∧
      (∀ (U : X.Opens)
          (f : Γ(pullback p (Spec.map (CommRingCat.ofHom (algebraMap K L))),
            pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap K L))) ⁻¹ᵁ U)),
        (X.basicOpen (Nm U f) : Set X) =
          {x : X | x ∈ U ∧
            ∀ y : (pullback p (Spec.map (CommRingCat.ofHom (algebraMap K L))) : Scheme.{u}),
            (pullback.fst p (Spec.map (CommRingCat.ofHom (algebraMap K L)))).base y = x →
              y ∈ (pullback p (Spec.map (CommRingCat.ofHom (algebraMap K L)))).basicOpen f})

end Langlands.AlgebraicGeometry.Picard
