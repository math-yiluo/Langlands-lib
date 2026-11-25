/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GlobalSectionsBijective

/-!
# Global functions on a proper scheme over a field

Let `X` be a proper scheme over a field `k`.

- If `X` is integral, then `Γ(X, 𝒪_X)` is a field, finite over `k`
  (`AlgebraicGeometry.Scheme.isField_globalSections_of_universallyClosed`,
  `AlgebraicGeometry.Scheme.finite_globalSectionsRingHom_of_isProper`).
- If `X` is geometrically integral, then `Γ(X, 𝒪_X) = k`
  (`AlgebraicGeometry.Scheme.GlobalSectionsBijective.of_geometricallyIntegral`).
- If `X` is geometrically reduced, then `Γ(X, 𝒪_X) = k` if and only if `X` is geometrically
  connected (`AlgebraicGeometry.Scheme.globalSectionsBijective_iff_geometricallyConnected`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]

/-- **Global functions on a proper integral scheme.** If `X` is integral and universally closed
(for instance proper) over a field `k`, then `Γ(X, 𝒪_X)` is a field: it is a domain which is
integral over `k` (`AlgebraicGeometry.Scheme.isIntegral_globalSectionsRingHom`). For proper `X`
it is moreover finite over `k` by finiteness of coherent cohomology
(`AlgebraicGeometry.Scheme.finite_globalSectionsRingHom_of_isProper`), so it is a finite field
extension of `k`. Part (2) of the blueprint node is
`AlgebraicGeometry.Scheme.GlobalSectionsBijective.of_geometricallyIntegral`.

(blueprint: `prose-C-04`) -/
theorem isField_globalSections_of_universallyClosed [UniversallyClosed (X ↘ Spec (.of k))]
    [IsIntegral X] : IsField Γ(X, ⊤) := by
  let : Algebra k Γ(X, ⊤) := (globalSectionsRingHom k (X := X)).toAlgebra
  have : Algebra.IsIntegral k Γ(X, ⊤) := ⟨isIntegral_globalSectionsRingHom (k := k) (X := X)⟩
  exact isField_of_isIntegral_of_isField' (R := k) (Field.toIsField k)

/-- **`H⁰(X, 𝒪_X) = k` is equivalent to geometric connectedness.** A proper geometrically
reduced scheme `X` over a field `k` has `Γ(X, 𝒪_X) = k` if and only if it is geometrically
connected. If `Γ(X, 𝒪_X) = k`, then by flat base change `Γ(X_K, 𝒪_{X_K}) = K` for every field
`K` over `k` (`AlgebraicGeometry.Scheme.GlobalSectionsBijective.pullback`), so `X_K` is connected;
the converse is Stacks 0BUG
(`AlgebraicGeometry.Scheme.GlobalSectionsBijective.of_geometricallyConnected`).

(blueprint: `lem-pc-h0-geom-connected`) -/
theorem globalSectionsBijective_iff_geometricallyConnected [IsProper (X ↘ Spec (.of k))]
    [GeometricallyReduced (X ↘ Spec (.of k))] :
    GlobalSectionsBijective k X ↔ GeometricallyConnected (X ↘ Spec (.of k)) := by
  refine ⟨fun _ ↦ ⟨?_⟩, fun _ ↦ inferInstance⟩
  rw [geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  intro K _ _
  exact GlobalSectionsBijective.connectedSpace (k := K)

end AlgebraicGeometry.Scheme
