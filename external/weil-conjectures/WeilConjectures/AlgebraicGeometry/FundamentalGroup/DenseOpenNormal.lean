/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.DenseOpen
public import WeilConjectures.AlgebraicGeometry.NormalEtale

/-!
# The fundamental group of a dense open of a normal scheme surjects

Let `X` be a connected locally noetherian scheme whose local rings are integrally closed
domains and `j : U ⟶ X` an open immersion with `U` nonempty. A connected finite étale cover `P`
of `X` has integrally closed local domains as local rings again
(`AlgebraicGeometry.Scheme.isDomain_and_isIntegrallyClosed_stalk_of_etale_of_isDomain`), hence is
irreducible, so its restriction to `U`, a nonempty open subscheme of `P`, is irreducible, hence
connected. Consequently the map `π₁(U) → π₁(X)` is surjective (SGA 1, Exp. V, Prop. 8.2;
Stacks `0BQM`).
This is part (1) of the blueprint lemma `theorem-purity-real-sheaves-curves`; the regular case is
`WeilConjectures.AlgebraicGeometry.FundamentalGroup.DenseOpen`.

## Main statements

- `AlgebraicGeometry.Scheme.FiniteEtale.isConnected_pullback_of_isIntegrallyClosed_stalk`
- `AlgebraicGeometry.Scheme.FiniteEtale.fundamentalGroupMap_surjective_of_isIntegrallyClosed_stalk`
-/

@[expose] public section

universe u

open CategoryTheory PreGaloisCategory

namespace AlgebraicGeometry.Scheme.FiniteEtale

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- Blueprint `theorem-purity-real-sheaves-curves`, part (1), second formulation: a connected
finite étale cover of a connected locally noetherian normal scheme `X` stays connected over a
nonempty open `U`. The cover is normal, being étale over `X`, hence irreducible, and its
restriction to `U` is a nonempty open of it. -/
lemma isConnected_pullback_of_isIntegrallyClosed_stalk [IsLocallyNoetherian X]
    [ConnectedSpace X]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x))
    [Nonempty U] (P : X.FiniteEtale) [IsConnected P] : IsConnected ((pullback j).obj P) := by
  have := connectedSpace_of_isConnected P
  have : Etale P.obj.hom := P.obj.prop
  have : IsLocallyNoetherian P.obj.left :=
    LocallyOfFiniteType.isLocallyNoetherian (Y := X) P.obj.hom
  have := irreducibleSpace_of_isDomain_stalk P.obj.left fun x ↦
    (Scheme.isDomain_and_isIntegrallyClosed_stalk_of_etale_of_isDomain P.obj.hom hX x).1
  have := irreducibleSpace_of_isDomain_stalk X fun x ↦ (hX x).1
  have := connectedSpace_of_isOpenImmersion j
  exact isConnected_pullback_of_irreducibleSpace j P

variable [ConnectedSpace U] [ConnectedSpace X] {Ω Ω' : Type u} [Field Ω] [IsSepClosed Ω]
  [Field Ω'] [IsSepClosed Ω']
  {s : Spec (.of Ω) ⟶ U} {t : Spec (.of Ω') ⟶ X} (τ : pullback j ⋙ fiber s ≅ fiber t)
  (GU : Type u) [Group GU] [∀ P, MulAction GU ((fiber s).obj P)] [TopologicalSpace GU]
  [IsTopologicalGroup GU] [CompactSpace GU] [IsFundamentalGroup (fiber s) GU]
  (GX : Type u) [Group GX] [TopologicalSpace GX] [IsTopologicalGroup GX] [CompactSpace GX]
  [∀ P, MulAction GX ((fiber t).obj P)] [IsFundamentalGroup (fiber t) GX]

/-- Blueprint `theorem-purity-real-sheaves-curves`, part (1): **the fundamental group of a
nonempty open of a connected normal scheme surjects onto that of the scheme.** For a connected
locally noetherian scheme `X` whose local rings are integrally closed domains, an open immersion
`j : U ⟶ X` with `U` nonempty and a path `τ` between the fibre functors, the map
`π₁(U) → π₁(X)` is surjective: connected finite étale covers of `X` stay connected over `U`
(`AlgebraicGeometry.Scheme.FiniteEtale.isConnected_pullback_of_isIntegrallyClosed_stalk`). -/
theorem fundamentalGroupMap_surjective_of_isIntegrallyClosed_stalk [IsLocallyNoetherian X]
    (hX : ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x))
    [Nonempty U] :
    Function.Surjective (fundamentalGroupMap τ GU GX) :=
  fundamentalGroupMap_surjective τ GX GU fun P _ ↦
    isConnected_pullback_of_isIntegrallyClosed_stalk j hX P

end AlgebraicGeometry.Scheme.FiniteEtale
