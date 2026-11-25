/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Restriction
public import WeilConjectures.AlgebraicGeometry.Regular

/-!
# The fundamental group of a dense open of a regular scheme surjects

Let `X` be a connected locally noetherian regular scheme and `j : U ⟶ X` an open immersion with
`U` nonempty. A connected finite étale cover `P` of `X` is again regular, hence irreducible, so
its restriction to `U`, a nonempty open subscheme of `P`, is irreducible, hence connected.
Consequently the map `π₁(U) → π₁(X)` is surjective (SGA 1, Exp. V, Prop. 8.2; Stacks `0BQM`).
This is part (1) of the blueprint lemma `theorem-purity-real-sheaves-curves`, with normality
strengthened to regularity.

## Main statements

- `AlgebraicGeometry.Scheme.FiniteEtale.isConnected_pullback_of_isRegular`: connected finite
  étale covers stay connected over a nonempty open.
- `AlgebraicGeometry.Scheme.FiniteEtale.fundamentalGroupMap_surjective_of_isRegular`: the map of
  fundamental groups is surjective.
-/

@[expose] public section

universe u

open CategoryTheory PreGaloisCategory

namespace AlgebraicGeometry.Scheme.FiniteEtale

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

include j in
/-- A nonempty open subscheme of an irreducible scheme is connected. -/
lemma connectedSpace_of_isOpenImmersion [IrreducibleSpace X] [Nonempty U] : ConnectedSpace U := by
  have := j.isOpenEmbedding.irreducibleSpace
  infer_instance

/-- Blueprint `theorem-purity-real-sheaves-curves`, part (1), second formulation: a connected
finite étale cover of a connected locally noetherian regular scheme `X` stays connected over a
nonempty open `U`. The cover is regular, being étale over `X`, hence irreducible, and its
restriction to `U` is a nonempty open of it. -/
lemma isConnected_pullback_of_isRegular [IsRegular X] [IsLocallyNoetherian X] [ConnectedSpace X]
    [Nonempty U] (P : X.FiniteEtale) [IsConnected P] : IsConnected ((pullback j).obj P) := by
  have := connectedSpace_of_isConnected P
  have : Etale P.obj.hom := P.obj.prop
  have : IsLocallyNoetherian P.obj.left :=
    LocallyOfFiniteType.isLocallyNoetherian (Y := X) P.obj.hom
  have : IsRegular P.obj.left :=
    ⟨isRegularLocalRing_stalk_of_etale (Y := X) P.obj.hom
      (fun _ ↦ IsRegular.isRegularLocalRing_stalk _)⟩
  have := IsRegular.irreducibleSpace P.obj.left
  have := IsRegular.irreducibleSpace X
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
nonempty open of a connected regular scheme surjects onto that of the scheme.** For a connected
locally noetherian regular scheme `X`, an open immersion `j : U ⟶ X` with `U` nonempty and a
path `τ` between the fibre functors, the map `π₁(U) → π₁(X)` is surjective: connected finite
étale covers of `X` stay connected over `U`
(`AlgebraicGeometry.Scheme.FiniteEtale.isConnected_pullback_of_isRegular`). -/
theorem fundamentalGroupMap_surjective_of_isRegular [IsRegular X] [IsLocallyNoetherian X]
    [Nonempty U] :
    Function.Surjective (fundamentalGroupMap τ GU GX) := by
  exact fundamentalGroupMap_surjective τ GX GU fun P _ ↦ isConnected_pullback_of_isRegular j P

end AlgebraicGeometry.Scheme.FiniteEtale
