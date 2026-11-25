/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor

import WeilConjectures.AlgebraicGeometry.Morphisms.UnderlyingFiniteEtaleExtension
import WeilConjectures.AlgebraicGeometry.Morphisms.GenericFibreActionExtension

/-!
# Spreading a finite étale Galois cover out from the generic fibre

Let `S` be a qcqs integral normal scheme with generic point `η`, let `c: C ⟶ S` be a qcqs
smooth morphism with geometrically connected fibres, and fix a section `σ` of `c`. An
`M`-torsor on the generic fibre `C_η`, for `M` a finite abelian group of order invertible on
`S`, carrying a `κ(η)`-rational point above `σ(η)`, extends to an `M`-torsor on `C`. This is
[Stacks 0EZJ]; the statement is the input taken by the induction in the proof of smooth base
change.

A finite étale Galois cover with abelian group `M` is the same thing as an `M`-torsor, so
the covers are recorded as `AlgebraicGeometry.Scheme.EtaleTorsor` of
`WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor`.

## Implementation notes

The statement takes the constructions it speaks about as explicit data rather than building
them, so that it is a statement and not a construction:

- the generic fibre `C_η` is a scheme `Cη` together with a cartesian square over
  `Spec S.functionField ⟶ S`, the latter being `AlgebraicGeometry.Scheme.fromSpecStalk` at
  the generic point;
- the generic point of the section is a morphism `sη: Spec S.functionField ⟶ Cη` which is a
  section of the generic fibre and lies over `σ`;
- the restriction of the produced torsor to the generic fibre is expressed by asking for a
  morphism `ψ` from the given torsor to the produced one which makes a cartesian square over
  `j: Cη ⟶ C` and commutes with the `M`-actions.

Normality of `S` is spelled out as integral closedness of all the stalks, there being no
`IsNormal` predicate on schemes; qcqs-ness of `S` is `CompactSpace` together with
`QuasiSeparatedSpace`.

Stacks `0EZJ` itself, for an arbitrary finite group `G`, is recorded as
`AlgebraicGeometry.Scheme.GaloisCover.exists_isPullback_of_genericFibre`, for Galois covers in
the sense of `AlgebraicGeometry.Scheme.GaloisCover` (finite étale `G`-torsors, whose total space
need not be connected). Only the abelian case is used by smooth base change; it is
`AlgebraicGeometry.Scheme.EtaleTorsor.exists_isPullback_of_genericFibre`, deduced by viewing an
`M`-torsor as a Galois cover with group `Multiplicative M`.

The uniqueness of the extension is not asserted. Connectedness of the torsor is not assumed:
the torsors spread in the proof of smooth base change are attached to arbitrary classes in
`H^1`, which need not be connected.

## Main statements

- `AlgebraicGeometry.Scheme.GaloisCover.exists_isPullback_of_genericFibre`: spreading a finite
  étale Galois cover with group `G`.
- `AlgebraicGeometry.Scheme.EtaleTorsor.exists_isPullback_of_genericFibre`: the spreading
  statement for torsors under a finite abelian group.

## References

- Stacks Project, Tag `0EZJ`, <https://stacks.math.columbia.edu/tag/0EZJ>
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- **Spreading a finite étale Galois cover.** Let `S` be a qcqs integral normal scheme with
generic point `η` and function field `κ(η) = S.functionField`, let `c: C ⟶ S` be a qcqs smooth
morphism with geometrically connected fibres, and let `σ` be a section of `c`. Let `G` be a
finite group whose order is invertible on `S`, let `Cη` be the generic fibre of `c`, given by
the cartesian square `hCη`, and let `Z` be a finite étale Galois cover of `Cη` with group `G`
carrying a `κ(η)`-rational point above the generic point `sη` of the section. Then there is a
finite étale Galois cover `T` of `C` with group `G` and a `G`-equivariant morphism
`ψ: Z.P ⟶ T.P` making `Z` the restriction of `T` to `Cη`, that is, making the square over
`j: Cη ⟶ C` cartesian. -/
@[stacks 0EZJ]
theorem GaloisCover.exists_isPullback_of_genericFibre {S C : Scheme.{u}} [CompactSpace S]
    [QuasiSeparatedSpace S] [IsIntegral S]
    (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [Smooth c] [GeometricallyConnected c]
    (σ : S ⟶ C) (hσ : σ ≫ c = 𝟙 S)
    (G : Type (u + 1)) [Group G] [Finite G]
    (hG : IsUnit (Nat.card G : Γ(S, ⊤)))
    {Cη : Scheme.{u}} (q : Cη ⟶ Spec S.functionField) (j : Cη ⟶ C)
    (hCη : IsPullback q j (S.fromSpecStalk (genericPoint S)) c)
    (sη : Spec S.functionField ⟶ Cη) (hsq : sη ≫ q = 𝟙 _)
    (hsj : sη ≫ j = S.fromSpecStalk (genericPoint S) ≫ σ)
    (Z : GaloisCover G Cη) (hZ : ∃ z : Spec S.functionField ⟶ Z.P, z ≫ Z.π = sη) :
    ∃ (T : GaloisCover G C) (ψ : Z.P ⟶ T.P), IsPullback ψ Z.π T.π j ∧
      ∀ g : G, Z.smul g ≫ ψ = ψ ≫ T.smul g := by
  obtain ⟨P, π, ψ, hfin, het, hsurj, hψ⟩ :=
    GaloisCover.exists_finiteEtale_extension hS c σ hσ G hG q j hCη sη hsq hsj Z hZ
  let := hfin
  let := het
  obtain ⟨a, ha, hunit, hmul, hequiv, htorsor⟩ :=
    GaloisCover.exists_action_on_finiteEtale_extension hS c G q j hCη Z π ψ hψ
  let T : GaloisCover G C :=
    { P := P
      π := π
      isFinite := hfin
      etale := het
      surjective := hsurj
      smul := a
      smul_π := ha
      one_smul := hunit
      mul_smul := hmul
      isIso_sigmaDesc := htorsor }
  exact ⟨T, ψ, hψ, hequiv⟩

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Scheme.EtaleTorsor

/-- **Spreading an étale torsor from the generic fibre.** Let `S` be a qcqs integral normal scheme
with generic point `η`, let `c: C ⟶ S` be a qcqs smooth morphism with geometrically connected
fibres with a section `σ`, and let `M` be a finite abelian group whose order is invertible on
`S`. Let `Cη` be the generic fibre of `c` (given by the cartesian square `hCη`) and let `Z` be an
`M`-torsor on `Cη` carrying a `κ(η)`-rational point above the generic point `sη` of the section.
Then there is an `M`-torsor `T` on `C` and an `M`-equivariant morphism `ψ: Z.P ⟶ T.P` making
the square over `j: Cη ⟶ C` cartesian, so that the restriction of `T` to `Cη` is `Z`. -/
@[stacks 0EZJ]
theorem exists_isPullback_of_genericFibre {S C : Scheme.{u}} [CompactSpace S]
    [QuasiSeparatedSpace S] [IsIntegral S]
    (hS : ∀ x : S, IsIntegrallyClosed (S.presheaf.stalk x))
    (c : C ⟶ S) [QuasiCompact c] [QuasiSeparated c] [Smooth c] [GeometricallyConnected c]
    (σ : S ⟶ C) (hσ : σ ≫ c = 𝟙 S)
    (M : Type (u + 1)) [AddCommGroup M] [Finite M]
    (hM : IsUnit (Nat.card M : Γ(S, ⊤)))
    {Cη : Scheme.{u}} (q : Cη ⟶ Spec S.functionField) (j : Cη ⟶ C)
    (hCη : IsPullback q j (S.fromSpecStalk (genericPoint S)) c)
    (sη : Spec S.functionField ⟶ Cη) (hsq : sη ≫ q = 𝟙 _)
    (hsj : sη ≫ j = S.fromSpecStalk (genericPoint S) ≫ σ)
    (Z : EtaleTorsor M Cη) (hZ : ∃ z : Spec S.functionField ⟶ Z.P, z ≫ Z.π = sη) :
    ∃ (T : EtaleTorsor M C) (ψ : Z.P ⟶ T.P), IsPullback ψ Z.π T.π j ∧
      ∀ m : M, Z.vadd m ≫ ψ = ψ ≫ T.vadd m := by
  obtain ⟨T, ψ, hψ, hψM⟩ := GaloisCover.exists_isPullback_of_genericFibre hS c σ hσ
    (Multiplicative M) hM q j hCη sη hsq hsj Z.toGaloisCover hZ
  exact ⟨T.toEtaleTorsor, ψ, hψ, fun m ↦ hψM (.ofAdd m)⟩

end AlgebraicGeometry.Scheme.EtaleTorsor
