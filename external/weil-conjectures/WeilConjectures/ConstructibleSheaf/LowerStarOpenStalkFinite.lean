/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.LowerStarOpenStalk
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.UnitMono
public import WeilConjectures.SixFunctors.Finite.Stalk
public import WeilConjectures.AlgebraicGeometry.GeometricPointFieldExtensionIso
public import Mathlib.Algebra.Category.ModuleCat.Products

/-!
# Finiteness of the stalks of a direct image along an open immersion, via a finite cover

Let `j : U ⟶ X` be an open immersion with `U` quasi-compact and `F` a finite locally constant
sheaf of modules over a finite ring on `U`. Suppose that `X` is covered by the images of finitely
many finite morphisms `ν_i : Y_i ⟶ X` from locally noetherian schemes `Y_i` all of whose étale
schemes have domains as local rings (for instance regular schemes, such as the normalizations of
the irreducible components of a curve). Then the geometric stalks of `j_* F` are finite.

Write `q_i : Y_i ×_X U ⟶ U` and `o_i : Y_i ×_X U ⟶ Y_i` for the projections. The `q_i` are
finite and jointly surjective, so `F ⟶ ∏ᵢ (q_i)_* (q_i)^* F` is a monomorphism
(`AlgebraicGeometry.Etale.mono_piLift_unit`), and so is its direct image along `j`. Since
`j_* (q_i)_* = (ν_i)_* (o_i)_*`, the stalk of `j_* (q_i)_* (q_i)^* F` at a geometric point `y`
is the finite product of the stalks of `(o_i)_* (q_i)^* F` at the geometric points of `Y_i`
over `y` (`AlgebraicGeometry.Etale.stalkIsoPi`), and these are finite by
`AlgebraicGeometry.Etale.finite_sheafFiber_lowerStar`.

## Main statements

- `AlgebraicGeometry.Etale.finite_sheafFiber_lowerStar_of_isFinite`
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ]

/-- The geometric stalks of `j_* F`, at geometric points with algebraically closed field, are
finite if `X` is covered by finitely many finite morphisms from schemes whose étale local
rings are domains. See `AlgebraicGeometry.Etale.finite_sheafFiber_lowerStar_of_isFinite`. -/
theorem finite_sheafFiber_lowerStar_of_isFinite_of_isAlgClosed
    {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [CompactSpace U]
    {ι : Type u} [Finite ι] {Y : ι → Scheme.{u}} (ν : ∀ i, Y i ⟶ X) [∀ i, IsFinite (ν i)]
    (hν : ∀ x : X, ∃ i, x ∈ Set.range (ν i).base) [∀ i, IsLocallyNoetherian (Y i)]
    (hY : ∀ i (W : (Y i).Etale) (w : W.left), IsDomain (W.left.presheaf.stalk w))
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsFiniteLocallyConstantSheaf F]
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (y : Spec (.of Ω) ⟶ X) :
    Finite (ToType ((pointSmallEtale y).sheafFiber.obj ((j)_*[ModuleCat.{u + 1} Λ].obj F))) := by
  let A := ModuleCat.{u + 1} Λ
  let q (i : ι) : pullback (ν i) j ⟶ U := pullback.snd (ν i) j
  let o (i : ι) : pullback (ν i) j ⟶ Y i := pullback.fst (ν i) j
  have hq (u : U) : ∃ (i : ι) (x : Spec (.of (AlgebraicClosure (U.residueField u))) ⟶
      pullback (ν i) j), x ≫ q i = U.algClosurePoint u := by
    obtain ⟨i, z, hz⟩ := hν (j.base u)
    obtain ⟨p, -, hp⟩ := Scheme.Pullback.exists_preimage_pullback z u hz
    obtain ⟨t, -⟩ := Hom.GeometricFiber.exists_apply_default_eq (f := q i)
      (y := U.algClosurePoint u) p (by simp [q, hp])
    exact ⟨i, t.1, t.2⟩
  have := mono_piLift_unit q hq F
  let G (i : ι) : Sheaf U.smallEtaleTopology A := (q i)_*[A].obj ((q i)^*[A].obj F)
  let S : Sheaf U.smallEtaleTopology A ⥤ A := (j)_*[A] ⋙ (pointSmallEtale y).sheafFiber
  have hinj : Function.Injective
      (S.map (Pi.lift fun i ↦ (upperStarLowerStarAdjunction A (q i)).unit.app F)) :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have hfin (i : ι) : Finite (ToType (S.obj (G i))) := by
    have := QuasiCompact.compactSpace_of_compactSpace (q i)
    have := IsFiniteLocallyConstantSheaf.upperStar (q i) F
    obtain ⟨B, hB⟩ := exists_natCard_sheafFiber_le ((q i)^*[A].obj F)
    let e :=
      (pointSmallEtale y).sheafFiber.mapIso
        (((lowerStarComp A (q i) j (o i ≫ ν i) pullback.condition) ≪≫
          (lowerStarComp A (o i) (ν i)).symm).app ((q i)^*[A].obj F)) ≪≫
        stalkIsoPi A (ν i) y _ ≪≫ ModuleCat.piIsoPi.{u + 1, u, u + 1} _
    have (t : Hom.GeometricFiber (ν i) y) := finite_sheafFiber_lowerStar (o i) (hY i)
      ((q i)^*[A].obj F) B hB t.1
    exact Finite.of_equiv _ e.toLinearEquiv.toEquiv.symm
  have : Finite (ToType (S.obj (∏ᶜ G))) :=
    Finite.of_equiv _ (PreservesProduct.iso S G ≪≫
      ModuleCat.piIsoPi.{u + 1, u, u + 1} _).toLinearEquiv.toEquiv.symm
  exact Finite.of_injective (β := ToType (S.obj (∏ᶜ G))) _ hinj

/-- **The stalks of a direct image along an open immersion are finite, given a finite regular
cover.** Let `j : U ⟶ X` be an open immersion with `U` quasi-compact, `F` a finite locally
constant sheaf of modules over a finite ring on `U`, and suppose that `X` is covered by the
images of finitely many finite morphisms `ν_i : Y_i ⟶ X` from locally noetherian schemes all of
whose étale schemes have domains as local rings. Then the geometric stalks of `j_* F` are
finite. -/
theorem finite_sheafFiber_lowerStar_of_isFinite
    {X U : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] [CompactSpace U]
    {ι : Type u} [Finite ι] {Y : ι → Scheme.{u}} (ν : ∀ i, Y i ⟶ X) [∀ i, IsFinite (ν i)]
    (hν : ∀ x : X, ∃ i, x ∈ Set.range (ν i).base) [∀ i, IsLocallyNoetherian (Y i)]
    (hY : ∀ i (W : (Y i).Etale) (w : W.left), IsDomain (W.left.presheaf.stalk w))
    (F : Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsFiniteLocallyConstantSheaf F]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (y : Spec (.of Ω) ⟶ X) :
    Finite (ToType ((pointSmallEtale y).sheafFiber.obj ((j)_*[ModuleCat.{u + 1} Λ].obj F))) := by
  let a : Spec (.of (AlgebraicClosure Ω)) ⟶ Spec (.of Ω) :=
    Spec.map (CommRingCat.ofHom (algebraMap Ω (AlgebraicClosure Ω)))
  have := finite_sheafFiber_lowerStar_of_isFinite_of_isAlgClosed j ν hν hY F (a ≫ y)
  exact Finite.of_equiv _
    ((sheafFiberPrecompIso y a (ModuleCat.{u + 1} Λ)).app _).toLinearEquiv.toEquiv.symm

end Etale

end AlgebraicGeometry
