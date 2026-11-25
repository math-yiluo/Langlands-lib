/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import WeilConjectures.AlgebraicGeometry.Curve
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.LinearAlgebra.SemilinearFrobenius
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import WeilConjectures.AlgebraicGeometry.ArtinSchreierSequence
import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism
import WeilConjectures.AlgebraicGeometry.Curve.AdditiveCohomologyComparison
import WeilConjectures.AlgebraicGeometry.Curve.AdditiveScalarBaseChange
import WeilConjectures.AlgebraicGeometry.Curve.ArtinSchreierFrobeniusExactRows
import WeilConjectures.AlgebraicGeometry.Curve.ArtinSchreierPrimeBaseChangeModel
import WeilConjectures.AlgebraicGeometry.Curve.Compactification
import WeilConjectures.AlgebraicGeometry.Curve.RiemannRoch
import WeilConjectures.AlgebraicGeometry.EtaleSheafHExtDerivedComparison
import WeilConjectures.AlgebraicGeometry.ZeroDimensionalEtaleCohomologyRest

/-!
# `H¹(C, 𝐅_p)` of a smooth proper curve in characteristic `p`

Let `C` be a smooth proper connected curve of genus `g` over an algebraically closed field `k`
of characteristic `p > 0`. The Artin–Schreier sequence `0 → 𝐅_p → 𝔾ₐ → 𝔾ₐ → 0` identifies
`H¹(C, 𝐅_p)` with the fixed points of the `p`-linear Frobenius `φ` of `H¹(C, 𝒪_C)`. Since
`H¹(C, 𝒪_C)` has dimension `g`, the group `H¹(C, 𝐅_p)` is finite of `𝐅_p`-dimension at most `g`,
and it is invariant under algebraically closed extension of `k`.

## Main statements

- `AlgebraicGeometry.IsCurve.exists_addEquiv_sheafH_one_constantZMod_fixedPoints`:
  `H¹(C, 𝐅_p) ≅ H¹(C, 𝒪_C)^{φ = 1}`.
- `AlgebraicGeometry.IsCurve.sheafH_one_constantZMod_of_charP`: `H¹(C, 𝐅_p)` is finite, has at
  most `p ^ g` elements, and its pullback map under algebraically closed extension is bijective.
-/

@[expose] public section

universe u

open CategoryTheory
open scoped TensorProduct

namespace AlgebraicGeometry.IsCurve

variable {k : Type u} [Field k] [IsAlgClosed k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))

/-- **`H¹(C, 𝐅_p)` as Frobenius fixed points of `H¹(C, 𝒪_C)`.** Let `C` be a smooth proper
connected curve over an algebraically closed field `k` of characteristic `p`. There is a
`p`-linear endomorphism `φ` of (a universe lift of) the coherent cohomology `H¹(C, 𝒪_C)` with
`H¹(C, 𝐅_p) ≅ H¹(C, 𝒪_C)^{φ = 1}`. -/
theorem exists_addEquiv_sheafH_one_constantZMod_fixedPoints [IsCurve f] [Smooth f]
    [ConnectedSpace C] [IsProper f] (p : ℕ) [Fact p.Prime] [CharP k p] :
    letI : C.Over (Spec (.of k)) := ⟨f⟩
    ∃ F : ULift.{u + 1} (Scheme.Modules.H (X := C) (SheafOfModules.unit C.ringCatSheaf) 1)
        →ₛₗ[frobenius k p]
          ULift.{u + 1} (Scheme.Modules.H (X := C) (SheafOfModules.unit C.ringCatSheaf) 1),
      Nonempty (Sheaf.H (C.constantZMod p) 1 ≃+ LinearMap.Frobenius.fixedPoints F) := by
  classical
  let : C.Over (Spec (.of k)) := ⟨f⟩
  obtain ⟨G, -, a, wp, i, z, ha, hwp, -, hS⟩ :=
    artinSchreier_shortExact f p (Fact.out : p.Prime).pos
  obtain ⟨m, hm⟩ := exists_additive_cohomology_scalar_action f G a ha
  obtain ⟨α⟩ := Scheme.nonempty_sheafH_extDerivedIso C 1
  obtain ⟨d, hd⟩ := exists_addEquiv_etaleCohomology_one_structureSheaf f G a ha
  let T := DerivedCategory.singleFunctor
    (Sheaf C.smallEtaleTopology AddCommGrpCat.{u + 1}) 0 ⋙
      Etale.cohomology AddCommGrpCat.{u + 1} C (1 : ℤ)
  let W := ULift.{u + 1} (Scheme.Modules.H (X := C) (SheafOfModules.unit C.ringCatSheaf) 1)
  let b : Sheaf.H G 1 ≃+ W :=
    ((α.app G).addCommGroupIsoToAddEquiv.trans d).trans AddEquiv.ulift.symm
  have hscalar (c : k) : ∃ μ : G ⟶ G,
      (∀ (U : C.Etaleᵒᵖ) (x : G.obj.obj U),
        let ρ : k →+* Γ(U.unop.left, ⊤) := U.unop.hom.appTop.hom.comp
          (f.appTop.hom.comp (Scheme.ΓSpecIso (.of k)).inv.hom)
        a U (μ.hom.app U x) = a U x * ρ c) ∧
      ∀ x : Sheaf.H G 1, b (Sheaf.H.map μ 1 x) = c • b x := by
    obtain ⟨μ, hμ, -⟩ := hm c
    refine ⟨μ, hμ, fun x ↦ ULift.ext ?_⟩
    change d ((α.hom.app G) (Sheaf.H.map μ 1 x)) = c • d ((α.hom.app G) x)
    have hn := congrArg (fun t ↦ t x) (α.hom.naturality μ)
    change (α.hom.app G) (Sheaf.H.map μ 1 x) = T.map μ ((α.hom.app G) x) at hn
    rw [hn]
    exact hd c μ hμ _
  obtain ⟨F, hF⟩ := exists_frobenius_model f p G a wp hwp W b hscalar
  obtain ⟨e, -⟩ := exists_fixedPoints_equiv_of_exact_row p i wp z hS
    (surjective_sheafH_zero_artinSchreier f p G a wp hwp) W F b hF
  exact ⟨F, ⟨e⟩⟩

/-- **`p`-torsion on a smooth proper curve, the first cohomology.** Let `C` be a smooth proper
connected curve of genus `g` over an algebraically closed field `k` of characteristic `p > 0`.
Then

* `H¹(C, 𝐅_p)` is finite;
* it has at most `p ^ g` elements, that is (being an `𝐅_p`-vector space), its
  `𝐅_p`-dimension is at most `g`;
* for every algebraically closed extension `k'` of `k` and every cartesian square
  `C' = C ×_k k'`, the pullback map `H¹(C, 𝐅_p) ⟶ H¹(C', 𝐅_p)` is bijective. -/
theorem sheafH_one_constantZMod_of_charP [IsCurve f] [Smooth f] [ConnectedSpace C]
    [IsProper f] (p : ℕ) [Fact p.Prime] [CharP k p] :
    Finite (Sheaf.H (C.constantZMod p) 1) ∧
      Nat.card (Sheaf.H (C.constantZMod p) 1) ≤ p ^ f.genus ∧
      ∀ (k' : Type u) [Field k'] [IsAlgClosed k'] {C' : Scheme.{u}}
        {ι : Spec (.of k') ⟶ Spec (.of k)} {f' : C' ⟶ Spec (.of k')} {ι' : C' ⟶ C},
        IsPullback ι' f' f ι →
          Function.Bijective (Etale.cohomologyMap ι' (C.constantZMod p) 1) := by
  classical
  let : C.Over (Spec (.of k)) := ⟨f⟩
  have hp := (Fact.out : p.Prime)
  obtain ⟨F, ⟨e⟩⟩ := exists_addEquiv_sheafH_one_constantZMod_fixedPoints f p
  have : IsProper (C ↘ Spec (.of k)) := inferInstanceAs (IsProper f)
  have : (SheafOfModules.unit C.ringCatSheaf).IsQuasicoherent :=
    SheafOfModules.isQuasicoherent_unit (R := C.ringCatSheaf)
  have : (SheafOfModules.unit C.ringCatSheaf).IsInvertible :=
    SheafOfModules.instIsInvertibleUnit.{u, u, u}
  have : (SheafOfModules.unit C.ringCatSheaf).IsFiniteLocallyFree :=
    SheafOfModules.IsInvertible.isFiniteLocallyFree.{u, u, u} _
  have : (SheafOfModules.unit C.ringCatSheaf).IsFinitePresentation :=
    SheafOfModules.IsFiniteLocallyFree.isFinitePresentation.{u, u, u} _
  have := Scheme.Modules.finiteDimensional_H_of_isProper (k := k)
    (SheafOfModules.unit C.ringCatSheaf) 1
  have := LinearEquiv.finiteDimensional (ULift.moduleEquiv (R := k)
    (M := Scheme.Modules.H (X := C) (SheafOfModules.unit C.ringCatSheaf) 1)).symm
  refine ⟨Finite.of_equiv _ e.toEquiv.symm, ?_, ?_⟩
  · by_cases hdim : topologicalKrullDim C = 1
    · have : IsConnectedCurve f :=
        { connectedSpace := inferInstance
          krullDim_eq_one := hdim }
      have : SmoothOfRelativeDimension 1 (C ↘ Spec (.of k)) :=
        IsConnectedCurve.smoothOfRelativeDimension_one f
      rw [Nat.card_congr e.toEquiv]
      refine (LinearMap.Frobenius.natCard_fixedPoints_le F).trans
        (Nat.pow_le_pow_right hp.pos (le_of_eq ?_))
      rw [ULift.moduleEquiv.finrank_eq]
      exact (Scheme.genus_eq_arithmeticGenus (k := k) (X := C)).symm
    · have hzero : topologicalKrullDim C ≤ 0 :=
        Order.le_of_lt_succ (lt_of_le_of_ne (IsCurve.krullDim_le_one (f := f)) hdim)
      have hvan := (zero_dimensional_etale_cohomology_rest k C f hzero
        (C.constantZMod p) (fun x ↦ AlgebraicClosure (C.residueField x)) C.algClosurePoint
        (fun x ↦ C.algClosurePoint_base x default)).1 1 (by decide)
      obtain ⟨α⟩ := Scheme.nonempty_sheafH_extDerivedIso C 1
      have hz : Limits.IsZero ((Sheaf.functorH.{u + 1} C.smallEtaleTopology 1).obj
          (C.constantZMod p)) :=
        Limits.IsZero.of_iso (AddCommGrpCat.isZero_iff_subsingleton.mpr hvan)
          (α.app (C.constantZMod p))
      have : Subsingleton (Sheaf.H (C.constantZMod p) 1) :=
        AddCommGrpCat.subsingleton_of_isZero hz
      rw [Nat.card_unique]
      exact Nat.one_le_pow _ _ hp.pos
  · intro k' _ _ C' ι f' ι' h
    obtain ⟨a, rfl⟩ := Spec.map_surjective ι
    let : Algebra k k' := a.hom.toAlgebra
    have : CharP k' p := charP_of_injective_algebraMap (algebraMap k k').injective p
    have hstd : IsPullback ι' f' f (Spec.map (CommRingCat.ofHom (algebraMap k k'))) := h
    obtain ⟨V, _, φ, φ', hφ', e, e', he⟩ :=
      exists_constantZMod_one_frobenius_baseChange_model f p hstd
    have ht := LinearMap.Frobenius.bijective_tmul_fixedPoints φ φ' hφ'
    rw [← Function.Bijective.of_comp_iff' e'.bijective]
    convert ht.comp e.bijective using 1
    exact funext he

end AlgebraicGeometry.IsCurve
