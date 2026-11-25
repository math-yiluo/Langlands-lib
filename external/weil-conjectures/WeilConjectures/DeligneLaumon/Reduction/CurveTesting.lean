/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Bertini
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Connected
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyIrreducible
public import WeilConjectures.SixFunctors.ProEtale.Adic.LisseMonodromyExtension
public import WeilConjectures.WeilSheaf.Category

/-!
# Curve testing for geometric irreducibility

Let `X₀` be a smooth geometrically connected affine scheme of dimension `d ≥ 1` over a finite
field `k₀`, with geometric fiber `X`, and let `𝒮₁, …, 𝒮ᵣ` be Weil sheaves on `X₀` whose
geometric restrictions are irreducible local systems. Through any nonempty finite set `S` of
`k̄`-points of `X` there is a smooth connected affine curve `C ⊆ X`, defined over a finite
extension of `k₀`, on which every `𝒮ⱼ` stays irreducible
(`AlgebraicGeometry.WeilSheaf.exists_isClosedImmersion_isIrreducibleLocalSystem_upperStar`,
blueprint `corollary-curve-preserving-geometric-irreducibility--1`).

## Implementation notes

For `d = 1` the curve is `X` itself. For `d ≥ 2`, the monodromy representations `ρⱼ` of
`π₁(X, s)` on the stalks of the `𝒮ⱼ` at a point `s ∈ S` are continuous and irreducible over
`ℚ̄_ℓ`. By Burnside's theorem there is a neighbourhood `U` of `1` such that every subgroup meeting
every coset `g U` still acts irreducibly through each `ρⱼ`
(`Representation.exists_mem_nhds_one_forall_isIrreducible`); this replaces the integral model and
the finite matrix witness of the blueprint, which serve to produce the same open subgroup.
Shrinking `U`, it is the stabilizer of a point `a` of the fibre of a connected (Galois) finite
étale cover `T ⟶ X`. The Bertini theorem
`AlgebraicGeometry.Scheme.Hom.exists_isClosedImmersion_connectedSpace_pullback` gives a curve
`i : C ⟶ X` through `S` with `T ×_X C` connected, so that `π₁(C, c)` acts transitively on the
fibre of `T` at `s = i(c)`: its image meets every coset `g U`. Finally the monodromy
representations of the `i^* 𝒮ⱼ` at `c` are the `ρⱼ` composed with `π₁(C, c) → π₁(X, s)`, by the
compatibility of the dictionary between lisse sheaves and representations with base change
(`AlgebraicGeometry.ProEtale.isCompatible_universalLisseMonodromy`).
-/

@[expose] public section

universe u

open CategoryTheory Limits PreGaloisCategory

namespace AlgebraicGeometry

open Scheme.FiniteEtale ProEtale

/-- **Curve testing for irreducible local systems** (blueprint:
`corollary-curve-preserving-geometric-irreducibility--1`). Let `f : X₀ ⟶ Spec k₀` be a smooth
geometrically connected affine scheme of relative dimension `d ≥ 1` over a finite field, with
geometric fiber `X`, let `F₁, …, Fᵣ` be irreducible `ℓ`-adic local systems on `X`, and let `S` be a
nonempty finite set of `k̄`-points of `X`. There is a closed immersion `i : C ⟶ X` of a smooth
connected affine curve over `k̄` through `S`, stable under a power of the geometric Galois Frobenius
of `X`, such that every `i^* Fⱼ` is still an irreducible local system. -/
theorem Scheme.Hom.exists_isClosedImmersion_isIrreducibleAdicLocalSystem_upperStar
    {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] {X₀ : Scheme.{u}}
    (f : X₀ ⟶ Spec (.of k₀)) [IsAffine X₀] {d : ℕ} (hd : 1 ≤ d) [SmoothOfRelativeDimension d f]
    [GeometricallyConnected f] {r : ℕ} (F : Fin r → AdicSheaf l f.geometricFiber)
    (hF : ∀ j, IsIrreducibleAdicLocalSystem (F j))
    (S : Finset (Spec (.of (AlgebraicClosure k₀)) ⟶ f.geometricFiber)) (hS : S.Nonempty)
    (hS' : ∀ s ∈ S, s ≫ f.geometricFiberToAlgebraicClosure = 𝟙 _) :
    ∃ (C : Scheme.{u}) (i : C ⟶ f.geometricFiber), IsClosedImmersion i ∧ IsAffine C ∧
      SmoothOfRelativeDimension 1 (i ≫ f.geometricFiberToAlgebraicClosure) ∧
      ConnectedSpace C ∧ (∀ s ∈ S, ∃ c, c ≫ i = s) ∧
      (∀ j, IsIrreducibleAdicLocalSystem ((i)^*ᵃ[l].obj (F j))) ∧
      ∃ m : ℕ, 0 < m ∧ ∃ φ : C ≅ C, φ.hom ≫ i = i ≫ (f.geometricGaloisFrobenius ^ m).asIso.hom := by
  have : ConnectedSpace f.geometricFiber :=
    GeometricallyConnected.geometrically_connectedSpace (f := f)
      (Scheme.specAlgebraicClosure k₀).hom f.geometricFiberProj
      f.geometricFiberToAlgebraicClosure (IsPullback.of_hasPullback _ _)
  have : SmoothOfRelativeDimension d f.geometricFiberToAlgebraicClosure :=
    inferInstanceAs (SmoothOfRelativeDimension d (Limits.pullback.snd _ _))
  have : IsAffineHom f.geometricFiberToAlgebraicClosure :=
    inferInstanceAs (IsAffineHom (Limits.pullback.snd _ _))
  have : IsAffine f.geometricFiber := isAffine_of_isAffineHom f.geometricFiberToAlgebraicClosure
  rcases hd.eq_or_lt with rfl | hd2
  · refine ⟨_, 𝟙 _, inferInstance, inferInstance, by rwa [Category.id_comp], inferInstance,
      fun s _ ↦ ⟨s, Category.comp_id s⟩,
      fun j ↦ (hF j).of_iso ((adicUpperStarId l _).app _).symm, 1, one_pos,
      (f.geometricGaloisFrobenius ^ 1).asIso, by simp⟩
  -- the geometric fiber is regular and locally Noetherian
  have : Smooth f.geometricFiberToAlgebraicClosure := SmoothOfRelativeDimension.smooth d _
  have := IsRegular.of_smooth f.geometricFiberToAlgebraicClosure
  have := LocallyOfFiniteType.isLocallyNoetherian f.geometricFiberToAlgebraicClosure
  -- a monodromy on `X`, compatible with pullback to curves, and a base point `s₀ ∈ S`
  let M := universalLisseMonodromy l f.geometricFiber k₀
  have hM := universalLisseMonodromy_isEquivalenceAt l f.geometricFiber k₀
  obtain ⟨s₀, hs₀⟩ := hS
  let G (j : Fin r) : LisseSheaf l f.geometricFiber := ⟨F j, (hF j).1⟩
  have hirr (j : Fin r) : (M.rep s₀ (G j)).IsIrreducible :=
    ((hM s₀).isIrreducibleAdicLocalSystem_iff (G j)).1 (hF j)
  -- neighbourhoods of `1` in `π₁(X, s₀)` witnessing irreducibility on subgroups
  have hU (j : Fin r) := by
    have := hirr j
    exact Representation.exists_mem_nhds_one_forall_isIrreducible (M.rep s₀ (G j))
      ((hM s₀).continuous_rep (G j))
  choose U hU hUirr using hU
  -- a pointed Galois cover `(T, a)` whose stabilizer is contained in all the `U j`
  obtain ⟨A, -, hA⟩ :=
    (nhds_one_has_basis_stabilizers (Scheme.FiniteEtale.fiber s₀)).mem_iff.1
      (Filter.iInter_mem.2 hU)
  have := A.isGalois
  have : ConnectedSpace A.obj.obj.left := connectedSpace_of_isConnected A.obj
  have : IsFinite A.obj.obj.hom := A.obj.property
  have : AlgebraicGeometry.Etale A.obj.obj.hom := A.obj.obj.prop
  -- Bertini
  obtain ⟨C, i, hi, hCaff, hCsm, hCconn, hSC, hTC, m, hm, φ, hφ⟩ :=
    Scheme.Hom.exists_isClosedImmersion_connectedSpace_pullback f (d := d) (by omega)
      (T := A.obj.obj.left) A.obj.obj.hom S ⟨s₀, hs₀⟩ hS'
  refine ⟨C, i, hi, hCaff, hCsm, hCconn, hSC, fun j ↦ ?_, m, hm, φ, hφ⟩
  obtain ⟨c, rfl⟩ := hSC s₀ hs₀
  have : Smooth (i ≫ f.geometricFiberToAlgebraicClosure) := SmoothOfRelativeDimension.smooth 1 _
  have := IsRegular.of_smooth (i ≫ f.geometricFiberToAlgebraicClosure)
  have := LocallyOfFiniteType.isLocallyNoetherian (i ≫ f.geometricFiberToAlgebraicClosure)
  have hM' := universalLisseMonodromy_isEquivalenceAt l C k₀
  have hcompat := isCompatible_universalLisseMonodromy l k₀ i
  have : ConnectedSpace ((Scheme.FiniteEtale.pullback i).obj A.obj).obj.left := hTC
  have : IsConnected ((Scheme.FiniteEtale.pullback i).obj A.obj) :=
    isConnected_of_connectedSpace _
  -- the image of `π₁(C, c) → π₁(X, i c)` meets every coset of the stabilizer of `a`
  have hΓ (g : Aut (Scheme.FiniteEtale.fiber (c ≫ i))) :
      ∃ γ ∈ (pullbackPathHom i c).range, g⁻¹ * γ ∈ ⋂ j, U j := by
    obtain ⟨h, hh⟩ := exists_pullbackPathHom_apply_eq i c A.obj A.pt (g • A.pt)
    refine ⟨_, ⟨h, rfl⟩, hA ?_⟩
    rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, mul_smul]
    exact (congrArg (g⁻¹ • ·) hh).trans (inv_smul_smul g _)
  -- the monodromy of `i^* Fⱼ` at `c` is that of `Fⱼ` at `i c`, restricted to `π₁(C, c)`
  refine ((hM' c).isIrreducibleAdicLocalSystem_iff ((G j).upperStar l i)).2 ?_
  refine Representation.IsIrreducible.of_comp_range (pullbackPathHom i c)
    (WeilCoefficients.linearEquivOfIso (upperStarStalkIso l i c (G j).obj.X)) (fun h v ↦ ?_)
    (hUirr j _ fun g ↦ ?_)
  · have := congrArg (fun φ ↦ ((WeilCoefficients.toModuleCat l).map φ).hom v)
      (hcompat h.asIso (G j))
    simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at this
    exact this
  · obtain ⟨γ, hγ, hγU⟩ := hΓ g
    exact ⟨γ, hγ, Set.mem_iInter.1 hγU j⟩

/-- **Curve testing for geometric irreducibility**
(blueprint: `corollary-curve-preserving-geometric-irreducibility--1`). Let `X₀` be a smooth
geometrically connected affine scheme of dimension `d ≥ 1` over a finite field `k₀`, with geometric
fiber `X`, let `𝒮₁, …, 𝒮ᵣ` be Weil sheaves on `X₀` whose geometric restrictions are irreducible
local systems, and let `S` be a nonempty finite set of `k̄`-points of `X`. There is a closed
immersion `i : C ⟶ X` of a smooth connected affine curve over `k̄` through `S`, defined over a
finite extension of `k₀` (stable under a power of the geometric Galois Frobenius of `X`), on which
every `𝒮ⱼ` remains geometrically irreducible. -/
theorem WeilSheaf.exists_isClosedImmersion_isIrreducibleLocalSystem_upperStar {k₀ : Type u}
    [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)] {X₀ : Scheme.{u}}
    [X₀.Over (Spec (CommRingCat.of k₀))] [IsAffine X₀] {d : ℕ} (hd : 1 ≤ d)
    [SmoothOfRelativeDimension d (X₀ ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (X₀ ↘ Spec (CommRingCat.of k₀))] {r : ℕ}
    (𝒮 : Fin r → WeilSheaf k₀ l X₀)
    (h𝒮 : ∀ j, ProEtale.IsIrreducibleAdicLocalSystem (𝒮 j).obj.carrier)
    (S : Finset
      (Spec (.of (AlgebraicClosure k₀)) ⟶ (X₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber))
    (hS : S.Nonempty)
    (hS' : ∀ s ∈ S, s ≫ (X₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure = 𝟙 _) :
    ∃ (C : Scheme.{u}) (i : C ⟶ (X₀ ↘ Spec (CommRingCat.of k₀)).geometricFiber),
      IsClosedImmersion i ∧ IsAffine C ∧
      SmoothOfRelativeDimension 1
        (i ≫ (X₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure) ∧
      ConnectedSpace C ∧ (∀ s ∈ S, ∃ c, c ≫ i = s) ∧
      (∀ j, ProEtale.IsIrreducibleAdicLocalSystem
        ((i)^*ᵃ[l].obj (𝒮 j).obj.carrier)) ∧
      ∃ m : ℕ, 0 < m ∧ ∃ φ : C ≅ C,
        φ.hom ≫ i = i ≫ ((X₀ ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ m).asIso.hom :=
  Scheme.Hom.exists_isClosedImmersion_isIrreducibleAdicLocalSystem_upperStar _ hd
    (fun j ↦ (𝒮 j).obj.carrier) h𝒮 S hS hS'

end AlgebraicGeometry
