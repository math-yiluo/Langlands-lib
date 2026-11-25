/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage
public import WeilConjectures.AlgebraicGeometry.Modules.IntegralSections

/-!
# The seesaw principle: closedness of the locus of triviality

Let `f : P ⟶ T` be proper, flat, locally of finite presentation and with geometrically integral
fibres, and let `M`, `N` be invertible modules on `P`. The set of points `t ∈ T` such that `M`
and `N` become isomorphic on the fibre `P_t` is closed in `T` (Stacks, Tags 0BDP and 0BF0; this
is the closedness half of Mumford's seesaw theorem).

On the fibre `P_t`, which is integral and proper over `κ(t)`, `M_t ≅ N_t` holds if and only if
both `M_t ⊗ N_tᵛ` and `N_t ⊗ M_tᵛ` have nonzero global sections
(`AlgebraicGeometry.Scheme.Modules.nonempty_iso_unit_of_tensorObj_iso_unit`). Both conditions
are closed in `t` by the upper semicontinuity of `t ↦ dim H⁰(P_t, -)`
(`AlgebraicGeometry.Scheme.Modules.upperSemicontinuous_hFiber`).

## Main statements

- `AlgebraicGeometry.Scheme.Modules.isClosed_setOf_nonempty_iso_fiber`: the locus of points
  over which `M` and `N` are isomorphic on the fibre is closed.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- Tensor inverses are unique: if `A ⊗ B ≅ 𝒪` and `B ⊗ C ≅ 𝒪`, then `A ≅ C`. -/
lemma nonempty_iso_of_tensorObj_iso_unit_of_tensorObj_iso_unit {X : Scheme.{u}}
    {A B C : X.Modules} (e₁ : A ⊗ B ≅ 𝟙_ X.Modules) (e₂ : B ⊗ C ≅ 𝟙_ X.Modules) :
    Nonempty (A ≅ C) :=
  ⟨(ρ_ A).symm ≪≫ whiskerLeftIso A e₂.symm ≪≫ (α_ A B C).symm ≪≫ whiskerRightIso e₁ C ≪≫ λ_ C⟩

/-- `(M ⊗ Nᵛ) ⊗ (N ⊗ Mᵛ) ≅ 𝒪` for invertible modules `M`, `N`. -/
lemma nonempty_tensorObj_dual_tensorObj_tensorObj_dual_iso_unit {X : Scheme.{u}}
    (M N : X.Modules) [M.IsInvertible] [N.IsInvertible] :
    Nonempty ((M ⊗ Nᵛ) ⊗ (N ⊗ Mᵛ) ≅ 𝟙_ X.Modules) := by
  obtain ⟨dM⟩ := nonempty_tensorObj_dual_iso_unit M
  obtain ⟨dN⟩ := nonempty_tensorObj_dual_iso_unit N
  exact ⟨α_ _ _ _ ≪≫ whiskerLeftIso M ((α_ _ _ _).symm ≪≫ whiskerRightIso (β_ _ _ ≪≫ dN) _ ≪≫
    λ_ _) ≪≫ dM⟩

/-- On a `k`-scheme whose `H⁰(X, F)` is finite-dimensional, `h⁰(X, F) > 0` if and only if `F` has
a nonzero global section. -/
lemma pos_finrankH_zero_iff {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    (F : X.Modules) [FiniteDimensional k (F.H 0)] :
    0 < F.finrankH k 0 ↔ ∃ s : Γ(F, ⊤), s ≠ 0 := by
  rw [finrankH, Module.finrank_pos_iff_exists_ne_zero]
  refine ⟨fun ⟨x, hx⟩ ↦ ⟨H.zeroLinearEquiv F x, by simpa using hx⟩,
    fun ⟨s, hs⟩ ↦ ⟨(H.zeroLinearEquiv F).symm s, by simpa using hs⟩⟩

/-- An invertible module is of finite presentation. -/
lemma IsInvertible.isFinitePresentation {X : Scheme.{u}} (L : X.Modules) [L.IsInvertible] :
    L.IsFinitePresentation := by
  have : SheafOfModules.IsInvertible.{u, u, u} L := IsInvertible.sheafOfModules_isInvertible L
  have : SheafOfModules.IsFiniteLocallyFree.{u, u, u} L :=
    SheafOfModules.IsInvertible.isFiniteLocallyFree.{u, u, u} _
  exact SheafOfModules.IsFiniteLocallyFree.isFinitePresentation.{u, u, u} _

variable {P T : Scheme.{u}}

/-- For `f` proper and `A` invertible, `h⁰(P_t, A_t) > 0` if and only if `A_t` has a nonzero
global section. -/
lemma pos_hFiber_zero_iff (f : P ⟶ T) [IsProper f] (A : P.Modules) [A.IsInvertible] (t : T) :
    0 < A.hFiber f 0 t ↔ ∃ s : Γ((Modules.pullback (f.fiberι t)).obj A, ⊤), s ≠ 0 := by
  let := f.fiberOverSpecResidueField t
  have : IsProper (f.fiber t ↘ Spec (T.residueField t)) :=
    inferInstanceAs (IsProper (pullback.snd f (T.fromSpecResidueField t)))
  have := IsInvertible.isFinitePresentation ((Modules.pullback (f.fiberι t)).obj A)
  have : FiniteDimensional (T.residueField t)
      (((Modules.pullback (f.fiberι t)).obj A).H 0) := finiteDimensional_H_of_isProper _ 0
  exact pos_finrankH_zero_iff _

/-- **Triviality on a fibre through `h⁰`.** Let `f : P ⟶ T` be proper with geometrically
integral fibres and let `A`, `B` be invertible modules on `P` with `A ⊗ B ≅ 𝒪_P`. Then `A` is
trivial on the fibre `P_t` if and only if `h⁰(P_t, A_t) > 0` and `h⁰(P_t, B_t) > 0`
(`AlgebraicGeometry.Scheme.Modules.nonempty_iso_unit_of_tensorObj_iso_unit`). -/
theorem nonempty_iso_unit_fiber_iff (f : P ⟶ T) [IsProper f] [GeometricallyIntegral f]
    {A B : P.Modules} [A.IsInvertible] [B.IsInvertible] (e : A ⊗ B ≅ 𝟙_ P.Modules) (t : T) :
    Nonempty ((Modules.pullback (f.fiberι t)).obj A ≅ 𝟙_ (f.fiber t).Modules) ↔
      0 < A.hFiber f 0 t ∧ 0 < B.hFiber f 0 t := by
  set g := f.fiberι t
  have : IsProper (f.fiberToSpecResidueField t) :=
    inferInstanceAs (IsProper (pullback.snd f (T.fromSpecResidueField t)))
  have hfield : IsField Γ(f.fiber t, ⊤) :=
    isField_of_universallyClosed (T.residueField t) (f.fiberToSpecResidueField t)
  obtain ⟨μ⟩ := nonempty_pullback_tensorObj_iso g A B
  let eB : (Modules.pullback g).obj A ⊗ (Modules.pullback g).obj B ≅ 𝟙_ (f.fiber t).Modules :=
    μ.symm ≪≫ (Modules.pullback g).mapIso e ≪≫ pullbackObjUnitIso g
  have hne (D : (f.fiber t).Modules) (d : D ≅ 𝟙_ (f.fiber t).Modules) :
      ∃ s : Γ(D, ⊤), s ≠ 0 := by
    refine ⟨d.inv.app ⊤ (1 : Γ(f.fiber t, ⊤)), fun h ↦ one_ne_zero (α := Γ(f.fiber t, ⊤)) ?_⟩
    exact (bijective_app_of_iso d.symm ⊤).1 (h.trans (map_zero _).symm)
  rw [pos_hFiber_zero_iff, pos_hFiber_zero_iff]
  constructor
  · rintro ⟨d⟩
    refine ⟨hne _ d, hne _ ?_⟩
    exact (λ_ _).symm ≪≫ whiskerRightIso d.symm _ ≪≫ eB
  · rintro ⟨⟨s, hs⟩, ⟨s', hs'⟩⟩
    exact nonempty_iso_unit_of_tensorObj_iso_unit hfield eB hs hs'

/-- **The seesaw criterion on a fibre.** Let `f : P ⟶ T` be proper with geometrically integral
fibres and let `M`, `N` be invertible modules on `P`. Then `M_t ≅ N_t` if and only if
`h⁰(P_t, (M ⊗ Nᵛ)_t) > 0` and `h⁰(P_t, (N ⊗ Mᵛ)_t) > 0`. -/
theorem nonempty_iso_fiber_iff (f : P ⟶ T) [IsProper f] [GeometricallyIntegral f]
    (M N : P.Modules) [M.IsInvertible] [N.IsInvertible] (t : T) :
    Nonempty ((Modules.pullback (f.fiberι t)).obj M ≅ (Modules.pullback (f.fiberι t)).obj N) ↔
      0 < (M ⊗ Nᵛ).hFiber f 0 t ∧ 0 < (N ⊗ Mᵛ).hFiber f 0 t := by
  set g := f.fiberι t
  obtain ⟨u⟩ := nonempty_tensorObj_dual_tensorObj_tensorObj_dual_iso_unit M N
  rw [← nonempty_iso_unit_fiber_iff f u]
  refine ⟨fun ⟨e⟩ ↦ nonempty_pullback_tensorObj_dual_iso_unit g M N e, fun ⟨d⟩ ↦ ?_⟩
  obtain ⟨μM⟩ := nonempty_pullback_tensorObj_iso g M Nᵛ
  obtain ⟨μN⟩ := nonempty_pullback_tensorObj_iso g Nᵛ N
  obtain ⟨dN⟩ := nonempty_tensorObj_dual_iso_unit N
  exact nonempty_iso_of_tensorObj_iso_unit_of_tensorObj_iso_unit (μM.symm ≪≫ d)
    (μN.symm ≪≫ (Modules.pullback g).mapIso (β_ _ _ ≪≫ dN) ≪≫ pullbackObjUnitIso g)

/-- **Triviality over a field-valued point is triviality over its residue field.** Let
`f : P ⟶ T` be proper with geometrically integral fibres, let `M`, `N` be invertible modules on
`P`, and let `φ : Spec F ⟶ T` be a point with values in a field `F`, with image `t`. If `M` and
`N` become isomorphic on `P ×_T Spec F`, they are isomorphic on the fibre `P_t` over `κ(t)`.

Both conditions are expressed through `h⁰` of `M ⊗ Nᵛ` and `N ⊗ Mᵛ` on the fibres
(`AlgebraicGeometry.Scheme.Modules.nonempty_iso_unit_fiber_iff`), and the fibre dimensions are
invariant under base change (`AlgebraicGeometry.Scheme.Modules.hFiber_pullback_of_isPullback`). -/
theorem nonempty_iso_fiber_of_nonempty_iso_pullback (f : P ⟶ T) [IsProper f]
    [GeometricallyIntegral f] (M N : P.Modules) [M.IsInvertible] [N.IsInvertible]
    {F : Type u} [Field F] (φ : Spec (.of F) ⟶ T)
    (hφ : Nonempty ((Modules.pullback (pullback.fst f φ)).obj M ≅
      (Modules.pullback (pullback.fst f φ)).obj N)) :
    Nonempty ((Modules.pullback (f.fiberι (φ.base (IsLocalRing.closedPoint F)))).obj M ≅
      (Modules.pullback (f.fiberι (φ.base (IsLocalRing.closedPoint F)))).obj N) := by
  set x := IsLocalRing.closedPoint F
  set g' := pullback.fst f φ
  set f' := pullback.snd f φ
  have sq : IsPullback g' f' f φ := IsPullback.of_hasPullback f φ
  have hpos {A B : P.Modules} [A.IsInvertible] [B.IsInvertible] (e : A ⊗ B ≅ 𝟙_ P.Modules)
      (d : (Modules.pullback g').obj A ≅ 𝟙_ _) : 0 < A.hFiber f 0 (φ.base x) := by
    have := IsInvertible.isFinitePresentation A
    rw [← hFiber_pullback_of_isPullback f A φ g' f' sq 0 x]
    obtain ⟨μ⟩ := nonempty_pullback_tensorObj_iso g' A B
    refine ((nonempty_iso_unit_fiber_iff f' (μ.symm ≪≫ (Modules.pullback g').mapIso e ≪≫
      pullbackObjUnitIso g') x).mp ⟨(Modules.pullback (f'.fiberι x)).mapIso d ≪≫
        pullbackObjUnitIso _⟩).1
  obtain ⟨u⟩ := nonempty_tensorObj_dual_tensorObj_tensorObj_dual_iso_unit M N
  obtain ⟨e⟩ := hφ
  rw [nonempty_iso_fiber_iff]
  exact ⟨hpos u (nonempty_pullback_tensorObj_dual_iso_unit g' M N e).some,
    hpos (β_ _ _ ≪≫ u) (nonempty_pullback_tensorObj_dual_iso_unit g' N M e.symm).some⟩

/-- **The seesaw principle: the locus of triviality on the fibres is closed** (Stacks, Tags 0BDP
and 0BF0). Let `f : P ⟶ T` be proper, flat, locally of finite presentation and with geometrically
integral fibres, and let `M`, `N` be invertible modules on `P`. The set of points `t ∈ T` such
that `M` and `N` become isomorphic on the fibre `P_t` is closed.

By `AlgebraicGeometry.Scheme.Modules.nonempty_iso_fiber_iff` it is the set of points where
`h⁰(P_t, (M ⊗ Nᵛ)_t) ≥ 1` and `h⁰(P_t, (N ⊗ Mᵛ)_t) ≥ 1`. Both conditions are closed by upper
semicontinuity (`AlgebraicGeometry.Scheme.Modules.upperSemicontinuous_hFiber`). -/
theorem isClosed_setOf_nonempty_iso_fiber (f : P ⟶ T) [IsProper f] [Flat f]
    [LocallyOfFinitePresentation f] [GeometricallyIntegral f] (M N : P.Modules) [M.IsInvertible]
    [N.IsInvertible] :
    IsClosed {t : T | Nonempty ((Modules.pullback (f.fiberι t)).obj M ≅
      (Modules.pullback (f.fiberι t)).obj N)} := by
  have := isGrothendieckAbelian P
  have hopen (L : P.Modules) [L.IsInvertible] : IsOpen {t | L.hFiber f 0 t < 1} :=
    have := IsInvertible.isFinitePresentation L
    have : SheafOfModules.IsInvertible.{u, u, u} L := IsInvertible.sheafOfModules_isInvertible L
    (upperSemicontinuous_hFiber f L (isFlatOver_of_isInvertible f L) 0).isOpen_preimage 1
  have hset : {t : T | Nonempty ((Modules.pullback (f.fiberι t)).obj M ≅
      (Modules.pullback (f.fiberι t)).obj N)} =
      {t | (M ⊗ Nᵛ).hFiber f 0 t < 1}ᶜ ∩ {t | (N ⊗ Mᵛ).hFiber f 0 t < 1}ᶜ := by
    ext t
    simp only [Set.mem_ofPred_eq, nonempty_iso_fiber_iff f M N t, Set.mem_inter_iff,
      Set.mem_compl_iff, not_lt, Nat.one_le_iff_ne_zero, Nat.pos_iff_ne_zero]
  rw [hset]
  exact (hopen _).isClosed_compl.inter (hopen _).isClosed_compl

/-- **Triviality on a fibre is preserved by restriction to an open of the base.** For `f`
proper with geometrically integral fibres and `L` invertible, if `L` is trivial on the fibre
over a point `t` of an open `V`, then so is its restriction for `f ∣_ V`. -/
lemma nonempty_iso_unit_fiber_morphismRestrict (f : P ⟶ T) [IsProper f]
    [GeometricallyIntegral f] (L : P.Modules) [L.IsInvertible] (V : T.Opens) (t : V)
    (ht : Nonempty ((Modules.pullback (f.fiberι (V.ι t))).obj L ≅ 𝟙_ (f.fiber (V.ι t)).Modules)) :
    Nonempty ((Modules.pullback ((f ∣_ V).fiberι t)).obj ((Modules.pullback (f ⁻¹ᵁ V).ι).obj L) ≅
      𝟙_ ((f ∣_ V).fiber t).Modules) := by
  have := IsInvertible.isFinitePresentation L
  have := IsInvertible.isFinitePresentation Lᵛ
  obtain ⟨d⟩ := nonempty_tensorObj_dual_iso_unit L
  obtain ⟨μ⟩ := nonempty_pullback_tensorObj_iso (f ⁻¹ᵁ V).ι L Lᵛ
  have sq : IsPullback (f ⁻¹ᵁ V).ι (f ∣_ V) f V.ι := (isPullback_morphismRestrict f V).flip
  rw [nonempty_iso_unit_fiber_iff f d] at ht
  rw [nonempty_iso_unit_fiber_iff (f ∣_ V) (μ.symm ≪≫ (Modules.pullback _).mapIso d ≪≫
    pullbackObjUnitIso _), hFiber_pullback_of_isPullback f L V.ι _ _ sq,
    hFiber_pullback_of_isPullback f Lᵛ V.ι _ _ sq]
  exact ht


/-- A free generator of `L` over an open `O` trivialises the restriction of `L` to `O`. -/
lemma nonempty_pullback_ι_iso_unit_of_isFreeGenerator (L : P.Modules) {O : P.Opens}
    {m : Γ(L, O)} (hm : IsFreeGenerator m) :
    Nonempty ((Modules.pullback O.ι).obj L ≅ 𝟙_ O.toScheme.Modules) := by
  have hm' : IsFreeGenerator (M := L.restrict O.ι) (U := ⊤)
      (L.presheaf.map (homOfLE (Scheme.Opens.ι_image_top O).le).op m) :=
    (isFreeGenerator_restrict_iff O.ι L _).mpr (hm.map _)
  have := isIso_homOfGlobalSection hm'
  exact ⟨((restrictFunctorIsoPullback O.ι).app L).symm ≪≫
    (asIso (homOfGlobalSection (L.restrict O.ι)
      (L.presheaf.map (homOfLE (Scheme.Opens.ι_image_top O).le).op m))).symm⟩

/-- If `g^* (M ⊗ Nᵛ)` is trivial for an invertible `N`, then `g^* M ≅ g^* N`. -/
lemma nonempty_pullback_iso_of_pullback_tensorObj_dual_iso_unit {A : Scheme.{u}} (g : A ⟶ P)
    (M N : P.Modules) [N.IsInvertible]
    (e : (Modules.pullback g).obj (M ⊗ Nᵛ) ≅ 𝟙_ A.Modules) :
    Nonempty ((Modules.pullback g).obj M ≅ (Modules.pullback g).obj N) := by
  obtain ⟨μ₁⟩ := nonempty_pullback_tensorObj_iso g M Nᵛ
  obtain ⟨μ₂⟩ := nonempty_pullback_tensorObj_iso g Nᵛ N
  obtain ⟨d⟩ := nonempty_tensorObj_dual_iso_unit N
  exact nonempty_iso_of_tensorObj_iso_unit_of_tensorObj_iso_unit (μ₁.symm ≪≫ e)
    (μ₂.symm ≪≫ (Modules.pullback g).mapIso (β_ _ _ ≪≫ d) ≪≫ pullbackObjUnitIso g)

end AlgebraicGeometry.Scheme.Modules
