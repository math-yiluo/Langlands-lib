/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import WeilConjectures.AlgebraicGeometry.Curve.AffineCount
public import WeilConjectures.AlgebraicGeometry.Curve.BaseChange

/-!
# Invariance of the cohomology of an affine curve under algebraically closed extension

Let `k ⊆ k'` be algebraically closed fields and `C` a smooth affine connected curve over `k`, with
smooth compactification `C ⊆ C̄`. The base change `C̄_{k'}` is a smooth compactification of
`C_{k'}` of the same genus, with a boundary of the same size, since the boundary points are
`k`-rational. Hence `|H¹(C, ℤ/n)| = |H¹(C_{k'}, ℤ/n)|`
(`AlgebraicGeometry.IsConnectedCurve.natCard_sheafH_one_constantZMod_mul`), and the pullback
`Hᵠ(C, ℤ/n) ⟶ Hᵠ(C_{k'}, ℤ/n)`, which is injective, is bijective.

## Main definitions

- `AlgebraicGeometry.Compactification.baseChangeField`: the base change of a compactification.

## Main statements

- `AlgebraicGeometry.IsConnectedCurve.bijective_fieldExtensionCohomologyMap_of_isAffine`: the
  invariance of `Hᵠ(C, ℤ/n)` for a smooth affine connected curve.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {C : Scheme.{u}} {f : C ⟶ Spec (.of k)} (k' : Type u) [Field k']
  [Algebra k k']

/-- The square `C_{k'} ⟶ C̄_{k'}` over `C ⟶ C̄` is cartesian. -/
lemma Compactification.isPullback_baseChangeField (c : Compactification f) :
    IsPullback (pullback.map f (Spec.map (CommRingCat.ofHom (algebraMap k k'))) c.g
        (Spec.map (CommRingCat.ofHom (algebraMap k k'))) c.i (𝟙 _) (𝟙 _)
        (by simp [c.comm]) (by simp))
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k k'))))
      (pullback.fst c.g (Spec.map (CommRingCat.ofHom (algebraMap k k')))) c.i := by
  have h := IsPullback.of_right (h₁₁ := pullback.map f
      (Spec.map (CommRingCat.ofHom (algebraMap k k'))) c.g
      (Spec.map (CommRingCat.ofHom (algebraMap k k'))) c.i (𝟙 _) (𝟙 _)
        (by simp [c.comm]) (by simp))
    (h₁₂ := pullback.snd c.g (Spec.map (CommRingCat.ofHom (algebraMap k k'))))
    (v₁₁ := pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k k'))))
    (v₁₂ := pullback.fst c.g (Spec.map (CommRingCat.ofHom (algebraMap k k'))))
    (v₁₃ := Spec.map (CommRingCat.ofHom (algebraMap k k'))) (h₂₁ := c.i) (h₂₂ := c.g)
    (by
      rw [pullback.lift_snd, Category.comp_id, ← c.comm]
      exact (IsPullback.of_hasPullback f _).flip)
    (by simp) (IsPullback.of_hasPullback c.g _).flip
  exact h

/-- The base change `C̄_{k'}` of a compactification `C̄` of `C` is a compactification of
`C_{k'}`. -/
@[simps]
noncomputable def Compactification.baseChangeField (c : Compactification f) :
    Compactification (f.baseChangeField k') where
  Z := pullback c.g (Spec.map (CommRingCat.ofHom (algebraMap k k')))
  g := c.g.baseChangeField k'
  i := pullback.map f (Spec.map (CommRingCat.ofHom (algebraMap k k'))) c.g
    (Spec.map (CommRingCat.ofHom (algebraMap k k'))) c.i (𝟙 _) (𝟙 _) (by simp [c.comm])
    (by simp)
  comm := by simp
  isProper := inferInstance
  isOpenImmersion := MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    (c.isPullback_baseChangeField k').flip c.isOpenImmersion

/-- A scheme isomorphic to a scheme with at most one point has at most one point. -/
lemma Scheme.subsingleton_of_iso {X Y : Scheme.{u}} (e : X ≅ Y) [Subsingleton Y] :
    Subsingleton X := by
  refine ⟨fun a b ↦ ?_⟩
  have h := congrArg e.inv.base (Subsingleton.elim (e.hom a) (e.hom b))
  simpa [← Scheme.Hom.comp_apply] using h

/-- **Fibres over rational points.** Let `X` be locally of finite type over an algebraically
closed field `k` and `k ⊆ k'` a field extension. Over a closed point `x` of `X`, the projection
`X_{k'} ⟶ X` has exactly one point: `x` is a `k`-rational point `σ : Spec k ⟶ X`, and the fibre
is the image of `Spec k ×_X X_{k'} ≅ Spec k'`. -/
lemma Scheme.Hom.subsingleton_preimage_pullback_fst [IsAlgClosed k] {X : Scheme.{u}}
    (g : X ⟶ Spec (.of k)) [LocallyOfFiniteType g] {x : X} (hx : IsClosed {x}) :
    ((pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap k k')))) ⁻¹' {x}).Subsingleton := by
  obtain ⟨σ, hσ⟩ := g.exists_fieldPoints_base_eq_of_isClosed hx
  let s : Spec (.of k) ⟶ X := σ.1
  have hσg : s ≫ g = 𝟙 _ := by
    rw [σ.2, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  have hrange : Set.range s = {x} := by
    ext y
    refine ⟨fun ⟨p, hp⟩ ↦ ?_, fun hy ↦ ⟨default, hσ.trans hy.symm⟩⟩
    rw [← hp, ← hσ, Subsingleton.elim p default]
    rfl
  have : IsIso (s ≫ g) := by rw [hσg]; infer_instance
  have : Subsingleton (pullback (C := Scheme.{u}) (s ≫ g)
      (Spec.map (CommRingCat.ofHom (algebraMap k k')))) :=
    Scheme.subsingleton_of_iso (asIso (pullback.snd (s ≫ g)
      (Spec.map (CommRingCat.ofHom (algebraMap k k')))))
  have : Subsingleton (pullback (C := Scheme.{u}) s (pullback.fst g
      (Spec.map (CommRingCat.ofHom (algebraMap k k'))))) :=
    Scheme.subsingleton_of_iso (pullbackRightPullbackFstIso _ _ _)
  intro z₁ hz₁ z₂ hz₂
  have hr := Scheme.Pullback.range_snd s
    (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap k k'))))
  rw [hrange] at hr
  obtain ⟨p₁, rfl⟩ : z₁ ∈ Set.range _ := hr ▸ hz₁
  obtain ⟨p₂, rfl⟩ : z₂ ∈ Set.range _ := hr ▸ hz₂
  rw [Subsingleton.elim p₁ p₂]

/-- The boundary of a compactification `C ⊆ C̄` of a nonempty curve by a smooth proper connected
curve consists of closed points. -/
lemma Compactification.isClosed_singleton_of_notMem_range (c : Compactification f)
    [IsConnectedCurve c.g] [Smooth c.g] [Nonempty C] {x : c.Z} (hx : x ∉ Set.range c.i) :
    IsClosed {x} := by
  have := IsConnectedCurve.connectedSpace (f := c.g)
  have : IsLocallyNoetherian c.Z := LocallyOfFiniteType.isLocallyNoetherian c.g
  have : IsRegular c.Z := IsRegular.of_smooth c.g
  have : IrreducibleSpace c.Z := IsRegular.irreducibleSpace c.Z
  obtain ⟨y⟩ := ‹Nonempty C›
  exact c.isOpenImmersion.isOpen_range.isClosed_singleton_of_mem_compl
    (IsConnectedCurve.krullDim_eq_one (f := c.g)).le ⟨c.i y, y, rfl⟩ hx

/-- The number of boundary points of a compactification, counted as closed points. -/
lemma Compactification.natCard_closedPoints_compl (c : Compactification f)
    [IsConnectedCurve c.g] [Smooth c.g] [Nonempty C] :
    Nat.card {P : closedPoints c.Z // P.1 ∉ Set.range c.i} =
      Nat.card {x : c.Z // x ∉ Set.range c.i} :=
  Nat.card_congr
    { toFun P := ⟨P.1.1, P.2⟩
      invFun x := ⟨⟨x.1, c.isClosed_singleton_of_notMem_range x.2⟩, x.2⟩
      left_inv _ := rfl
      right_inv _ := rfl }

/-- **The boundary of the base change.** For a compactification `C ⊆ C̄` over an algebraically
closed field `k` whose boundary consists of closed points, the boundary of `C_{k'} ⊆ C̄_{k'}` is
in bijection with that of `C ⊆ C̄`: it is the preimage of the boundary, and the fibres of
`C̄_{k'} ⟶ C̄` over closed points are single points. -/
lemma Compactification.natCard_compl_baseChangeField [IsAlgClosed k] (c : Compactification f)
    [LocallyOfFiniteType c.g] (hcl : ∀ x ∉ Set.range c.i, IsClosed ({x} : Set c.Z)) :
    Nat.card {x : (c.baseChangeField k').Z // x ∉ Set.range (c.baseChangeField k').i} =
      Nat.card {x : c.Z // x ∉ Set.range c.i} := by
  set π := pullback.fst c.g (Spec.map (CommRingCat.ofHom (algebraMap k k')))
  have hrange : Set.range (c.baseChangeField k').i = π ⁻¹' Set.range c.i := by
    have h := Scheme.Pullback.range_map f (Spec.map (CommRingCat.ofHom (algebraMap k k'))) c.g
      (Spec.map (CommRingCat.ofHom (algebraMap k k'))) c.i (𝟙 _) (𝟙 _) (by simp [c.comm])
      (by simp)
    refine h.trans ?_
    ext z
    simp [π]
  refine Nat.card_congr (Equiv.ofBijective
    (fun z ↦ ⟨π z.1, fun h ↦ z.2 ((Set.ext_iff.1 hrange _).2 h)⟩) ⟨fun z₁ z₂ h ↦ ?_, fun x ↦ ?_⟩)
  · have h' : π z₁.1 = π z₂.1 := congrArg Subtype.val h
    refine Subtype.ext (Scheme.Hom.subsingleton_preimage_pullback_fst k' c.g
      (hcl _ fun hr ↦ z₂.2 ((Set.ext_iff.1 hrange _).2 hr)) h' rfl)
  · obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := c.g) (g := Spec.map (CommRingCat.ofHom (algebraMap k k'))) x.1
      (default : Spec (.of k')) (Subsingleton.elim _ _)
    exact ⟨⟨z, fun h ↦ x.2 (by
      have := (Set.ext_iff.1 hrange _).1 h; rwa [Set.mem_preimage, hz] at this)⟩,
      Subtype.ext hz⟩

/-- **Base change of a connected curve.** Over an algebraically closed field `k`, the base change
of a smooth connected curve `C` with a smooth proper connected compactification `C̄` to a field
extension `k'` is a smooth connected curve: it is a nonempty open subscheme of the irreducible
curve `C̄_{k'}` (`AlgebraicGeometry.IsConnectedCurve.baseChangeField`).
(blueprint: `lem-sc-base-change-curve`) -/
theorem IsConnectedCurve.baseChangeField_of_compactification [IsAlgClosed k] [IsConnectedCurve f]
    [Smooth f] (c : Compactification f) [IsConnectedCurve c.g] [Smooth c.g] :
    IsConnectedCurve (f.baseChangeField k') := by
  have : SmoothOfRelativeDimension 1 f := IsConnectedCurve.smoothOfRelativeDimension_one f
  have : SmoothOfRelativeDimension 1 c.g := IsConnectedCurve.smoothOfRelativeDimension_one c.g
  obtain ⟨hs, hc, -, -⟩ := f.baseChangeField_isCurve k'
  obtain ⟨hs', -, -, -⟩ := c.g.baseChangeField_isCurve k'
  have : Smooth (c.g.baseChangeField k') := hs'.smooth
  have := IsConnectedCurve.baseChangeField c.g k'
  have : ConnectedSpace (c.baseChangeField k').Z :=
    IsConnectedCurve.connectedSpace (f := c.g.baseChangeField k')
  have : IsLocallyNoetherian (c.baseChangeField k').Z :=
    LocallyOfFiniteType.isLocallyNoetherian (c.g.baseChangeField k')
  have : IsRegular (c.baseChangeField k').Z := IsRegular.of_smooth (c.g.baseChangeField k')
  have : IrreducibleSpace (c.baseChangeField k').Z := IsRegular.irreducibleSpace _
  obtain ⟨x₀⟩ := IsConnectedCurve.nonempty f
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback
    (f := f) (g := Spec.map (CommRingCat.ofHom (algebraMap k k'))) x₀
    (default : Spec (.of k')) (Subsingleton.elim _ _)
  have : Nonempty
      (pullback (C := Scheme.{u}) f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) := ⟨z⟩
  have := (c.baseChangeField k').i.isOpenEmbedding.irreducibleSpace
  exact { krullDim_le_one := hc.krullDim_le_one
          connectedSpace := inferInstance
          krullDim_eq_one :=
            topologicalKrullDim_eq_of_smoothOfRelativeDimension (f.baseChangeField k') 1 }

/-- **Invariance of the cohomology of a smooth affine curve.** Let `k ⊆ k'` be algebraically
closed fields, `C` a smooth affine connected curve over `k` and `n` prime to `char k`. Then the
pullback `Hᵠ(C, ℤ/n) ⟶ Hᵠ(C_{k'}, ℤ/n)` is bijective for every `q`. It is injective
(`AlgebraicGeometry.injective_cohomologyMap_pullback_fst_of_isAlgClosed`); both sides are `ℤ/n`
for `q = 0` and vanish for `q ≥ 2`
(`AlgebraicGeometry.IsConnectedCurve.sheafH_constantZMod_of_isAffine`). For `q = 1`, if `C̄` is
a smooth compactification of `C` of genus `g` with `r` boundary points, then `C̄_{k'}` is a smooth
compactification of the smooth affine connected curve `C_{k'}`, of genus `g`
(`AlgebraicGeometry.Scheme.Hom.genus_baseChangeField`) with `r` boundary points
(`AlgebraicGeometry.Compactification.natCard_compl_baseChangeField`), so both groups have order
`n ^ (2g + r - 1)` (`AlgebraicGeometry.IsConnectedCurve.natCard_sheafH_one_constantZMod_mul`).
(blueprint: `proposition-cohomology-smooth-affine-curve`, affine case) -/
theorem IsConnectedCurve.bijective_fieldExtensionCohomologyMap_of_isAffine [IsAlgClosed k]
    [IsConnectedCurve f] [Smooth f] [IsAffine C] [IsAlgClosed k'] (n : ℕ) (hn : (n : k) ≠ 0)
    (q : ℕ) : Function.Bijective (f.fieldExtensionCohomologyMap k' (C.constantZMod n) q) := by
  have := IsConnectedCurve.connectedSpace (f := f)
  have := IsConnectedCurve.nonempty f
  have : CompactSpace C := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace C := (quasiSeparated_iff_quasiSeparatedSpace f).mp inferInstance
  have : SmoothOfRelativeDimension 1 f := IsConnectedCurve.smoothOfRelativeDimension_one f
  have hinj := injective_cohomologyMap_pullback_fst_of_isAlgClosed f k' (C.constantZMod n) q
  obtain ⟨c, hc, hsm, -, hcl⟩ := IsConnectedCurve.exists_smooth_properCompactification f
  have : SmoothOfRelativeDimension 1 c.g := IsConnectedCurve.smoothOfRelativeDimension_one c.g
  obtain ⟨hs, -, -, ha⟩ := f.baseChangeField_isCurve k'
  have := ha inferInstance
  have : Smooth (f.baseChangeField k') := hs.smooth
  have := IsConnectedCurve.baseChangeField_of_compactification k' c
  obtain ⟨hs', -, -, -⟩ := c.g.baseChangeField_isCurve k'
  have : Smooth (c.baseChangeField k').g := hs'.smooth
  have : IsConnectedCurve (c.baseChangeField k').g := IsConnectedCurve.baseChangeField c.g k'
  have := IsConnectedCurve.nonempty (f.baseChangeField k')
  have hn' : (n : k') ≠ 0 := by
    rw [← map_natCast (algebraMap k k')]
    exact (map_ne_zero _).2 hn
  have hn0 : n ≠ 0 := by rintro rfl; exact hn Nat.cast_zero
  obtain ⟨⟨e₀⟩, -, -, -, h₂⟩ := IsConnectedCurve.sheafH_constantZMod_of_isAffine f n hn
  obtain ⟨⟨e₀'⟩, -, -, -, h₂'⟩ :=
    IsConnectedCurve.sheafH_constantZMod_of_isAffine (f.baseChangeField k') n hn'
  let E := f.sheafHBaseChangeConstantZModAddEquiv k' n q
  have : NeZero n := ⟨hn0⟩
  rcases (show q = 0 ∨ q = 1 ∨ 1 < q by omega) with rfl | rfl | hq
  · have : Finite (Sheaf.H
        ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k')))).constantZMod n) 0) :=
      Finite.of_equiv _ e₀'.symm.toEquiv
    have := Finite.of_equiv _ E.symm.toEquiv
    refine hinj.bijective_of_nat_card_le ?_
    rw [Nat.card_congr E.toEquiv, Nat.card_congr e₀.toEquiv, Nat.card_congr e₀'.toEquiv]
  · have h₁ := natCard_sheafH_one_constantZMod_mul f c hn
    have h₁' := natCard_sheafH_one_constantZMod_mul (f.baseChangeField k')
      (c.baseChangeField k') hn'
    rw [c.natCard_closedPoints_compl] at h₁
    rw [(c.baseChangeField k').natCard_closedPoints_compl,
      c.natCard_compl_baseChangeField k' hcl] at h₁'
    have hg : (c.baseChangeField k').g.genus = c.g.genus := c.g.genus_baseChangeField k'
    rw [hg, ← h₁] at h₁'
    have hcard := Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hn0) h₁'
    have hpos : Nat.card (Sheaf.H
        ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k')))).constantZMod n) 1) ≠ 0 := by
      rw [hcard]
      intro h0
      rw [h0, zero_mul] at h₁
      exact pow_ne_zero _ hn0 h₁.symm
    have : Finite (Sheaf.H
        ((pullback f (Spec.map (CommRingCat.ofHom (algebraMap k k')))).constantZMod n) 1) :=
      Nat.finite_of_card_ne_zero hpos
    have := Finite.of_equiv _ E.symm.toEquiv
    refine hinj.bijective_of_nat_card_le ?_
    rw [Nat.card_congr E.toEquiv, hcard]
  · have := h₂' q hq
    have : Subsingleton (Sheaf.H ((Etale.upperStar AddCommGrpCat.{u + 1}
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k k'))))).obj
          (C.constantZMod n)) q) := E.toEquiv.subsingleton
    exact ⟨hinj, fun y ↦ ⟨0, Subsingleton.elim _ _⟩⟩

end AlgebraicGeometry
