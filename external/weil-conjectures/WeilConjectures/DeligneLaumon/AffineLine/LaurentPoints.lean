/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line
public import WeilConjectures.Mathlib.RingTheory.LaurentSeries
public import WeilConjectures.DeligneLaumon.AffineLine.GeometricSMul

/-!
# The punctured formal disc at infinity

Let `k̄` be an algebraic closure of the finite field `k₀`, `R = k̄⟦t⟧`, `K = k̄((t))` and `L` an
algebraic closure of `K`. The coordinate `t = 1 / x` at `∞ ∈ ℙ¹` gives

- the point `Spec R ⟶ ℙ¹_{k̄}`, `z = t` in the chart at infinity
  (`AlgebraicGeometry.powerSeriesInfinityPoint`), whose closed point maps to `∞`;
- the points `Spec K ⟶ 𝔸¹_{k̄}`, `x = b / t` (`AlgebraicGeometry.laurentPoint`), which are
  generic, so they factor through every nonempty open `Ū`;

and over `x = b / t`, `b ≠ 0`, a root `u ∈ L` of the Artin–Schreier equation `u^q - u = b / t`
gives a point `Spec L ⟶ 𝔸¹_{k̄}` over `Spec K` lifting `x = b / t` along `ĀS`, which every
translation `σ̄_c`, `c ∈ k₀`, carries to its image under some `K`-automorphism of `L`
(`LaurentSeries.exists_algEquiv_apply_eq_add_C_of_pow_sub_eq_single`).

This is the formal local geometry at `∞` behind the ramification of the linear Artin–Schreier
sheaves at infinity (blueprint `lemma-unramified-at-infinity-no-linear-characters--1`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable (k₀ : Type u) [Field k₀]

local notation "Ā" => Scheme.Hom.geometricFiber (affineLine k₀ ↘ Spec (CommRingCat.of k₀))

section GeometricPoint

variable (A : Type u) [CommRing A] [Algebra k₀ A] [Algebra (AlgebraicClosure k₀) A]
  [IsScalarTower k₀ (AlgebraicClosure k₀) A]

/-- The point `x = v` of `𝔸¹_{k₀}` with values in a `k̄`-algebra `A` lies over `Spec k̄`. -/
lemma affineLine.homOfVector_comp_over_eq (v : A) :
    AffineSpace.homOfVector (Spec.map (CommRingCat.ofHom (algebraMap k₀ A)))
        (fun _ ↦ (Scheme.ΓSpecIso (.of A)).inv.hom v) ≫
        (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) =
      Spec.map (CommRingCat.ofHom (algebraMap (AlgebraicClosure k₀) A)) ≫
        (Scheme.specAlgebraicClosure k₀).hom := by
  rw [AffineSpace.homOfVector_over]
  simp only [Scheme.specAlgebraicClosure, Over.mk_hom]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

/-- The point `x = v` of the geometric affine line `𝔸¹_{k̄}` with values in a `k̄`-algebra `A`. -/
noncomputable def affineLine.geometricPoint (v : A) : Spec (.of A) ⟶ Ā :=
  pullback.lift
    (AffineSpace.homOfVector (Spec.map (CommRingCat.ofHom (algebraMap k₀ A)))
      fun _ ↦ (Scheme.ΓSpecIso (.of A)).inv.hom v)
    (Spec.map (CommRingCat.ofHom (algebraMap (AlgebraicClosure k₀) A)))
    (affineLine.homOfVector_comp_over_eq k₀ A v)

@[reassoc (attr := simp)]
lemma affineLine.geometricPoint_geometricFiberProj (v : A) :
    affineLine.geometricPoint k₀ A v ≫
        (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberProj =
      AffineSpace.homOfVector (Spec.map (CommRingCat.ofHom (algebraMap k₀ A)))
        fun _ ↦ (Scheme.ΓSpecIso (.of A)).inv.hom v :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma affineLine.geometricPoint_geometricFiberToAlgebraicClosure (v : A) :
    affineLine.geometricPoint k₀ A v ≫
        (affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure =
      Spec.map (CommRingCat.ofHom (algebraMap (AlgebraicClosure k₀) A)) :=
  pullback.lift_snd _ _ _

/-- A `k̄`-algebra map `φ : A → B` carries the point `x = v` to the point `x = φ v`. -/
lemma affineLine.specMap_comp_geometricPoint {B : Type u} [CommRing B] [Algebra k₀ B]
    [Algebra (AlgebraicClosure k₀) B] [IsScalarTower k₀ (AlgebraicClosure k₀) B] (φ : A →+* B)
    (hφ : ∀ x, φ (algebraMap (AlgebraicClosure k₀) A x) = algebraMap (AlgebraicClosure k₀) B x)
    (v : A) :
    Spec.map (CommRingCat.ofHom φ) ≫ affineLine.geometricPoint k₀ A v =
      affineLine.geometricPoint k₀ B (φ v) := by
  have hφ₀ (x : k₀) : φ (algebraMap k₀ A x) = algebraMap k₀ B x := by
    rw [IsScalarTower.algebraMap_apply k₀ (AlgebraicClosure k₀) A, hφ,
      ← IsScalarTower.algebraMap_apply]
  refine Scheme.Hom.geometricFiber_hom_ext _ ?_ ?_
  · rw [Category.assoc, affineLine.geometricPoint_geometricFiberProj,
      affineLine.geometricPoint_geometricFiberProj]
    refine AffineSpace.hom_ext ?_ fun _ ↦ ?_
    · rw [Category.assoc, AffineSpace.homOfVector_over, AffineSpace.homOfVector_over,
        ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      exact RingHom.ext hφ₀
    · rw [AffineSpace.comp_homOfVector_appTop_coord, AffineSpace.homOfVector_appTop_coord,
        Scheme.specMap_appTop_ΓSpecIso_inv]
      rfl
  · rw [Category.assoc, affineLine.geometricPoint_geometricFiberToAlgebraicClosure,
      affineLine.geometricPoint_geometricFiberToAlgebraicClosure, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext hφ

/-- The base change of an endomorphism `g` of `𝔸¹_{k₀}` over `k₀` maps the point `x = v` to the
point `x = w` as soon as the coordinate of `g` evaluated at `v` is `w`. -/
lemma affineLine.geometricPoint_comp_geometricFiberMap (g : affineLine k₀ ⟶ affineLine k₀)
    (hg : g ≫ (affineLine k₀ ↘ Spec (CommRingCat.of k₀)) = affineLine k₀ ↘ Spec (CommRingCat.of k₀))
    (v w : A)
    (h : (AffineSpace.homOfVector (Spec.map (CommRingCat.ofHom (algebraMap k₀ A)))
        fun _ ↦ (Scheme.ΓSpecIso (.of A)).inv.hom v).appTop
          (g.appTop (AffineSpace.coord _ PUnit.unit)) = (Scheme.ΓSpecIso (.of A)).inv.hom w) :
    affineLine.geometricPoint k₀ A v ≫ Scheme.Hom.geometricFiberMap g hg =
      affineLine.geometricPoint k₀ A w := by
  refine Scheme.Hom.geometricFiber_hom_ext _ ?_ ?_
  · rw [Category.assoc, Scheme.Hom.geometricFiberMap_comp_geometricFiberProj,
      affineLine.geometricPoint_geometricFiberProj_assoc,
      affineLine.geometricPoint_geometricFiberProj]
    refine AffineSpace.hom_ext ?_ fun _ ↦ ?_
    · rw [Category.assoc, hg, AffineSpace.homOfVector_over, AffineSpace.homOfVector_over]
    · rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, h, AffineSpace.homOfVector_appTop_coord]
  · simp

omit [Algebra (AlgebraicClosure k₀) A] [IsScalarTower k₀ (AlgebraicClosure k₀) A] in
/-- The coordinate of the point `x = v` evaluated on a global function `c ∈ k₀` of the base. -/
lemma affineLine.homOfVector_appTop_appTop (v : A) (c : k₀) :
    (AffineSpace.homOfVector (Spec.map (CommRingCat.ofHom (algebraMap k₀ A)))
        fun _ ↦ (Scheme.ΓSpecIso (.of A)).inv.hom v).appTop
          ((affineLine k₀ ↘ Spec (CommRingCat.of k₀)).appTop
            ((Scheme.ΓSpecIso (.of k₀)).inv.hom c)) =
      (Scheme.ΓSpecIso (.of A)).inv.hom (algebraMap k₀ A c) := by
  rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, AffineSpace.homOfVector_over,
    Scheme.specMap_appTop_ΓSpecIso_inv]
  rfl

end GeometricPoint

/-- The scalar tower `k₀ → k̄ → k̄((t))`, stated with the scalar actions coming from the algebra
structures (the instance found by unification is slow to compare with them). -/
instance _root_.LaurentSeries.isScalarTower_algebraicClosure :
    @IsScalarTower k₀ (AlgebraicClosure k₀) (LaurentSeries (AlgebraicClosure k₀)) Algebra.toSMul
      Algebra.toSMul Algebra.toSMul :=
  .of_algebraMap_eq fun _ ↦ by
    simp [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply]

/-- The scalar tower `k₀ → k̄ → k̄⟦t⟧`, stated with the scalar actions coming from the algebra
structures. -/
instance _root_.PowerSeries.isScalarTower_algebraicClosure :
    @IsScalarTower k₀ (AlgebraicClosure k₀) (PowerSeries (AlgebraicClosure k₀)) Algebra.toSMul
      Algebra.toSMul Algebra.toSMul :=
  .of_algebraMap_eq fun _ ↦ by simp [PowerSeries.algebraMap_apply]

/-- The point `x = b / t` of the geometric affine line `𝔸¹_{k̄}` with values in the Laurent series
field `k̄((t))`. -/
noncomputable def laurentPoint (b : AlgebraicClosure k₀) :
    Spec (.of (LaurentSeries (AlgebraicClosure k₀))) ⟶ Ā :=
  pullback.lift
    (AffineSpace.homOfVector
      (Spec.map (CommRingCat.ofHom (algebraMap k₀ (LaurentSeries (AlgebraicClosure k₀)))))
      fun _ ↦ (Scheme.ΓSpecIso (.of (LaurentSeries (AlgebraicClosure k₀)))).inv.hom
        (HahnSeries.single (-1) b))
    (Spec.map (CommRingCat.ofHom
      (algebraMap (AlgebraicClosure k₀) (LaurentSeries (AlgebraicClosure k₀)))))
    (affineLine.homOfVector_comp_over_eq k₀ _ _)

lemma laurentPoint_eq (b : AlgebraicClosure k₀) :
    laurentPoint k₀ b = affineLine.geometricPoint k₀ _ (HahnSeries.single (-1) b) :=
  rfl

/-- The point `z = t` of the chart at infinity of the geometric projective line `ℙ¹_{k̄}` with
values in the power series ring `k̄⟦t⟧`; its closed point maps to `∞`. -/
noncomputable def powerSeriesInfinityPoint :
    Spec (.of (PowerSeries (AlgebraicClosure k₀))) ⟶
      (ProjectiveLine (Spec (.of k₀)) ↘ Spec (.of k₀)).geometricFiber :=
  pullback.lift
    (AffineSpace.homOfVector
      (Spec.map (CommRingCat.ofHom (algebraMap k₀ (PowerSeries (AlgebraicClosure k₀)))))
      (fun _ ↦ (Scheme.ΓSpecIso (.of (PowerSeries (AlgebraicClosure k₀)))).inv.hom
        PowerSeries.X) ≫ ProjectiveLine.infinityChart _)
    (Spec.map (CommRingCat.ofHom
      (algebraMap (AlgebraicClosure k₀) (PowerSeries (AlgebraicClosure k₀)))))
    (by
      rw [Category.assoc, ProjectiveLine.infinityChart_over]
      exact affineLine.homOfVector_comp_over_eq k₀ _ _)

@[reassoc (attr := simp)]
lemma powerSeriesInfinityPoint_geometricFiberProj :
    powerSeriesInfinityPoint k₀ ≫
        (ProjectiveLine (Spec (.of k₀)) ↘ Spec (.of k₀)).geometricFiberProj =
      AffineSpace.homOfVector
        (Spec.map (CommRingCat.ofHom (algebraMap k₀ (PowerSeries (AlgebraicClosure k₀)))))
        (fun _ ↦ (Scheme.ΓSpecIso (.of (PowerSeries (AlgebraicClosure k₀)))).inv.hom
          PowerSeries.X) ≫ ProjectiveLine.infinityChart _ :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma powerSeriesInfinityPoint_geometricFiberToAlgebraicClosure :
    powerSeriesInfinityPoint k₀ ≫
        (ProjectiveLine (Spec (.of k₀)) ↘ Spec (.of k₀)).geometricFiberToAlgebraicClosure =
      Spec.map (CommRingCat.ofHom
        (algebraMap (AlgebraicClosure k₀) (PowerSeries (AlgebraicClosure k₀)))) :=
  pullback.lift_snd _ _ _

/-- The transition map of the two charts of `ℙ¹`: the point `t = a` of the affine chart is the
point `z = b` of the chart at infinity when `a b = 1`. -/
lemma ProjectiveLine.homOfVector_comp_affineChart_eq_of_mul_eq_one {X S : Scheme.{u}}
    (g : X ⟶ S) {a b : Γ(X, ⊤)} (h : a * b = 1) :
    AffineSpace.homOfVector g (fun _ ↦ a) ≫ ProjectiveLine.affineChart S =
      AffineSpace.homOfVector g (fun _ ↦ b) ≫ ProjectiveLine.infinityChart S :=
  ProjectiveLine.homOfVector_comp_affineChart_eq g ⟨a, b, h, by rw [mul_comm, h]⟩

/-- On the punctured disc, the point `z = t` of the chart at infinity is the point `x = 1 / t` of
the affine chart. -/
theorem laurentPoint_one_comp_geometricFiberMap_affineChart :
    laurentPoint k₀ 1 ≫ Scheme.Hom.geometricFiberMap
        (ProjectiveLine.affineChart (Spec (.of k₀))) (comp_over _ _) =
      Spec.map (CommRingCat.ofHom
          (algebraMap (PowerSeries (AlgebraicClosure k₀)) (LaurentSeries (AlgebraicClosure k₀)))) ≫
        powerSeriesInfinityPoint k₀ := by
  refine Scheme.Hom.geometricFiber_hom_ext _ ?_ ?_
  · rw [Category.assoc, Scheme.Hom.geometricFiberMap_comp_geometricFiberProj, laurentPoint_eq,
      affineLine.geometricPoint_geometricFiberProj_assoc, Category.assoc,
      powerSeriesInfinityPoint_geometricFiberProj,
      ProjectiveLine.homOfVector_comp_affineChart_eq_of_mul_eq_one _
        (b := (Scheme.ΓSpecIso _).inv.hom (HahnSeries.single 1 1))
        (by rw [← map_mul, HahnSeries.single_mul_single, neg_add_cancel, mul_one,
          HahnSeries.single_zero_one, map_one]), ← Category.assoc]
    congr 1
    refine AffineSpace.hom_ext ?_ fun _ ↦ ?_
    · rw [AffineSpace.homOfVector_over, Category.assoc, AffineSpace.homOfVector_over,
        ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
    · rw [AffineSpace.homOfVector_appTop_coord, AffineSpace.comp_homOfVector_appTop_coord,
        Scheme.specMap_appTop_ΓSpecIso_inv]
      exact congrArg _ HahnSeries.ofPowerSeries_X.symm
  · rw [Category.assoc, Scheme.Hom.geometricFiberMap_comp_geometricFiberToAlgebraicClosure,
      laurentPoint_eq, affineLine.geometricPoint_geometricFiberToAlgebraicClosure, Category.assoc,
      powerSeriesInfinityPoint_geometricFiberToAlgebraicClosure, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp]
    congr 2

/-- The point `z = t` of `ℙ¹_{k̄}` factors through the geometric fiber of every open `W ⊆ ℙ¹`
containing `∞`, that is, with `𝔸¹ ∪ W = ℙ¹`: its closed point maps to `∞`, and every open of
the local scheme `Spec k̄⟦t⟧` containing the closed point is everything. -/
theorem exists_comp_geometricFiberMap_eq_powerSeriesInfinityPoint
    (W : (ProjectiveLine (Spec (.of k₀))).Opens)
    (hW : (ProjectiveLine.affineChart (Spec (.of k₀))).opensRange ⊔ W = ⊤) :
    ∃ z : Spec (.of (PowerSeries (AlgebraicClosure k₀))) ⟶
        (W.toScheme ↘ Spec (.of k₀)).geometricFiber,
      z ≫ Scheme.Hom.geometricFiberMap W.ι (comp_over _ _) = powerSeriesInfinityPoint k₀ := by
  set f := AffineSpace.homOfVector
      (Spec.map (CommRingCat.ofHom (algebraMap k₀ (PowerSeries (AlgebraicClosure k₀)))))
      (fun _ ↦ (Scheme.ΓSpecIso (.of (PowerSeries (AlgebraicClosure k₀)))).inv.hom
        PowerSeries.X) ≫ ProjectiveLine.infinityChart _ with hf
  have hclosed : IsLocalRing.closedPoint (PowerSeries (AlgebraicClosure k₀)) ∈ f ⁻¹ᵁ W := by
    have h : f (IsLocalRing.closedPoint _) ∈
        (ProjectiveLine.affineChart (Spec (.of k₀))).opensRange ⊔ W := by
      rw [hW]
      trivial
    refine h.resolve_left fun h' ↦ ?_
    have h'' : IsLocalRing.closedPoint (PowerSeries (AlgebraicClosure k₀)) ∈
        f ⁻¹ᵁ (ProjectiveLine.affineChart (Spec (.of k₀))).opensRange := h'
    rw [hf, Scheme.Hom.comp_preimage, ProjectiveLine.infinityChart_preimage_opensRange_affineChart,
      Scheme.preimage_basicOpen_top, AffineSpace.homOfVector_appTop_coord,
      basicOpen_eq_of_affine] at h''
    refine (PrimeSpectrum.mem_basicOpen _ _).1 h'' ?_
    rw [IsLocalRing.closedPoint, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      PowerSeries.isUnit_iff_constantCoeff]
    simp
  have hrange : Set.range f ⊆ Set.range W.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    have hx : x ∈ f ⁻¹ᵁ W := by
      rw [(IsLocalRing.closedPoint_mem_iff (f ⁻¹ᵁ W)).1 hclosed]
      trivial
    exact hx
  refine ⟨pullback.lift (IsOpenImmersion.lift W.ι f hrange)
    (Spec.map (CommRingCat.ofHom
      (algebraMap (AlgebraicClosure k₀) (PowerSeries (AlgebraicClosure k₀))))) ?_, ?_⟩
  · rw [← comp_over W.ι (Spec (.of k₀)), IsOpenImmersion.lift_fac_assoc, hf, Category.assoc,
      ProjectiveLine.infinityChart_over]
    exact affineLine.homOfVector_comp_over_eq k₀ _ _
  · apply pullback.hom_ext <;> simp [Scheme.Hom.geometricFiberMap, powerSeriesInfinityPoint, hf]

/-- The point `x = 1 / t` of `𝔸¹_{k₀}` with values in `k̄((t))` is `Spec` of the evaluation at
`1 / t`. -/
lemma affineLine.homOfVector_single_neg_one_eq :
    AffineSpace.homOfVector
        (Spec.map (CommRingCat.ofHom (algebraMap k₀ (LaurentSeries (AlgebraicClosure k₀)))))
        (fun _ ↦ (Scheme.ΓSpecIso (.of (LaurentSeries (AlgebraicClosure k₀)))).inv.hom
          (HahnSeries.single (-1) 1)) =
      Spec.map (CommRingCat.ofHom (MvPolynomial.eval₂Hom
          (algebraMap k₀ (LaurentSeries (AlgebraicClosure k₀)))
          fun _ : PUnit.{u + 1} ↦ HahnSeries.single (-1) 1)) ≫
        (AffineSpace.SpecIso PUnit.{u + 1} (.of k₀)).inv := by
  refine AffineSpace.hom_ext ?_ fun _ ↦ ?_
  · rw [AffineSpace.homOfVector_over, Category.assoc, AffineSpace.SpecIso_inv_over,
      ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact RingHom.ext fun x ↦ by simp
  · rw [AffineSpace.homOfVector_appTop_coord, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
      AffineSpace.SpecIso_inv_appTop_coord, Scheme.specMap_appTop_ΓSpecIso_inv]
    simp

/-- The point `x = 1 / t` is generic: it factors through the geometric fiber of every nonempty
open `j : U ↪ 𝔸¹`. -/
theorem exists_comp_geometricFiberMap_eq_laurentPoint {U : Scheme.{u}}
    [U.Over (Spec (CommRingCat.of k₀))] [Nonempty U] (j : U ⟶ affineLine k₀) [IsOpenImmersion j]
    [j.IsOver (Spec (CommRingCat.of k₀))] :
    ∃ z : Spec (.of (LaurentSeries (AlgebraicClosure k₀))) ⟶
        (U ↘ Spec (CommRingCat.of k₀)).geometricFiber,
      z ≫ Scheme.Hom.geometricFiberMap j (comp_over j _) = laurentPoint k₀ 1 := by
  set f := AffineSpace.homOfVector
      (Spec.map (CommRingCat.ofHom (algebraMap k₀ (LaurentSeries (AlgebraicClosure k₀)))))
      (fun _ ↦ (Scheme.ΓSpecIso (.of (LaurentSeries (AlgebraicClosure k₀)))).inv.hom
        (HahnSeries.single (-1) 1)) with hf
  set ψ := MvPolynomial.eval₂Hom (algebraMap k₀ (LaurentSeries (AlgebraicClosure k₀)))
    fun _ : PUnit.{u + 1} ↦ HahnSeries.single (-1 : ℤ) (1 : AlgebraicClosure k₀)
  have hψ : Function.Injective ψ :=
    algebraicIndependent_iff_injective_aeval.1 (algebraicIndependent_unique_type_iff.2
      (LaurentSeries.transcendental_single_neg_one.restrictScalars
        (algebraMap k₀ (AlgebraicClosure k₀)).injective))
  have hrange : Set.range f ⊆ Set.range j := by
    obtain ⟨y⟩ := ‹Nonempty U›
    rintro _ ⟨x, rfl⟩
    have hgen : Spec.map (CommRingCat.ofHom ψ) x ⤳
        (AffineSpace.SpecIso PUnit.{u + 1} (.of k₀)).hom (j y) := by
      rw [← PrimeSpectrum.le_iff_specializes, ← PrimeSpectrum.asIdeal_le_asIdeal]
      intro p hp
      have hp' : ψ p ∈ x.asIdeal := hp
      rw [Ideal.eq_bot_of_prime x.asIdeal, Ideal.mem_bot] at hp'
      rw [(injective_iff_map_eq_zero ψ).1 hψ p hp']
      exact zero_mem _
    have hmem := (hgen.map (AffineSpace.SpecIso PUnit.{u + 1} (.of k₀)).inv.continuous).mem_open
      j.opensRange.isOpen ⟨y, (Scheme.hom_inv_apply _ _).symm⟩
    rw [hf, affineLine.homOfVector_single_neg_one_eq]
    exact hmem
  refine ⟨pullback.lift (IsOpenImmersion.lift j f hrange)
    (Spec.map (CommRingCat.ofHom
      (algebraMap (AlgebraicClosure k₀) (LaurentSeries (AlgebraicClosure k₀))))) ?_, ?_⟩
  · rw [← comp_over j (Spec (CommRingCat.of k₀)), IsOpenImmersion.lift_fac_assoc, hf]
    exact affineLine.homOfVector_comp_over_eq k₀ _ _
  · apply pullback.hom_ext <;> simp [Scheme.Hom.geometricFiberMap, laurentPoint, hf]

/-- The geometric multiplication by `a` maps the point `x = v` to the point `x = a v`. -/
lemma affineLine.geometricPoint_comp_geometricSMul (A : Type u) [CommRing A] [Algebra k₀ A]
    [Algebra (AlgebraicClosure k₀) A] [IsScalarTower k₀ (AlgebraicClosure k₀) A]
    (a : AlgebraicClosure k₀) (v : A) :
    affineLine.geometricPoint k₀ A v ≫ affineLine.geometricSMul k₀ a =
      affineLine.geometricPoint k₀ A (algebraMap (AlgebraicClosure k₀) A a * v) := by
  refine Scheme.Hom.geometricFiber_hom_ext _ ?_ (by simp)
  rw [Category.assoc, affineLine.geometricSMul_comp_geometricFiberProj,
    affineLine.geometricPoint_geometricFiberProj, AffineSpace.comp_homOfVector]
  refine AffineSpace.hom_ext ?_ fun _ ↦ ?_
  · rw [AffineSpace.homOfVector_over, AffineSpace.homOfVector_over,
      affineLine.geometricPoint_geometricFiberToAlgebraicClosure_assoc,
      ← affineLine.homOfVector_comp_over_eq k₀ A (algebraMap (AlgebraicClosure k₀) A a * v),
      AffineSpace.homOfVector_over]
  · have h₁ : (affineLine.geometricPoint k₀ A v).appTop
        ((affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberToAlgebraicClosure.appTop
          ((Scheme.ΓSpecIso (.of (AlgebraicClosure k₀))).inv.hom a)) =
        (Scheme.ΓSpecIso (.of A)).inv.hom (algebraMap (AlgebraicClosure k₀) A a) := by
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
        affineLine.geometricPoint_geometricFiberToAlgebraicClosure,
        Scheme.specMap_appTop_ΓSpecIso_inv]
      rfl
    have h₂ : (affineLine.geometricPoint k₀ A v).appTop
        ((affineLine k₀ ↘ Spec (CommRingCat.of k₀)).geometricFiberProj.appTop
          (AffineSpace.coord _ PUnit.unit)) = (Scheme.ΓSpecIso (.of A)).inv.hom v := by
      rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
        affineLine.geometricPoint_geometricFiberProj, AffineSpace.homOfVector_appTop_coord]
    rw [AffineSpace.homOfVector_appTop_coord, AffineSpace.homOfVector_appTop_coord,
      Function.comp_apply, map_mul, h₁, h₂, map_mul]

/-- The geometric multiplication by `a` maps `x = b / t` to `x = a b / t`. -/
theorem laurentPoint_comp_geometricSMul (a b : AlgebraicClosure k₀) :
    laurentPoint k₀ b ≫ affineLine.geometricSMul k₀ a = laurentPoint k₀ (a * b) := by
  rw [laurentPoint_eq, laurentPoint_eq, affineLine.geometricPoint_comp_geometricSMul]
  congr 1
  rw [LaurentSeries.algebraMap_apply, HahnSeries.C_apply, HahnSeries.single_mul_single, zero_add]

/-- The base change of the multiplication by `a ∈ k₀` maps `x = b / t` to `x = a b / t`. -/
theorem laurentPoint_comp_geometricFiberMap_smul (a : k₀) (b : AlgebraicClosure k₀) :
    laurentPoint k₀ b ≫ Scheme.Hom.geometricFiberMap (affineLine.smul k₀ a) (comp_over _ _) =
      laurentPoint k₀ (algebraMap k₀ (AlgebraicClosure k₀) a * b) := by
  rw [laurentPoint_eq, laurentPoint_eq]
  refine affineLine.geometricPoint_comp_geometricFiberMap k₀ _ _ _ _ _ ?_
  rw [affineLine.smul, AffineSpace.smul_appTop_coord, map_mul,
    affineLine.homOfVector_appTop_appTop, AffineSpace.homOfVector_appTop_coord, ← map_mul,
    HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply, HahnSeries.ofPowerSeries_C,
    HahnSeries.C_apply, HahnSeries.single_mul_single, zero_add]

variable [Finite k₀]

/-- A root `u` of the Artin–Schreier equation `u^q - u = w`, `q = #k₀`, in an algebraically
closed field. -/
lemma exists_pow_card_sub_eq (L : Type*) [Field L] [IsAlgClosed L] (w : L) :
    ∃ u : L, u ^ Nat.card k₀ - u = w := by
  have hq : 2 ≤ Nat.card k₀ := Finite.one_lt_card
  have hdeg : (Polynomial.X ^ Nat.card k₀ - (Polynomial.X + Polynomial.C w) : Polynomial L).degree =
      Nat.card k₀ := by
    rw [Polynomial.degree_sub_eq_left_of_degree_lt] <;> rw [Polynomial.degree_X_pow]
    rw [Polynomial.degree_X_add_C]
    exact_mod_cast (by omega : 1 < Nat.card k₀)
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_root _ (by rw [hdeg]; exact_mod_cast (by omega))
  refine ⟨u, ?_⟩
  rw [Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_C] at hu
  linear_combination hu

/-- **The Artin–Schreier cover over the punctured disc at infinity.** For `b ≠ 0`, a root `u` of
`u^q - u = b / t` in an algebraic closure `L` of `K = k̄((t))` gives a point `x = u` of `𝔸¹_{k̄}`
over `Spec L ⟶ Spec K` lifting `x = b / t` along `ĀS`, and for every `c ∈ k₀` some
`K`-automorphism of `L`, acting on `Spec L` over `Spec K`, moves it by the translation `σ̄_c`. -/
theorem exists_comp_geometricArtinSchreierMap_eq_laurentPoint {b : AlgebraicClosure k₀}
    (hb : b ≠ 0) :
    ∃ z' : Spec (.of (AlgebraicClosure (LaurentSeries (AlgebraicClosure k₀)))) ⟶ Ā,
      z' ≫ affineLine.geometricArtinSchreierMap k₀ =
          Spec.map (CommRingCat.ofHom (algebraMap (LaurentSeries (AlgebraicClosure k₀))
            (AlgebraicClosure (LaurentSeries (AlgebraicClosure k₀))))) ≫ laurentPoint k₀ b ∧
        ∀ c : k₀, ∃ σ : Spec (.of (AlgebraicClosure (LaurentSeries (AlgebraicClosure k₀)))) ⟶
            Spec (.of (AlgebraicClosure (LaurentSeries (AlgebraicClosure k₀)))),
          σ ≫ Spec.map (CommRingCat.ofHom (algebraMap (LaurentSeries (AlgebraicClosure k₀))
              (AlgebraicClosure (LaurentSeries (AlgebraicClosure k₀))))) =
            Spec.map (CommRingCat.ofHom (algebraMap (LaurentSeries (AlgebraicClosure k₀))
              (AlgebraicClosure (LaurentSeries (AlgebraicClosure k₀))))) ∧
          σ ≫ z' = z' ≫ (affineLine.geometricTranslationIso k₀ c).hom := by
  set K := LaurentSeries (AlgebraicClosure k₀)
  set L := AlgebraicClosure K
  obtain ⟨u, hu⟩ := exists_pow_card_sub_eq k₀ L (algebraMap K L (HahnSeries.single (-1) b))
  refine ⟨affineLine.geometricPoint k₀ L u, ?_, fun c ↦ ?_⟩
  · rw [laurentPoint_eq, affineLine.specMap_comp_geometricPoint k₀ K (algebraMap K L)
      (fun x ↦ (IsScalarTower.algebraMap_apply (AlgebraicClosure k₀) K L x).symm)]
    refine affineLine.geometricPoint_comp_geometricFiberMap k₀ _ _ _ _ _ ?_
    let := Fintype.ofFinite k₀
    rw [affineLine.artinSchreierMap, AffineSpace.artinSchreierMap_appTop_coord, map_sub, map_pow,
      AffineSpace.homOfVector_appTop_coord, ← map_pow, ← map_sub, Fintype.card_eq_nat_card, hu]
  · obtain ⟨σ, hσ⟩ := LaurentSeries.exists_algEquiv_apply_eq_add_C_of_pow_sub_eq_single_of_ne_zero
      hb L hu c
    refine ⟨Spec.map (CommRingCat.ofHom (σ : L →+* L)), ?_, ?_⟩
    · rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      exact RingHom.ext fun x ↦ σ.commutes x
    · rw [affineLine.specMap_comp_geometricPoint k₀ L (σ : L →+* L) fun x ↦ by
          rw [IsScalarTower.algebraMap_apply (AlgebraicClosure k₀) K L x]
          exact σ.commutes _]
      refine (affineLine.geometricPoint_comp_geometricFiberMap k₀ L (affineLine.translation k₀ c)
        (comp_over _ _) u _ ?_).symm
      rw [affineLine.translation, AffineSpace.translation_appTop_coord, map_add,
        affineLine.homOfVector_appTop_appTop, AffineSpace.homOfVector_appTop_coord, ← map_add]
      congr 1
      rw [IsScalarTower.algebraMap_apply k₀ K L c, HahnSeries.algebraMap_apply',
        PowerSeries.algebraMap_apply, HahnSeries.ofPowerSeries_C]
      exact hσ.symm

end AlgebraicGeometry
