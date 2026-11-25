/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius.FiniteModel
public import WeilConjectures.DeligneLaumon.Reduction.CurveTesting
public import WeilConjectures.DeligneLaumon.Reduction.RealCurveConstituent
public import WeilConjectures.WeilSheaf.EquivariantPullback
public import WeilConjectures.WeilSheaf.FrobeniusTwistStalk

/-!
# Purity of the irreducible constituents of real lisse sheaves on smooth affine schemes

Let `X₀` be a smooth geometrically connected affine scheme of dimension `d ≥ 2` over a finite
field `k₀` and `𝒢` an `ι`-real lisse Weil sheaf on `X₀`. Every irreducible lisse subquotient `V`
of `𝒢` is punctually `ι`-pure (blueprint `theorem-real-constructible-sheaves-are-mixed--1`, the
lisse stratum).

The proof follows the blueprint, with the finite constant extension replaced by the Frobenius
twist of subsheaves (`AlgebraicGeometry.WeilSheaf.frobeniusTwist`): `V̄` has a geometrically
irreducible subsheaf `P`, defined over the extension of degree `M`, whose twists
`P, T P, …, T^{M-1} P` span `V̄`. A curve `Y` through a geometric point `t₀` over a closed point
`x₀`, its Frobenius translates and a geometric point over a closed point `x`, defined over a finite
field `L` and on which every `Tⁿ P` stays irreducible, carries the real lisse sheaf `𝒢|_Y`, of
which the restrictions of the `Tⁿ P` are irreducible constituents. By purity on curves they are
pure, all of the same weight `w`: the weight of `Tᵃ P` at `t₀` is that of `P` at `t₀ ≫ Frᵃ`.
So `V|_Y` is pure of weight `w`, which is read off at `x₀` and holds at `x`.

## Main statements

- `AlgebraicGeometry.WeilSheaf.exists_isPunctuallyPureOfWeight_curvePullback`: the curve step.
-/

@[expose] public section

universe u

open CategoryTheory Limits

-- As in `WeilConjectures.WeilSheaf.CurvePullback`: elaborating through these instances produces
-- terms which the kernel compares slowly with the imported ones.
attribute [-instance] ModuleCat.instIsRightAdjointForgetLinearMapIdCarrier
  ModuleCat.isGrothendieckAbelian_of_commRing
  CategoryTheory.hasGlobalSectionsFunctor_of_hasLimitsOfShape

namespace AlgebraicGeometry.WeilSheaf

open ProEtale

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {ι : PadicAlgCl l →+* ℂ}

/-- Powers of an automorphism commute, in the form `g⁻ᵃ ≫ gᵇ = gᵇ ≫ g⁻ᵃ`. -/
lemma _root_.CategoryTheory.Aut.pow_inv_comp_pow_hom {C : Type*} [Category C] {Z : C}
    (g : Aut Z) (a b : ℕ) :
    (g ^ a).asIso.inv ≫ (g ^ b).asIso.hom = (g ^ b).asIso.hom ≫ (g ^ a).asIso.inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, Aut.pow_hom_comp_pow_hom,
    Aut.pow_hom_comp_pow_hom, add_comm]

section CurveStep

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  {L : Type u} [Field L] [Finite L] [Algebra k₀ L] [Fact (ringChar L ≠ l)]
  {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of L))]
  (j : (Y ↘ Spec (CommRingCat.of L)).geometricFiber ⟶ (X ↘ Spec (CommRingCat.of k₀)).geometricFiber)
  (hj : j ≫ ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^
      Module.finrank k₀ L).asIso.hom =
    (Y ↘ Spec (CommRingCat.of L)).geometricGaloisFrobenius.asIso.hom ≫ j)
  (θ : AlgebraicClosure k₀ →ₐ[k₀] AlgebraicClosure L)

/-- **Purity at a closed point read off on a curve** (blueprint:
`theorem-real-constructible-sheaves-are-mixed--1`, "the same power calculation at `x`"). If the
pullback of `F` to a curve `Y` over `L` through a geometric point over the closed point `x` is
punctually pure of weight `w`, then so is the stalk of `F` at `x`: the stalk of the pullback at a
point of `Y` over `x` is the stalk of `F` with a power of its Frobenius. -/
theorem isPureOfWeight_stalk_of_curvePullback [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of L))]
    [Mono j] {F : WeilSheaf k₀ l X} {w : ℝ}
    (hF : ((curvePullback j hj).obj F).IsPunctuallyPureOfWeight ι w) (x : X.finitePoints)
    {s' : Spec (.of (AlgebraicClosure L)) ⟶ (Y ↘ Spec (CommRingCat.of L)).geometricFiber}
    (hs' : s' ≫ j = (specAlgHomAlgebraicClosureIso θ).hom ≫
      (X ↘ Spec (CommRingCat.of k₀)).geometricFiberPointOfFinitePoint x) :
    (F.stalk x).IsPureOfWeight ι ((X ↘ Spec (CommRingCat.of k₀)).residueCard x.1) w := by
  have : Module.Finite k₀ L := Module.Finite.of_finite
  have he : 0 < (X ↘ Spec (CommRingCat.of k₀)).degreeOver x.1 :=
    Nat.pos_of_ne_zero (Scheme.Hom.degreeOver_ne_zero _ x.2)
  have ht := comp_geometricGaloisFrobenius_pow_mul _
    (Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow (k := k₀) _ x)
    (Module.finrank k₀ L)
  have hs'Y := comp_geometricGaloisFrobenius_pow_of_comp_eq j hj θ hs' ht
  obtain ⟨hs, E, -⟩ := exists_equiv_stalkAt_curvePullback j hj rfl θ F hs' hs'Y
  have h1 := hF.stalkAt s' he hs'Y
  rw [natCard_eq_natCard_pow_finrank (k₀ := k₀) (k₁ := L), ← pow_mul] at h1
  exact (isPureOfWeight_stalk_iff_stalkAt F ι w _ (Nat.mul_pos Module.finrank_pos he) hs x
    ((X ↘ Spec (CommRingCat.of k₀)).geometricFiberPointOfFinitePoint_comp_geometricFiberProj_base
      x)).2 (h1.of_equiv E.symm)


/-- **The curve step** (blueprint: `theorem-real-constructible-sheaves-are-mixed--1`). Let `𝒢` be an
`ι`-real lisse Weil sheaf on `X` with an irreducible lisse subquotient `V = 𝒢₂ / 𝒢₁`, let `P ⊆ V̄`
be an irreducible local system fixed by the `M`-th power of the Frobenius twist `T`, whose twists
`P, …, T^{M-1} P` span `V̄`. Let `j : Ȳ ⟶ X̄` be a curve over a finite field `L` with
`M ∣ [L : k₀]`, on which every `Tⁿ P` stays irreducible, passing through the translates
`σ⁻ᵃ ≫ t₀ ≫ Frᵃ` of the geometric point `t₀` over a closed point `x₀`. Then the restriction of
`V` to the curve is punctually pure: its constituents `Tⁿ P|_Y` are pure by purity on curves, of
a common weight since the weight of `Tᵃ P` at `t₀` is that of `P` at `σ⁻ᵃ ≫ t₀ ≫ Frᵃ`. -/
theorem exists_isPunctuallyPureOfWeight_curvePullback
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [ConnectedSpace (X ↘ Spec (CommRingCat.of k₀)).geometricFiber]
    [IsRegular (X ↘ Spec (CommRingCat.of k₀)).geometricFiber]
    [IsLocallyNoetherian (X ↘ Spec (CommRingCat.of k₀)).geometricFiber]
    [CompactSpace (X ↘ Spec (CommRingCat.of k₀)).geometricFiber]
    [SmoothOfRelativeDimension 1 (Y ↘ Spec (CommRingCat.of L))]
    [GeometricallyConnected (Y ↘ Spec (CommRingCat.of L))]
    [IsSeparated (Y ↘ Spec (CommRingCat.of L))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of L))]
    [QuasiCompact (Y ↘ Spec (CommRingCat.of L))] [Mono j]
    {𝒢 : WeilSheaf k₀ l X} (h𝒢 : 𝒢.IsLisse) (hreal : 𝒢.IsReal ι) {𝒢₁ 𝒢₂ : WeilSheaf k₀ l X}
    (i : 𝒢₁ ⟶ 𝒢₂) (j₂ : 𝒢₂ ⟶ 𝒢) [Mono i] [Mono j₂] (h₁ : 𝒢₁.IsLisse) (h₂ : 𝒢₂.IsLisse)
    {V : WeilSheaf k₀ l X} (π : 𝒢₂ ⟶ V) (hπ : i ≫ π = 0)
    (hV : IsColimit (CokernelCofork.ofπ π hπ)) {P : Subobject V.obj.carrier}
    (hP : IsIrreducibleAdicLocalSystem (Subobject.underlying.obj P)) {M : ℕ} (hM : 0 < M)
    (hPM : (⇑V.frobeniusTwist)^[M] P = P)
    (hspan : (Finset.univ : Finset (Fin M)).sup (fun n ↦ (⇑V.frobeniusTwist)^[n] P) = ⊤)
    (hMN : M ∣ Module.finrank k₀ L)
    (hjirr : ∀ n : Fin M, IsIrreducibleAdicLocalSystem
      ((j)^*ᵃ[l].obj (Subobject.underlying.obj ((⇑V.frobeniusTwist)^[n] P))))
    (x₀ : X.finitePoints)
    (hpts : ∀ a : Fin M, ∃ s' : Spec (.of (AlgebraicClosure L)) ⟶
        (Y ↘ Spec (CommRingCat.of L)).geometricFiber,
      s' ≫ j = (specAlgHomAlgebraicClosureIso θ).hom ≫
        ((specGeometricFrobenius k₀ ^ (a : ℕ)).asIso.inv ≫
          (X ↘ Spec (CommRingCat.of k₀)).geometricFiberPointOfFinitePoint x₀ ≫
            ((X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius ^ (a : ℕ)).asIso.hom)) :
    ∃ w : ℝ, ((curvePullback j hj).obj V).IsPunctuallyPureOfWeight ι w := by
  have : Module.Finite k₀ L := Module.Finite.of_finite
  let Fr := (X ↘ Spec (CommRingCat.of k₀)).geometricGaloisFrobenius
  let σ := specGeometricFrobenius k₀
  -- the twists `Q n = Tⁿ P` are irreducible local systems defined over `L`
  have hTM (c n : ℕ) : (⇑V.frobeniusTwist)^[M * c] ((⇑V.frobeniusTwist)^[n] P) =
      (⇑V.frobeniusTwist)^[n] P := by
    rw [← Function.iterate_add_apply, add_comm, Function.iterate_add_apply,
      Function.iterate_mul, Function.iterate_fixed hPM]
  have hQN (n : ℕ) : (⇑V.frobeniusTwist)^[Module.finrank k₀ L] ((⇑V.frobeniusTwist)^[n] P) =
      (⇑V.frobeniusTwist)^[n] P := by
    obtain ⟨c, hc⟩ := hMN
    rw [hc]
    exact hTM c n
  have hQirr (n : ℕ) := V.isIrreducibleAdicLocalSystem_frobeniusTwist_iterate hP n
  have hQl (n : ℕ) : IsAdicLisseSheaf (Subobject.underlying.obj ((⇑V.frobeniusTwist)^[n] P)) :=
    (hQirr n).1
  -- the restriction of the chain `𝒢₁ ⊆ 𝒢₂ ⊆ 𝒢` to the curve
  have hreal' : ((curvePullback j hj).obj 𝒢).IsReal ι := hreal.curvePullback j hj rfl
  have : Mono ((curvePullback j hj).map i) := inferInstance
  have : Mono ((curvePullback j hj).map j₂) := inferInstance
  -- each `Tⁿ P|_Y` is an irreducible constituent, hence pure
  have hpure (n : Fin M) : ∃ w : ℝ, (curvePullbackSub j hj V ((⇑V.frobeniusTwist)^[n] P)
      (hQN n) (hQl n)).IsPunctuallyPureOfWeight ι w :=
    hreal'.exists_isPunctuallyPureOfWeight_of_mono_obj (curvePullback j hj) i j₂ π hπ hV
      (h𝒢.curvePullback j hj) (h₁.curvePullback j hj) (h₂.curvePullback j hj)
      (curvePullbackSubι j hj V _ (hQN n) (hQl n))
      (isIrreducibleLisse_curvePullbackSub j hj V _ (hQN n) (hQl n) (hjirr n))
  choose w hw using hpure
  -- the weights at the geometric point `t₀` over `x₀`
  let t₀ := (X ↘ Spec (CommRingCat.of k₀)).geometricFiberPointOfFinitePoint x₀
  let e₀ := (X ↘ Spec (CommRingCat.of k₀)).degreeOver x₀.1
  have he₀ : 0 < e₀ := Nat.pos_of_ne_zero (Scheme.Hom.degreeOver_ne_zero _ x₀.2)
  have ht₀ : t₀ ≫ (Fr ^ e₀).asIso.hom = (σ ^ e₀).asIso.hom ≫ t₀ :=
    Scheme.Hom.geometricFiberPointOfFinitePoint_comp_geometricGaloisFrobenius_pow (k := k₀) _ x₀
  have hsa (a : ℕ) : ((σ ^ a).asIso.inv ≫ t₀ ≫ (Fr ^ a).asIso.hom) ≫ (Fr ^ e₀).asIso.hom =
      (σ ^ e₀).asIso.hom ≫ (σ ^ a).asIso.inv ≫ t₀ ≫ (Fr ^ a).asIso.hom := by
    rw [Category.assoc, Category.assoc, Aut.pow_hom_comp_pow_hom, add_comm,
      ← Aut.pow_hom_comp_pow_hom, reassoc_of% ht₀, ← Category.assoc, ← Category.assoc,
      Aut.pow_inv_comp_pow_hom]
    simp only [Category.assoc]
  have hq : 1 < Nat.card k₀ ^ (Module.finrank k₀ L * e₀) :=
    Nat.one_lt_pow (Nat.mul_pos Module.finrank_pos he₀).ne' Finite.one_lt_card
  -- purity of `Tⁿ P` on the stalk at the translate `σ⁻ᵃ ≫ t₀ ≫ Frᵃ`, with its Frobenius
  -- relative to `𝔽_{q^{N e₀}}`, `N = [L : k₀]`
  have hstalk (n : Fin M) (a : Fin M) :
      (V.stalkAt _ (Module.finrank k₀ L * e₀)
        (comp_geometricGaloisFrobenius_pow_mul _ (hsa a) (Module.finrank k₀ L))).IsPureOfWeightOn
        ι (Nat.card k₀ ^ (Module.finrank k₀ L * e₀))
          (V.stalkSubspace _ ((⇑V.frobeniusTwist)^[n] P)) (w n) := by
    obtain ⟨s', hs'⟩ := hpts a
    have hs'Y := comp_geometricGaloisFrobenius_pow_of_comp_eq j hj θ hs'
      (comp_geometricGaloisFrobenius_pow_mul _ (hsa a) (Module.finrank k₀ L))
    obtain ⟨hs, E, hE⟩ := exists_equiv_stalkAt_curvePullback j hj rfl θ V hs' hs'Y
    have h1 := ((hw n).stalkAt s' he₀ hs'Y).isPureOfWeightOn_range _
      (stalkAtMap_frobenius s' e₀ hs'Y (curvePullbackSubι j hj V _ (hQN n) (hQl n)))
      (injective_stalkAtMap s' e₀ hs'Y (curvePullbackSubι j hj V _ (hQN n) (hQl n)))
    have h2 := h1.map E.toLinearEquiv E.map_frobenius
    rw [hE _ (hQN n) (hQl n), natCard_eq_natCard_pow_finrank (k₀ := k₀) (k₁ := L),
      ← pow_mul] at h2
    exact h2
  -- all the weights are equal
  have hP0 (a : Fin M) : (V.stalkAt t₀ (Module.finrank k₀ L * e₀)
      (comp_geometricGaloisFrobenius_pow_mul _ ht₀ (Module.finrank k₀ L))).IsPureOfWeightOn ι
        (Nat.card k₀ ^ (Module.finrank k₀ L * e₀))
          (V.stalkSubspace t₀ ((⇑V.frobeniusTwist)^[a] P)) (w ⟨0, hM⟩) :=
    isPureOfWeightOn_stalkSubspace_frobeniusTwist_iterate V _ a (Iso.hom_inv_id_assoc _ _) _ P _ _
      (hstalk ⟨0, hM⟩ a)
  have hPa (a : Fin M) : (V.stalkAt t₀ (Module.finrank k₀ L * e₀)
      (comp_geometricGaloisFrobenius_pow_mul _ ht₀ (Module.finrank k₀ L))).IsPureOfWeightOn ι
        (Nat.card k₀ ^ (Module.finrank k₀ L * e₀))
          (V.stalkSubspace t₀ ((⇑V.frobeniusTwist)^[a] P)) (w a) := by
    have h := hstalk a ⟨0, hM⟩
    have h0 : (σ ^ ((⟨0, hM⟩ : Fin M) : ℕ)).asIso.inv ≫ t₀ ≫
        (Fr ^ ((⟨0, hM⟩ : Fin M) : ℕ)).asIso.hom = t₀ := by
      change (σ ^ 0).asIso.inv ≫ t₀ ≫ (Fr ^ 0).asIso.hom = t₀
      rw [pow_zero, pow_zero]
      exact (Category.id_comp _).trans (Category.comp_id _)
    exact (isPureOfWeightOn_stalkSubspace_congr V h0 _ _ _ _ _).1 h
  have hweq (a : Fin M) : w a = w ⟨0, hM⟩ := by
    obtain ⟨c, hc⟩ := hMN
    have hfix : (⇑V.frobeniusTwist)^[Module.finrank k₀ L * e₀] ((⇑V.frobeniusTwist)^[a] P) =
        (⇑V.frobeniusTwist)^[a] P := by
      rw [hc, Nat.mul_assoc]
      exact hTM _ a
    exact (hPa a).weight_eq (hP0 a) (V.stalkSubspace_ne_bot t₀ (hQirr a))
      (fun _ hv ↦ V.frobenius_mem_stalkSubspace _ hfix hv) hq
  -- so the restriction of `V`, spanned by the `Tⁿ P|_Y`, is pure
  refine ⟨w ⟨0, hM⟩, isPunctuallyPureOfWeight_curvePullback_of_iSup_eq_top j hj V
    (fun n : Fin M ↦ (⇑V.frobeniusTwist)^[n] P) hspan (fun n ↦ hQN n) (fun n ↦ hQl n)
      fun n ↦ ?_⟩
  rw [← hweq n]
  exact hw n

end CurveStep

/-- The pullback of an irreducible local system along `e ≫ i`, for an isomorphism `e`, is an
irreducible local system if its pullback along `i` is. -/
theorem _root_.AlgebraicGeometry.ProEtale.IsIrreducibleAdicLocalSystem.upperStar_iso_comp
    {Z C W : Scheme.{u}} (e : Z ≅ C) (i : C ⟶ W) {F : AdicSheaf l W}
    (hF : IsIrreducibleAdicLocalSystem ((i)^*ᵃ[l].obj F)) :
    IsIrreducibleAdicLocalSystem ((e.hom ≫ i)^*ᵃ[l].obj F) :=
  (hF.adicLowerStar_of_iso e.symm).of_iso
    (((adicUpperStarIsoLowerStarInv l e).app _).symm ≪≫ ((adicUpperStarComp l e.hom i).app F).symm)

/-- **Purity of the irreducible constituents of a real lisse sheaf on a smooth affine scheme**
(blueprint: `theorem-real-constructible-sheaves-are-mixed--1`, the lisse stratum). Let `X₀` be a
smooth geometrically connected affine scheme of dimension `d ≥ 2` over `k₀` and `𝒢` an `ι`-real
lisse Weil sheaf on `X₀`. Every irreducible lisse subquotient `𝒢₂ / 𝒢₁` of lisse Weil subsheaves
`𝒢₁ ⊆ 𝒢₂ ⊆ 𝒢` is punctually `ι`-pure.

Its underlying sheaf contains an irreducible local system `P` defined over a finite extension
(`AlgebraicGeometry.WeilSheaf.exists_isIrreducibleAdicLocalSystem_frobeniusTwist_iterate_eq`)
whose Frobenius twists span it (`AlgebraicGeometry.WeilSheaf.iSup_frobeniusTwist_iterate_eq_top`).
Curve testing (`AlgebraicGeometry.Scheme.Hom.exists_isClosedImmersion_isIrreducibleAdicLocalSystem_
upperStar`) through a geometric point over a fixed closed point `x₀`, its Frobenius translates and
a geometric point over an arbitrary closed point `x` gives a curve, which has a model over a finite
field (`AlgebraicGeometry.Scheme.Hom.exists_finiteModel_of_isClosedImmersion`). On it the
subquotient is pure (`AlgebraicGeometry.WeilSheaf.exists_isPunctuallyPureOfWeight_curvePullback`),
of a weight read off at `x₀`, and this weight is the weight at `x`. -/
theorem IsReal.exists_isPunctuallyPureOfWeight_cokernel_of_smooth {X₀ : Scheme.{u}}
    [X₀.Over (Spec (CommRingCat.of k₀))] [IsAffine X₀] {d : ℕ} (hd : 2 ≤ d)
    [SmoothOfRelativeDimension d (X₀ ↘ Spec (CommRingCat.of k₀))]
    [GeometricallyConnected (X₀ ↘ Spec (CommRingCat.of k₀))]
    [IsSeparated (X₀ ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X₀ ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X₀ ↘ Spec (CommRingCat.of k₀))]
    {𝒢 : WeilSheaf k₀ l X₀} (h𝒢 : 𝒢.IsLisse) (hreal : 𝒢.IsReal ι) {𝒢₁ 𝒢₂ : WeilSheaf k₀ l X₀}
    (i : 𝒢₁ ⟶ 𝒢₂) (j : 𝒢₂ ⟶ 𝒢) [Mono i] [Mono j] (h₁ : 𝒢₁.IsLisse) (h₂ : 𝒢₂.IsLisse)
    (hirr : (cokernel i).IsIrreducibleLisse) :
    ∃ w : ℝ, (cokernel i).IsPunctuallyPureOfWeight ι w := by
  classical
  let f := X₀ ↘ Spec (CommRingCat.of k₀)
  -- the geometric fiber is connected, regular and Noetherian
  have : ConnectedSpace f.geometricFiber :=
    GeometricallyConnected.geometrically_connectedSpace (f := f)
      (Scheme.specAlgebraicClosure k₀).hom f.geometricFiberProj
      f.geometricFiberToAlgebraicClosure (IsPullback.of_hasPullback _ _)
  have : SmoothOfRelativeDimension d f.geometricFiberToAlgebraicClosure :=
    inferInstanceAs (SmoothOfRelativeDimension d (Limits.pullback.snd _ _))
  have : Smooth f.geometricFiberToAlgebraicClosure := SmoothOfRelativeDimension.smooth d _
  have := IsRegular.of_smooth f.geometricFiberToAlgebraicClosure
  have := LocallyOfFiniteType.isLocallyNoetherian f.geometricFiberToAlgebraicClosure
  have : IsAffineHom f.geometricFiberToAlgebraicClosure :=
    inferInstanceAs (IsAffineHom (Limits.pullback.snd _ _))
  have : IsAffine f.geometricFiber := isAffine_of_isAffineHom f.geometricFiberToAlgebraicClosure
  let V := cokernel i
  let T := V.frobeniusTwist
  let Fr := f.geometricGaloisFrobenius
  let σ := specGeometricFrobenius k₀
  -- a geometric constituent `P`, defined over the extension of degree `M`
  obtain ⟨P, hP, M, hM, hPM⟩ :=
    V.exists_isIrreducibleAdicLocalSystem_frobeniusTwist_iterate_eq hirr.1 hirr.2.1
  have hP0 : P ≠ ⊥ := by
    rintro rfl
    exact hP.2.1 ((isZero_zero _).of_iso Subobject.botCoeIsoZero)
  have hspan := V.iSup_frobeniusTwist_iterate_eq_top hirr hP.1 hP0 hM hPM
  -- a closed point `x₀` with nonzero stalk
  obtain ⟨x₀, hx₀⟩ := V.exists_nontrivial_stalk_of_not_isZero hirr.2.1
  let t₀ := f.geometricFiberPointOfFinitePoint x₀
  have ht₀ : t₀ ≫ f.geometricFiberToAlgebraicClosure = 𝟙 _ := by
    simp [t₀, Scheme.Hom.geometricFiberPointOfFinitePoint]
  -- for every closed point `x`, a curve through `x₀` and `x`
  have key (x : X₀.finitePoints) : ∃ w : ℝ,
      (V.stalk x₀).IsPureOfWeight ι (f.residueCard x₀.1) w ∧
        (V.stalk x).IsPureOfWeight ι (f.residueCard x.1) w := by
    let sa (a : Fin M) := (σ ^ (a : ℕ)).asIso.inv ≫ t₀ ≫ (Fr ^ (a : ℕ)).asIso.hom
    let S := insert (f.geometricFiberPointOfFinitePoint x) (Finset.univ.image sa)
    have hS' : ∀ s ∈ S, s ≫ f.geometricFiberToAlgebraicClosure = 𝟙 _ := by
      intro s hs
      rcases Finset.mem_insert.1 hs with rfl | hs
      · simp [Scheme.Hom.geometricFiberPointOfFinitePoint]
      · obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hs
        simp only [sa, Category.assoc, Fr,
          Scheme.Hom.geometricGaloisFrobenius_pow_hom_comp_geometricFiberToAlgebraicClosure]
        rw [reassoc_of% ht₀, Iso.inv_hom_id]
    obtain ⟨C, iC, hiC, -, hCsm, hCconn, hSC, hCirr, -⟩ :=
      Scheme.Hom.exists_isClosedImmersion_isIrreducibleAdicLocalSystem_upperStar f (d := d)
        (by omega) (fun n : Fin M ↦ Subobject.underlying.obj ((⇑T)^[n] P))
        (fun n ↦ V.isIrreducibleAdicLocalSystem_frobeniusTwist_iterate hP n) S
        (Finset.insert_nonempty _ _) hS'
    obtain ⟨cx, hcx⟩ := hSC _ (Finset.mem_insert_self _ _)
    obtain ⟨L, _, _, _, Y, g, hMN, -, hYsm, hYgc, hYsep, hYlft, hYqc, θ, e, -, he⟩ :=
      f.exists_finiteModel_of_isClosedImmersion iC hCsm cx
        (by rw [reassoc_of% hcx]; exact hS' _ (Finset.mem_insert_self _ _)) hM
    let : Y.Over (Spec (CommRingCat.of L)) := ⟨g⟩
    have : Fact (ringChar L ≠ l) := ⟨(Algebra.ringChar_eq k₀ L) ▸ Fact.out⟩
    have : SmoothOfRelativeDimension 1 (Y ↘ Spec (CommRingCat.of L)) := hYsm
    have : GeometricallyConnected (Y ↘ Spec (CommRingCat.of L)) := hYgc
    have : IsSeparated (Y ↘ Spec (CommRingCat.of L)) := hYsep
    have : LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of L)) := hYlft
    have : QuasiCompact (Y ↘ Spec (CommRingCat.of L)) := hYqc
    let jY : (Y ↘ Spec (CommRingCat.of L)).geometricFiber ⟶ f.geometricFiber := e.hom ≫ iC
    have hjY : jY ≫ (Fr ^ Module.finrank k₀ L).asIso.hom =
        (Y ↘ Spec (CommRingCat.of L)).geometricGaloisFrobenius.asIso.hom ≫ jY := he
    have : Mono jY := mono_comp _ _
    have hpt {s} (hs : s ∈ S) : ∃ s' : Spec (.of (AlgebraicClosure L)) ⟶
        (Y ↘ Spec (CommRingCat.of L)).geometricFiber,
          s' ≫ jY = (specAlgHomAlgebraicClosureIso θ).hom ≫ s := by
      obtain ⟨c, hc⟩ := hSC s hs
      exact ⟨(specAlgHomAlgebraicClosureIso θ).hom ≫ c ≫ e.inv, by
        simp only [jY, Category.assoc, Iso.inv_hom_id_assoc, hc]⟩
    obtain ⟨w, hw⟩ := exists_isPunctuallyPureOfWeight_curvePullback jY hjY θ h𝒢 hreal i j h₁ h₂
      (cokernel.π i) (cokernel.condition i) (cokernelIsCokernel i) hP hM hPM hspan hMN
      (fun n ↦ (hCirr n).upperStar_iso_comp e iC) x₀
      (fun a ↦ hpt (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ a))))
    obtain ⟨s₀, hs₀⟩ :=
      hpt (Finset.mem_insert_of_mem (Finset.mem_image_of_mem sa (Finset.mem_univ ⟨0, hM⟩)))
    have hsa0 : sa ⟨0, hM⟩ = t₀ := by
      change (σ ^ 0).asIso.inv ≫ t₀ ≫ (Fr ^ 0).asIso.hom = t₀
      rw [pow_zero, pow_zero]
      exact (Category.id_comp _).trans (Category.comp_id _)
    rw [hsa0] at hs₀
    obtain ⟨sx, hsx⟩ := hpt (Finset.mem_insert_self _ _)
    exact ⟨w, isPureOfWeight_stalk_of_curvePullback jY hjY θ hw x₀ hs₀,
      isPureOfWeight_stalk_of_curvePullback jY hjY θ hw x hsx⟩
  choose w hw using key
  refine ⟨w x₀, fun x ↦ ?_⟩
  have hq : 1 < f.residueCard x₀.1 :=
    Nat.one_lt_pow (Scheme.Hom.degreeOver_ne_zero _ x₀.2) Finite.one_lt_card
  have := hx₀
  rw [← (hw x).1.weight_eq (hw x₀).1 hq]
  exact (hw x).2

end AlgebraicGeometry.WeilSheaf
