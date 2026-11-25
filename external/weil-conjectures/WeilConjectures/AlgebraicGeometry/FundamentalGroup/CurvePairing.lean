/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.Estimate
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.PicTorsionPairingMonodromy
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.TorsorExtensionAdd
public import WeilConjectures.AlgebraicGeometry.Sites.RootsOfUnity

/-!
# The finite-level Poincaré pairing in degree one on a curve

Let `X` be a smooth proper connected curve over an algebraically closed field `k`, with a
geometric point `s` and fundamental group `G = π₁(X, s)`, and let `m = lⁿ` with `l` a prime
invertible in `k`. In the torsor model, `H¹(X, ℤ/m)` is the group of continuous characters
`G → ℤ/m` (`AlgebraicGeometry.Scheme.EtaleTorsor.sheafHEquivContinuousMonoidHom`). The cup
product of the class of a `ℤ/m`-torsor with `H¹(X, μ_m)` followed by the trace
`H²(X, μ_m) ≅ ℤ/m` gives a pairing

`AlgebraicGeometry.Scheme.EtaleTorsor.curvePairing : H¹(X, ℤ/m) × H¹(X, μ_m) ⟶ ℤ/m`,

which is bi-additive: additivity in the torsor
(`AlgebraicGeometry.Scheme.EtaleTorsor.cupMu_eq_add`) comes from the `ℤ/m × ℤ/m`-torsor
attached to a pair of characters. We show that it is perfect
(`AlgebraicGeometry.Scheme.EtaleTorsor.bijective_curvePairing`, blueprint
`proposition-kummer-duality-integral-tate-module--2`):

* its left kernel is trivial: a torsor whose pairing vanishes has a section
  (`AlgebraicGeometry.Scheme.EtaleTorsor.exists_section_of_picPairing_eq_zero`);
* both sides have `m ^ (2 g)` elements: `H¹(X, μ_m) ≅ H¹(X, ℤ/m) ≅ (ℤ/m)^{2g}` after the choice
  of a primitive `m`-th root of unity
  (`AlgebraicGeometry.IsCurve.nonempty_addEquiv_sheafH_constantZMod_one`).

An injective map between finite sets of the same cardinality is bijective, and the coordinate
functions of `(ℤ/m)^{2g}` separate the points of `H¹(X, μ_m)`, which gives the right kernel.
-/

@[expose] public section

universe u

open CategoryTheory Limits PreGaloisCategory

/-- The `ℤ/m`-dual of a group isomorphic to `(ℤ/m)^r` is isomorphic to `(ℤ/m)^r`. -/
noncomputable def AddEquiv.addMonoidHomZModPi {A : Type*} [AddCommGroup A] {m r : ℕ}
    (e : A ≃+ (Fin r → ZMod m)) : (A →+ ZMod m) ≃+ (Fin r → ZMod m) :=
  (AddEquiv.addMonoidHomCongrLeft e).trans ((AddMonoidHom.toZModLinearMapEquiv m).trans
    (Module.piEquiv (Fin r) (ZMod m) (ZMod m)).symm.toAddEquiv)

namespace AlgebraicGeometry.Scheme.EtaleTorsor

open FiniteEtale

/-! ### Additivity of the cup product in the torsor -/

section Add

variable {Y : Scheme.{u}} {m : ℕ} [NeZero m]
  (T : EtaleTorsor (ULift.{u + 1} (ZMod m) × ULift.{u + 1} (ZMod m)) Y)

/-- **Additivity of the cup product in the torsor.** Let `T` be a `ℤ/m × ℤ/m`-torsor and `t₁`,
`t₂`, `t₃` be `ℤ/m`-torsors receiving morphisms from `T` along the first projection, the second
projection and the sum `ℤ/m × ℤ/m ⟶ ℤ/m`. Then the cup product with `t₃` is the sum of the cup
products with `t₁` and `t₂`. -/
lemma cupMu_eq_add (t₁ t₂ t₃ : EtaleTorsor (ULift.{u + 1} (ZMod m)) Y)
    (h₁ : T.P ⟶ t₁.P) (hπ₁ : h₁ ≫ t₁.π = T.π)
    (hv₁₁ : T.vadd (1, 0) ≫ h₁ = h₁ ≫ t₁.vadd (1 • 1))
    (hv₁₂ : T.vadd (0, 1) ≫ h₁ = h₁ ≫ t₁.vadd (0 • 1))
    (h₂ : T.P ⟶ t₂.P) (hπ₂ : h₂ ≫ t₂.π = T.π)
    (hv₂₁ : T.vadd (1, 0) ≫ h₂ = h₂ ≫ t₂.vadd (0 • 1))
    (hv₂₂ : T.vadd (0, 1) ≫ h₂ = h₂ ≫ t₂.vadd (1 • 1))
    (h₃ : T.P ⟶ t₃.P) (hπ₃ : h₃ ≫ t₃.π = T.π)
    (hv₃₁ : T.vadd (1, 0) ≫ h₃ = h₃ ≫ t₃.vadd (1 • 1))
    (hv₃₂ : T.vadd (0, 1) ≫ h₃ = h₃ ≫ t₃.vadd (1 • 1))
    (x : Sheaf.H (Y.rootsOfUnitySheaf m) 1) :
    t₃.cupMu x = t₁.cupMu x + t₂.cupMu x := by
  have := T.isIso_pairUnit
  apply (Sheaf.H.bijective_map_of_isIso T.pairUnit 2).1
  have e : biprod.lift (1 • T.pairUnit) (1 • T.pairUnit) =
      biprod.lift (1 • T.pairUnit) (0 • T.pairUnit) +
        biprod.lift (0 • T.pairUnit) (1 • T.pairUnit) := by
    apply biprod.hom_ext <;> simp
  rw [map_add, map_pairUnit_cupMu t₁ h₁ hπ₁ 1 0 hv₁₁ hv₁₂ x,
    map_pairUnit_cupMu t₂ h₂ hπ₂ 0 1 hv₂₁ hv₂₂ x, map_pairUnit_cupMu t₃ h₃ hπ₃ 1 1 hv₃₁ hv₃₂ x, e]
  exact (congrArg _ (Sheaf.H.map_add_apply _ _ x)).trans (map_add _ _ _)

end Add

/-! ### The pairing on characters -/

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
  [ConnectedSpace X] (s : Spec (.of k) ⟶ X)
  (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [∀ P, MulAction G ((fiber s).obj P)] [IsFundamentalGroup (fiber s) G]

omit [IsAlgClosed k] [SmoothOfRelativeDimension 1 (X ↘ Spec (.of k))]
  [IsProper (X ↘ Spec (.of k))] [ConnectedSpace X] in
/-- Isomorphic torsors have the same cup product. -/
lemma cupMu_eq_of_isIsomorphic {m : ℕ} [NeZero m]
    {t₁ t₂ : EtaleTorsor (ULift.{u + 1} (ZMod m)) X} (h : t₁.IsIsomorphic t₂) :
    t₁.cupMu = t₂.cupMu := by
  obtain ⟨φ, hφ, hv⟩ := h
  refine AddMonoidHom.ext fun y ↦ ?_
  have := t₁.map_cupMu t₂ φ.inv 1 (by rw [← hφ, Iso.inv_hom_id_assoc])
    (by rw [one_nsmul, Iso.comp_inv_eq, Category.assoc, hv, Iso.inv_hom_id_assoc]) dvd_rfl y
  rw [rootsOfUnityInclusion_self, Sheaf.H.map_id_apply, Sheaf.H.map_id_apply, one_nsmul] at this
  exact this

/-- The pairing of a continuous character `χ : π₁(X, s) → ℤ/m` with `H¹(X, μ_m)`: the trace of
the cup product with the class of a `ℤ/m`-torsor with monodromy `χ`. -/
noncomputable def charPairing {m : ℕ} [NeZero m] (hm : (m : k) ≠ 0)
    (χ : G →ₜ* Multiplicative (ULift.{u + 1} (ZMod m))) :
    Sheaf.H (X.rootsOfUnitySheaf m) 1 →+ ZMod m :=
  (sheafHTwoTrace m hm).comp (exists_monodromy_eq s G χ).choose.cupMu

/-- The pairing of a character is computed by any torsor with this monodromy. -/
lemma charPairing_eq {m : ℕ} [NeZero m] (hm : (m : k) ≠ 0)
    (t : EtaleTorsor (ULift.{u + 1} (ZMod m)) X) {χ : G →ₜ* Multiplicative (ULift.{u + 1} (ZMod m))}
    (ht : t.monodromy s G = χ) :
    charPairing s G hm χ = (sheafHTwoTrace m hm).comp t.cupMu := by
  rw [charPairing, cupMu_eq_of_isIsomorphic (isIsomorphic_of_monodromy_eq s G
    ((exists_monodromy_eq s G χ).choose_spec.trans ht.symm))]

/-- The pairing is additive in the character. -/
lemma charPairing_mul {m : ℕ} [NeZero m] (hm : (m : k) ≠ 0)
    (χ₁ χ₂ : G →ₜ* Multiplicative (ULift.{u + 1} (ZMod m))) :
    charPairing s G hm (χ₁ * χ₂) = charPairing s G hm χ₁ + charPairing s G hm χ₂ := by
  let A := ULift.{u + 1} (ZMod m)
  let ψ : G →ₜ* Multiplicative (A × A) :=
    { toFun g := Multiplicative.ofAdd ((χ₁ g).toAdd, (χ₂ g).toAdd)
      map_one' := by simp
      map_mul' a b := by simp; rfl
      continuous_toFun := continuous_ofAdd.comp
        ((continuous_toAdd.comp χ₁.continuous).prodMk (continuous_toAdd.comp χ₂.continuous)) }
  obtain ⟨T, hT⟩ := exists_monodromy_eq s G ψ
  obtain ⟨t₁, ht₁⟩ := exists_monodromy_eq s G χ₁
  obtain ⟨t₂, ht₂⟩ := exists_monodromy_eq s G χ₂
  obtain ⟨t₃, ht₃⟩ := exists_monodromy_eq s G (χ₁ * χ₂)
  obtain ⟨f₁, hf₁, hv₁⟩ := exists_hom_of_monodromy s G (AddMonoidHom.fst A A) T t₁
    fun g ↦ by rw [hT, ht₁]; rfl
  obtain ⟨f₂, hf₂, hv₂⟩ := exists_hom_of_monodromy s G (AddMonoidHom.snd A A) T t₂
    fun g ↦ by rw [hT, ht₂]; rfl
  obtain ⟨f₃, hf₃, hv₃⟩ := exists_hom_of_monodromy s G
    (AddMonoidHom.fst A A + AddMonoidHom.snd A A) T t₃ fun g ↦ by rw [hT, ht₃]; rfl
  rw [charPairing_eq s G hm t₁ ht₁, charPairing_eq s G hm t₂ ht₂, charPairing_eq s G hm t₃ ht₃]
  ext x
  simp only [AddMonoidHom.comp_apply, AddMonoidHom.add_apply]
  rw [cupMu_eq_add T t₁ t₂ t₃ f₁ hf₁ (by rw [hv₁]; congr 2; simp) (by rw [hv₁]; congr 2; simp)
    f₂ hf₂ (by rw [hv₂]; congr 2; simp) (by rw [hv₂]; congr 2; simp)
    f₃ hf₃ (by rw [hv₃]; congr 2; simp) (by rw [hv₃]; congr 2; simp), map_add]

/-- The cup-trace pairing `H¹(X, ℤ/m) × H¹(X, μ_m) ⟶ ℤ/m` of a smooth proper connected curve,
with `H¹(X, ℤ/m)` the group of continuous characters `π₁(X, s) → ℤ/m`. -/
noncomputable def curvePairing {m : ℕ} [NeZero m] (hm : (m : k) ≠ 0) :
    Additive (G →ₜ* Multiplicative (ULift.{u + 1} (ZMod m))) →+
      (Sheaf.H (X.rootsOfUnitySheaf m) 1 →+ ZMod m) where
  toFun χ := charPairing s G hm χ.toMul
  map_zero' := by
    have h := charPairing_mul s G hm 1 1
    rw [mul_one, left_eq_add] at h
    exact h
  map_add' χ₁ χ₂ := charPairing_mul s G hm χ₁.toMul χ₂.toMul

/-- The cup-trace pairing of a character `χ` with a class `x`. -/
lemma curvePairing_apply {m : ℕ} [NeZero m] (hm : (m : k) ≠ 0)
    (χ : Additive (G →ₜ* Multiplicative (ULift.{u + 1} (ZMod m))))
    (x : Sheaf.H (X.rootsOfUnitySheaf m) 1) :
    curvePairing s G hm χ x = charPairing s G hm χ.toMul x :=
  rfl

/-- **Left nondegeneracy.** A character whose pairing with `H¹(X, μ_{lⁿ})` vanishes is trivial,
provided `π₁(X, s)` has exactly `l ^ (r k)` characters with values in `ℤ / lᵏ` for `k ≤ n`. -/
lemma eq_one_of_charPairing_eq_zero [GeometricallyIntegral (X ↘ Spec (.of k))] [Nonempty X]
    {l : ℕ} [Fact l.Prime] {n r : ℕ}
    (hcard : ∀ k ≤ n, Nat.card (G →ₜ* Multiplicative (ULift.{u + 1} (ZMod (l ^ k)))) =
      l ^ (r * k)) [NeZero (l ^ n)] (hm : ((l ^ n : ℕ) : k) ≠ 0)
    (χ : G →ₜ* Multiplicative (ULift.{u + 1} (ZMod (l ^ n))))
    (h : charPairing s G hm χ = 0) : χ = 1 := by
  obtain ⟨t, rfl⟩ := exists_monodromy_eq s G χ
  have hp : t.picPairing hm = 0 := by
    ext y
    have := DFunLike.congr_fun h ((kummerTorsionEquiv _ hm).symm y)
    rwa [charPairing_eq s G hm t rfl] at this
  obtain ⟨σ, hσ⟩ := exists_section_of_picPairing_eq_zero s G hcard hm t hp
  exact monodromy_eq_one_of_section s G t hσ

omit [IsAlgClosed k] [ConnectedSpace X] in
/-- A smooth proper connected nonempty scheme of relative dimension one over a field is a
connected curve. -/
lemma isConnectedCurve [ConnectedSpace X] [Nonempty X] : IsConnectedCurve (X ↘ Spec (.of k)) :=
  { krullDim_le_one := by
      exact_mod_cast topologicalKrullDim_le_of_smoothOfRelativeDimension (X ↘ Spec (.of k)) 1
    connectedSpace := inferInstance
    krullDim_eq_one := by
      exact_mod_cast topologicalKrullDim_eq_of_smoothOfRelativeDimension (X ↘ Spec (.of k)) 1 }

omit [ConnectedSpace X] in
/-- `H¹(X, μ_m) ≅ (ℤ/m)^{2g}` for a smooth proper connected curve of genus `g`: choosing a
primitive `m`-th root of unity identifies `μ_m` with `ℤ/m`. -/
lemma nonempty_addEquiv_sheafH_rootsOfUnitySheaf_one [ConnectedSpace X] [Nonempty X] (m : ℕ)
    [NeZero m] (hm : (m : k) ≠ 0) :
    Nonempty (Sheaf.H (X.rootsOfUnitySheaf m) 1 ≃+
      (Fin (2 * (X ↘ Spec (.of k)).genus) → ZMod m)) := by
  have := isConnectedCurve (k := k) (X := X)
  have : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 1 _
  have : NeZero (m : k) := ⟨hm⟩
  obtain ⟨-, -, ζ, hζ, -⟩ := IsSepClosed.exists_isPrimitiveRoot.{u, u} k m
  obtain ⟨e⟩ := IsCurve.nonempty_addEquiv_sheafH_constantZMod_one (X ↘ Spec (.of k)) m hm
  exact ⟨((Sheaf.functorH _ 1).mapIso
    (X.constantZModIsoRootsOfUnitySheaf m (X ↘ Spec (.of k)) hζ)).addCommGroupIsoToAddEquiv.symm
      |>.trans e⟩

include s in
/-- `π₁(X, s)` has `m ^ (2 g)` continuous characters with values in `ℤ/m`: they are the elements
of `H¹(X, ℤ/m) ≅ (ℤ/m)^{2g}`. -/
lemma card_continuousMonoidHom_zmod [Nonempty X] (m : ℕ) [NeZero m] (hm : (m : k) ≠ 0) :
    Nat.card (G →ₜ* Multiplicative (ULift.{u + 1} (ZMod m))) =
      m ^ (2 * (X ↘ Spec (.of k)).genus) := by
  have := isConnectedCurve (k := k) (X := X)
  have : Smooth (X ↘ Spec (.of k)) := SmoothOfRelativeDimension.smooth 1 _
  obtain ⟨e⟩ := IsCurve.nonempty_addEquiv_sheafH_constantZMod_one (X ↘ Spec (.of k)) m hm
  rw [Nat.card_congr ((sheafHEquivContinuousMonoidHom (ULift.{u + 1} (ZMod m)) s G).symm.trans
    e.toEquiv), Nat.card_fun, Nat.card_zmod, Nat.card_fin]

/-- Blueprint `proposition-kummer-duality-integral-tate-module--2`: Finite-level degree-one Poincaré
pairing on a curve.

Let `X` be a smooth proper connected curve over an algebraically closed field `k` (e.g. the
geometric fibre of a curve over a finite field), `s` a geometric point with fundamental group
`G = π₁(X, s)`, and `A_n = ℤ / lⁿ` with `l` a prime invertible in `k`. The cup product followed
by the trace,

`H¹(X, A_n) × H¹(X, A_n(1)) ⟶ H²(X, A_n(1)) ≅ A_n`,

is a perfect pairing. Here `H¹(X, A_n)` is the group of continuous characters `G → ℤ / lⁿ`
(`AlgebraicGeometry.Scheme.EtaleTorsor.sheafHEquivContinuousMonoidHom`) and
`H¹(X, A_n(1)) = H¹(X, μ_{lⁿ})`; perfectness means that both induced maps into the `ℤ / lⁿ`-duals
are bijective. -/
theorem bijective_curvePairing [GeometricallyIntegral (X ↘ Spec (.of k))] [Nonempty X]
    (l n : ℕ) [Fact l.Prime] [NeZero (l ^ n)] (hm : ((l ^ n : ℕ) : k) ≠ 0) :
    Function.Bijective (curvePairing s G hm) ∧ Function.Bijective (curvePairing s G hm).flip := by
  set r := 2 * (X ↘ Spec (.of k)).genus
  have hcard (j : ℕ) (hj : j ≤ n) :
      Nat.card (G →ₜ* Multiplicative (ULift.{u + 1} (ZMod (l ^ j)))) = l ^ (r * j) := by
    have : NeZero (l ^ j) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    have hj' : ((l ^ j : ℕ) : k) ≠ 0 := fun h ↦ hm <| by
      obtain ⟨c, hc⟩ := pow_dvd_pow l hj
      rw [hc, Nat.cast_mul, h, zero_mul]
    rw [card_continuousMonoidHom_zmod s G _ hj', ← pow_mul, mul_comm]
  obtain ⟨eR⟩ := nonempty_addEquiv_sheafH_rootsOfUnitySheaf_one (X := X) (l ^ n) hm
  have hL : Nat.card (Additive (G →ₜ* Multiplicative (ULift.{u + 1} (ZMod (l ^ n))))) =
      Nat.card (Fin r → ZMod (l ^ n)) := by
    rw [Nat.card_congr Additive.toMul, card_continuousMonoidHom_zmod s G _ hm, Nat.card_fun,
      Nat.card_zmod, Nat.card_fin]
  have hleft : Function.Bijective (curvePairing s G hm) := by
    have : Finite (Sheaf.H (X.rootsOfUnitySheaf (l ^ n)) 1 →+ ZMod (l ^ n)) :=
      Finite.of_equiv _ eR.addMonoidHomZModPi.symm.toEquiv
    refine Function.Injective.bijective_of_nat_card_le ?_ ?_
    · refine (injective_iff_map_eq_zero _).2 fun χ hχ ↦ ?_
      exact congrArg Additive.ofMul (eq_one_of_charPairing_eq_zero s G hcard hm χ.toMul hχ)
    · rw [Nat.card_congr eR.addMonoidHomZModPi.toEquiv, hL]
  refine ⟨hleft, ?_⟩
  let eL := (AddEquiv.ofBijective _ hleft).trans eR.addMonoidHomZModPi
  have : Finite (Additive (G →ₜ* Multiplicative (ULift.{u + 1} (ZMod (l ^ n)))) →+
      ZMod (l ^ n)) :=
    Finite.of_equiv _ eL.addMonoidHomZModPi.symm.toEquiv
  refine Function.Injective.bijective_of_nat_card_le ?_ ?_
  · refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
    by_contra hx0
    obtain ⟨i, hi⟩ : ∃ i, eR x i ≠ 0 := by
      by_contra! h
      exact hx0 (eR.injective ((funext h).trans (map_zero eR).symm))
    obtain ⟨χ, hχ⟩ := hleft.2 ((Pi.evalAddMonoidHom (fun _ ↦ ZMod (l ^ n)) i).comp
      eR.toAddMonoidHom)
    have := DFunLike.congr_fun hx χ
    rw [AddMonoidHom.flip_apply, hχ] at this
    exact hi this
  · rw [Nat.card_congr eL.addMonoidHomZModPi.toEquiv, Nat.card_congr eR.toEquiv]

end AlgebraicGeometry.Scheme.EtaleTorsor
