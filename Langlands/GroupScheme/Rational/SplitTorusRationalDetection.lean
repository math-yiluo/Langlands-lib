import Langlands.GroupScheme.Torus.Diagonalizable
import Langlands.GroupScheme.Torus.UniversalPoint
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Rational-point detection for a split torus over an infinite field -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry Polynomial
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false

namespace splitTorus

variable {k : Type u} [Field k] [Infinite k]

/-- The units of an infinite field have no common nonzero integer exponent. -/
theorem eq_zero_of_forall_units_zpow_eq_one (d : ℤ)
    (h : ∀ x : kˣ, x ^ d = 1) : d = 0 := by
  by_contra hd
  have hpos : 0 < d.natAbs := Int.natAbs_pos.mpr hd
  have hp : (Polynomial.X ^ d.natAbs - 1 : k[X]) = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply (Set.finite_singleton (0 : k)).infinite_compl.mono
    intro x hx
    have hx0 : x ≠ 0 := by simpa using hx
    have hh := congrArg (fun u : kˣ => (u : k)) ((pow_natAbs_eq_one).mpr (h (Units.mk0 x hx0)))
    simpa [Polynomial.IsRoot, sub_eq_zero] using hh
  have hc := congrArg (fun p : k[X] => p.coeff d.natAbs) hp
  simp [Polynomial.coeff_X_pow, Polynomial.coeff_one, Nat.ne_of_gt hpos] at hc

variable (I : Type u) [Fintype I] [DecidableEq I]

/-- A Laurent monomial as a multiplicative character of the group of rational points. -/
def rationalMonomial (m : I → ℤ) : (I → kˣ) →* k where
  toFun t := (exponentValue I t (Multiplicative.ofAdd m) : k)
  map_one' := by simp [exponentValue]
  map_mul' t s := by
    simp [exponentValue, mul_zpow, Finset.prod_mul_distrib]

omit [Infinite k] in
theorem exponentValue_mulSingle (m : I → ℤ) (i : I) (x : kˣ) :
    exponentValue I (Pi.mulSingle i x) (Multiplicative.ofAdd m) = x ^ m i := by
  classical
  change (∏ j, (Pi.mulSingle i x : I → kˣ) j ^ m j) = _
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hji
    simp [Pi.mulSingle_eq_of_ne hji]
  · simp

/-- Distinct exponent vectors give distinct characters over an infinite field. -/
theorem rationalMonomial_injective : Function.Injective (rationalMonomial (k := k) I) := by
  intro m n h
  funext i
  apply sub_eq_zero.mp
  apply eq_zero_of_forall_units_zpow_eq_one (k := k)
  intro x
  have hx := congrArg (fun f : (I → kˣ) →* k => f (Pi.mulSingle i x)) h
  have he : x ^ m i = x ^ n i := by
    apply Units.ext
    simpa only [rationalMonomial, MonoidHom.coe_mk, OneHom.coe_mk, exponentValue_mulSingle] using hx
  rw [zpow_sub, he, mul_inv_cancel]

/-- Evaluations at all rational unit tuples detect a Laurent polynomial. -/
theorem eq_zero_of_evaluateUnits_eq_zero (p : AddMonoidAlgebra k (I → ℤ))
    (hp : ∀ t : I → kˣ, evaluateUnits (R := CommRingCat.of k) I t p = 0) : p = 0 := by
  have hi : LinearIndependent k (fun m : I → ℤ =>
      (rationalMonomial (k := k) I m : (I → kˣ) → k)) :=
    (linearIndependent_monoidHom (I → kˣ) k).comp _ (rationalMonomial_injective I)
  apply AddMonoidAlgebra.coeff_injective
  apply (linearIndependent_iff.mp hi) p.coeff
  funext t
  have he : (Finsupp.linearCombination k
      (fun m : I → ℤ => (rationalMonomial (k := k) I m : (I → kˣ) → k)) p.coeff) t =
      evaluateUnits (R := CommRingCat.of k) I t p := by
    clear hp
    induction p using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add p q hp hq => simp [hp, hq]
    | single m r =>
      rw [evaluateUnits_single (R := CommRingCat.of k)]
      simp [rationalMonomial]
  simpa [he] using hp t

end splitTorus

variable {k : Type u} [Field k] [Infinite k]

/-- Rational points detect a regular function if vanishing at every point implies zero. -/
def RationalPointsDetectFunctions (X : Over (Spec (CommRingCat.of k))) : Prop :=
  ∀ s : Γ(X.left, ⊤),
    (∀ x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X, x.left.appTop s = 0) → s = 0

omit [Infinite k] in
theorem RationalPointsDetectFunctions.of_iso
    {X Y : Over (Spec (CommRingCat.of k))} (e : X ≅ Y)
    (hX : RationalPointsDetectFunctions X) : RationalPointsDetectFunctions Y := by
  intro s hs
  have he : e.hom.left.appTop s = 0 := by
    apply hX
    intro x
    simpa only [Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
      using hs (x ≫ e.hom)
  have hh := congrArg e.inv.left.appTop he
  simpa only [map_zero, ← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop,
    ← Over.comp_left, e.inv_hom_id, Over.id_left, Scheme.Hom.id_appTop,
    CommRingCat.id_apply] using hh

namespace splitTorus

variable (I : Type u) [Fintype I] [DecidableEq I]

/-- The spectrum of the split character algebra has enough rational points. -/
theorem rationalPointsDetectFunctions_diagonalizable :
    RationalPointsDetectFunctions
      ((Diagonalizable.groupScheme (CommRingCat.of k) (I → ℤ)).toGrp.X) := by
  intro s hs
  change Γ(Spec (CommRingCat.of (AddMonoidAlgebra k (I → ℤ))), ⊤) at s
  apply (Scheme.ΓSpecIso (CommRingCat.of (AddMonoidAlgebra k (I → ℤ)))).commRingCatIsoToRingEquiv.injective
  change (Scheme.ΓSpecIso (CommRingCat.of (AddMonoidAlgebra k (I → ℤ)))).hom s =
    (Scheme.ΓSpecIso (CommRingCat.of (AddMonoidAlgebra k (I → ℤ)))).hom 0
  rw [map_zero]
  apply eq_zero_of_evaluateUnits_eq_zero (k := k) I
  intro t
  let ev := evaluateUnits (R := CommRingCat.of k) I t
  let x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
      ((Diagonalizable.groupScheme (CommRingCat.of k) (I → ℤ)).toGrp.X) :=
    Over.homMk (Spec.map (CommRingCat.ofHom ev.toRingHom)) (by
      change Spec.map (CommRingCat.ofHom ev.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap k (AddMonoidAlgebra k (I → ℤ)))) = 𝟙 _
      rw [← Spec.map_comp]
      convert Spec.map_id (CommRingCat.of k) using 1
      congr 1
      ext r
      exact ev.commutes r)
  change ((Scheme.ΓSpecIso (CommRingCat.of (AddMonoidAlgebra k (I → ℤ)))).hom ≫
    CommRingCat.ofHom ev.toRingHom) s = 0
  rw [← Scheme.ΓSpecIso_naturality]
  change (Scheme.ΓSpecIso (CommRingCat.of k)).hom (x.left.appTop s) = 0
  rw [hs x, map_zero]

/-- Rational points of a split torus detect regular functions. -/
theorem rationalPointsDetectFunctions :
    RationalPointsDetectFunctions (splitTorus (Spec (CommRingCat.of k)) I).X := by
  exact (rationalPointsDetectFunctions_diagonalizable (k := k) I).of_iso
    ((Grp.forget _).mapIso
      (Diagonalizable.splitIso (CommRingCat.of k) (AddEquiv.refl (I → ℤ))))

end splitTorus

/-- Rational points of any split torus over an infinite field detect its regular functions. -/
theorem IsSplitTorus.rationalPointsDetectFunctions
    {T : GroupScheme (Spec (CommRingCat.of k))} (hT : IsSplitTorus T) :
    RationalPointsDetectFunctions T.X := by
  classical
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let := Fintype.ofFinite I
  exact (splitTorus.rationalPointsDetectFunctions (k := k) I).of_iso
    ((Grp.forget _).mapIso e.symm)

/-- Maps from a split torus to an affine scheme agree when they agree at rational points. -/
theorem IsSplitTorus.hom_ext_kpoints
    {T : GroupScheme (Spec (CommRingCat.of k))} (hT : IsSplitTorus T)
    {Y : Over (Spec (CommRingCat.of k))} [IsAffine Y.left] {f g : T.X ⟶ Y}
    (h : ∀ x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ T.X, x ≫ f = x ≫ g) :
    f = g := by
  apply Over.OverMorphism.ext
  apply ext_of_isAffine
  ext s
  apply sub_eq_zero.mp
  apply hT.rationalPointsDetectFunctions
  intro x
  rw [map_sub]
  apply sub_eq_zero.mpr
  have hx := congrArg
    (fun q : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Y => q.left.appTop s) (h x)
  simpa only [Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.comp_apply] using hx

/-- A split-torus map factors through a closed immersion if it does so at rational points. -/
theorem IsSplitTorus.exists_factor_of_kpoints
    {T : GroupScheme (Spec (CommRingCat.of k))} (hT : IsSplitTorus T)
    {Y Z : Over (Spec (CommRingCat.of k))} [IsAffine Z.left]
    (j : Y ⟶ Z) [IsClosedImmersion j.left] (f : T.X ⟶ Z)
    (h : ∀ x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ T.X,
      ∃ y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Y, y ≫ j = x ≫ f) :
    ∃ l : T.X ⟶ Y, l ≫ j = f := by
  have hk : RingHom.ker j.left.appTop.hom ≤ RingHom.ker f.left.appTop.hom := by
    intro s hs
    change f.left.appTop s = 0
    apply hT.rationalPointsDetectFunctions
    intro x
    obtain ⟨y, hy⟩ := h x
    have hh := congrArg
      (fun q : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Z => q.left.appTop s) hy
    simp only [Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at hh
    rw [← hh, RingHom.mem_ker.mp hs, map_zero]
  have hker : j.left.ker ≤ f.left.ker := by
    rw [Scheme.ker_of_isAffine, Scheme.ker_of_isAffine]
    apply Scheme.IdealSheafData.le_of_isAffine
    simpa using hk
  let l := IsClosedImmersion.lift j.left f.left hker
  have hlj : l ≫ j.left = f.left := IsClosedImmersion.lift_fac _ _ _
  refine ⟨Over.homMk l ?_, ?_⟩
  · rw [← Over.w j, ← Category.assoc, hlj, Over.w f]
  · exact Over.OverMorphism.ext hlj

end Langlands.GroupScheme
