import Langlands.GroupScheme.Reductive.CovariantKunneth
import Langlands.GroupScheme.Reductive.CovariantProductInjective
import Mathlib.RingTheory.Localization.Away.Basic

/-! # Exhaustion of invariant coordinates by products of covariant coordinates -/

noncomputable section

universe u

open TensorProduct Coalgebra WithConv

namespace Langlands.GroupScheme.Chevalley

namespace CellExhaustion

section Points

variable {k A R : Type u} [Field k] [CommRing A] [HopfAlgebra k A] [CommRing R] [Algebra k R]

/-- The group of `R`-points of the affine group with coordinate Hopf algebra `A`: algebra maps
out of `A` under convolution, with inverse given by composition with the antipode. -/
abbrev pointGroup : Group (WithConv (A →ₐ[k] R)) :=
  { (inferInstance : Monoid (WithConv (A →ₐ[k] R))) with
    inv := fun f => toConv (f.ofConv.comp (HopfAlgebra.antipodeAlgHom k A))
    inv_mul_cancel := fun f => by
      apply WithConv.ofConv_injective
      have h := AlgHom.comp_convMul_distrib f.ofConv
        (toConv (HopfAlgebra.antipodeAlgHom k A)) (toConv (AlgHom.id k A))
      rw [AlgHom.antipode_id_cancel, AlgHom.comp_id, toConv_ofConv] at h
      refine h.symm.trans ?_
      ext a
      simp [AlgHom.convOne_def] }

attribute [local instance] pointGroup

theorem inv_ofConv_apply (f : WithConv (A →ₐ[k] R)) (a : A) :
    (f⁻¹).ofConv a = f.ofConv (HopfAlgebra.antipode k a) :=
  rfl

theorem one_ofConv_apply (a : A) :
    (1 : WithConv (A →ₐ[k] R)).ofConv a = algebraMap k R (counit a) :=
  rfl

variable {R' : Type u} [CommRing R'] [Algebra k R']

/-- Pushing points forward along an algebra map of test algebras. -/
def postcomp (h : R →ₐ[k] R') : WithConv (A →ₐ[k] R) →* WithConv (A →ₐ[k] R') where
  toFun g := toConv (h.comp g.ofConv)
  map_one' := by
    apply WithConv.ofConv_injective
    ext a
    simp [AlgHom.convOne_def]
  map_mul' g g' := by
    apply WithConv.ofConv_injective
    exact AlgHom.comp_convMul_distrib h g g'

theorem postcomp_ofConv_apply (h : R →ₐ[k] R') (g : WithConv (A →ₐ[k] R)) (a : A) :
    (postcomp h g).ofConv a = h (g.ofConv a) :=
  rfl

variable {C : Type u} [CommRing C] [HopfAlgebra k C]

/-- Restriction of points along a coordinate bialgebra map. -/
def pointMap (r : A →ₐc[k] C) : WithConv (C →ₐ[k] R) →* WithConv (A →ₐ[k] R) where
  toFun c := toConv (c.ofConv.comp (r : A →ₐ[k] C))
  map_one' := by
    apply WithConv.ofConv_injective
    ext a
    simp [AlgHom.convOne_def]
  map_mul' c c' := by
    apply WithConv.ofConv_injective
    exact AlgHom.convMul_comp_bialgHom_distrib c c' r

theorem pointMap_ofConv_apply (r : A →ₐc[k] C) (c : WithConv (C →ₐ[k] R)) (a : A) :
    (pointMap r c).ofConv a = c.ofConv (r a) :=
  rfl

theorem postcomp_pointMap (h : R →ₐ[k] R') (r : A →ₐc[k] C) (c : WithConv (C →ₐ[k] R)) :
    postcomp h (pointMap r c) = pointMap r (postcomp h c) :=
  rfl

/-- Left convolution by a restricted point splits off the weight of a left covariant
coordinate. -/
theorem pointMap_mul_apply (r : A →ₐc[k] C) {χ : C} {a : A}
    (ha : a ∈ leftCovariantSubspace (r : A →ₗ[k] C) χ) (c : WithConv (C →ₐ[k] R))
    (g : WithConv (A →ₐ[k] R)) :
    (pointMap r c * g).ofConv a = c.ofConv χ * g.ofConv a := by
  rw [mem_leftCovariantSubspace] at ha
  have hmap : (Algebra.TensorProduct.map (c.ofConv.comp (r : A →ₐ[k] C)) g.ofConv).toLinearMap =
      (Algebra.TensorProduct.map c.ofConv g.ofConv).toLinearMap ∘ₗ
        (r : A →ₗ[k] C).rTensor A := by
    apply TensorProduct.ext'
    intro x y
    rfl
  change (toConv (c.ofConv.comp (r : A →ₐ[k] C)) * g).ofConv a = _
  rw [AlgHom.convMul_def, ofConv_toConv]
  simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply]
  have h := LinearMap.congr_fun hmap (comul (R := k) a)
  simp only [AlgHom.toLinearMap_apply, LinearMap.comp_apply] at h
  rw [h, ha]
  simp

/-- The weight of a left covariant coordinate with counit one takes unit values. -/
theorem isUnit_ofConv_weight (r : A →ₐc[k] C) {χ : C} {a : A}
    (ha : a ∈ leftCovariantSubspace (r : A →ₗ[k] C) χ) (hε : counit (R := k) a = 1)
    (c : WithConv (C →ₐ[k] R)) : IsUnit (c.ofConv χ) := by
  have h := pointMap_mul_apply r ha c (pointMap r c)⁻¹
  rw [mul_inv_cancel, one_ofConv_apply, hε, map_one] at h
  exact IsUnit.of_mul_eq_one _ h.symm

/-- Right convolution by an inverse restricted point splits off the weight of a coordinate
whose antipode is left covariant. -/
theorem mul_inv_pointMap_apply (s : A →ₐc[k] C) {χ : C} {a : A}
    (ha : HopfAlgebra.antipode k a ∈ leftCovariantSubspace (s : A →ₗ[k] C) χ)
    (e : WithConv (C →ₐ[k] R)) (g : WithConv (A →ₐ[k] R)) :
    (g * (pointMap s e)⁻¹).ofConv a = e.ofConv χ * g.ofConv a := by
  have h := pointMap_mul_apply s ha e g⁻¹
  rw [← inv_ofConv_apply, mul_inv_rev, inv_inv, ← inv_ofConv_apply, inv_inv] at h
  exact h

/-- The weight of a coordinate with left covariant antipode and counit one takes unit
values. -/
theorem isUnit_ofConv_weight' (s : A →ₐc[k] C) {χ : C} {a : A}
    (ha : HopfAlgebra.antipode k a ∈ leftCovariantSubspace (s : A →ₗ[k] C) χ)
    (hε : counit (R := k) a = 1) (e : WithConv (C →ₐ[k] R)) : IsUnit (e.ofConv χ) :=
  isUnit_ofConv_weight s ha (by rw [HopfAlgebra.counit_antipode, hε]) e

end Points

section Separation

variable {k T : Type u} [Field k] [CommRing T] [Algebra k T]

/-- Two elements agreeing after every algebra map inverting `Q` agree after multiplication by
a power of `Q`. -/
theorem exists_pow_mul_eq_of_forall_isUnit {Q E E' : T}
    (h : ∀ (R : Type u) [CommRing R] [Algebra k R] (τ : T →ₐ[k] R), IsUnit (τ Q) → τ E = τ E') :
    ∃ m : ℕ, Q ^ m * E = Q ^ m * E' :=
  IsLocalization.Away.exists_of_eq Q
    (h (Localization.Away Q) (IsScalarTower.toAlgHom k T _)
      (IsLocalization.Away.algebraMap_isUnit Q))

end Separation

section Cell

open Algebra.TensorProduct

variable {k A R R' : Type u} [Field k] [CommRing A] [HopfAlgebra k A] [CommRing R] [Algebra k R]
  [CommRing R'] [Algebra k R']

attribute [local instance] pointGroup

/-- The coordinate `(x, y) ↦ d (x y⁻¹)` on the product of the group with itself. -/
def cellDifference (d : A) : A ⊗[k] A :=
  (toConv (includeLeft : A →ₐ[k] A ⊗[k] A) *
    (toConv (includeRight : A →ₐ[k] A ⊗[k] A))⁻¹).ofConv d

theorem postcomp_productMap_includeLeft (X Y : WithConv (A →ₐ[k] R)) :
    postcomp (productMap X.ofConv Y.ofConv) (toConv (includeLeft : A →ₐ[k] A ⊗[k] A)) = X :=
  WithConv.ofConv_injective (productMap_left _ _)

theorem postcomp_productMap_includeRight (X Y : WithConv (A →ₐ[k] R)) :
    postcomp (productMap X.ofConv Y.ofConv) (toConv (includeRight : A →ₐ[k] A ⊗[k] A)) = Y :=
  WithConv.ofConv_injective (productMap_right _ _)

/-- Evaluating the cell difference at the pair `(X, Y)` evaluates `d` at `X Y⁻¹`. -/
theorem productMap_cellDifference (d : A) (X Y : WithConv (A →ₐ[k] R)) :
    productMap X.ofConv Y.ofConv (cellDifference d) = (X * Y⁻¹).ofConv d := by
  have h := congrArg (fun z => z.ofConv d)
    (map_mul (postcomp (productMap X.ofConv Y.ofConv))
      (toConv (includeLeft : A →ₐ[k] A ⊗[k] A))
      (toConv (includeRight : A →ₐ[k] A ⊗[k] A))⁻¹)
  simp only [map_inv, postcomp_productMap_includeLeft, postcomp_productMap_includeRight] at h
  exact h

/-- Postcomposition with an algebra map commutes with forming product maps. -/
theorem apply_productMap (τ : R →ₐ[k] R') (X Y : WithConv (A →ₐ[k] R)) (z : A ⊗[k] A) :
    τ (productMap X.ofConv Y.ofConv z) =
      productMap (postcomp τ X).ofConv (postcomp τ Y).ofConv z := by
  induction z using TensorProduct.inductionOn with
  | tmul a b => simp [postcomp_ofConv_apply]
  | add z z' hz hz' => simp only [map_add, hz, hz']

variable {C C' : Type u} [CommRing C] [HopfAlgebra k C] [CommRing C'] [HopfAlgebra k C']

/-- Left translation of the first point by a restricted point scales the cell difference by
the weight of `d`. -/
theorem productMap_mul_left_cellDifference (r : A →ₐc[k] C) {χ : C} {d : A}
    (hd : d ∈ leftCovariantSubspace (r : A →ₗ[k] C) χ) (c : WithConv (C →ₐ[k] R))
    (X Y : WithConv (A →ₐ[k] R)) :
    productMap (pointMap r c * X).ofConv Y.ofConv (cellDifference d) =
      c.ofConv χ * productMap X.ofConv Y.ofConv (cellDifference d) := by
  rw [productMap_cellDifference, productMap_cellDifference, mul_assoc, pointMap_mul_apply r hd]

/-- Left translation of the second point by a restricted point scales the cell difference by
the weight of the antipode of `d`. -/
theorem productMap_mul_right_cellDifference (s : A →ₐc[k] C') {ψ : C'} {d : A}
    (hd : HopfAlgebra.antipode k d ∈ leftCovariantSubspace (s : A →ₗ[k] C') ψ)
    (e : WithConv (C' →ₐ[k] R)) (X Y : WithConv (A →ₐ[k] R)) :
    productMap X.ofConv (pointMap s e * Y).ofConv (cellDifference d) =
      e.ofConv ψ * productMap X.ofConv Y.ofConv (cellDifference d) := by
  rw [productMap_cellDifference, productMap_cellDifference, mul_inv_rev, ← mul_assoc,
    mul_inv_pointMap_apply s hd]

/-- The value of `d` at a point `i(b) i'(b')⁻¹` of the cell. -/
theorem ofConv_pointMap_mul_inv (r : A →ₐc[k] C) (s : A →ₐc[k] C') {χ : C} {ψ : C'} {d : A}
    (hd : d ∈ leftCovariantSubspace (r : A →ₗ[k] C) χ)
    (hd' : HopfAlgebra.antipode k d ∈ leftCovariantSubspace (s : A →ₗ[k] C') ψ)
    (hε : counit (R := k) d = 1) (b : WithConv (C →ₐ[k] R)) (b' : WithConv (C' →ₐ[k] R)) :
    (pointMap r b * (pointMap s b')⁻¹).ofConv d = b.ofConv χ * b'.ofConv ψ := by
  rw [pointMap_mul_apply r hd, ← one_mul (pointMap s b')⁻¹, mul_inv_pointMap_apply s hd',
    one_ofConv_apply, hε, map_one, mul_one]

/-- Two factorizations of the same point through the cell give the same value of a
coordinate invariant under the intersection of the two subgroups. -/
theorem ofConv_inv_pointMap_mul_eq (r : A →ₐc[k] C) (s : A →ₐc[k] C') {f : A}
    (hf : ∀ (c : WithConv (C →ₐ[k] R)) (c' : WithConv (C' →ₐ[k] R)),
      pointMap r c = pointMap s c' →
        ∀ g : WithConv (A →ₐ[k] R), (pointMap r c * g).ofConv f = g.ofConv f)
    (X : WithConv (A →ₐ[k] R)) {b q : WithConv (C →ₐ[k] R)} {b' q' : WithConv (C' →ₐ[k] R)}
    (h : pointMap r b * (pointMap s b')⁻¹ = pointMap r q * (pointMap s q')⁻¹) :
    ((pointMap r b)⁻¹ * X).ofConv f = ((pointMap r q)⁻¹ * X).ofConv f := by
  have e : pointMap r (b⁻¹ * q) = pointMap s (b'⁻¹ * q') := by
    rw [map_mul, map_mul, map_inv, map_inv]
    calc (pointMap r b)⁻¹ * pointMap r q
        = (pointMap r b)⁻¹ * (pointMap r q * (pointMap s q')⁻¹) * pointMap s q' := by group
      _ = (pointMap r b)⁻¹ * (pointMap r b * (pointMap s b')⁻¹) * pointMap s q' := by rw [h]
      _ = (pointMap s b')⁻¹ * pointMap s q' := by group
  have hx : (pointMap r b)⁻¹ * X = pointMap r (b⁻¹ * q) * ((pointMap r q)⁻¹ * X) := by
    rw [map_mul, map_inv]
    group
  rw [hx]
  exact hf _ _ e _

/-- `F` lifts `f` along the cell with denominator exponent `n`: at every pair of points
`(X, Y)` with `X Y⁻¹ = i(b) i'(b')⁻¹` one has `F(X, Y) = D(X, Y)ⁿ f(i(b)⁻¹ X)`, where
`D(X, Y) = d(X Y⁻¹)`. -/
def IsCellLift (r : A →ₐc[k] C) (s : A →ₐc[k] C') (d f : A) (n : ℕ) (F : A ⊗[k] A) : Prop :=
  ∀ (R : Type u) [CommRing R] [Algebra k R] (X Y : WithConv (A →ₐ[k] R))
    (b : WithConv (C →ₐ[k] R)) (b' : WithConv (C' →ₐ[k] R)),
    X * Y⁻¹ = pointMap r b * (pointMap s b')⁻¹ →
      productMap X.ofConv Y.ofConv F =
        productMap X.ofConv Y.ofConv (cellDifference d) ^ n * ((pointMap r b)⁻¹ * X).ofConv f

/-- The product map of the two coordinate inclusions into a localization of `A ⊗ A` is the
localization map. -/
theorem productMap_comp_include {T : Type u} [CommRing T] [Algebra k T]
    (loc : A ⊗[k] A →ₐ[k] T) :
    productMap (loc.comp includeLeft) (loc.comp includeRight) = loc := by
  apply Algebra.TensorProduct.ext'
  intro a b
  rw [productMap_apply_tmul, AlgHom.comp_apply, AlgHom.comp_apply, ← map_mul, includeLeft_apply,
    includeRight_apply, tmul_mul_tmul, mul_one, one_mul]

/-- A coordinate invariant under the intersection of the two subgroups lifts along the cell. -/
theorem exists_isCellLift (r : A →ₐc[k] C) (s : A →ₐc[k] C') {χ : C} {ψ : C'} {d f : A}
    (hd : d ∈ leftCovariantSubspace (r : A →ₗ[k] C) χ)
    (hd' : HopfAlgebra.antipode k d ∈ leftCovariantSubspace (s : A →ₗ[k] C') ψ)
    (hε : counit (R := k) d = 1)
    (hdec : ∀ (R : Type u) [CommRing R] [Algebra k R] (g : WithConv (A →ₐ[k] R)),
      IsUnit (g.ofConv d) → ∃ b b', g * pointMap s b' = pointMap r b)
    (hf : ∀ (R : Type u) [CommRing R] [Algebra k R] (c : WithConv (C →ₐ[k] R))
      (c' : WithConv (C' →ₐ[k] R)), pointMap r c = pointMap s c' →
        ∀ g : WithConv (A →ₐ[k] R), (pointMap r c * g).ofConv f = g.ofConv f) :
    ∃ n F, IsCellLift r s d f n F := by
  let D := cellDifference (k := k) d
  let R0 := Localization.Away D
  let loc : A ⊗[k] A →ₐ[k] R0 := IsScalarTower.toAlgHom k (A ⊗[k] A) R0
  let X0 : WithConv (A →ₐ[k] R0) := toConv (loc.comp includeLeft)
  let Y0 : WithConv (A →ₐ[k] R0) := toConv (loc.comp includeRight)
  have hunit : IsUnit ((X0 * Y0⁻¹).ofConv d) := by
    rw [← productMap_cellDifference, ofConv_toConv, ofConv_toConv, productMap_comp_include]
    exact IsLocalization.Away.algebraMap_isUnit D
  obtain ⟨b0, b0', hb0⟩ := hdec R0 (X0 * Y0⁻¹) hunit
  obtain ⟨n, F, hF⟩ := IsLocalization.Away.surj D (((pointMap r b0)⁻¹ * X0).ofConv f)
  refine ⟨n, F, ?_⟩
  intro R _ _ X Y b b' hXY
  let φ := productMap X.ofConv Y.ofConv
  have hφD : IsUnit (φ D) := by
    simp only [φ, D]
    rw [productMap_cellDifference, hXY, ofConv_pointMap_mul_inv r s hd hd' hε]
    exact (isUnit_ofConv_weight r hd hε b).mul (isUnit_ofConv_weight' s hd' hε b')
  have hpow : ∀ y : Submonoid.powers D, IsUnit (φ y) := by
    rintro ⟨y, m, rfl⟩
    rw [map_pow]
    exact hφD.pow m
  let τ : R0 →ₐ[k] R := IsLocalization.liftAlgHom (M := Submonoid.powers D) hpow
  have hτ : ∀ z, τ (loc z) = φ z := fun z => IsLocalization.lift_eq hpow z
  have hτX : postcomp τ X0 = X := by
    apply WithConv.ofConv_injective
    ext a
    exact (hτ _).trans (productMap_left_apply _ _ a)
  have hτY : postcomp τ Y0 = Y := by
    apply WithConv.ofConv_injective
    ext a
    exact (hτ _).trans (productMap_right_apply _ _ a)
  have hcell : X * Y⁻¹ = pointMap r (postcomp τ b0) * (pointMap s (postcomp τ b0'))⁻¹ := by
    have h := congrArg (postcomp τ) hb0
    rw [map_mul, map_mul, map_inv, hτX, hτY, postcomp_pointMap, postcomp_pointMap] at h
    exact eq_mul_inv_of_mul_eq h
  have hτF : φ F = τ (((pointMap r b0)⁻¹ * X0).ofConv f) * φ D ^ n := by
    rw [← hτ, ← hτ, ← map_pow, ← map_mul]
    congr 1
    exact hF.symm
  change φ F = φ D ^ n * _
  rw [hτF, mul_comm, ← postcomp_ofConv_apply, map_mul, map_inv, postcomp_pointMap, hτX,
    ofConv_inv_pointMap_mul_eq r s (hf R) X (hXY.symm.trans hcell)]

/-- Translating the first point by the first subgroup multiplies a cell lift by a power of
the weight of `d`, wherever `D` is a unit. -/
theorem IsCellLift.mul_left {r : A →ₐc[k] C} {s : A →ₐc[k] C'} {χ : C} {d f : A} {n : ℕ}
    {F : A ⊗[k] A} (hF : IsCellLift r s d f n F)
    (hd : d ∈ leftCovariantSubspace (r : A →ₗ[k] C) χ)
    (hdec : ∀ (g : WithConv (A →ₐ[k] R)), IsUnit (g.ofConv d) →
      ∃ b b', g * pointMap s b' = pointMap r b)
    (c : WithConv (C →ₐ[k] R)) (X Y : WithConv (A →ₐ[k] R))
    (hXY : IsUnit (productMap X.ofConv Y.ofConv (cellDifference d))) :
    productMap (pointMap r c * X).ofConv Y.ofConv F =
      c.ofConv χ ^ n * productMap X.ofConv Y.ofConv F := by
  rw [productMap_cellDifference] at hXY
  obtain ⟨b, b', hb⟩ := hdec (X * Y⁻¹) hXY
  have h1 : X * Y⁻¹ = pointMap r b * (pointMap s b')⁻¹ := eq_mul_inv_of_mul_eq hb
  have h2 : pointMap r c * X * Y⁻¹ = pointMap r (c * b) * (pointMap s b')⁻¹ := by
    rw [mul_assoc, h1, map_mul, mul_assoc]
  have h3 : (pointMap r (c * b))⁻¹ * (pointMap r c * X) = (pointMap r b)⁻¹ * X := by
    rw [map_mul]
    group
  rw [hF R _ _ _ _ h2, hF R _ _ _ _ h1, productMap_mul_left_cellDifference r hd, h3, mul_pow]
  ring

/-- Translating the second point by the second subgroup multiplies a cell lift by a power of
the weight of the antipode of `d`, wherever `D` is a unit. -/
theorem IsCellLift.mul_right {r : A →ₐc[k] C} {s : A →ₐc[k] C'} {ψ : C'} {d f : A} {n : ℕ}
    {F : A ⊗[k] A} (hF : IsCellLift r s d f n F)
    (hd' : HopfAlgebra.antipode k d ∈ leftCovariantSubspace (s : A →ₗ[k] C') ψ)
    (hdec : ∀ (g : WithConv (A →ₐ[k] R)), IsUnit (g.ofConv d) →
      ∃ b b', g * pointMap s b' = pointMap r b)
    (e : WithConv (C' →ₐ[k] R)) (X Y : WithConv (A →ₐ[k] R))
    (hXY : IsUnit (productMap X.ofConv Y.ofConv (cellDifference d))) :
    productMap X.ofConv (pointMap s e * Y).ofConv F =
      e.ofConv ψ ^ n * productMap X.ofConv Y.ofConv F := by
  rw [productMap_cellDifference] at hXY
  obtain ⟨b, b', hb⟩ := hdec (X * Y⁻¹) hXY
  have h1 : X * Y⁻¹ = pointMap r b * (pointMap s b')⁻¹ := eq_mul_inv_of_mul_eq hb
  have h2 : X * (pointMap s e * Y)⁻¹ = pointMap r b * (pointMap s (e * b'))⁻¹ := by
    rw [mul_inv_rev, ← mul_assoc, h1, map_mul, mul_inv_rev, mul_assoc]
  rw [hF R _ _ _ _ h2, hF R _ _ _ _ h1, productMap_mul_right_cellDifference s hd', mul_pow]
  ring

/-- Multiplication on `A ⊗ A` is the product map of two copies of the identity. -/
theorem mul'_eq_productMap (z : A ⊗[k] A) :
    LinearMap.mul' k A z = productMap (AlgHom.id k A) (AlgHom.id k A) z := by
  have hmul : productMap (AlgHom.id k A) (AlgHom.id k A) = lmul' k := by
    apply Algebra.TensorProduct.ext'
    intro a b
    simp
  rw [hmul, ← lmul'_toLinearMap, AlgHom.toLinearMap_apply]

/-- The cell difference multiplies to `1`. -/
theorem mul'_cellDifference {d : A} (hε : counit (R := k) d = 1) :
    LinearMap.mul' k A (cellDifference d) = 1 := by
  rw [mul'_eq_productMap]
  exact (productMap_cellDifference (R := A) d (toConv (AlgHom.id k A))
    (toConv (AlgHom.id k A))).trans (by rw [mul_inv_cancel, one_ofConv_apply, hε, map_one])

/-- A cell lift multiplies back to the coordinate it lifts. -/
theorem IsCellLift.mul' {r : A →ₐc[k] C} {s : A →ₐc[k] C'} {d f : A} {n : ℕ}
    {F : A ⊗[k] A} (hF : IsCellLift r s d f n F) (hε : counit (R := k) d = 1) :
    LinearMap.mul' k A F = f := by
  have h := hF A (toConv (AlgHom.id k A)) (toConv (AlgHom.id k A)) 1 1
    (by rw [mul_inv_cancel, map_one, map_one, inv_one, mul_one])
  rw [productMap_cellDifference, mul_inv_cancel, one_ofConv_apply, hε, map_one, one_pow,
    one_mul, map_one, inv_one, one_mul, ofConv_toConv, AlgHom.id_apply] at h
  rw [← h, mul'_eq_productMap]

/-- Multiplying a cell lift by a power of `D` gives a cell lift with a larger exponent. -/
theorem IsCellLift.cellDifference_pow_mul {r : A →ₐc[k] C} {s : A →ₐc[k] C'} {d f : A}
    {n : ℕ} {F : A ⊗[k] A} (hF : IsCellLift r s d f n F) (j : ℕ) :
    IsCellLift r s d f (n + j) (cellDifference d ^ j * F) := by
  intro R _ _ X Y b b' hXY
  rw [map_mul, map_pow, hF R X Y b b' hXY, pow_add]
  ring

/-! ### Universal test points -/

/-- Convolving a restricted point with a point, both read off from one algebra map out of
`C ⊗ A`, evaluates that algebra map on `(r ⊗ id) ∘ Δ`. -/
theorem pointMap_toConv_comp_mul_apply (r : A →ₐc[k] C) (θ : C ⊗[k] A →ₐ[k] R) (a : A) :
    (pointMap r (toConv (θ.comp includeLeft)) * toConv (θ.comp includeRight)).ofConv a =
      θ ((r : A →ₗ[k] C).rTensor A (comul a)) := by
  change (toConv ((θ.comp includeLeft).comp (r : A →ₐ[k] C)) *
    toConv (θ.comp includeRight)).ofConv a = _
  rw [AlgHom.convMul_def, ofConv_toConv]
  simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply]
  induction comul (R := k) a using TensorProduct.inductionOn with
  | tmul x y =>
    rw [Algebra.TensorProduct.map_tmul, lmul'_apply_tmul, LinearMap.rTensor_tmul]
    simp only [AlgHom.comp_apply, includeLeft_apply, includeRight_apply, ← map_mul,
      tmul_mul_tmul, mul_one, one_mul]
    rfl
  | add z z' hz hz' => simp only [map_add, hz, hz']

/-- First universal test for left covariance in the first factor. -/
theorem productMap_testLeft (r : A →ₐc[k] C) (F : A ⊗[k] A) :
    productMap (pointMap r (toConv ((includeLeft : C ⊗[k] A →ₐ[k] (C ⊗[k] A) ⊗[k] A).comp
        includeLeft)) * toConv ((includeLeft : C ⊗[k] A →ₐ[k] (C ⊗[k] A) ⊗[k] A).comp
          includeRight)).ofConv (includeRight : A →ₐ[k] (C ⊗[k] A) ⊗[k] A) F =
      ((r : A →ₗ[k] C).rTensor A ∘ₗ comul).rTensor A F := by
  induction F using TensorProduct.inductionOn with
  | tmul a b =>
    rw [productMap_apply_tmul, pointMap_toConv_comp_mul_apply, LinearMap.rTensor_tmul,
      LinearMap.comp_apply, includeLeft_apply, includeRight_apply, tmul_mul_tmul, mul_one,
      one_mul]
  | add z z' hz hz' => simp only [map_add, hz, hz']

/-- Second universal test for left covariance in the first factor. -/
theorem productMap_testLeft' (μ : C) (F : A ⊗[k] A) :
    ((includeLeft : C ⊗[k] A →ₐ[k] (C ⊗[k] A) ⊗[k] A).comp includeLeft) μ *
        productMap ((includeLeft : C ⊗[k] A →ₐ[k] (C ⊗[k] A) ⊗[k] A).comp includeRight)
          (includeRight : A →ₐ[k] (C ⊗[k] A) ⊗[k] A) F =
      (TensorProduct.mk k C A μ).rTensor A F := by
  induction F using TensorProduct.inductionOn with
  | tmul a b =>
    rw [productMap_apply_tmul, LinearMap.rTensor_tmul, TensorProduct.mk_apply]
    simp only [AlgHom.comp_apply, includeLeft_apply, includeRight_apply, tmul_mul_tmul,
      mul_one, one_mul]
  | add z z' hz hz' => simp only [map_add, mul_add, hz, hz']

/-- First universal test for left covariance in the second factor. -/
theorem productMap_testRight (s : A →ₐc[k] C') (F : A ⊗[k] A) :
    productMap (includeLeft : A →ₐ[k] A ⊗[k] (C' ⊗[k] A))
      (pointMap s (toConv ((includeRight : C' ⊗[k] A →ₐ[k] A ⊗[k] (C' ⊗[k] A)).comp
        includeLeft)) * toConv ((includeRight : C' ⊗[k] A →ₐ[k] A ⊗[k] (C' ⊗[k] A)).comp
          includeRight)).ofConv F =
      ((s : A →ₗ[k] C').rTensor A ∘ₗ comul).lTensor A F := by
  induction F using TensorProduct.inductionOn with
  | tmul a b =>
    rw [productMap_apply_tmul, pointMap_toConv_comp_mul_apply, LinearMap.lTensor_tmul,
      LinearMap.comp_apply, includeLeft_apply, includeRight_apply, tmul_mul_tmul, mul_one,
      one_mul]
  | add z z' hz hz' => simp only [map_add, hz, hz']

/-- Second universal test for left covariance in the second factor. -/
theorem productMap_testRight' (μ : C') (F : A ⊗[k] A) :
    ((includeRight : C' ⊗[k] A →ₐ[k] A ⊗[k] (C' ⊗[k] A)).comp includeLeft) μ *
        productMap (includeLeft : A →ₐ[k] A ⊗[k] (C' ⊗[k] A))
          ((includeRight : C' ⊗[k] A →ₐ[k] A ⊗[k] (C' ⊗[k] A)).comp includeRight) F =
      (TensorProduct.mk k C' A μ).lTensor A F := by
  induction F using TensorProduct.inductionOn with
  | tmul a b =>
    rw [productMap_apply_tmul, LinearMap.lTensor_tmul, TensorProduct.mk_apply]
    simp only [AlgHom.comp_apply, includeLeft_apply, includeRight_apply, tmul_mul_tmul,
      mul_one, one_mul]
  | add z z' hz hz' => simp only [map_add, mul_add, hz, hz']

/-! ### Covariance of cell lifts -/

section Covariance

variable {r : A →ₐc[k] C} {s : A →ₐc[k] C'} {χ : C} {ψ : C'} {d f : A} {n : ℕ}
  {F : A ⊗[k] A}

/-- At any triple of test points, translating a cell lift on the left of its first point
agrees, after multiplying by a power of `D`, with scaling by a power of the weight. -/
theorem IsCellLift.exists_pow_mul_eq_left (hF : IsCellLift r s d f n F)
    (hd : d ∈ leftCovariantSubspace (r : A →ₗ[k] C) χ)
    (hdec : ∀ (R : Type u) [CommRing R] [Algebra k R] (g : WithConv (A →ₐ[k] R)),
      IsUnit (g.ofConv d) → ∃ b b', g * pointMap s b' = pointMap r b)
    (c : WithConv (C →ₐ[k] R)) (X Y : WithConv (A →ₐ[k] R)) :
    ∃ m : ℕ, productMap X.ofConv Y.ofConv (cellDifference d) ^ m *
        productMap (pointMap r c * X).ofConv Y.ofConv F =
      productMap X.ofConv Y.ofConv (cellDifference d) ^ m *
        (c.ofConv χ ^ n * productMap X.ofConv Y.ofConv F) := by
  refine exists_pow_mul_eq_of_forall_isUnit (k := k) fun R' _ _ τ hτ => ?_
  rw [apply_productMap] at hτ
  simp only [apply_productMap, map_mul, map_pow, postcomp_pointMap]
  rw [← postcomp_ofConv_apply]
  exact hF.mul_left hd (hdec R') _ _ _ hτ

/-- At any triple of test points, translating a cell lift on the left of its second point
agrees, after multiplying by a power of `D`, with scaling by a power of the weight. -/
theorem IsCellLift.exists_pow_mul_eq_right (hF : IsCellLift r s d f n F)
    (hd' : HopfAlgebra.antipode k d ∈ leftCovariantSubspace (s : A →ₗ[k] C') ψ)
    (hdec : ∀ (R : Type u) [CommRing R] [Algebra k R] (g : WithConv (A →ₐ[k] R)),
      IsUnit (g.ofConv d) → ∃ b b', g * pointMap s b' = pointMap r b)
    (e : WithConv (C' →ₐ[k] R)) (X Y : WithConv (A →ₐ[k] R)) :
    ∃ m : ℕ, productMap X.ofConv Y.ofConv (cellDifference d) ^ m *
        productMap X.ofConv (pointMap s e * Y).ofConv F =
      productMap X.ofConv Y.ofConv (cellDifference d) ^ m *
        (e.ofConv ψ ^ n * productMap X.ofConv Y.ofConv F) := by
  refine exists_pow_mul_eq_of_forall_isUnit (k := k) fun R' _ _ τ hτ => ?_
  rw [apply_productMap] at hτ
  simp only [apply_productMap, map_mul, map_pow, postcomp_pointMap]
  rw [← postcomp_ofConv_apply]
  exact hF.mul_right hd' (hdec R') _ _ _ hτ

/-- After multiplication by a sufficiently high power of `D`, a cell lift is left covariant
in its first factor. -/
theorem IsCellLift.exists_rTensor_eq (hF : IsCellLift r s d f n F)
    (hd : d ∈ leftCovariantSubspace (r : A →ₗ[k] C) χ)
    (hdec : ∀ (R : Type u) [CommRing R] [Algebra k R] (g : WithConv (A →ₐ[k] R)),
      IsUnit (g.ofConv d) → ∃ b b', g * pointMap s b' = pointMap r b) :
    ∃ m : ℕ, ∀ t : ℕ,
      ((r : A →ₗ[k] C).rTensor A ∘ₗ comul).rTensor A (cellDifference d ^ (m + t) * F) =
        (TensorProduct.mk k C A (χ ^ (n + (m + t)))).rTensor A
          (cellDifference d ^ (m + t) * F) := by
  let c1 : WithConv (C →ₐ[k] (C ⊗[k] A) ⊗[k] A) :=
    toConv ((includeLeft : C ⊗[k] A →ₐ[k] (C ⊗[k] A) ⊗[k] A).comp includeLeft)
  let x1 : WithConv (A →ₐ[k] (C ⊗[k] A) ⊗[k] A) :=
    toConv ((includeLeft : C ⊗[k] A →ₐ[k] (C ⊗[k] A) ⊗[k] A).comp includeRight)
  let y1 : WithConv (A →ₐ[k] (C ⊗[k] A) ⊗[k] A) := toConv includeRight
  obtain ⟨m, hm⟩ := hF.exists_pow_mul_eq_left hd hdec c1 x1 y1
  refine ⟨m, fun t => ?_⟩
  calc ((r : A →ₗ[k] C).rTensor A ∘ₗ comul).rTensor A (cellDifference d ^ (m + t) * F)
      = productMap (pointMap r c1 * x1).ofConv y1.ofConv (cellDifference d ^ (m + t) * F) :=
        (productMap_testLeft r _).symm
    _ = c1.ofConv (χ ^ (n + (m + t))) *
          productMap x1.ofConv y1.ofConv (cellDifference d ^ (m + t) * F) := by
        rw [map_mul, map_pow, productMap_mul_left_cellDifference r hd, map_mul, map_pow,
          map_pow]
        linear_combination c1.ofConv χ ^ (m + t) *
          productMap x1.ofConv y1.ofConv (cellDifference d) ^ t * hm
    _ = (TensorProduct.mk k C A (χ ^ (n + (m + t)))).rTensor A
          (cellDifference d ^ (m + t) * F) :=
        productMap_testLeft' _ _

/-- After multiplication by a sufficiently high power of `D`, a cell lift is left covariant
in its second factor. -/
theorem IsCellLift.exists_lTensor_eq (hF : IsCellLift r s d f n F)
    (hd' : HopfAlgebra.antipode k d ∈ leftCovariantSubspace (s : A →ₗ[k] C') ψ)
    (hdec : ∀ (R : Type u) [CommRing R] [Algebra k R] (g : WithConv (A →ₐ[k] R)),
      IsUnit (g.ofConv d) → ∃ b b', g * pointMap s b' = pointMap r b) :
    ∃ m : ℕ, ∀ t : ℕ,
      ((s : A →ₗ[k] C').rTensor A ∘ₗ comul).lTensor A (cellDifference d ^ (m + t) * F) =
        (TensorProduct.mk k C' A (ψ ^ (n + (m + t)))).lTensor A
          (cellDifference d ^ (m + t) * F) := by
  let e2 : WithConv (C' →ₐ[k] A ⊗[k] (C' ⊗[k] A)) :=
    toConv ((includeRight : C' ⊗[k] A →ₐ[k] A ⊗[k] (C' ⊗[k] A)).comp includeLeft)
  let x2 : WithConv (A →ₐ[k] A ⊗[k] (C' ⊗[k] A)) := toConv includeLeft
  let y2 : WithConv (A →ₐ[k] A ⊗[k] (C' ⊗[k] A)) :=
    toConv ((includeRight : C' ⊗[k] A →ₐ[k] A ⊗[k] (C' ⊗[k] A)).comp includeRight)
  obtain ⟨m, hm⟩ := hF.exists_pow_mul_eq_right hd' hdec e2 x2 y2
  refine ⟨m, fun t => ?_⟩
  calc ((s : A →ₗ[k] C').rTensor A ∘ₗ comul).lTensor A (cellDifference d ^ (m + t) * F)
      = productMap x2.ofConv (pointMap s e2 * y2).ofConv (cellDifference d ^ (m + t) * F) :=
        (productMap_testRight s _).symm
    _ = e2.ofConv (ψ ^ (n + (m + t))) *
          productMap x2.ofConv y2.ofConv (cellDifference d ^ (m + t) * F) := by
        rw [map_mul, map_pow, productMap_mul_right_cellDifference s hd', map_mul, map_pow,
          map_pow]
        linear_combination e2.ofConv ψ ^ (m + t) *
          productMap x2.ofConv y2.ofConv (cellDifference d) ^ t * hm
    _ = (TensorProduct.mk k C' A (ψ ^ (n + (m + t)))).lTensor A
          (cellDifference d ^ (m + t) * F) :=
        productMap_testRight' _ _

end Covariance

/-! ### Exhaustion -/

/-- **Products of covariant coordinates contain `1`.** If `d` is left `r`-covariant of weight
`χ`, its antipode is left `s`-covariant of weight `ψ` and `d` has counit `1`, then `1` is a
sum of products of a left `r`-covariant coordinate of weight `χ` and a left `s`-covariant
coordinate of weight `ψ`. -/
theorem one_mem_mul_leftCovariantSubspace (r : A →ₐc[k] C) (s : A →ₐc[k] C') {χ : C} {ψ : C'}
    {d : A} (hd : d ∈ leftCovariantSubspace (r : A →ₗ[k] C) χ)
    (hd' : HopfAlgebra.antipode k d ∈ leftCovariantSubspace (s : A →ₗ[k] C') ψ)
    (hε : counit (R := k) d = 1) :
    (1 : A) ∈ leftCovariantSubspace (r : A →ₗ[k] C) χ *
      leftCovariantSubspace (s : A →ₗ[k] C') ψ := by
  rw [← mul'_cellDifference hε]
  refine mul'_mem_mul_leftCovariantSubspace _ _ _ _ ?_ ?_
  · refine (productMap_testLeft r _).symm.trans ?_
    refine (productMap_mul_left_cellDifference r hd _ _ _).trans ?_
    exact productMap_testLeft' _ _
  · refine (productMap_testRight s _).symm.trans ?_
    refine (productMap_mul_right_cellDifference s hd' _ _ _).trans ?_
    exact productMap_testRight' _ _

/-- **Exhaustion of invariant coordinates by products of covariant coordinates.** Let `d`
be left `r`-covariant of weight `χ` with antipode left `s`-covariant of weight `ψ` and counit
`1`, and suppose every point at which `d` is a unit factors as `i(b) i'(b')⁻¹` (in the form
`g i'(b') = i(b)`). Then every coordinate `f` that is left invariant under the pairs of
points with `i(c) = i'(c')` is, for some `N`, a sum of products of a left `r`-covariant
coordinate of weight `χ ^ N` and a left `s`-covariant coordinate of weight `ψ ^ N`. -/
theorem exists_mem_mul_leftCovariantSubspace (r : A →ₐc[k] C) (s : A →ₐc[k] C') {χ : C}
    {ψ : C'} {d f : A} (hd : d ∈ leftCovariantSubspace (r : A →ₗ[k] C) χ)
    (hd' : HopfAlgebra.antipode k d ∈ leftCovariantSubspace (s : A →ₗ[k] C') ψ)
    (hε : counit (R := k) d = 1)
    (hdec : ∀ (R : Type u) [CommRing R] [Algebra k R] (g : WithConv (A →ₐ[k] R)),
      IsUnit (g.ofConv d) → ∃ b b', g * pointMap s b' = pointMap r b)
    (hf : ∀ (R : Type u) [CommRing R] [Algebra k R] (c : WithConv (C →ₐ[k] R))
      (c' : WithConv (C' →ₐ[k] R)), pointMap r c = pointMap s c' →
        ∀ g : WithConv (A →ₐ[k] R), (pointMap r c * g).ofConv f = g.ofConv f) :
    ∃ N : ℕ, f ∈ leftCovariantSubspace (r : A →ₗ[k] C) (χ ^ N) *
      leftCovariantSubspace (s : A →ₗ[k] C') (ψ ^ N) := by
  obtain ⟨n, F, hF⟩ := exists_isCellLift r s hd hd' hε hdec hf
  obtain ⟨m₁, h₁⟩ := hF.exists_rTensor_eq hd hdec
  obtain ⟨m₂, h₂⟩ := hF.exists_lTensor_eq hd' hdec
  refine ⟨n + (m₁ + m₂), ?_⟩
  rw [← (hF.cellDifference_pow_mul (m₁ + m₂)).mul' hε]
  have e₂ := h₂ m₁
  rw [add_comm m₂ m₁] at e₂
  exact mul'_mem_mul_leftCovariantSubspace _ _ _ _ (h₁ m₂) e₂

end Cell

/-! ### Density of the cell -/

section Density

variable {k A R : Type u} [Field k] [CommRing A] [HopfAlgebra k A] [CommRing R] [Algebra k R]
  {C C' : Type u} [CommRing C] [HopfAlgebra k C] [CommRing C'] [HopfAlgebra k C']

attribute [local instance] pointGroup

/-- The value of a coordinate at `i(b) i'(b')⁻¹` is the value at `(b, b')` of its pullback
along `(p, q) ↦ i(p) i'(q)⁻¹`. -/
theorem ofConv_pointMap_mul_inv_apply (r : A →ₐc[k] C) (s : A →ₐc[k] C')
    (b : WithConv (C →ₐ[k] R)) (b' : WithConv (C' →ₐ[k] R)) (w : A) :
    (pointMap r b * (pointMap s b')⁻¹).ofConv w =
      Algebra.TensorProduct.productMap b.ofConv b'.ofConv
        (differenceComorphism (r : A →ₐ[k] C) (s : A →ₐ[k] C') w) := by
  change (toConv (b.ofConv.comp (r : A →ₐ[k] C)) *
    toConv ((b'.ofConv.comp (s : A →ₐ[k] C')).comp
      (HopfAlgebra.antipodeAlgHom k A))).ofConv w = _
  rw [AlgHom.convMul_def, ofConv_toConv]
  simp only [differenceComorphism, AlgHom.comp_apply, Bialgebra.comulAlgHom_apply]
  induction comul (R := k) w using TensorProduct.inductionOn with
  | tmul x y =>
    rw [Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul,
      Algebra.TensorProduct.lmul'_apply_tmul, Algebra.TensorProduct.productMap_apply_tmul]
    rfl
  | add z z' hz hz' => simp only [map_add, hz, hz']

/-- **Density of the cell.** If every point at which `d` is a unit factors as `i(b) i'(b')⁻¹`
(in the form `g i'(b') = i(b)`) and `d` is a non-zero-divisor, then the comorphism of
`(p, q) ↦ i(p) i'(q)⁻¹` is injective. -/
theorem injective_differenceComorphism (r : A →ₐc[k] C) (s : A →ₐc[k] C') {d : A}
    (hdec : ∀ (R : Type u) [CommRing R] [Algebra k R] (g : WithConv (A →ₐ[k] R)),
      IsUnit (g.ofConv d) → ∃ b b', g * pointMap s b' = pointMap r b)
    (hreg : IsLeftRegular d) :
    Function.Injective (differenceComorphism (r : A →ₐ[k] C) (s : A →ₐ[k] C')) := by
  rw [injective_iff_map_eq_zero]
  intro w hw
  let R0 := Localization.Away d
  let g0 : WithConv (A →ₐ[k] R0) := toConv (IsScalarTower.toAlgHom k A R0)
  obtain ⟨b, b', hb⟩ := hdec R0 g0 (IsLocalization.Away.algebraMap_isUnit d)
  have hw0 : algebraMap A R0 w = algebraMap A R0 0 := by
    have h := ofConv_pointMap_mul_inv_apply r s b b' w
    rw [← eq_mul_inv_of_mul_eq hb, hw, map_zero] at h
    rw [map_zero]
    exact h
  obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq d hw0
  exact (hreg.pow n) hn

end Density

end CellExhaustion

end Langlands.GroupScheme.Chevalley
