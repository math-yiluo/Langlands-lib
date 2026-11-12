import Langlands.Shimura.Unitary.CentralExchangeSplitting
import Langlands.Shimura.Unitary.Adelic
import Mathlib.NumberTheory.NumberField.CMField
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Similitude points over coefficient rings on which an imaginary quadratic field splits

Let `L` be an imaginary quadratic field, `A` an `L`-algebra and `σ` a
`ℚ`-linear involution of `A` restricting to complex conjugation on `L`. For a
commutative `L`-algebra `S`, the tensor algebra `S ⊗[ℚ] A` has a central
idempotent exchanged with its complement by `σ`, and the similitude points of
`σ` over `S` are the units of `S ⊗[L] A` times the units of `S`.
-/

noncomputable section

open scoped TensorProduct
open NumberField

set_option autoImplicit false

universe u v w z

namespace Langlands.Shimura.ImaginaryQuadraticSplit

variable (L : Type u) [Field L] [NumberField L] [IsCMField L] [Algebra.IsQuadraticExtension ℚ L]

local notation "conj" => IsCMField.complexConj L

omit [Algebra.IsQuadraticExtension ℚ L] in
theorem exists_complexConj_ne : ∃ t : L, conj t ≠ t := by
  by_contra! h
  exact IsCMField.complexConj_ne_one (K := L) (AlgEquiv.ext h)

/-- A fixed element of `L` not fixed by complex conjugation. -/
def generator : L := (exists_complexConj_ne L).choose

omit [Algebra.IsQuadraticExtension ℚ L] in
theorem complexConj_generator_ne : conj (generator L) ≠ generator L :=
  (exists_complexConj_ne L).choose_spec

omit [Algebra.IsQuadraticExtension ℚ L] in
theorem generator_sub_ne_zero : generator L - conj (generator L) ≠ 0 :=
  sub_ne_zero.mpr (complexConj_generator_ne L).symm

/-- Every element of `L` is a rational combination of `1` and the generator. -/
theorem exists_rat_combination (t : L) :
    ∃ a b : ℚ, t = (a : L) + (b : L) * generator L := by
  have hli : LinearIndependent ℚ ![(1 : L), generator L] := by
    rw [LinearIndependent.pair_iff]
    intro s r hsr
    by_cases hr : r = 0
    · subst hr
      refine ⟨?_, rfl⟩
      simpa using hsr
    · exfalso
      have hg : generator L = ((-s / r : ℚ) : L) := by
        rw [Rat.smul_def, Rat.smul_def, mul_one] at hsr
        have hr' : (r : L) ≠ 0 := Rat.cast_ne_zero.mpr hr
        push_cast
        field_simp
        linear_combination hsr
      apply complexConj_generator_ne L
      rw [hg, map_ratCast]
  have hspan := hli.span_eq_top_of_card_eq_finrank (by
    rw [Fintype.card_fin, Algebra.IsQuadraticExtension.finrank_eq_two ℚ L])
  have ht : t ∈ Submodule.span ℚ (Set.range ![(1 : L), generator L]) := by
    rw [hspan]; trivial
  rw [Matrix.range_cons_cons_empty, Submodule.mem_span_pair] at ht
  obtain ⟨a, b, hab⟩ := ht
  exact ⟨a, b, by rw [← hab, Rat.smul_def, Rat.smul_def, mul_one]⟩

section Idempotent

variable {L}
variable {Z : Type v} [CommRing Z] (i j : L →+* Z)

/-- The idempotent of a commutative ring receiving two homomorphisms from `L`,
which is `1` on the factor where they agree and `0` on the factor where the
second one is the conjugate of the first. -/
def idempotent : Z :=
  i (generator L - conj (generator L))⁻¹ * (j (generator L) - i (conj (generator L)))

omit [IsCMField L] [Algebra.IsQuadraticExtension ℚ L] in
theorem ratCast_eq (q : ℚ) : j (q : L) = i (q : L) := by
  have h : j.comp (Rat.castHom L) = i.comp (Rat.castHom L) := Subsingleton.elim _ _
  exact RingHom.congr_fun h q

omit [Algebra.IsQuadraticExtension ℚ L] in
theorem inv_mul_self : i (generator L - conj (generator L))⁻¹ *
    i (generator L - conj (generator L)) = 1 := by
  rw [← map_mul, inv_mul_cancel₀ (generator_sub_ne_zero L), map_one]

/-- The two conjugate values of the generator are the roots of its quadratic
relation. -/
theorem generator_relation :
    (j (generator L) - i (conj (generator L))) * (j (generator L) - i (generator L)) = 0 := by
  obtain ⟨a, b, hab⟩ := exists_rat_combination L (generator L ^ 2)
  set g := generator L
  have hconj : conj g ^ 2 = (a : L) + (b : L) * conj g := by
    have := congrArg conj hab
    simpa [map_add, map_mul, map_pow, map_ratCast] using this
  have hsum : g + conj g = (b : L) := by
    have hd : g - conj g ≠ 0 := generator_sub_ne_zero L
    have hprod : (g - conj g) * (g + conj g - b) = 0 := by
      linear_combination hab - hconj
    rcases mul_eq_zero.mp hprod with h | h
    · exact absurd h hd
    · linear_combination h
  have hprodL : g * conj g = -(a : L) := by
    linear_combination g * hsum - hab
  have hJ : j g ^ 2 = i (a : L) + i (b : L) * j g := by
    rw [← map_pow, hab, map_add, map_mul, ratCast_eq i j, ratCast_eq i j]
  have hs : i g + i (conj g) = i (b : L) := by rw [← map_add, hsum]
  have hp : i g * i (conj g) = -i (a : L) := by rw [← map_mul, hprodL, map_neg]
  linear_combination hJ - j g * hs + hp

theorem idempotent_mul_generator :
    idempotent i j * j (generator L) = idempotent i j * i (generator L) := by
  have h := generator_relation i j
  unfold idempotent
  linear_combination i (generator L - conj (generator L))⁻¹ * h

theorem idempotent_mul_apply (t : L) : idempotent i j * j t = idempotent i j * i t := by
  obtain ⟨a, b, rfl⟩ := exists_rat_combination L t
  rw [map_add, map_mul, map_add, map_mul, ratCast_eq i j, ratCast_eq i j]
  linear_combination i (b : L) * idempotent_mul_generator i j

theorem idempotent_mul_self : idempotent i j * idempotent i j = idempotent i j := by
  have h := idempotent_mul_generator i j
  have hinv := inv_mul_self (L := L) i
  have hdiff : i (generator L - conj (generator L)) = i (generator L) - i (conj (generator L)) :=
    map_sub _ _ _
  set e := idempotent i j
  have he : e = i (generator L - conj (generator L))⁻¹ *
      (j (generator L) - i (conj (generator L))) := rfl
  calc e * e = i (generator L - conj (generator L))⁻¹ *
        (e * j (generator L) - e * i (conj (generator L))) := by rw [he]; ring
    _ = e * (i (generator L - conj (generator L))⁻¹ * i (generator L - conj (generator L))) := by
        rw [h, hdiff]; ring
    _ = e := by rw [hinv, mul_one]

theorem idempotent_conj (j' : L →+* Z) (hj' : ∀ t, j' t = j (conj t)) :
    idempotent i j' = 1 - idempotent i j := by
  obtain ⟨a, b, hab⟩ := exists_rat_combination L (generator L ^ 2)
  have hsum : generator L + conj (generator L) = (b : L) := by
    have hconj : conj (generator L) ^ 2 = (a : L) + (b : L) * conj (generator L) := by
      have := congrArg conj hab
      simpa [map_add, map_mul, map_pow, map_ratCast] using this
    have hprod : (generator L - conj (generator L)) *
        (generator L + conj (generator L) - b) = 0 := by
      linear_combination hab - hconj
    rcases mul_eq_zero.mp hprod with h | h
    · exact absurd h (generator_sub_ne_zero L)
    · linear_combination h
  have hjc : j (conj (generator L)) = i (b : L) - j (generator L) := by
    rw [← ratCast_eq i j, ← map_sub, ← hsum, add_sub_cancel_left]
  have hic : i (conj (generator L)) = i (b : L) - i (generator L) := by
    rw [← map_sub, ← hsum, add_sub_cancel_left]
  have hinv := inv_mul_self (L := L) i
  rw [map_sub, hic] at hinv
  unfold idempotent
  rw [hj', hjc, hic]
  linear_combination hinv

omit [Algebra.IsQuadraticExtension ℚ L] in
theorem idempotent_map {Q : Type w} [Ring Q] (φ : Z →+* Q) (hφ : ∀ t, φ (j t) = φ (i t)) :
    φ (idempotent i j) = 1 := by
  unfold idempotent
  rw [map_mul, map_sub, hφ, ← map_sub, ← map_mul, ← map_sub, ← map_mul,
    inv_mul_cancel₀ (generator_sub_ne_zero L), map_one, map_one]

end Idempotent

section Tensor

variable (A : Type v) [Ring A] [Algebra ℚ A] [Algebra L A]
variable (S : Type w) [CommRing S] [Algebra ℚ S] [Algebra L S]

/-- The scalar homomorphism from `L` into the center of `S ⊗[ℚ] A`, through `S`. -/
def scalarHom : L →+* Subring.center (S ⊗[ℚ] A) where
  toFun t := ⟨algebraMap S (S ⊗[ℚ] A) (algebraMap L S t),
    Subring.mem_center_iff.mpr fun x => (Algebra.commutes _ x).symm⟩
  map_one' := Subtype.ext (by simp; rfl)
  map_mul' _ _ := Subtype.ext (by simp)
  map_zero' := Subtype.ext (by simp)
  map_add' _ _ := Subtype.ext (by simp [TensorProduct.add_tmul])

omit [Algebra ℚ S] in
theorem tmul_central [Algebra ℚ S] (c : A) (hc : ∀ a : A, a * c = c * a) (x : S ⊗[ℚ] A) :
    x * ((1 : S) ⊗ₜ[ℚ] c) = ((1 : S) ⊗ₜ[ℚ] c) * x := by
  induction x using TensorProduct.inductionOn with
  | tmul s a => simp [Algebra.TensorProduct.tmul_mul_tmul, hc a]
  | add x y hx hy => rw [add_mul, mul_add, hx, hy]

/-- The homomorphism from `L` into the center of `S ⊗[ℚ] A`, through `A`. -/
def algebraHom : L →+* Subring.center (S ⊗[ℚ] A) where
  toFun t := ⟨(1 : S) ⊗ₜ[ℚ] algebraMap L A t,
    Subring.mem_center_iff.mpr fun x =>
      tmul_central A S _ (fun a => (Algebra.commutes t a).symm) x⟩
  map_one' := Subtype.ext (by simp [Algebra.TensorProduct.one_def])
  map_mul' _ _ := Subtype.ext (by simp [Algebra.TensorProduct.tmul_mul_tmul])
  map_zero' := Subtype.ext (by simp)
  map_add' _ _ := Subtype.ext (by simp [TensorProduct.tmul_add])

omit [NumberField L] [IsCMField L] [Algebra.IsQuadraticExtension ℚ L] [Algebra L A] in
@[simp] theorem scalarHom_val (t : L) :
    (scalarHom L A S t : S ⊗[ℚ] A) = algebraMap S (S ⊗[ℚ] A) (algebraMap L S t) := rfl

omit [NumberField L] [IsCMField L] [Algebra.IsQuadraticExtension ℚ L] [Algebra L S] in
@[simp] theorem algebraHom_val (t : L) :
    (algebraHom L A S t : S ⊗[ℚ] A) = (1 : S) ⊗ₜ[ℚ] algebraMap L A t := rfl

/-- The central idempotent of `S ⊗[ℚ] A` cutting out the factor on which the two
actions of `L` agree. -/
def tensorIdempotent : S ⊗[ℚ] A :=
  (idempotent (scalarHom L A S) (algebraHom L A S) : Subring.center (S ⊗[ℚ] A))

omit [Algebra.IsQuadraticExtension ℚ L] in
theorem tensorIdempotent_mul_comm (x : S ⊗[ℚ] A) :
    tensorIdempotent L A S * x = x * tensorIdempotent L A S :=
  ((Subring.mem_center_iff.mp
    (idempotent (scalarHom L A S) (algebraHom L A S)).property) x).symm

theorem tensorIdempotent_mul_self :
    tensorIdempotent L A S * tensorIdempotent L A S = tensorIdempotent L A S :=
  congrArg Subtype.val (idempotent_mul_self (scalarHom L A S) (algebraHom L A S))

theorem tensorIdempotent_mul_algebraMap (t : L) :
    tensorIdempotent L A S * ((1 : S) ⊗ₜ[ℚ] algebraMap L A t) =
      tensorIdempotent L A S * algebraMap S (S ⊗[ℚ] A) (algebraMap L S t) :=
  congrArg Subtype.val (idempotent_mul_apply (scalarHom L A S) (algebraHom L A S) t)

/-- The projection `s ⊗ a ↦ s ⊗ a` from the rational to the `L`-linear tensor product. -/
def projection : S ⊗[ℚ] A →ₐ[S] S ⊗[L] A :=
  Algebra.TensorProduct.lift (Algebra.TensorProduct.includeLeft (R := L) (S := S))
    (Algebra.TensorProduct.includeRight (R := L) (A := S) (B := A)).toRingHom.toRatAlgHom
    (fun s a => by
      change Commute (s ⊗ₜ[L] (1 : A)) ((1 : S) ⊗ₜ[L] a)
      simp [Commute, SemiconjBy, Algebra.TensorProduct.tmul_mul_tmul])

omit [NumberField L] [IsCMField L] [Algebra.IsQuadraticExtension ℚ L] in
@[simp] theorem projection_tmul (s : S) (a : A) :
    projection L A S (s ⊗ₜ[ℚ] a) = s ⊗ₜ[L] a := by
  change s ⊗ₜ[L] (1 : A) * (1 : S) ⊗ₜ[L] a = _
  simp [Algebra.TensorProduct.tmul_mul_tmul]

omit [NumberField L] [IsCMField L] [Algebra.IsQuadraticExtension ℚ L] in
theorem projection_algebraHom (t : L) :
    projection L A S ((1 : S) ⊗ₜ[ℚ] algebraMap L A t) =
      projection L A S (algebraMap S (S ⊗[ℚ] A) (algebraMap L S t)) := by
  rw [projection_tmul, AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply,
    Algebra.algebraMap_self, RingHom.id_apply, Algebra.algebraMap_eq_smul_one (A := A) t,
    Algebra.algebraMap_eq_smul_one (A := S) t, TensorProduct.smul_tmul]

theorem projection_tensorIdempotent : projection L A S (tensorIdempotent L A S) = 1 :=
  idempotent_map (scalarHom L A S) (algebraHom L A S)
    ((projection L A S).toRingHom.comp (Subring.center (S ⊗[ℚ] A)).subtype)
    (fun t => projection_algebraHom L A S t)

/-- The additive map `s ⊗ a ↦ e (s ⊗ a)`, balanced over `L` because the two
actions of `L` agree after multiplication by `e`. -/
def liftAddHom : S ⊗[L] A →+ S ⊗[ℚ] A :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun s => AddMonoidHom.mk'
      (fun a => tensorIdempotent L A S * (s ⊗ₜ[ℚ] a))
      (fun a a' => by rw [TensorProduct.tmul_add, mul_add]))
      (fun s s' => by ext a; simp [TensorProduct.add_tmul, mul_add]))
    (fun t s a => by
      change tensorIdempotent L A S * ((t • s) ⊗ₜ[ℚ] a) =
        tensorIdempotent L A S * (s ⊗ₜ[ℚ] (t • a))
      have hs : (t • s) ⊗ₜ[ℚ] a =
          algebraMap S (S ⊗[ℚ] A) (algebraMap L S t) * (s ⊗ₜ[ℚ] a) := by
        rw [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul,
          Algebra.algebraMap_self, RingHom.id_apply, one_mul, Algebra.smul_def]
      have ha : s ⊗ₜ[ℚ] (t • a) = ((1 : S) ⊗ₜ[ℚ] algebraMap L A t) * (s ⊗ₜ[ℚ] a) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, Algebra.smul_def]
      rw [hs, ha, ← mul_assoc, ← mul_assoc, tensorIdempotent_mul_algebraMap])

@[simp] theorem liftAddHom_tmul (s : S) (a : A) :
    liftAddHom L A S (s ⊗ₜ[L] a) = tensorIdempotent L A S * (s ⊗ₜ[ℚ] a) := rfl

theorem liftAddHom_mul (x y : S ⊗[L] A) :
    liftAddHom L A S (x * y) = liftAddHom L A S x * liftAddHom L A S y := by
  induction x using TensorProduct.inductionOn with
  | add x x' hx hx' => rw [add_mul, map_add, map_add, hx, hx', add_mul]
  | tmul s a =>
    induction y using TensorProduct.inductionOn with
    | add y y' hy hy' => rw [mul_add, map_add, map_add, hy, hy', mul_add]
    | tmul s' a' =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, liftAddHom_tmul, liftAddHom_tmul,
        liftAddHom_tmul, ← Algebra.TensorProduct.tmul_mul_tmul,
        ← mul_assoc (tensorIdempotent L A S * _) (tensorIdempotent L A S) _,
        mul_assoc (tensorIdempotent L A S) _ (tensorIdempotent L A S),
        ← tensorIdempotent_mul_comm L A S (s ⊗ₜ[ℚ] a),
        ← mul_assoc (tensorIdempotent L A S) (tensorIdempotent L A S),
        tensorIdempotent_mul_self, mul_assoc]

theorem projection_liftAddHom (x : S ⊗[L] A) :
    projection L A S (liftAddHom L A S x) = x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul s a => rw [liftAddHom_tmul, map_mul, projection_tensorIdempotent, one_mul,
      projection_tmul]

theorem liftAddHom_projection (x : S ⊗[ℚ] A) :
    liftAddHom L A S (projection L A S x) = tensorIdempotent L A S * x := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, map_add, hx, hy, mul_add]
  | tmul s a => rw [projection_tmul, liftAddHom_tmul]

end Tensor

section Involution

variable {A : Type v} [Ring A] [Algebra ℚ A] [Algebra L A]

/-- The rational involution `σ` restricts to complex conjugation on `L`: it is
of the second kind with respect to `L`. -/
def IsConjugationOn (σ : AlgebraInvolution ℚ A) : Prop :=
  ∀ t : L, σ (algebraMap L A t) = algebraMap L A (conj t)

variable {L}
variable (σ : AlgebraInvolution ℚ A)
variable (S : Type w) [CommRing S] [Algebra ℚ S] [Algebra L S]

theorem baseChange_tensorIdempotent (hσ : IsConjugationOn L σ) :
    σ.baseChange S (tensorIdempotent L A S) = 1 - tensorIdempotent L A S := by
  let j' : L →+* Subring.center (S ⊗[ℚ] A) :=
    (algebraHom L A S).comp (conj : L →+* L)
  have h := congrArg Subtype.val
    (idempotent_conj (scalarHom L A S) (algebraHom L A S) j' (fun _ => rfl))
  rw [AddSubgroupClass.coe_sub, Subring.coe_one] at h
  rw [tensorIdempotent, ← h]
  simp only [idempotent, Subring.coe_mul, AddSubgroupClass.coe_sub, scalarHom_val,
    algebraHom_val, j', RingHom.comp_apply]
  rw [(σ.baseChange S).apply_mul, (σ.baseChange S).linear.map_sub,
    AlgebraInvolution.apply_algebraMap, AlgebraInvolution.apply_algebraMap,
    AlgebraInvolution.baseChange_tmul, hσ, Algebra.commutes]
  rfl

/-- The central idempotent splitting of the scalar-extended involution. -/
def splitting (hσ : IsConjugationOn L σ) :
    AlgebraInvolution.CentralExchangeSplitting (σ.baseChange S) (S ⊗[L] A) where
  idempotent := tensorIdempotent L A S
  idempotent_mul_self := tensorIdempotent_mul_self L A S
  idempotent_mul_comm := tensorIdempotent_mul_comm L A S
  involution_idempotent := baseChange_tensorIdempotent σ S hσ
  projection := (projection L A S).toRingHom
  lift := liftAddHom L A S
  lift_mul := liftAddHom_mul L A S
  projection_lift := projection_liftAddHom L A S
  lift_projection := liftAddHom_projection L A S

/-- The similitude points of `σ` over a commutative `L`-algebra `S` are the units of
`S ⊗[L] A` times the units of `S`: a point is sent to the image of its algebra unit
under `s ⊗ a ↦ s ⊗ a` and to its multiplier. -/
def pointsEquiv (hσ : IsConjugationOn L σ) : σ.Points S ≃* (S ⊗[L] A)ˣ × Sˣ :=
  (splitting σ S hσ).similitudesEquiv

@[simp] theorem pointsEquiv_fst_val (hσ : IsConjugationOn L σ) (g : σ.Points S) :
    ((pointsEquiv σ S hσ g).1 : S ⊗[L] A) = projection L A S g.1.1 := rfl

@[simp] theorem pointsEquiv_snd (hσ : IsConjugationOn L σ) (g : σ.Points S) :
    (pointsEquiv σ S hσ g).2 = AlgebraInvolution.Points.multiplier σ S g := rfl

theorem pointsEquiv_symm_val (hσ : IsConjugationOn L σ) (p : (S ⊗[L] A)ˣ × Sˣ) :
    (((pointsEquiv σ S hσ).symm p).1.1 : S ⊗[ℚ] A) =
      liftAddHom L A S p.1 + (p.2 : S) • σ.baseChange S (liftAddHom L A S ↑p.1⁻¹) := rfl

variable {S}
variable {S' : Type z} [CommRing S'] [Algebra ℚ S'] [Algebra L S']

omit [NumberField L] [IsCMField L] [Algebra.IsQuadraticExtension ℚ L] in
/-- The projection commutes with change of `L`-algebra coefficients. -/
theorem projection_changeCoefficients (f : S →ₐ[L] S') (x : S ⊗[ℚ] A) :
    projection L A S' (AlgebraInvolution.changeCoefficients (A := A)
        (f : S →+* S').toRatAlgHom x) =
      Algebra.TensorProduct.map f (AlgHom.id L A) (projection L A S x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | tmul s a =>
    rw [AlgebraInvolution.changeCoefficients_tmul, projection_tmul, projection_tmul,
      Algebra.TensorProduct.map_tmul]
    rfl

/-- Naturality of `pointsEquiv` in the `L`-algebra of coefficients. -/
theorem pointsEquiv_pointsMap (hσ : IsConjugationOn L σ) (f : S →ₐ[L] S') (g : σ.Points S) :
    pointsEquiv σ S' hσ (σ.pointsMap (f : S →+* S').toRatAlgHom g) =
      (Units.map (Algebra.TensorProduct.map f (AlgHom.id L A)).toMonoidHom
          (pointsEquiv σ S hσ g).1,
        Units.map f.toMonoidHom (pointsEquiv σ S hσ g).2) := by
  apply Prod.ext
  · apply Units.ext
    exact projection_changeCoefficients f (g.1.1 : S ⊗[ℚ] A)
  · apply Units.ext
    rfl

end Involution

end Langlands.Shimura.ImaginaryQuadraticSplit
