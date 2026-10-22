import Langlands.AbelianScheme.Tate.TwistDivisibility

noncomputable section
open scoped TensorProduct

namespace Langlands.TateTwist.Divisibility
universe u v w
variable (R : Type u) [CommRing R]

/-- Rationalization of the actual roots-of-unity inverse limit. -/
abbrev Rational (P : ℕ → Prop) := ℚ ⊗[ℤ] Integral R P

/-- The full rational Tate twist. -/
abbrev RationalFull := Rational R (fun _ => True)

/-- The prime-to-`p` rational Tate twist. -/
abbrev RationalAway (p : ℕ) := Rational R (fun n => Nat.Coprime n p)

/-- Comparison with the convention having the rational factor on the right. -/
def rationalTensorComm (P : ℕ → Prop) :
    Rational R P ≃ₗ[ℤ] Integral R P ⊗[ℤ] ℚ :=
  TensorProduct.comm ℤ ℚ (Integral R P)

@[simp] lemma rationalTensorComm_tmul (P : ℕ → Prop) (q : ℚ) (x : Integral R P) :
    rationalTensorComm R P (q ⊗ₜ[ℤ] x) = x ⊗ₜ[ℤ] q := rfl

/-- The canonical map to the rationalization; no injectivity is asserted here. -/
def toRational (P : ℕ → Prop) : Integral R P →ₗ[ℤ] Rational R P :=
  TensorProduct.mk ℤ ℚ (Integral R P) 1

variable {R} {S : Type v} {T : Type w} [CommRing S] [CommRing T]

/-- Scalar extension of the map induced on actual roots of unity. -/
def rationalMap (P : ℕ → Prop) (f : R →+* S) :
    Rational R P →ₗ[ℚ] Rational S P :=
  (map P f).toIntLinearMap.baseChange ℚ

@[simp] lemma rationalMap_tmul (P : ℕ → Prop) (f : R →+* S)
    (q : ℚ) (x : Integral R P) :
    rationalMap P f (q ⊗ₜ[ℤ] x) = q ⊗ₜ[ℤ] map P f x := rfl

@[simp] lemma rationalMap_id (P : ℕ → Prop) :
    rationalMap P (RingHom.id R) = LinearMap.id := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro q x
  simp

lemma rationalMap_comp (P : ℕ → Prop) (f : R →+* S) (g : S →+* T) :
    rationalMap P (g.comp f) = (rationalMap P g).comp (rationalMap P f) := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro q x
  simp [map_comp]

@[simp] lemma rationalMap_toRational (P : ℕ → Prop) (f : R →+* S) (x : Integral R P) :
    rationalMap P f (toRational R P x) = toRational S P (map P f x) := rfl

variable (R)

/-- Restriction to the prime-to-`p` indices after rationalization. -/
def rationalRestrictAway (p : ℕ) : RationalFull R →ₗ[ℚ] RationalAway R p :=
  (restrictAway R p).toIntLinearMap.baseChange ℚ

@[simp] lemma rationalRestrictAway_tmul (p : ℕ) (q : ℚ) (x : Full R) :
    rationalRestrictAway R p (q ⊗ₜ[ℤ] x) = q ⊗ₜ[ℤ] restrictAway R p x := rfl

@[simp] lemma rationalRestrictAway_toRational (p : ℕ) (x : Full R) :
    rationalRestrictAway R p (toRational R (fun _ => True) x) =
      toRational R (fun n => Nat.Coprime n p) (restrictAway R p x) := rfl

variable {R}

lemma rationalRestrictAway_map (p : ℕ) (f : R →+* S) :
    (rationalRestrictAway S p).comp (rationalMap (fun _ => True) f) =
      (rationalMap (fun n => Nat.Coprime n p) f).comp (rationalRestrictAway R p) := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro q x
  simp [restrictAway_map]

/-- A ring equivalence acts invertibly on coherent families of actual roots. -/
def mapEquiv (P : ℕ → Prop) (f : R ≃+* S) : Integral R P ≃+ Integral S P where
  toFun := map P f.toRingHom
  map_add' := (map P f.toRingHom).map_add
  invFun := map P f.symm.toRingHom
  left_inv x := by
    change ((map P f.symm.toRingHom).comp (map P f.toRingHom)) x = x
    rw [← map_comp, RingEquiv.symm_toRingHom_comp_toRingHom, map_id]
    rfl
  right_inv x := by
    change ((map P f.toRingHom).comp (map P f.symm.toRingHom)) x = x
    rw [← map_comp, RingEquiv.toRingHom_comp_symm_toRingHom, map_id]
    rfl

@[simp] lemma mapEquiv_apply (P : ℕ → Prop) (f : R ≃+* S) (x : Integral R P) :
    mapEquiv P f x = map P f.toRingHom x := rfl

/-- The same equivalence is linear over the full profinite-integer ring. -/
def fullLinearEquiv (P : ℕ → Prop) (f : R ≃+* S) :
    Integral R P ≃ₗ[Global.ProfiniteIntegerRing] Integral S P :=
  { mapEquiv P f with map_smul' := (fullLinearMap P f.toRingHom).map_smul' }

/-- On the away limit it is also linear over the prime-to-`p` scalar ring. -/
def awayLinearEquiv (p : ℕ) (f : R ≃+* S) :
    Away R p ≃ₗ[Global.PrimeToProfiniteIntegerRing p] Away S p :=
  { mapEquiv (fun n => Nat.Coprime n p) f with
    map_smul' := (awayLinearMap p f.toRingHom).map_smul' }

/-- A ring equivalence acts invertibly on the rationalization. -/
def rationalMapEquiv (P : ℕ → Prop) (f : R ≃+* S) :
    Rational R P ≃ₗ[ℚ] Rational S P :=
  (mapEquiv P f).toIntLinearEquiv.baseChange ℤ ℚ _ _

@[simp] lemma rationalMapEquiv_tmul (P : ℕ → Prop) (f : R ≃+* S)
    (q : ℚ) (x : Integral R P) :
    rationalMapEquiv P f (q ⊗ₜ[ℤ] x) = q ⊗ₜ[ℤ] map P f.toRingHom x := rfl

lemma rationalMapEquiv_toLinearMap (P : ℕ → Prop) (f : R ≃+* S) :
    (rationalMapEquiv P f).toLinearMap = rationalMap P f.toRingHom := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro q x
  rfl

variable (R)

/-- The natural action applies each ring automorphism to every root of unity. -/
def automorphismAction (P : ℕ → Prop) :
    (R ≃+* R) →* (Integral R P ≃ₗ[Global.ProfiniteIntegerRing] Integral R P) where
  toFun := fullLinearEquiv P
  map_one' := by
    apply LinearEquiv.ext
    intro x
    exact DFunLike.congr_fun (map_id P) x
  map_mul' f g := by
    apply LinearEquiv.ext
    intro x
    exact DFunLike.congr_fun (map_comp P g.toRingHom f.toRingHom) x

/-- The natural away action with its prime-to-`p` linear structure. -/
def awayAutomorphismAction (p : ℕ) :
    (R ≃+* R) →* (Away R p ≃ₗ[Global.PrimeToProfiniteIntegerRing p] Away R p) where
  toFun := awayLinearEquiv p
  map_one' := by
    apply LinearEquiv.ext
    intro x
    exact DFunLike.congr_fun (map_id (fun n => Nat.Coprime n p)) x
  map_mul' f g := by
    apply LinearEquiv.ext
    intro x
    exact DFunLike.congr_fun
      (map_comp (fun n => Nat.Coprime n p) g.toRingHom f.toRingHom) x

@[simp] lemma evaluation_automorphismAction (P : ℕ → Prop) (f : R ≃+* R)
    (n : GroupScheme.Tate.Index P) (x : Integral R P) :
    evaluation R P n (automorphismAction R P f x) =
      levelMap f.toRingHom n.val (evaluation R P n x) := rfl

lemma continuous_automorphismAction (P : ℕ → Prop) (f : R ≃+* R) :
    Continuous (automorphismAction R P f) := continuous_map P f.toRingHom

lemma continuous_awayAutomorphismAction (p : ℕ) (f : R ≃+* R) :
    Continuous (awayAutomorphismAction R p f) :=
  continuous_map (fun n => Nat.Coprime n p) f.toRingHom

lemma awayAutomorphismAction_eq (p : ℕ) (f : R ≃+* R) (x : Away R p) :
    awayAutomorphismAction R p f x =
      automorphismAction R (fun n => Nat.Coprime n p) f x := rfl

lemma restrictAway_automorphismAction (p : ℕ) (f : R ≃+* R) (x : Full R) :
    restrictAway R p (automorphismAction R (fun _ => True) f x) =
      awayAutomorphismAction R p f (restrictAway R p x) := rfl

/-- Scalar extension retains the natural action rather than choosing a basis. -/
def rationalAutomorphismAction (P : ℕ → Prop) :
    (R ≃+* R) →* (Rational R P ≃ₗ[ℚ] Rational R P) where
  toFun := rationalMapEquiv P
  map_one' := by
    apply LinearEquiv.toLinearMap_injective
    change (rationalMapEquiv P (RingEquiv.refl R)).toLinearMap = LinearMap.id
    rw [rationalMapEquiv_toLinearMap]
    exact rationalMap_id P
  map_mul' f g := by
    apply LinearEquiv.toLinearMap_injective
    change (rationalMapEquiv P (f * g)).toLinearMap =
      (rationalMapEquiv P f).toLinearMap.comp (rationalMapEquiv P g).toLinearMap
    simp only [rationalMapEquiv_toLinearMap]
    exact rationalMap_comp P g.toRingHom f.toRingHom

@[simp] lemma rationalAutomorphismAction_tmul (P : ℕ → Prop) (f : R ≃+* R)
    (q : ℚ) (x : Integral R P) :
    rationalAutomorphismAction R P f (q ⊗ₜ[ℤ] x) =
      q ⊗ₜ[ℤ] automorphismAction R P f x := rfl

@[simp] lemma rationalAutomorphismAction_toRational (P : ℕ → Prop) (f : R ≃+* R)
    (x : Integral R P) :
    rationalAutomorphismAction R P f (toRational R P x) =
      toRational R P (automorphismAction R P f x) := rfl

lemma rationalRestrictAway_automorphismAction (p : ℕ) (f : R ≃+* R)
    (x : RationalFull R) :
    rationalRestrictAway R p (rationalAutomorphismAction R (fun _ => True) f x) =
      rationalAutomorphismAction R (fun n => Nat.Coprime n p) f
        (rationalRestrictAway R p x) :=
  LinearMap.congr_fun (rationalRestrictAway_map p f.toRingHom) x

section Galois
variable (K : Type*) (L : Type*) [Field K] [Field L] [Algebra K L]

/-- The actual field automorphism action on the integral root limit. -/
def galoisAction (P : ℕ → Prop) :
    Gal(L/K) →* (Integral L P ≃ₗ[Global.ProfiniteIntegerRing] Integral L P) :=
  (automorphismAction L P).comp (MulSemiringAction.toRingAut Gal(L/K) L)

/-- The same field automorphisms act linearly over the away scalar ring. -/
def awayGaloisAction (p : ℕ) :
    Gal(L/K) →* (Away L p ≃ₗ[Global.PrimeToProfiniteIntegerRing p] Away L p) :=
  (awayAutomorphismAction L p).comp (MulSemiringAction.toRingAut Gal(L/K) L)

/-- The actual field automorphism action after rationalization. -/
def rationalGaloisAction (P : ℕ → Prop) :
    Gal(L/K) →* (Rational L P ≃ₗ[ℚ] Rational L P) :=
  (rationalAutomorphismAction L P).comp (MulSemiringAction.toRingAut Gal(L/K) L)

end Galois
end Langlands.TateTwist.Divisibility

namespace Langlands.TateTwist

/-- The full rational roots-of-unity twist. -/
abbrev RationalFull (R : Type*) [CommRing R] := Divisibility.RationalFull R

/-- The prime-to-`p` rational roots-of-unity twist. -/
abbrev RationalAway (R : Type*) [CommRing R] (p : ℕ) := Divisibility.RationalAway R p

end Langlands.TateTwist
