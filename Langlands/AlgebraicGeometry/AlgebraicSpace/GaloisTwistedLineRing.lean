import Langlands.AlgebraicGeometry.AlgebraicSpace.GaloisTwistedLineAlgebra

/-!
# The rings of the Galois-twisted line

`A = K'[X]` is the ring of the affine `K'`-line, viewed over `K`. The relation ring is
`B = A × A[1/X]`. The two ring maps `tStar sStar : A → B` are the identity on the first factor.
On the second factor, `tStar` is the localization map and `sStar` is the localization map after
conjugating the coefficients by `σ`. A ring map `φ : B → Γ` is determined by the two composites
`x = φ ∘ tStar` and `z = φ ∘ sStar`. Pairs `(x, z)` arise this way exactly when `x` and `z` agree
on `K[X]` and the element `e + (1 - e) x(X)` is a unit, where `e` is the idempotent of
`splitIdem` attached to the restrictions of `x` and `z` to `K'`.
-/

noncomputable section

universe u

open Polynomial

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace GaloisTwistedLine

variable {K K' : Type u} [Field K] [Field K'] [Algebra K K'] (D : QuadraticConj K K')

variable (K') in
/-- The punctured line ring `K'[X, 1/X]`. -/
abbrev PuncturedRing := Localization.Away (X : K'[X])

variable (K') in
/-- The relation ring `K'[X] × K'[X, 1/X]`. -/
abbrev RelationRing := K'[X] × PuncturedRing K'

/-- Conjugation of coefficients. -/
def conjPoly : K'[X] →+* K'[X] := Polynomial.mapRingHom D.σ.toRingHom

@[simp]
theorem conjPoly_C (a : K') : conjPoly D (C a) = C (D.σ a) := by
  simp [conjPoly]

@[simp]
theorem conjPoly_X : conjPoly D X = X := by
  simp [conjPoly]

theorem conjPoly_conjPoly (p : K'[X]) : conjPoly D (conjPoly D p) = p := by
  have : (conjPoly D).comp (conjPoly D) = RingHom.id _ := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [D.invol]
    · simp
  exact congrArg (fun f : K'[X] →+* K'[X] => f p) this

theorem powers_le_comap_conjPoly :
    Submonoid.powers (X : K'[X]) ≤ (Submonoid.powers (X : K'[X])).comap (conjPoly D) := by
  rintro _ ⟨n, rfl⟩
  exact ⟨n, by simp⟩

/-- Conjugation of coefficients on the punctured line ring. -/
def conjPunct : PuncturedRing K' →+* PuncturedRing K' :=
  IsLocalization.map (M := Submonoid.powers (X : K'[X])) (T := Submonoid.powers (X : K'[X]))
    (PuncturedRing K') (conjPoly D) (powers_le_comap_conjPoly D)

theorem conjPunct_algebraMap (p : K'[X]) :
    conjPunct D (algebraMap K'[X] (PuncturedRing K') p) =
      algebraMap K'[X] (PuncturedRing K') (conjPoly D p) :=
  IsLocalization.map_eq _ _

/-- The first relation map: identity and localization. -/
def tStar : K'[X] →+* RelationRing K' :=
  (RingHom.id _).prod (algebraMap K'[X] (PuncturedRing K'))

/-- The second relation map: identity, and conjugation followed by localization. -/
def sStar : K'[X] →+* RelationRing K' :=
  (RingHom.id _).prod ((algebraMap K'[X] (PuncturedRing K')).comp (conjPoly D))

/-- The involution of the relation ring exchanging the two relation maps. -/
def swapStar : RelationRing K' →+* RelationRing K' :=
  (RingHom.fst _ _).prod ((conjPunct D).comp (RingHom.snd _ _))

theorem swapStar_comp_tStar : (swapStar D).comp tStar = sStar D :=
  RingHom.ext fun p => Prod.ext rfl (conjPunct_algebraMap D p)

theorem swapStar_comp_sStar : (swapStar D).comp (sStar D) = tStar :=
  RingHom.ext fun p => Prod.ext rfl (by
    change conjPunct D (algebraMap _ _ (conjPoly D p)) = algebraMap _ _ p
    rw [conjPunct_algebraMap, conjPoly_conjPoly])

theorem conjPunct_conjPunct : (conjPunct D).comp (conjPunct D) = RingHom.id _ := by
  apply IsLocalization.ringHom_ext (Submonoid.powers (X : K'[X]))
  refine RingHom.ext fun p => ?_
  simp only [RingHom.comp_apply, RingHom.id_apply, conjPunct_algebraMap, conjPoly_conjPoly]

theorem swapStar_swapStar : (swapStar D).comp (swapStar D) = RingHom.id _ :=
  RingHom.ext fun p => Prod.ext rfl (congrArg (fun f => f p.2) (conjPunct_conjPunct D))

/-! ### Corner ring maps -/

variable {Γ : Type*} [CommRing Γ]

/-- The ring map `(a, c) ↦ e f(a) + (1 - e) g(c)` for an idempotent `e`. -/
def cornerHom {R S : Type*} [Semiring R] [Semiring S] (e : Γ) (he : IsIdempotentElem e)
    (f : R →+* Γ) (g : S →+* Γ) : R × S →+* Γ where
  toFun p := e * f p.1 + (1 - e) * g p.2
  map_one' := by simp
  map_mul' p q := by
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul]
    have he' : e * e = e := he
    linear_combination (-(f p.1 * f q.1 - f p.1 * g q.2 - g p.2 * f q.1 + g p.2 * g q.2)) * he'
  map_zero' := by simp
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, map_add]
    ring

theorem cornerHom_apply {R S : Type*} [Semiring R] [Semiring S] (e : Γ) (he : IsIdempotentElem e)
    (f : R →+* Γ) (g : S →+* Γ) (p : R × S) :
    cornerHom e he f g p = e * f p.1 + (1 - e) * g p.2 := rfl

/-! ### The idempotent and the unit attached to a pair of points -/

/-- The idempotent of a pair of points of the line. -/
def pairIdem (x z : K'[X] →+* Γ) : Γ := splitIdem D (x.comp C) (z.comp C)

/-- The element that is a unit exactly on related pairs. -/
def pairUnit (x z : K'[X] →+* Γ) : Γ := pairIdem D x z + (1 - pairIdem D x z) * x X

variable (K) in
/-- Two points of the line over the same point of the `K`-line. -/
def SameBase (x z : K'[X] →+* Γ) : Prop :=
  (∀ k : K, x (C (algebraMap K K' k)) = z (C (algebraMap K K' k))) ∧ x X = z X

/-- A ring map out of the relation ring gives a pair of points over the same base point,
whose idempotent is the image of `(1, 0)` and whose unit element is a unit. -/
theorem sameBase_of_hom (φ : RelationRing K' →+* Γ) :
    SameBase K (φ.comp tStar) (φ.comp (sStar D)) := by
  refine ⟨fun k => ?_, ?_⟩
  · change φ (tStar _) = φ (sStar D _)
    congr 1
    refine Prod.ext rfl ?_
    simp [tStar, sStar, AlgEquiv.commutes]
  · change φ (tStar _) = φ (sStar D _)
    congr 1
    refine Prod.ext rfl ?_
    simp [tStar, sStar]

theorem one_sub_hom_one_zero (φ : RelationRing K' →+* Γ) : (1 : Γ) - φ (1, 0) = φ (0, 1) := by
  rw [← map_one φ, ← map_sub]
  congr 1
  ext <;> simp

theorem pairIdem_of_hom (φ : RelationRing K' →+* Γ) :
    φ (1, 0) = pairIdem D (φ.comp tStar) (φ.comp (sStar D)) := by
  have hb := (sameBase_of_hom D φ).1
  apply splitIdem_unique (D := D) (μ₁ := (φ.comp tStar).comp C) (μ₂ := (φ.comp (sStar D)).comp C)
    (fun k => hb k)
  · intro α
    change φ (1, 0) * (φ (sStar D (C α)) - φ (tStar (C α))) = 0
    rw [← map_sub, ← map_mul]
    convert map_zero φ using 2
    ext
    · simp [tStar, sStar]
    · simp
  · intro α
    have h1 := one_sub_hom_one_zero φ
    change (1 - φ (1, 0)) * (φ (sStar D (C α)) - φ (tStar (C (D.σ α)))) = 0
    rw [h1, ← map_sub, ← map_mul]
    convert map_zero φ using 2
    ext
    · simp
    · simp [tStar, sStar]

theorem isUnit_pairUnit_of_hom (φ : RelationRing K' →+* Γ) :
    IsUnit (pairUnit D (φ.comp tStar) (φ.comp (sStar D))) := by
  have h : pairUnit D (φ.comp tStar) (φ.comp (sStar D)) =
      φ (1, algebraMap K'[X] (PuncturedRing K') X) := by
    rw [pairUnit, ← pairIdem_of_hom]
    have h1 := one_sub_hom_one_zero φ
    rw [h1]
    change φ (1, 0) + φ (0, 1) * φ (tStar X) = _
    rw [← map_mul, ← map_add]
    congr 1
    ext
    · simp [tStar]
    · simp [tStar]
  rw [h]
  apply IsUnit.map
  exact (Prod.isUnit_iff).mpr ⟨isUnit_one, IsLocalization.Away.algebraMap_isUnit _⟩

/-! ### Existence and uniqueness of ring maps out of the relation ring -/

/-- The substitution `X ↦ 1`. -/
def evOne : K'[X] →+* K'[X] := Polynomial.eval₂RingHom C 1

@[simp]
theorem evOne_X : evOne (X : K'[X]) = 1 := by simp [evOne]

@[simp]
theorem evOne_C (a : K') : evOne (C a) = C a := by simp [evOne]

/-- The substitution `X ↦ 1` on the punctured ring. -/
def evOnePunct : PuncturedRing K' →+* K'[X] :=
  IsLocalization.Away.lift (X : K'[X]) (g := evOne) (by rw [evOne_X]; exact isUnit_one)

theorem evOnePunct_algebraMap (p : K'[X]) :
    evOnePunct (algebraMap K'[X] (PuncturedRing K') p) = evOne p :=
  IsLocalization.Away.lift_eq _ _ _

variable (K') in
/-- The section of the second projection given by `X ↦ 1` on the first factor. -/
def jHom : PuncturedRing K' →+* RelationRing K' := evOnePunct.prod (RingHom.id _)

theorem relationRing_decomp (p : RelationRing K') :
    p = (1, 0) * tStar p.1 + jHom K' p.2 - (1, 0) * tStar (evOnePunct p.2) := by
  ext <;> simp [tStar, jHom]

/-- **Uniqueness.** A ring map out of the relation ring is determined by its two composites. -/
theorem hom_ext {φ ψ : RelationRing K' →+* Γ} (ht : φ.comp tStar = ψ.comp tStar)
    (hs : φ.comp (sStar D) = ψ.comp (sStar D)) : φ = ψ := by
  have he : φ (1, 0) = ψ (1, 0) := by
    rw [pairIdem_of_hom D φ, pairIdem_of_hom D ψ, ht, hs]
  have ht' : ∀ a, φ (tStar a) = ψ (tStar a) := fun a => congrArg (fun f => f a) ht
  have hj : φ.comp (jHom K') = ψ.comp (jHom K') := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (X : K'[X]))
    refine RingHom.ext fun a => ?_
    have hdec : jHom K' (algebraMap K'[X] (PuncturedRing K') a) =
        (1, 0) * tStar (evOne a) + (tStar a - (1, 0) * tStar a) := by
      ext <;> simp [tStar, jHom, evOnePunct_algebraMap]
    simp only [RingHom.comp_apply]
    rw [hdec, map_add, map_add, map_sub, map_sub, map_mul, map_mul, map_mul, map_mul, he,
      ht', ht']
  ext1 p
  rw [relationRing_decomp p, map_sub, map_sub, map_add, map_add, map_mul, map_mul, map_mul,
    map_mul, he, ht', ht']
  congr 2
  exact congrArg (fun f => f p.2) hj

section Existence

variable {x z : K'[X] →+* Γ} (hb : SameBase K x z)

include hb in
theorem pairIdem_isIdempotentElem : IsIdempotentElem (pairIdem D x z) :=
  splitIdem_isIdempotentElem (D := D) (μ₁ := x.comp C) (μ₂ := z.comp C) hb.1

/-- The point `x` modified to send `X` to `1` on the idempotent `pairIdem`. -/
def modPoint : K'[X] →+* Γ :=
  (cornerHom (pairIdem D x z) (pairIdem_isIdempotentElem D hb) (x.comp evOne) x).comp
    ((RingHom.id _).prod (RingHom.id _))

theorem modPoint_apply (a : K'[X]) :
    modPoint D hb a = pairIdem D x z * x (evOne a) + (1 - pairIdem D x z) * x a := rfl

theorem modPoint_X : modPoint D hb X = pairUnit D x z := by
  rw [modPoint_apply, evOne_X, map_one, mul_one, pairUnit]

variable (hu : IsUnit (pairUnit D x z))

/-- **Existence.** The ring map out of the relation ring with composites `x` and `z`. -/
def relHom : RelationRing K' →+* Γ :=
  cornerHom (pairIdem D x z) (pairIdem_isIdempotentElem D hb) x
    (IsLocalization.Away.lift (X : K'[X]) (g := modPoint D hb) (by rw [modPoint_X]; exact hu))

theorem relHom_snd_algebraMap (a : K'[X]) :
    IsLocalization.Away.lift (X : K'[X]) (g := modPoint D hb)
        (by rw [modPoint_X]; exact hu) (algebraMap K'[X] (PuncturedRing K') a) =
      modPoint D hb a :=
  IsLocalization.Away.lift_eq _ _ _

theorem relHom_comp_tStar : (relHom D hb hu).comp tStar = x := by
  refine RingHom.ext fun a => ?_
  have he : pairIdem D x z * pairIdem D x z = pairIdem D x z := pairIdem_isIdempotentElem D hb
  change pairIdem D x z * x a + (1 - pairIdem D x z) *
    IsLocalization.Away.lift (X : K'[X]) (g := modPoint D hb) _
      (algebraMap K'[X] (PuncturedRing K') a) = x a
  rw [relHom_snd_algebraMap D hb hu, modPoint_apply]
  linear_combination (x a - x (evOne a)) * he

theorem relHom_comp_sStar : (relHom D hb hu).comp (sStar D) = z := by
  have he : pairIdem D x z * pairIdem D x z = pairIdem D x z := pairIdem_isIdempotentElem D hb
  have hval : ∀ a, (relHom D hb hu).comp (sStar D) a =
      pairIdem D x z * x a + (1 - pairIdem D x z) * x (conjPoly D a) := by
    intro a
    change pairIdem D x z * x a + (1 - pairIdem D x z) *
      IsLocalization.Away.lift (X : K'[X]) (g := modPoint D hb) _
        (algebraMap K'[X] (PuncturedRing K') (conjPoly D a)) = _
    rw [relHom_snd_algebraMap D hb hu, modPoint_apply]
    linear_combination (x (conjPoly D a) - x (evOne (conjPoly D a))) * he
  apply Polynomial.ringHom_ext
  · intro α
    rw [hval, conjPoly_C]
    have h1 := splitIdem_mul (D := D) (μ₁ := x.comp C) (μ₂ := z.comp C) hb.1 α
    have h2 := one_sub_splitIdem_mul (D := D) (μ₁ := x.comp C) (μ₂ := z.comp C) hb.1 α
    change pairIdem D x z * (z (C α) - x (C α)) = 0 at h1
    change (1 - pairIdem D x z) * (z (C α) - x (C (D.σ α))) = 0 at h2
    linear_combination -h1 - h2
  · rw [hval, conjPoly_X, ← hb.2]
    ring

end Existence

/-! ### Reflexivity, symmetry and transitivity of the relation on pairs -/

section Relation

variable {x y z : K'[X] →+* Γ}

theorem pairIdem_self : pairIdem D x x = 1 :=
  (splitIdem_unique (D := D) (μ₁ := x.comp C) (μ₂ := x.comp C) (fun _ => rfl)
    (fun _ => by simp) (fun _ => by simp)).symm

theorem pairIdem_trans (hxy : SameBase K x y) (hyz : SameBase K y z) :
    pairIdem D x z = pairIdem D x y * pairIdem D y z +
      (1 - pairIdem D x y) * (1 - pairIdem D y z) := by
  have hxz : ∀ k : K, (x.comp C) (algebraMap K K' k) = (z.comp C) (algebraMap K K' k) :=
    fun k => (hxy.1 k).trans (hyz.1 k)
  symm
  apply splitIdem_unique (D := D) hxz
  · intro α
    have a1 := splitIdem_mul (D := D) (μ₁ := x.comp C) (μ₂ := y.comp C) hxy.1 α
    have a2 := one_sub_splitIdem_mul (D := D) (μ₁ := x.comp C) (μ₂ := y.comp C) hxy.1 (D.σ α)
    have b1 := splitIdem_mul (D := D) (μ₁ := y.comp C) (μ₂ := z.comp C) hyz.1 α
    have b2 := one_sub_splitIdem_mul (D := D) (μ₁ := y.comp C) (μ₂ := z.comp C) hyz.1 α
    rw [D.invol] at a2
    change pairIdem D x y * _ = 0 at a1
    change (1 - pairIdem D x y) * _ = 0 at a2
    change pairIdem D y z * _ = 0 at b1
    change (1 - pairIdem D y z) * _ = 0 at b2
    linear_combination (pairIdem D y z) * a1 + (pairIdem D x y) * b1 +
      (1 - pairIdem D y z) * a2 + (1 - pairIdem D x y) * b2
  · intro α
    have a1 := splitIdem_mul (D := D) (μ₁ := x.comp C) (μ₂ := y.comp C) hxy.1 (D.σ α)
    have a2 := one_sub_splitIdem_mul (D := D) (μ₁ := x.comp C) (μ₂ := y.comp C) hxy.1 α
    have b1 := splitIdem_mul (D := D) (μ₁ := y.comp C) (μ₂ := z.comp C) hyz.1 α
    have b2 := one_sub_splitIdem_mul (D := D) (μ₁ := y.comp C) (μ₂ := z.comp C) hyz.1 α
    change pairIdem D x y * _ = 0 at a1
    change (1 - pairIdem D x y) * _ = 0 at a2
    change pairIdem D y z * _ = 0 at b1
    change (1 - pairIdem D y z) * _ = 0 at b2
    linear_combination (1 - pairIdem D y z) * a1 + (pairIdem D x y) * b2 +
      (pairIdem D y z) * a2 + (1 - pairIdem D x y) * b1

theorem isUnit_pairUnit_trans (hxy : SameBase K x y) (hyz : SameBase K y z)
    (h₁ : IsUnit (pairUnit D x y)) (h₂ : IsUnit (pairUnit D y z)) :
    IsUnit (pairUnit D x z) := by
  have ha : pairIdem D x y * pairIdem D x y = pairIdem D x y := pairIdem_isIdempotentElem D hxy
  have hb : pairIdem D y z * pairIdem D y z = pairIdem D y z := pairIdem_isIdempotentElem D hyz
  obtain ⟨v1, hv1⟩ := h₁.exists_right_inv
  obtain ⟨v2, hv2⟩ := h₂.exists_right_inv
  unfold pairUnit at hv1 hv2 ⊢
  rw [pairIdem_trans D hxy hyz]
  rw [← hxy.2] at hv2
  generalize pairIdem D x y = a at *
  generalize pairIdem D y z = b at *
  generalize x X = f at *
  have hPf : a * (1 - b) * f * v2 = a * (1 - b) := by
    linear_combination (a * (1 - b)) * hv2 + (a * (v2 - f * v2)) * hb
  have hQf : (1 - a) * b * f * v1 = (1 - a) * b := by
    linear_combination (b * (1 - a)) * hv1 + (b * (v1 - f * v1)) * ha
  refine IsUnit.of_mul_eq_one (a * b + (1 - a) * (1 - b) + a * (1 - b) * v2 +
    (1 - a) * b * v1) ?_
  linear_combination ((2 * b - 1) ^ 2 - v2 * (1 - b) ^ 2 - v1 * b ^ 2 -
      f * ((1 - b) ^ 2 + b ^ 2) + f * v2 * (1 - b) ^ 2 - f * v1 * b * (1 - b) -
      f * v2 * b * (1 - b) + f * v1 * b) * ha +
    (1 - v2 * a ^ 2 - v1 * (1 - a) ^ 2 - f * (a ^ 2 + (1 - a) ^ 2) + f * v2 * a +
      f * v1 * (1 - a) ^ 2) * hb + hPf + hQf

end Relation

end GaloisTwistedLine

end Langlands.AlgebraicGeometry.AlgebraicSpace
