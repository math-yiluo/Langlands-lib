import Langlands.Cohomology.Profinite.Characters
import Mathlib.Algebra.Module.CharacterModule
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality

namespace Langlands.ProfiniteCohomology

open Function

namespace QZ

theorem finite_setOf_nsmul_eq_zero {n : ℕ} (hn : 0 < n) : {x : QZ | n • x = 0}.Finite :=
  AddCircle.finite_torsion (1 : ℚ) hn

noncomputable def toReal : QZ →+ AddCircle (1 : ℝ) :=
  (QuotientAddGroup.map (AddSubgroup.zmultiples (1 : ℚ)) (AddSubgroup.zmultiples (1 : ℝ))
    (Rat.castHom ℝ).toAddMonoidHom (by
      rw [AddSubgroup.zmultiples_le]
      exact ⟨1, by simp⟩)).comp toAddCircle.toAddMonoidHom

theorem toReal_mk (q : ℚ) : toReal (mk q) = ((q : ℝ) : AddCircle (1 : ℝ)) :=
  rfl

theorem toReal_injective : Injective toReal := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨q, rfl⟩ := mk_surjective x
  rw [toReal_mk, AddCircle.coe_eq_zero_iff] at hx
  obtain ⟨n, hn⟩ := hx
  rw [mk_eq_zero_iff]
  refine ⟨n, ?_⟩
  have : ((n : ℚ) : ℝ) = (q : ℝ) := by simpa using hn
  exact_mod_cast this

noncomputable def toComplex (x : QZ) : ℂ :=
  (AddCircle.toCircle (toReal x) : ℂ)

theorem toComplex_injective : Injective toComplex := fun _ _ h =>
  toReal_injective (AddCircle.injective_toCircle one_ne_zero (Circle.ext h))

@[simp]
theorem toComplex_zero : toComplex 0 = 1 := by
  simp [toComplex]

theorem toComplex_add (x y : QZ) : toComplex (x + y) = toComplex x * toComplex y := by
  simp [toComplex, AddCircle.toCircle_add]

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]

noncomputable def toAddChar (f : G →+ QZ) : AddChar G ℂ where
  toFun g := toComplex (f g)
  map_zero_eq_one' := by simp
  map_add_eq_mul' a b := by simp [toComplex_add]

@[simp]
theorem toAddChar_apply (f : G →+ QZ) (g : G) : toAddChar f g = toComplex (f g) :=
  rfl

theorem toAddChar_injective : Injective (toAddChar (G := G)) := fun _ _ h =>
  AddMonoidHom.ext fun a => toComplex_injective (DFunLike.congr_fun h a)

theorem toAddChar_add (f f' : G →+ QZ) : toAddChar (f + f') = toAddChar f + toAddChar f' := by
  ext a
  simp [toComplex_add]

theorem exists_comp_eq_of_injective (i : G →+ H) (hi : Injective i) (f : G →+ QZ) :
    ∃ g : H →+ QZ, g.comp i = f := by
  obtain ⟨g, hg⟩ := (Module.Baer.of_divisible (AddCircle (1 : ℚ))).extension_property_addMonoidHom
    i hi (toAddCircle.toAddMonoidHom.comp f)
  refine ⟨toAddCircle.symm.toAddMonoidHom.comp g, AddMonoidHom.ext fun a => ?_⟩
  have h1 := DFunLike.congr_fun hg a
  simp only [AddMonoidHom.coe_comp, comp_apply, AddEquiv.coe_toAddMonoidHom] at h1 ⊢
  rw [h1, AddEquiv.symm_apply_apply]

theorem exists_comp_eq_of_ker_le (h : G →+ H) (χ : G →+ QZ) (hχ : h.ker ≤ χ.ker) :
    ∃ ψ : H →+ QZ, ψ.comp h = χ := by
  let χ₀ : h.range →+ QZ := (QuotientAddGroup.lift h.ker χ hχ).comp
    (QuotientAddGroup.quotientKerEquivRange h).symm.toAddMonoidHom
  obtain ⟨ψ, hψ⟩ := exists_comp_eq_of_injective h.range.subtype h.range.subtype_injective χ₀
  refine ⟨ψ, AddMonoidHom.ext fun a => ?_⟩
  have h1 := DFunLike.congr_fun hψ ⟨h a, a, rfl⟩
  have h2 : (QuotientAddGroup.quotientKerEquivRange h).symm ⟨h a, a, rfl⟩ =
      (a : G ⧸ h.ker) := by
    rw [AddEquiv.symm_apply_eq]
    rfl
  simp only [AddMonoidHom.coe_comp, comp_apply, AddSubgroup.coe_subtype, χ₀,
    AddEquiv.coe_toAddMonoidHom, h2] at h1
  simpa using h1

theorem exists_apply_ne_zero {a : G} (ha : a ≠ 0) : ∃ f : G →+ QZ, f a ≠ 0 := by
  obtain ⟨c, hc⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero ha
  refine ⟨toAddCircle.symm.toAddMonoidHom.comp (c : G →+ AddCircle (1 : ℚ)), fun h => hc ?_⟩
  exact (AddEquiv.map_eq_zero_iff toAddCircle.symm).mp h

variable (G) in

def evalHom : G →+ ((G →+ QZ) →+ QZ) where
  toFun a :=
    { toFun := fun f => f a
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  map_zero' := by ext f; simp
  map_add' a b := by ext f; simp

@[simp]
theorem evalHom_apply (a : G) (f : G →+ QZ) : evalHom G a f = f a :=
  rfl

theorem evalHom_injective : Injective (evalHom G) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra hne
  obtain ⟨f, hf⟩ := exists_apply_ne_zero hne
  exact hf (DFunLike.congr_fun ha f)

instance [Finite G] : Finite (G →+ QZ) :=
  Finite.of_injective _ toAddChar_injective

theorem card_hom_le [Finite G] : Nat.card (G →+ QZ) ≤ Nat.card G := by
  have := Fintype.ofFinite G
  calc Nat.card (G →+ QZ) ≤ Nat.card (AddChar G ℂ) :=
        Nat.card_le_card_of_injective _ toAddChar_injective
    _ ≤ Nat.card G := by
        rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
        exact AddChar.card_addChar_le G ℂ

theorem card_hom [Finite G] : Nat.card (G →+ QZ) = Nat.card G :=
  card_hom_le.antisymm <| (Nat.card_le_card_of_injective _ evalHom_injective).trans card_hom_le

variable (G) in

noncomputable def addCharEquiv [Finite G] : (G →+ QZ) ≃+ AddChar G ℂ :=
  AddEquiv.ofBijective
    (AddMonoidHom.mk' toAddChar toAddChar_add)
    (by
      have := Fintype.ofFinite G
      refine toAddChar_injective.bijective_of_nat_card_le ?_
      rw [card_hom, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, AddChar.card_eq])

@[simp]
theorem addCharEquiv_apply [Finite G] (f : G →+ QZ) (a : G) :
    addCharEquiv G f a = toComplex (f a) :=
  rfl

end QZ

namespace QZDual

variable {N : Type*} [AddCommGroup N] [TopologicalSpace N] [DiscreteTopology N]

noncomputable def addCharEquiv [Finite N] : QZDual N ≃+ AddChar N ℂ :=
  toAddMonoidHomEquiv.trans (QZ.addCharEquiv N)

@[simp]
theorem addCharEquiv_apply [Finite N] (χ : QZDual N) (a : N) :
    addCharEquiv χ a = QZ.toComplex (χ a) :=
  rfl

instance [Finite N] : Finite (QZDual N) :=
  Finite.of_injective _ (toAddMonoidHomEquiv (A := N)).injective

theorem card_eq [Finite N] : Nat.card (QZDual N) = Nat.card N :=
  (Nat.card_congr (toAddMonoidHomEquiv (A := N)).toEquiv).trans QZ.card_hom

end QZDual

end Langlands.ProfiniteCohomology

noncomputable section

namespace Langlands.ProfiniteCohomology

section Annihilator

variable {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]

/-- The dual of a finite abelian group with values in `ℚ/ℤ` has as many elements as the group. -/
theorem card_addMonoidHom_rationalModIntegers [Finite X] :
    Nat.card (X →+ Langlands.ClassFieldTheory.Local.RationalModIntegers) = Nat.card X := by
  refine (Nat.card_congr ?_).trans (QZ.card_hom (G := X))
  exact
    { toFun := fun f => QZ.toRationalModIntegers.symm.toAddMonoidHom.comp f
      invFun := fun g => QZ.toRationalModIntegers.toAddMonoidHom.comp g
      left_inv := fun f => by ext; simp
      right_inv := fun g => by ext; simp }

/-- For a pairing `P : X × Y → ℚ/ℤ` of finite groups identifying `Y` with the dual of `X`, the
annihilator of a subgroup `S ⊆ X` has `|X|/|S|` elements. -/
theorem card_annihilator_mul_card [Finite X]
    (P : X →+ Y →+ Langlands.ClassFieldTheory.Local.RationalModIntegers)
    (hP : Function.Bijective P.flip) (S : AddSubgroup X) :
    Nat.card {y : Y // ∀ x ∈ S, P x y = 0} * Nat.card S = Nat.card X := by
  have e1 : {y : Y // ∀ x ∈ S, P x y = 0} ≃
      {f : X →+ Langlands.ClassFieldTheory.Local.RationalModIntegers // ∀ x ∈ S, f x = 0} :=
    (Equiv.ofBijective _ hP).subtypeEquiv fun y => Iff.rfl
  have e2 : {f : X →+ Langlands.ClassFieldTheory.Local.RationalModIntegers // ∀ x ∈ S, f x = 0} ≃
      (X ⧸ S →+ Langlands.ClassFieldTheory.Local.RationalModIntegers) :=
    { toFun := fun f => QuotientAddGroup.lift S f.1 fun x hx => f.2 x hx
      invFun := fun g => ⟨g.comp (QuotientAddGroup.mk' S), fun x hx => by
        simp [(QuotientAddGroup.eq_zero_iff x).2 hx]⟩
      left_inv := fun f => Subtype.ext (AddMonoidHom.ext fun x => rfl)
      right_inv := fun g => by
        refine AddMonoidHom.ext fun q => ?_
        induction q using QuotientAddGroup.induction_on
        rfl }
  rw [Nat.card_congr (e1.trans e2), card_addMonoidHom_rationalModIntegers,
    ← AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup]

end Annihilator

section Orthogonal

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B] (P : A →+ B →+ QZ)

/-- The right orthogonal `X^⊥ = {b ∈ B | P a b = 0 for all a ∈ X}` of a subgroup `X ⊆ A`. -/
def rightOrthogonal (X : AddSubgroup A) : AddSubgroup B where
  carrier := {b | ∀ a ∈ X, P a b = 0}
  add_mem' {b b'} hb hb' a ha := by
    change P a (b + b') = 0
    rw [map_add, hb a ha, hb' a ha, add_zero]
  zero_mem' a _ := map_zero (P a)
  neg_mem' {b} hb a ha := by
    change P a (-b) = 0
    rw [map_neg, hb a ha, neg_zero]

theorem mem_rightOrthogonal {X : AddSubgroup A} {b : B} :
    b ∈ rightOrthogonal P X ↔ ∀ a ∈ X, P a b = 0 :=
  Iff.rfl

/-- The left orthogonal `⊥Y = {a ∈ A | P a b = 0 for all b ∈ Y}` of a subgroup `Y ⊆ B`. -/
def leftOrthogonal (Y : AddSubgroup B) : AddSubgroup A :=
  rightOrthogonal P.flip Y

theorem mem_leftOrthogonal {Y : AddSubgroup B} {a : A} :
    a ∈ leftOrthogonal P Y ↔ ∀ b ∈ Y, P a b = 0 :=
  Iff.rfl

theorem le_rightOrthogonal_iff {X : AddSubgroup A} {Y : AddSubgroup B} :
    Y ≤ rightOrthogonal P X ↔ X ≤ leftOrthogonal P Y :=
  ⟨fun h a ha _ hb => h hb a ha, fun h b hb _ ha => h ha b hb⟩

theorem le_leftOrthogonal_rightOrthogonal (X : AddSubgroup A) :
    X ≤ leftOrthogonal P (rightOrthogonal P X) :=
  (le_rightOrthogonal_iff P).1 le_rfl

theorem le_rightOrthogonal_leftOrthogonal (Y : AddSubgroup B) :
    Y ≤ rightOrthogonal P (leftOrthogonal P Y) :=
  (le_rightOrthogonal_iff P).2 le_rfl

theorem rightOrthogonal_anti {X X' : AddSubgroup A} (h : X ≤ X') :
    rightOrthogonal P X' ≤ rightOrthogonal P X :=
  fun _ hb a ha => hb a (h ha)

theorem leftOrthogonal_anti {Y Y' : AddSubgroup B} (h : Y ≤ Y') :
    leftOrthogonal P Y' ≤ leftOrthogonal P Y :=
  rightOrthogonal_anti P.flip h

theorem rightOrthogonal_sup (X X' : AddSubgroup A) :
    rightOrthogonal P (X ⊔ X') = rightOrthogonal P X ⊓ rightOrthogonal P X' := by
  refine le_antisymm (le_inf (rightOrthogonal_anti P le_sup_left)
    (rightOrthogonal_anti P le_sup_right)) fun b hb a ha => ?_
  obtain ⟨x, hx, x', hx', rfl⟩ := AddSubgroup.mem_sup.1 ha
  rw [map_add, AddMonoidHom.add_apply, hb.1 x hx, hb.2 x' hx', add_zero]

theorem leftOrthogonal_sup (Y Y' : AddSubgroup B) :
    leftOrthogonal P (Y ⊔ Y') = leftOrthogonal P Y ⊓ leftOrthogonal P Y' :=
  rightOrthogonal_sup P.flip Y Y'

@[simp]
theorem rightOrthogonal_bot : rightOrthogonal P (⊥ : AddSubgroup A) = ⊤ :=
  eq_top_iff.2 fun _ _ a ha => by rw [(AddSubgroup.mem_bot).1 ha, map_zero, AddMonoidHom.zero_apply]

@[simp]
theorem leftOrthogonal_bot : leftOrthogonal P (⊥ : AddSubgroup B) = ⊤ :=
  rightOrthogonal_bot P.flip

/-- If `B → A^∨` is injective, the orthogonal of `A` is `0`. -/
theorem rightOrthogonal_top (hP : Function.Injective P.flip) :
    rightOrthogonal P (⊤ : AddSubgroup A) = ⊥ :=
  eq_bot_iff.2 fun b hb => (AddSubgroup.mem_bot).2 <|
    (injective_iff_map_eq_zero _).1 hP b (AddMonoidHom.ext fun a => hb a trivial)

/-- If `A → B^∨` is injective, the orthogonal of `B` is `0`. -/
theorem leftOrthogonal_top (hP : Function.Injective P) :
    leftOrthogonal P (⊤ : AddSubgroup B) = ⊥ :=
  rightOrthogonal_top P.flip hP

section Finite

/-- For `B ≅ A^∨` through `P` and `A` finite: `#X^⊥ · #X = #A`. -/
theorem card_rightOrthogonal_mul_card [Finite A] (hP : Function.Bijective P.flip)
    (X : AddSubgroup A) : Nat.card (rightOrthogonal P X) * Nat.card X = Nat.card A := by
  have e1 : rightOrthogonal P X ≃ {f : A →+ QZ // ∀ x ∈ X, f x = 0} :=
    (Equiv.ofBijective _ hP).subtypeEquiv fun _ => Iff.rfl
  have e2 : {f : A →+ QZ // ∀ x ∈ X, f x = 0} ≃ (A ⧸ X →+ QZ) :=
    { toFun := fun f => QuotientAddGroup.lift X f.1 fun x hx => f.2 x hx
      invFun := fun g => ⟨g.comp (QuotientAddGroup.mk' X), fun x hx => by
        simp [(QuotientAddGroup.eq_zero_iff x).2 hx]⟩
      left_inv := fun f => Subtype.ext (AddMonoidHom.ext fun x => rfl)
      right_inv := fun g => by
        refine AddMonoidHom.ext fun q => ?_
        induction q using QuotientAddGroup.induction_on
        rfl }
  rw [Nat.card_congr (e1.trans e2), QZ.card_hom,
    ← AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup]

/-- For `A ≅ B^∨` through `P` and `B` finite: `#⊥Y · #Y = #B`. -/
theorem card_leftOrthogonal_mul_card [Finite B] (hP : Function.Bijective P)
    (Y : AddSubgroup B) : Nat.card (leftOrthogonal P Y) * Nat.card Y = Nat.card B :=
  card_rightOrthogonal_mul_card P.flip hP Y

/-- A perfect pairing of finite groups: `#A = #B`. -/
theorem card_eq_card_of_bijective [Finite B] (hP : Function.Bijective P) :
    Nat.card A = Nat.card B := by
  rw [Nat.card_congr (Equiv.ofBijective _ hP), QZ.card_hom]

variable [Finite A] [Finite B] (hP : Function.Bijective P) (hP' : Function.Bijective P.flip)

include hP hP' in
/-- For a perfect pairing of finite groups, `⊥(X^⊥) = X`. -/
theorem leftOrthogonal_rightOrthogonal (X : AddSubgroup A) :
    leftOrthogonal P (rightOrthogonal P X) = X := by
  refine (AddSubgroup.eq_of_le_of_card_ge (le_leftOrthogonal_rightOrthogonal P X) ?_).symm
  have h1 := card_leftOrthogonal_mul_card P hP (rightOrthogonal P X)
  have h2 := card_rightOrthogonal_mul_card P hP' X
  have h3 := card_eq_card_of_bijective P hP
  have hpos : 0 < Nat.card (rightOrthogonal P X) := Nat.card_pos
  refine (Nat.eq_of_mul_eq_mul_left hpos ?_).le
  rw [mul_comm] at h1
  rw [h1, h2, h3]

include hP hP' in
/-- For a perfect pairing of finite groups, `(⊥Y)^⊥ = Y`. -/
theorem rightOrthogonal_leftOrthogonal (Y : AddSubgroup B) :
    rightOrthogonal P (leftOrthogonal P Y) = Y :=
  leftOrthogonal_rightOrthogonal P.flip hP' hP Y

include hP hP' in
/-- For a perfect pairing of finite groups, `⊥(Y ∩ Y') = ⊥Y + ⊥Y'`. -/
theorem leftOrthogonal_inf (Y Y' : AddSubgroup B) :
    leftOrthogonal P (Y ⊓ Y') = leftOrthogonal P Y ⊔ leftOrthogonal P Y' := by
  conv_lhs => rw [← rightOrthogonal_leftOrthogonal P hP hP' Y,
    ← rightOrthogonal_leftOrthogonal P hP hP' Y', ← rightOrthogonal_sup]
  exact leftOrthogonal_rightOrthogonal P hP hP' _

include hP hP' in
/-- For a perfect pairing of finite groups, `(X ∩ X')^⊥ = X^⊥ + X'^⊥`. -/
theorem rightOrthogonal_inf (X X' : AddSubgroup A) :
    rightOrthogonal P (X ⊓ X') = rightOrthogonal P X ⊔ rightOrthogonal P X' :=
  leftOrthogonal_inf P.flip hP' hP X X'

end Finite

end Orthogonal

section Transport

variable {A A' B B' C : Type*} [AddCommGroup A] [AddCommGroup A'] [AddCommGroup B]
  [AddCommGroup B'] [AddCommGroup C]

/-- Perfectness (on the left) is transported along isomorphisms of the two arguments and of the
group of values. -/
theorem bijective_of_pairing_eq_addEquiv (P : A →+ B →+ QZ) (Q : A' →+ B' →+ C)
    (eA : A' ≃+ A) (eB : B' ≃+ B) (eC : C ≃+ QZ) (h : ∀ a b, P (eA a) (eB b) = eC (Q a b))
    (hQ : Function.Bijective Q) : Function.Bijective P := by
  let pre : (B' →+ C) ≃ (B →+ QZ) :=
    { toFun := fun χ => eC.toAddMonoidHom.comp (χ.comp eB.symm.toAddMonoidHom)
      invFun := fun ψ => eC.symm.toAddMonoidHom.comp (ψ.comp eB.toAddMonoidHom)
      left_inv := fun χ => by ext; simp
      right_inv := fun ψ => by ext; simp }
  have hP : ⇑P = pre ∘ Q ∘ eA.symm := by
    funext a
    refine AddMonoidHom.ext fun b => ?_
    change P a b = eC (Q (eA.symm a) (eB.symm b))
    rw [← h, eA.apply_symm_apply, eB.apply_symm_apply]
  rw [hP]
  exact pre.bijective.comp (hQ.comp eA.symm.bijective)

/-- Perfectness (on the right) is transported along isomorphisms of the two arguments and of the
group of values. -/
theorem bijective_flip_of_pairing_eq_addEquiv (P : A →+ B →+ QZ) (Q : A' →+ B' →+ C)
    (eA : A' ≃+ A) (eB : B' ≃+ B) (eC : C ≃+ QZ) (h : ∀ a b, P (eA a) (eB b) = eC (Q a b))
    (hQ : Function.Bijective Q.flip) : Function.Bijective P.flip :=
  bijective_of_pairing_eq_addEquiv P.flip Q.flip eB eA eC (fun b a => h a b) hQ

end Transport

section Sums

open scoped Classical in
/-- The sum `Σ_i P_i(a_i, b_i)` of a finite family of pairings, a pairing of the products. -/
noncomputable def piPairing {ι : Type*} [Fintype ι] {A B : ι → Type*} [∀ i, AddCommGroup (A i)]
    [∀ i, AddCommGroup (B i)] (P : ∀ i, A i →+ B i →+ QZ) : (∀ i, A i) →+ (∀ i, B i) →+ QZ :=
  ∑ i, ((P i).comp (Pi.evalAddMonoidHom A i)).compl₂ (Pi.evalAddMonoidHom B i)

section Pi

variable {ι : Type*} [Fintype ι] {A B : ι → Type*} [∀ i, AddCommGroup (A i)]
  [∀ i, AddCommGroup (B i)] (P : ∀ i, A i →+ B i →+ QZ)

theorem piPairing_apply (a : ∀ i, A i) (b : ∀ i, B i) :
    piPairing P a b = ∑ i, P i (a i) (b i) := by
  rw [piPairing, AddMonoidHom.finsetSum_apply, AddMonoidHom.finsetSum_apply]
  rfl

theorem piPairing_flip : (piPairing P).flip = piPairing fun i => (P i).flip :=
  AddMonoidHom.ext fun b => AddMonoidHom.ext fun a => by
    rw [AddMonoidHom.flip_apply, piPairing_apply, piPairing_apply]
    rfl

open scoped Classical in
theorem piPairing_single (a : ∀ i, A i) (i : ι) (b : B i) :
    piPairing P a (Pi.single i b) = P i (a i) b := by
  rw [piPairing_apply, Finset.sum_eq_single i (fun j _ hj => by
    rw [Pi.single_eq_of_ne hj, map_zero]) (fun h => absurd (Finset.mem_univ i) h),
    Pi.single_eq_same]

/-- The sum of a finite family of perfect pairings is perfect (on the left). -/
theorem bijective_piPairing (hP : ∀ i, Function.Bijective (P i)) :
    Function.Bijective (piPairing P) := by
  classical
  refine ⟨(injective_iff_map_eq_zero _).2 fun a ha => funext fun i => ?_, fun χ => ?_⟩
  · refine (injective_iff_map_eq_zero _).1 (hP i).1 (a i) (AddMonoidHom.ext fun b => ?_)
    rw [← piPairing_single P a i b, ha]
    rfl
  · choose a ha using fun i => (hP i).2 (χ.comp (AddMonoidHom.single B i))
    refine ⟨a, AddMonoidHom.ext fun b => ?_⟩
    rw [piPairing_apply]
    conv_rhs => rw [← Finset.univ_sum_single b, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ha i]
    rfl

/-- The sum of a finite family of perfect pairings is perfect (on the right). -/
theorem bijective_piPairing_flip (hP : ∀ i, Function.Bijective (P i).flip) :
    Function.Bijective (piPairing P).flip := by
  rw [piPairing_flip]
  exact bijective_piPairing _ hP

open scoped Classical in
theorem piPairing_single_left (i : ι) (a : A i) (b : ∀ i, B i) :
    piPairing P (Pi.single i a) b = P i a (b i) := by
  rw [piPairing_apply, Finset.sum_eq_single i (fun j _ hj => by
    rw [Pi.single_eq_of_ne hj, map_zero, AddMonoidHom.zero_apply])
    (fun h => absurd (Finset.mem_univ i) h), Pi.single_eq_same]

/-- The orthogonal of a product of subgroups for the sum pairing is the product of the
orthogonals. -/
theorem rightOrthogonal_piPairing_pi (X : ∀ i, AddSubgroup (A i)) :
    rightOrthogonal (piPairing P) (AddSubgroup.pi Set.univ X) =
      AddSubgroup.pi Set.univ fun i => rightOrthogonal (P i) (X i) := by
  classical
  ext b
  refine ⟨fun hb i _ a ha => ?_, fun hb a ha => ?_⟩
  · rw [← piPairing_single_left P i a b]
    refine hb _ fun j _ => ?_
    by_cases hj : j = i
    · subst hj
      rw [Pi.single_eq_same]
      exact ha
    · rw [Pi.single_eq_of_ne hj]
      exact (X j).zero_mem
  · rw [piPairing_apply]
    exact Finset.sum_eq_zero fun i _ => hb i trivial (a i) (ha i trivial)

/-- The left orthogonal of a product of subgroups for the sum pairing is the product of the left
orthogonals. -/
theorem leftOrthogonal_piPairing_pi (Y : ∀ i, AddSubgroup (B i)) :
    leftOrthogonal (piPairing P) (AddSubgroup.pi Set.univ Y) =
      AddSubgroup.pi Set.univ fun i => leftOrthogonal (P i) (Y i) := by
  rw [leftOrthogonal, piPairing_flip]
  exact rightOrthogonal_piPairing_pi _ Y

end Pi

section Prod

variable {A₁ A₂ B₁ B₂ : Type*} [AddCommGroup A₁] [AddCommGroup A₂] [AddCommGroup B₁]
  [AddCommGroup B₂] (P : A₁ →+ B₁ →+ QZ) (Q : A₂ →+ B₂ →+ QZ)

/-- The sum `P(a₁, b₁) + Q(a₂, b₂)` of two pairings, a pairing of the products. -/
def prodPairing : (A₁ × A₂) →+ (B₁ × B₂) →+ QZ :=
  (P.comp (AddMonoidHom.fst A₁ A₂)).compl₂ (AddMonoidHom.fst B₁ B₂) +
    (Q.comp (AddMonoidHom.snd A₁ A₂)).compl₂ (AddMonoidHom.snd B₁ B₂)

theorem prodPairing_apply (a : A₁ × A₂) (b : B₁ × B₂) :
    prodPairing P Q a b = P a.1 b.1 + Q a.2 b.2 :=
  rfl

theorem prodPairing_flip : (prodPairing P Q).flip = prodPairing P.flip Q.flip :=
  AddMonoidHom.ext fun _ => AddMonoidHom.ext fun _ => rfl

/-- The sum of two perfect pairings is perfect (on the left). -/
theorem bijective_prodPairing (hP : Function.Bijective P) (hQ : Function.Bijective Q) :
    Function.Bijective (prodPairing P Q) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun a ha => Prod.ext ?_ ?_, fun χ => ?_⟩
  · refine (injective_iff_map_eq_zero _).1 hP.1 a.1 (AddMonoidHom.ext fun b => ?_)
    have h := DFunLike.congr_fun ha (b, 0)
    rw [prodPairing_apply, map_zero, add_zero] at h
    exact h
  · refine (injective_iff_map_eq_zero _).1 hQ.1 a.2 (AddMonoidHom.ext fun b => ?_)
    have h := DFunLike.congr_fun ha (0, b)
    rw [prodPairing_apply, map_zero, zero_add] at h
    exact h
  · obtain ⟨a₁, h₁⟩ := hP.2 (χ.comp (AddMonoidHom.inl B₁ B₂))
    obtain ⟨a₂, h₂⟩ := hQ.2 (χ.comp (AddMonoidHom.inr B₁ B₂))
    refine ⟨(a₁, a₂), AddMonoidHom.ext fun b => ?_⟩
    rw [prodPairing_apply, h₁, h₂]
    change χ (b.1, 0) + χ (0, b.2) = χ b
    rw [← map_add, Prod.mk_add_mk, add_zero, zero_add]

/-- The sum of two perfect pairings is perfect (on the right). -/
theorem bijective_prodPairing_flip (hP : Function.Bijective P.flip)
    (hQ : Function.Bijective Q.flip) : Function.Bijective (prodPairing P Q).flip := by
  rw [prodPairing_flip]
  exact bijective_prodPairing _ _ hP hQ

/-- The orthogonal of a product of two subgroups for the sum pairing is the product of the
orthogonals. -/
theorem rightOrthogonal_prodPairing_prod (X₁ : AddSubgroup A₁) (X₂ : AddSubgroup A₂) :
    rightOrthogonal (prodPairing P Q) (X₁.prod X₂) =
      (rightOrthogonal P X₁).prod (rightOrthogonal Q X₂) := by
  ext b
  refine ⟨fun hb => ⟨fun a ha => ?_, fun a ha => ?_⟩, fun hb a ha => ?_⟩
  · have h := hb (a, 0) ⟨ha, X₂.zero_mem⟩
    rwa [prodPairing_apply, map_zero, AddMonoidHom.zero_apply, add_zero] at h
  · have h := hb (0, a) ⟨X₁.zero_mem, ha⟩
    rwa [prodPairing_apply, map_zero, AddMonoidHom.zero_apply, zero_add] at h
  · rw [prodPairing_apply, hb.1 a.1 ha.1, hb.2 a.2 ha.2, add_zero]

/-- The left orthogonal of a product of two subgroups for the sum pairing is the product of the
left orthogonals. -/
theorem leftOrthogonal_prodPairing_prod (Y₁ : AddSubgroup B₁) (Y₂ : AddSubgroup B₂) :
    leftOrthogonal (prodPairing P Q) (Y₁.prod Y₂) =
      (leftOrthogonal P Y₁).prod (leftOrthogonal Q Y₂) := by
  rw [leftOrthogonal, prodPairing_flip]
  exact rightOrthogonal_prodPairing_prod _ _ Y₁ Y₂

end Prod

end Sums

end Langlands.ProfiniteCohomology

end
