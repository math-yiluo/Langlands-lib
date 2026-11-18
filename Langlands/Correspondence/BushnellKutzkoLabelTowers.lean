import Langlands.Correspondence.BushnellKutzkoLabelCount
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Perfect
import Mathlib.Algebra.BigOperators.Fin

/-! Finite-field towers for the count in the route note, Lemma `lem:BKlabels`. -/

noncomputable section

namespace Langlands.Henniart.LabelCounting

open Polynomial IntermediateField Langlands.BushnellKutzko Langlands.FieldTheory
open Langlands.Henniart.Numerical
open scoped BigOperators

/-- Product of the degrees preceding the indicated index. -/
def prefixProd {t : ℕ} (d : Fin t → ℕ) (i : ℕ) : ℕ :=
  ∏ j ∈ Finset.univ.filter (fun j : Fin t => (j : ℕ) < i), d j

@[simp] theorem prefixProd_zero {t : ℕ} (d : Fin t → ℕ) : prefixProd d 0 = 1 := by
  simp [prefixProd]

@[simp] theorem prefixProd_full {t : ℕ} (d : Fin t → ℕ) :
    prefixProd d t = ∏ j, d j := by
  simp [prefixProd]

theorem filter_prefix_succ {t : ℕ} (i : Fin t) :
    (Finset.univ.filter fun j : Fin t => (j : ℕ) < (i : ℕ) + 1) =
      insert i (Finset.univ.filter fun j : Fin t => (j : ℕ) < i) := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
  omega

theorem prefixProd_succ {t : ℕ} (d : Fin t → ℕ) (i : Fin t) :
    prefixProd d ((i : ℕ) + 1) = prefixProd d i * d i := by
  unfold prefixProd
  rw [filter_prefix_succ i, Finset.prod_insert (by simp), mul_comm]

theorem prefixProd_dvd {t : ℕ} (d : Fin t → ℕ) (i : ℕ) : prefixProd d i ∣ ∏ j, d j :=
  Finset.prod_dvd_prod_of_subset _ _ d (Finset.filter_subset _ _)

theorem prefixProd_pos {t : ℕ} {d : Fin t → ℕ} (hd : ∀ j, 0 < d j) (i : ℕ) :
    0 < prefixProd d i := Finset.prod_pos fun j _ => hd j

theorem prefixProd_castSucc {t : ℕ} (d : Fin (t + 1) → ℕ) {i : ℕ} (hi : i ≤ t) :
    prefixProd d i = prefixProd (fun j : Fin t => d j.castSucc) i := by
  simp only [prefixProd, Finset.prod_filter, Fin.prod_univ_castSucc, Fin.val_castSucc,
    Fin.val_last, Nat.not_lt.mpr hi, ite_false, mul_one]

/-- The relative degrees in a tuple which generates an extension of degree `f`. -/
@[ext] structure DegreeProfile (t f : ℕ) where
  degree : Fin t → ℕ
  pos : ∀ i, 0 < degree i
  prod_eq : ∏ i, degree i = f

/-- The exponent of the coefficient field at stage `i`. -/
def DegreeProfile.exponent {t f : ℕ} (d : DegreeProfile t f) (i : ℕ) : ℕ+ :=
  ⟨prefixProd d.degree i, prefixProd_pos d.pos i⟩

abbrev BaseField (q : ℕ) := polarBaseField (labelFieldSize q)

abbrev ExtensionField (q f : ℕ) [NeZero f] := polarExtensionField (labelFieldSize q) f

/-- One monic irreducible polynomial other than `X` at every stage of a degree profile. -/
abbrev TowerPolynomials (q : ℕ) {t f : ℕ} (d : DegreeProfile t f) :=
  (i : Fin t) → irreduciblePolynomialLabels (d.degree i) (ExtensionField q (d.exponent i))

/-- The nonzero coefficient tuple, in order of adjoining, which generates the extension. -/
abbrev GeneratingTuple (k L : Type*) [Field k] [Field L] [Algebra k L] (t : ℕ) :=
  {x : Fin t → L // (∀ i, x i ≠ 0) ∧ adjoin k (Set.range x) = ⊤}

section PrefixFields

variable {k L : Type*} [Field k] [Field L] [Algebra k L] [Finite L]

private def prefixSet {t : ℕ} (x : Fin t → L) (i : ℕ) : Set L :=
  {z | ∃ j : Fin t, (j : ℕ) < i ∧ x j = z}

private def prefixField {t : ℕ} (x : Fin t → L) (i : ℕ) : IntermediateField k L :=
  adjoin k (prefixSet x i)

omit [Field L] [Finite L] in
private theorem prefixSet_succ {t : ℕ} (x : Fin t → L) (i : Fin t) :
    prefixSet x ((i : ℕ) + 1) = prefixSet x i ∪ {x i} := by
  ext z
  constructor
  · rintro ⟨j, hj, rfl⟩
    by_cases hji : j = i
    · subst j
      exact Or.inr rfl
    · exact Or.inl ⟨j, by
        have := mt Fin.ext hji
        omega, rfl⟩
  · rintro (⟨j, hj, rfl⟩ | hj)
    · exact ⟨j, by omega, rfl⟩
    · exact ⟨i, by omega, hj.symm⟩

omit [Finite L] in
private theorem prefixField_zero {t : ℕ} (x : Fin t → L) :
    prefixField (k := k) x 0 = ⊥ := by
  simp [prefixField, prefixSet]

omit [Finite L] in
private theorem prefixField_full {t : ℕ} (x : Fin t → L) :
    prefixField (k := k) x t = adjoin k (Set.range x) := by
  apply congrArg (adjoin k)
  ext z
  simp [prefixSet, Set.mem_range]

private theorem prefixRank_succ {t : ℕ} (x : Fin t → L) (i : Fin t) :
    Module.finrank k (prefixField (k := k) x ((i : ℕ) + 1)) =
      Module.finrank k (prefixField (k := k) x i) *
        (minpoly (prefixField (k := k) x i) (x i)).natDegree := by
  have h : prefixField (k := k) x ((i : ℕ) + 1) =
      (adjoin (prefixField (k := k) x i) ({x i} : Set L)).restrictScalars k := by
    unfold prefixField
    rw [prefixSet_succ x i, ← adjoin_adjoin_left]
  rw [h]
  change Module.finrank k (adjoin (prefixField (k := k) x i) ({x i} : Set L)) = _
  rw [← Module.finrank_mul_finrank k (prefixField (k := k) x i),
    adjoin.finrank (IsIntegral.of_finite _ _)]

private def relativeDegrees {t : ℕ} (x : Fin t → L) (i : Fin t) : ℕ :=
  (minpoly (prefixField (k := k) x i) (x i)).natDegree

private theorem prefixRank {t : ℕ} (x : Fin t → L) {i : ℕ} (hi : i ≤ t) :
    Module.finrank k (prefixField (k := k) x i) = prefixProd (relativeDegrees (k := k) x) i := by
  induction i with
  | zero => rw [prefixField_zero, prefixProd_zero, IntermediateField.finrank_bot]
  | succ i ih =>
    have h : i < t := by omega
    rw [prefixRank_succ x ⟨i, h⟩, prefixProd_succ _ ⟨i, h⟩, ih (by omega)]
    rfl

private theorem field_eq_of_finrank_eq (A B : IntermediateField k L)
    (h : Module.finrank k A = Module.finrank k B) : A = B := by
  have sub {C D : IntermediateField k L} (hCD : Module.finrank k C ∣ Module.finrank k D) :
      C ≤ D := by
    let e := (FiniteField.nonempty_algHom_of_finrank_dvd hCD).some
    have hC : (D.val.comp e).fieldRange = C := AlgHom.fieldRange_of_normal _
    intro x hx
    obtain ⟨y, rfl⟩ := hC ▸ hx
    exact (e y).property
  exact le_antisymm (sub h.dvd) (sub h.symm.dvd)

end PrefixFields

section EmbeddedRoots

variable {k A L : Type*} [Field k] [Field A] [Field L] [Algebra k A] [Algebra k L]
  [Finite L]

private def embeddedMinpoly (e : A →ₐ[k] L) (x : L) : A[X] :=
  letI : Algebra A L := e.toRingHom.toAlgebra
  minpoly A x

private theorem embeddedMinpoly_degree (e : A →ₐ[k] L) (x : L) :
    (embeddedMinpoly e x).natDegree = (minpoly e.fieldRange x).natDegree := by
  let : Algebra A L := e.toRingHom.toAlgebra
  let E := e.equivFieldRange.toRingEquiv
  have hx : IsIntegral A x := IsIntegral.of_finite _ _
  have hm : (minpoly A x).map E.toRingHom = minpoly e.fieldRange x := by
    apply minpoly.eq_of_irreducible_of_monic
    · exact (minpoly.irreducible hx).map (Polynomial.mapEquiv E)
    · rw [aeval_def, eval₂_map]
      exact minpoly.aeval A x
    · exact (minpoly.monic hx).map _
  change (minpoly A x).natDegree = _
  rw [← hm, natDegree_map]

private def EmbeddedRoots (e : A →ₐ[k] L) (P : A[X]) :=
  letI : Algebra A L := e.toRingHom.toAlgebra
  P.rootSet L

omit [Finite L] in
private theorem embeddedRoots_iff {e : A →ₐ[k] L} {P : A[X]} {x : L}
    (hP : P.Monic) (hi : Irreducible P) :
    x ∈ EmbeddedRoots e P ↔ P = embeddedMinpoly e x := by
  let : Algebra A L := e.toRingHom.toAlgebra
  exact hP.mem_rootSet.trans (minpoly.eq_iff_aeval_eq_zero hi hP).symm

private theorem embeddedMinpoly_mem (e : A →ₐ[k] L) {x : L} (hx : x ≠ 0) {d : ℕ}
    (hd : (embeddedMinpoly e x).natDegree = d) :
    embeddedMinpoly e x ∈ irreduciblePolynomialLabels d A := by
  let : Algebra A L := e.toRingHom.toAlgebra
  have hint : IsIntegral A x := IsIntegral.of_finite _ _
  refine mem_irreduciblePolynomialLabels_iff.mpr
    ⟨minpoly.monic hint, minpoly.irreducible hint, hd, ?_⟩
  change minpoly A x ≠ X
  intro h
  exact hx (by simpa only [h, aeval_X] using minpoly.aeval A x)

omit [Finite L] in
private theorem embeddedRoot_ne_zero {e : A →ₐ[k] L} {d : ℕ}
    (P : irreduciblePolynomialLabels d A) (x : EmbeddedRoots e P.val) :
    x.val ≠ 0 := by
  let : Algebra A L := e.toRingHom.toAlgebra
  obtain ⟨hm, hi, -, hn⟩ := mem_irreduciblePolynomialLabels_iff.mp P.property
  have h := (embeddedRoots_iff hm hi).mp x.property
  change (P : A[X]) = minpoly A x.val at h
  intro hx
  rw [hx, minpoly.zero] at h
  exact hn h

private def embeddedRootsEquivFin [Finite A] (e : A →ₐ[k] L) {d : ℕ}
    (P : irreduciblePolynomialLabels d A)
    (hd : letI : Algebra A L := e.toRingHom.toAlgebra; d ∣ Module.finrank A L) :
    EmbeddedRoots e P.val ≃ Fin d := by
  letI : Algebra A L := e.toRingHom.toAlgebra
  obtain ⟨hm, hi, hdeg, -⟩ := mem_irreduciblePolynomialLabels_iff.mp P.property
  have hdiv := hi.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X.mp (hdeg ▸ hd)
  have hdiv' : P.val.map (algebraMap A L) ∣ X ^ Nat.card L - X := by
    rw [Module.natCard_eq_pow_finrank (K := A) (V := L)]
    have hmap := map_dvd (Polynomial.mapRingHom (algebraMap A L)) hdiv
    change P.val.map (algebraMap A L) ∣
      (X ^ Nat.card A ^ Module.finrank A L - X : A[X]).map (algebraMap A L) at hmap
    simpa only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X] using
      hmap
  have hn : (X ^ Nat.card L - X : L[X]) ≠ 0 :=
    FiniteField.X_pow_card_sub_X_ne_zero L Finite.one_lt_card
  have hs := (Polynomial.splits_X_pow_nat_card_sub_X (K := L)).of_dvd hn hdiv'
  change P.val.rootSet L ≃ Fin d
  exact Fintype.equivFinOfCardEq
    ((card_rootSet_eq_natDegree (PerfectField.separable_of_irreducible hi) hs).trans hdeg)

end EmbeddedRoots

section FixedProfile

variable (q : ℕ) {t f : ℕ} [NeZero f] (d : DegreeProfile t f)

private def towerEmbedding (i : Fin t) :
    ExtensionField q (d.exponent i) →ₐ[BaseField q] ExtensionField q f :=
  (FiniteField.nonempty_algHom_of_finrank_dvd (by
    simp only [FiniteField.finrank_extension]
    exact (prefixProd_dvd d.degree i).trans d.prod_eq.dvd)).some

private theorem towerEmbedding_rank (i : Fin t) :
    Module.finrank (BaseField q) (towerEmbedding q d i).fieldRange =
      prefixProd d.degree i := by
  rw [← (towerEmbedding q d i).equivFieldRange.toLinearEquiv.finrank_eq,
    FiniteField.finrank_extension]
  rfl

private theorem towerEmbedding_degree_dvd (i : Fin t) :
    letI : Algebra (ExtensionField q (d.exponent i)) (ExtensionField q f) :=
      (towerEmbedding q d i).toRingHom.toAlgebra
    d.degree i ∣ Module.finrank (ExtensionField q (d.exponent i)) (ExtensionField q f) := by
  let A := ExtensionField q (d.exponent i)
  let L := ExtensionField q f
  let e := towerEmbedding q d i
  let : Algebra A L := e.toRingHom.toAlgebra
  let : IsScalarTower (BaseField q) A L := IsScalarTower.of_algHom e
  have h := Module.finrank_mul_finrank (BaseField q) A L
  have hA : Module.finrank (BaseField q) A = prefixProd d.degree i :=
    FiniteField.finrank_extension _ _ _
  have hL : Module.finrank (BaseField q) L = f := FiniteField.finrank_extension _ _ _
  rw [hA, hL] at h
  have hdiv : prefixProd d.degree i * d.degree i ∣ f := by
    rw [← prefixProd_succ]
    exact (prefixProd_dvd d.degree _).trans d.prod_eq.dvd
  change d.degree i ∣ Module.finrank A L
  exact Nat.dvd_of_mul_dvd_mul_left (prefixProd_pos d.pos i) (hdiv.trans h.symm.dvd)

private abbrev ProfileTuple :=
  {x : Fin t → ExtensionField q f //
    (∀ i, x i ≠ 0) ∧ relativeDegrees (k := BaseField q) x = d.degree}

private theorem embeddedDegree_eq_relative (x : Fin t → ExtensionField q f) (i : Fin t)
    (h : Module.finrank (BaseField q) (prefixField (k := BaseField q) x i) =
      prefixProd d.degree i) :
    (embeddedMinpoly (towerEmbedding q d i) (x i)).natDegree =
      relativeDegrees (k := BaseField q) x i := by
  rw [embeddedMinpoly_degree, field_eq_of_finrank_eq _ _ ((towerEmbedding_rank q d i).trans h.symm)]
  rfl

private theorem profile_degree_iff (x : Fin t → ExtensionField q f) :
    relativeDegrees (k := BaseField q) x = d.degree ↔
      ∀ i, (embeddedMinpoly (towerEmbedding q d i) (x i)).natDegree = d.degree i := by
  constructor
  · intro h i
    rw [embeddedDegree_eq_relative q d x i, h]
    rw [prefixRank x i.isLt.le, h]
  · intro h
    have hrank (j : ℕ) (hj : j ≤ t) :
        Module.finrank (BaseField q) (prefixField (k := BaseField q) x j) =
          prefixProd d.degree j := by
      induction j with
      | zero => rw [prefixField_zero, prefixProd_zero, IntermediateField.finrank_bot]
      | succ j ih =>
        let i : Fin t := ⟨j, by omega⟩
        have hi := ih (by omega)
        have hdeg := (embeddedDegree_eq_relative q d x i hi).symm.trans (h i)
        rw [prefixRank_succ x i, prefixProd_succ _ i, hi, ← relativeDegrees, hdeg]
    funext i
    exact (embeddedDegree_eq_relative q d x i (hrank i i.isLt.le)).symm.trans (h i)

private abbrev TowerRootTuples :=
  Σ P : TowerPolynomials q d, (i : Fin t) → EmbeddedRoots (towerEmbedding q d i) (P i).val

private theorem towerRoot_minpoly (z : TowerRootTuples q d) (i : Fin t) :
    (z.1 i).val = embeddedMinpoly (towerEmbedding q d i) (z.2 i).val := by
  obtain ⟨hm, hi, -, -⟩ := mem_irreduciblePolynomialLabels_iff.mp (z.1 i).property
  exact (embeddedRoots_iff hm hi).mp (z.2 i).property

private def rootTupleToProfile (z : TowerRootTuples q d) : ProfileTuple q d :=
  ⟨fun i => (z.2 i).val, fun i => embeddedRoot_ne_zero (z.1 i) (z.2 i),
    (profile_degree_iff q d _).mpr fun i => by
      rw [← towerRoot_minpoly q d z i]
      exact (mem_irreduciblePolynomialLabels_iff.mp (z.1 i).property).2.2.1⟩

private def rootTupleEquiv : TowerRootTuples q d ≃ ProfileTuple q d :=
  Equiv.ofBijective (rootTupleToProfile q d) (by
    constructor
    · intro u v h
      have hx (i : Fin t) : (u.2 i).val = (v.2 i).val :=
        congrFun (congrArg Subtype.val h) i
      have hP : u.1 = v.1 := funext fun i => Subtype.ext (by
        rw [towerRoot_minpoly q d u i, towerRoot_minpoly q d v i, hx i])
      obtain ⟨P, x⟩ := u
      obtain ⟨Q, y⟩ := v
      change P = Q at hP
      subst Q
      exact congrArg (Sigma.mk P) (funext fun i => Subtype.ext (hx i))
    · intro x
      let P : TowerPolynomials q d := fun i =>
        ⟨embeddedMinpoly (towerEmbedding q d i) (x.val i),
          embeddedMinpoly_mem _ (x.property.1 i)
            ((profile_degree_iff q d x.val).mp x.property.2 i)⟩
      refine ⟨⟨P, fun i => ⟨x.val i, ?_⟩⟩, Subtype.ext rfl⟩
      obtain ⟨hm, hi, -, -⟩ := mem_irreduciblePolynomialLabels_iff.mp (P i).property
      exact (embeddedRoots_iff hm hi).mpr rfl)

private def profileTupleEquiv : ProfileTuple q d ≃ TowerPolynomials q d × Fin f :=
  (rootTupleEquiv q d).symm.trans <| Equiv.sigmaEquivProdOfEquiv fun P => by
    classical
    let e := Equiv.piCongrRight fun i =>
      embeddedRootsEquivFin (towerEmbedding q d i) (P i) (towerEmbedding_degree_dvd q d i)
    refine e.trans (Fintype.equivFinOfCardEq ?_)
    simpa only [Fintype.card_pi, Fintype.card_fin] using d.prod_eq

end FixedProfile

/-- Degree profiles with one polynomial over each prescribed coefficient field. -/
abbrev PolynomialTowers (q t f : ℕ) :=
  Σ d : DegreeProfile t f, TowerPolynomials q d

section Generators

variable (q : ℕ) {t f : ℕ} [NeZero f]

private def tupleProfile (x : GeneratingTuple (BaseField q) (ExtensionField q f) t) :
    DegreeProfile t f where
  degree := relativeDegrees (k := BaseField q) x.val
  pos i := minpoly.natDegree_pos (IsIntegral.of_finite _ (x.val i))
  prod_eq := by
    have htop : prefixField (k := BaseField q) x.val t = ⊤ :=
      (prefixField_full x.val).trans x.property.2
    rw [← prefixProd_full, ← prefixRank x.val (i := t) le_rfl, htop,
      IntermediateField.finrank_top', FiniteField.finrank_extension]

private def generatorProfileEquiv :
    GeneratingTuple (BaseField q) (ExtensionField q f) t ≃
      Σ d : DegreeProfile t f, ProfileTuple q d :=
  Equiv.ofBijective (fun x => ⟨tupleProfile q x, ⟨x.val, x.property.1, rfl⟩⟩) (by
    constructor
    · intro x y h
      exact Subtype.ext (congrArg (fun z => z.2.val) h)
    · rintro ⟨⟨d, hpos, hprod⟩, x, hn, hd⟩
      change relativeDegrees (k := BaseField q) x = d at hd
      subst d
      have htop : adjoin (BaseField q) (Set.range x) = ⊤ := by
        apply field_eq_of_finrank_eq
        rw [← prefixField_full, prefixRank x (i := t) le_rfl, prefixProd_full,
          hprod, IntermediateField.finrank_top', FiniteField.finrank_extension]
      exact ⟨⟨x, hn, htop⟩, rfl⟩)

/-- Every generating nonzero tuple gives a polynomial tower with `f` choices of roots. -/
def generatingTupleEquiv :
    GeneratingTuple (BaseField q) (ExtensionField q f) t ≃ PolynomialTowers q t f × Fin f :=
  (generatorProfileEquiv q).trans <|
    (Equiv.sigmaCongrRight fun d => profileTupleEquiv q d).trans
      (Equiv.sigmaProdDistrib _ _).symm

end Generators

end Langlands.Henniart.LabelCounting
