import Langlands.GroupScheme.Torus.UniversalPoint

/-! # Natural endomorphisms of families of units

A family of maps `(I → Aˣ) → (I → Aˣ)`, one for every ring `A` under a fixed ring `R`, that is
multiplicative and natural in ring maps under `R`, is determined by its value at the universal
family of monomials in the Laurent polynomial ring `R[ℤ^I]`. Its coefficients are orthogonal
idempotents. Consequently the family agrees with the monomial map of an exponent matrix `m` over a
ring `B` under `R` exactly when the `m`-coefficients map to `1` in `B`, and over an integral domain
there is always such a matrix.
-/

noncomputable section

universe u

open CategoryTheory

namespace Langlands.GroupScheme.splitTorus

/-- The Laurent polynomial ring `R[ℤ^I]`. -/
abbrev laurentRing (R : CommRingCat.{u}) (I : Type u) : CommRingCat.{u} :=
  CommRingCat.of (AddMonoidAlgebra R (I → ℤ))

/-- The structure map `R ⟶ R[ℤ^I]`. -/
abbrev laurentAlgebraMap (R : CommRingCat.{u}) (I : Type u) : R ⟶ laurentRing R I :=
  CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R (I → ℤ)))

/-- The monomial map of an exponent matrix `m`: the `j`-th entry of the image of a family of units
`x` is `∏ l, x l ^ m j l`. -/
def powUnits {I : Type u} [Fintype I] {A : Type u} [CommRing A] (m : Matrix I I ℤ)
    (x : I → Aˣ) : I → Aˣ :=
  fun j => ∏ l, x l ^ m j l

theorem powUnits_map {I : Type u} [Fintype I] {A B : Type u} [CommRing A] [CommRing B]
    (f : A →+* B) (m : Matrix I I ℤ) (x : I → Aˣ) :
    powUnits m (fun j => Units.map f.toMonoidHom (x j)) =
      fun j => Units.map f.toMonoidHom (powUnits m x j) := by
  funext j
  simp [powUnits, map_prod, map_zpow]

theorem powUnits_one {I : Type u} [Fintype I] [DecidableEq I] {A : Type u} [CommRing A]
    (x : I → Aˣ) : powUnits (1 : Matrix I I ℤ) x = x := by
  funext j
  simp [powUnits, Matrix.one_apply]

theorem powUnits_mul {I : Type u} [Fintype I] {A : Type u} [CommRing A] (m : Matrix I I ℤ)
    (x y : I → Aˣ) : powUnits m (x * y) = powUnits m x * powUnits m y := by
  funext j
  simp [powUnits, mul_zpow, Finset.prod_mul_distrib]

/-- Monomial maps compose by matrix multiplication. -/
theorem powUnits_powUnits {I : Type u} [Fintype I] {A : Type u} [CommRing A]
    (m m' : Matrix I I ℤ) (x : I → Aˣ) : powUnits m' (powUnits m x) = powUnits (m' * m) x := by
  have hsum : ∀ (t : Finset I) (a : Aˣ) (f : I → ℤ), ∏ l ∈ t, a ^ f l = a ^ ∑ l ∈ t, f l := by
    intro t a f
    classical
    induction t using Finset.induction_on with
    | empty => simp
    | insert l t hl ih => rw [Finset.prod_insert hl, Finset.sum_insert hl, ih, zpow_add]
  funext j
  simp only [powUnits, Matrix.mul_apply, ← Finset.prod_zpow, ← zpow_mul]
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [hsum]
  congr 1
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

/-- The monomial map of an invertible exponent matrix, as a multiplicative equivalence. -/
def powUnitsEquiv {I : Type u} [Fintype I] [DecidableEq I] (A : Type u) [CommRing A]
    {m m' : Matrix I I ℤ} (h₁ : m' * m = 1) (h₂ : m * m' = 1) : (I → Aˣ) ≃* (I → Aˣ) where
  toFun := powUnits m
  invFun := powUnits m'
  left_inv x := by rw [powUnits_powUnits, h₁, powUnits_one]
  right_inv x := by rw [powUnits_powUnits, h₂, powUnits_one]
  map_mul' := powUnits_mul m

/-- A family of maps on unit families over all rings under `R`, multiplicative and natural in
ring maps under `R`. -/
structure UnitsNatEnd (R : CommRingCat.{u}) (I : Type u) where
  /-- The map on unit families over a ring `A` under `R`. -/
  app : ∀ {A : CommRingCat.{u}}, (R ⟶ A) → (I → Aˣ) → (I → Aˣ)
  app_mul : ∀ {A : CommRingCat.{u}} (α : R ⟶ A) (x y : I → Aˣ),
    app α (x * y) = app α x * app α y
  naturality : ∀ {A B : CommRingCat.{u}} (α : R ⟶ A) (f : A ⟶ B) (x : I → Aˣ),
    app (α ≫ f) (fun j => Units.map f.hom.toMonoidHom (x j)) =
      fun j => Units.map f.hom.toMonoidHom (app α x j)

namespace UnitsNatEnd

variable {R : CommRingCat.{u}} {I : Type u} (φ : UnitsNatEnd R I)

theorem naturality_of_eq {A B : CommRingCat.{u}} (α : R ⟶ A) (f : A ⟶ B) {β : R ⟶ B}
    (h : α ≫ f = β) (x : I → Aˣ) :
    φ.app β (fun j => Units.map f.hom.toMonoidHom (x j)) =
      fun j => Units.map f.hom.toMonoidHom (φ.app α x j) := by
  subst h
  exact φ.naturality α f x

/-- Change of coefficients `R[ℤ^I] ⟶ B[ℤ^I]` along `β : R ⟶ B`. -/
abbrev coeffMap {B : CommRingCat.{u}} (β : R ⟶ B) : laurentRing R I ⟶ laurentRing B I :=
  CommRingCat.ofHom (AddMonoidAlgebra.mapRingHom (I → ℤ) β.hom)

theorem laurentAlgebraMap_comp_coeffMap {B : CommRingCat.{u}} (β : R ⟶ B) :
    laurentAlgebraMap R I ≫ coeffMap β = β ≫ laurentAlgebraMap B I := by
  ext r
  simp [AddMonoidAlgebra.coe_algebraMap]

variable [DecidableEq I]

/-- The universal family of units: the monomials `T_j` of `R[ℤ^I]`. -/
abbrev universalUnits (R : CommRingCat.{u}) (I : Type u) [DecidableEq I] :
    I → (laurentRing R I)ˣ :=
  fun j => exponentUnit I (Pi.single j 1)

theorem coeffMap_universalUnits {B : CommRingCat.{u}} (β : R ⟶ B) :
    (fun j => Units.map (coeffMap (I := I) β).hom.toMonoidHom (universalUnits R I j)) =
      universalUnits B I := by
  funext j
  ext
  simp [coeffMap]

/-- The coordinates of the image of the universal family. -/
def coeffs (j : I) : AddMonoidAlgebra R (I → ℤ) :=
  ((φ.app (laurentAlgebraMap R I) (universalUnits R I) j : laurentRing R I) :
    AddMonoidAlgebra R (I → ℤ))

/-- The image of the universal family over `B` is the coefficient change of the image of the
universal family over `R`. -/
theorem app_universalUnits {B : CommRingCat.{u}} (β : R ⟶ B) (j : I) :
    ((φ.app (β ≫ laurentAlgebraMap B I) (universalUnits B I) j : laurentRing B I) :
      AddMonoidAlgebra B (I → ℤ)) = AddMonoidAlgebra.mapRingHom (I → ℤ) β.hom (φ.coeffs j) := by
  have h := φ.naturality_of_eq (laurentAlgebraMap R I) (coeffMap β)
    (laurentAlgebraMap_comp_coeffMap β) (universalUnits R I)
  rw [coeffMap_universalUnits] at h
  rw [h]
  rfl

section Coefficients

variable {S : Type u} [CommRing S] {M : Type u} [AddCommMonoid M] [DecidableEq M]

theorem coeff_mapDomain_inl_mul_inr (x y : AddMonoidAlgebra S M) (m m' : M) :
    (AddMonoidAlgebra.mapDomainRingHom S (AddMonoidHom.inl M M) x *
        AddMonoidAlgebra.mapDomainRingHom S (AddMonoidHom.inr M M) y).coeff (m, m') =
      x.coeff m * y.coeff m' := by
  classical
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x x' hx hx' =>
    rw [map_add, add_mul, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hx, hx',
      AddMonoidAlgebra.coeff_add, Finsupp.add_apply, add_mul]
  | single a r =>
    induction y using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add y y' hy hy' =>
      rw [map_add, mul_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hy, hy',
        AddMonoidAlgebra.coeff_add, Finsupp.add_apply, mul_add]
    | single b s =>
      simp only [AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single,
        AddMonoidAlgebra.single_mul_single, AddMonoidHom.inl_apply, AddMonoidHom.inr_apply,
        Prod.mk_add_mk, add_zero, zero_add, AddMonoidAlgebra.coeff_single, Finsupp.single_apply,
        Prod.mk.injEq]
      by_cases ha : a = m <;> by_cases hb : b = m' <;> simp [ha, hb]

theorem coeff_mapDomain_diag (x : AddMonoidAlgebra S M) (m m' : M) :
    (AddMonoidAlgebra.mapDomainRingHom S ((AddMonoidHom.id M).prod (AddMonoidHom.id M)) x).coeff
        (m, m') = if m = m' then x.coeff m else 0 := by
  classical
  induction x using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x x' hx hx' =>
    rw [map_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, hx, hx']
    split_ifs <;> simp
  | single a r =>
    simp only [AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single,
      AddMonoidHom.prod_apply, AddMonoidHom.id_apply, AddMonoidAlgebra.coeff_single,
      Finsupp.single_apply, Prod.mk.injEq]
    by_cases ha : a = m <;> by_cases hb : m = m'
    · subst ha hb; simp
    · subst ha; simp [hb]
    · simp [hb]
    · simp [ha, hb]

end Coefficients

open Classical in
/-- The coordinates of the image of the universal family are orthogonal idempotents. -/
theorem coeff_mul_coeff (j : I) (m m' : I → ℤ) :
    (φ.coeffs j).coeff m * (φ.coeffs j).coeff m' =
      if m = m' then (φ.coeffs j).coeff m else 0 := by
  let M := I → ℤ
  let R₂ : CommRingCat.{u} := CommRingCat.of (AddMonoidAlgebra R (M × M))
  let α₂ : R ⟶ R₂ := CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R (M × M)))
  let ι₁ : laurentRing R I ⟶ R₂ :=
    CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom R (AddMonoidHom.inl M M))
  let ι₂ : laurentRing R I ⟶ R₂ :=
    CommRingCat.ofHom (AddMonoidAlgebra.mapDomainRingHom R (AddMonoidHom.inr M M))
  let δ : laurentRing R I ⟶ R₂ := CommRingCat.ofHom
    (AddMonoidAlgebra.mapDomainRingHom R ((AddMonoidHom.id M).prod (AddMonoidHom.id M)))
  have h₁ : laurentAlgebraMap R I ≫ ι₁ = α₂ :=
    CommRingCat.hom_ext (AddMonoidAlgebra.mapDomainRingHom_comp_algebraMap _)
  have h₂ : laurentAlgebraMap R I ≫ ι₂ = α₂ :=
    CommRingCat.hom_ext (AddMonoidAlgebra.mapDomainRingHom_comp_algebraMap _)
  have hδ : laurentAlgebraMap R I ≫ δ = α₂ :=
    CommRingCat.hom_ext (AddMonoidAlgebra.mapDomainRingHom_comp_algebraMap _)
  have hprod : (fun j => Units.map ι₁.hom.toMonoidHom (universalUnits R I j)) *
      (fun j => Units.map ι₂.hom.toMonoidHom (universalUnits R I j)) =
        fun j => Units.map δ.hom.toMonoidHom (universalUnits R I j) := by
    funext j
    apply Units.ext
    change AddMonoidAlgebra.mapDomainRingHom R (AddMonoidHom.inl M M)
        (AddMonoidAlgebra.single (Pi.single j 1) 1) *
      AddMonoidAlgebra.mapDomainRingHom R (AddMonoidHom.inr M M)
        (AddMonoidAlgebra.single (Pi.single j 1) 1) =
      AddMonoidAlgebra.mapDomainRingHom R ((AddMonoidHom.id M).prod (AddMonoidHom.id M))
        (AddMonoidAlgebra.single (Pi.single j 1) 1)
    simp only [AddMonoidAlgebra.mapDomainRingHom_apply, AddMonoidAlgebra.mapDomain_single,
      AddMonoidAlgebra.single_mul_single, AddMonoidHom.inl_apply, AddMonoidHom.inr_apply,
      AddMonoidHom.prod_apply, AddMonoidHom.id_apply, Prod.mk_add_mk, add_zero, zero_add,
      mul_one]
  have key := φ.app_mul α₂ (fun j => Units.map ι₁.hom.toMonoidHom (universalUnits R I j))
    (fun j => Units.map ι₂.hom.toMonoidHom (universalUnits R I j))
  rw [hprod, φ.naturality_of_eq _ δ hδ, φ.naturality_of_eq _ ι₁ h₁,
    φ.naturality_of_eq _ ι₂ h₂] at key
  have key' := congrArg
    (fun x : I → R₂ˣ => ((x j : R₂) : AddMonoidAlgebra R (M × M)).coeff (m, m')) key
  simp only [Pi.mul_apply, Units.val_mul, Units.coe_map] at key'
  change (AddMonoidAlgebra.mapDomainRingHom R ((AddMonoidHom.id M).prod (AddMonoidHom.id M))
      (φ.coeffs j)).coeff (m, m') =
    (AddMonoidAlgebra.mapDomainRingHom R (AddMonoidHom.inl M M) (φ.coeffs j) *
      AddMonoidAlgebra.mapDomainRingHom R (AddMonoidHom.inr M M) (φ.coeffs j)).coeff (m, m')
    at key'
  rw [coeff_mapDomain_diag, coeff_mapDomain_inl_mul_inr] at key'
  exact key'.symm

theorem isIdempotentElem_coeff (j : I) (m : I → ℤ) : IsIdempotentElem ((φ.coeffs j).coeff m) := by
  classical
  have h := φ.coeff_mul_coeff j m m
  rw [ite_eq_left rfl] at h
  exact h

variable [Fintype I]

theorem powUnits_universalUnits (B : CommRingCat.{u}) (m : Matrix I I ℤ) :
    powUnits m (universalUnits B I) = fun j => exponentUnit I (m j) := by
  funext j
  have hsum : ∑ l, m j l • (Pi.single l (1 : ℤ) : I → ℤ) = m j := by
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  simp only [powUnits, exponentUnit, ← map_zpow, ← map_prod, ← ofAdd_zsmul, ← ofAdd_sum, hsum]

/-- **Comparison with a monomial map.** Over a ring `B` under `R`, the family agrees with the
monomial map of `m` on all rings under `B` exactly when every `m j`-th coefficient of the
`j`-th coordinate maps to `1` in `B`. -/
theorem forall_app_eq_powUnits_iff {B : CommRingCat.{u}} (β : R ⟶ B) (m : Matrix I I ℤ) :
    (∀ (A : CommRingCat.{u}) (f : B ⟶ A) (x : I → Aˣ), φ.app (β ≫ f) x = powUnits m x) ↔
      ∀ j, β ((φ.coeffs j).coeff (m j)) = 1 := by
  constructor
  · intro h j
    have h1 := congrArg
      (fun x : I → (laurentRing B I)ˣ =>
        ((x j : laurentRing B I) : AddMonoidAlgebra B (I → ℤ)).coeff (m j))
      (h (laurentRing B I) (laurentAlgebraMap B I) (universalUnits B I))
    simp only at h1
    rw [φ.app_universalUnits β j, powUnits_universalUnits] at h1
    simpa using h1
  · intro hβ A f x
    have hc : ∀ j, AddMonoidAlgebra.mapRingHom (I → ℤ) β.hom (φ.coeffs j) =
        AddMonoidAlgebra.single (m j) 1 := by
      intro j
      apply AddMonoidAlgebra.coeff_injective
      ext v
      rw [AddMonoidAlgebra.coeff_mapRingHom, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
      by_cases hv : m j = v
      · subst hv
        rw [ite_eq_left rfl]
        exact hβ j
      · rw [ite_eq_right hv]
        have h0 := φ.coeff_mul_coeff j v (m j)
        rw [ite_eq_right (Ne.symm hv)] at h0
        have h1 := congrArg β.hom h0
        rw [map_mul, map_zero] at h1
        change β ((φ.coeffs j).coeff v) * β ((φ.coeffs j).coeff (m j)) = 0 at h1
        rwa [hβ j, mul_one] at h1
    have hU : φ.app (β ≫ laurentAlgebraMap B I) (universalUnits B I) =
        fun j => exponentUnit I (m j) := by
      funext j
      ext
      rw [φ.app_universalUnits β j, hc j]
      rfl
    let _ : Algebra B A := f.hom.toAlgebra
    let ev : laurentRing B I ⟶ A := CommRingCat.ofHom (evaluateUnits (R := B) I x).toRingHom
    have hev : laurentAlgebraMap B I ≫ ev = f := by
      ext b
      change evaluateUnits (R := B) I x (algebraMap B (AddMonoidAlgebra B (I → ℤ)) b) = f b
      rw [AlgHom.commutes]
      rfl
    have hx : (fun j => Units.map ev.hom.toMonoidHom (universalUnits B I j)) = x := by
      funext j
      ext
      change evaluateUnits (R := B) I x (AddMonoidAlgebra.single (Pi.single j 1) 1) = (x j : A)
      rw [evaluateUnits_single, map_one, one_mul, exponentValue_single]
    have hm : (fun j => Units.map ev.hom.toMonoidHom (exponentUnit (R := B) I (m j))) =
        powUnits m x := by
      funext j
      ext
      change evaluateUnits (R := B) I x (AddMonoidAlgebra.single (m j) 1) = _
      rw [evaluateUnits_single, map_one, one_mul]
      rfl
    have h := φ.naturality_of_eq (β ≫ laurentAlgebraMap B I) ev
      (by rw [Category.assoc, hev]) (universalUnits B I)
    rw [hx, hU, hm] at h
    exact h

omit [Fintype I] in
/-- Over an integral domain under `R` the family is a monomial map: each coordinate has exactly
one coefficient mapping to `1`. -/
theorem exists_forall_coeff_eq_one {K : CommRingCat.{u}} [IsDomain K] (β : R ⟶ K) :
    ∃ m : Matrix I I ℤ, ∀ j, β ((φ.coeffs j).coeff (m j)) = 1 := by
  have h : ∀ j, ∃ v : I → ℤ, β ((φ.coeffs j).coeff v) = 1 := by
    intro j
    have hu := (φ.app (β ≫ laurentAlgebraMap K I) (universalUnits K I) j).ne_zero
    rw [φ.app_universalUnits β j] at hu
    obtain ⟨v, hv⟩ : ∃ v, (AddMonoidAlgebra.mapRingHom (I → ℤ) β.hom (φ.coeffs j)).coeff v ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hu
      apply AddMonoidAlgebra.coeff_injective
      ext v
      simp [hcon v]
    rw [AddMonoidAlgebra.coeff_mapRingHom] at hv
    refine ⟨v, ?_⟩
    have hid : IsIdempotentElem (β ((φ.coeffs j).coeff v)) :=
      (φ.isIdempotentElem_coeff j v).map β.hom
    rcases IsIdempotentElem.iff_eq_zero_or_one.1 hid with h0 | h1
    · exact absurd h0 hv
    · exact h1
  choose m hm using h
  exact ⟨Matrix.of m, hm⟩

end UnitsNatEnd

end Langlands.GroupScheme.splitTorus
