import Langlands.Algebra.HopfPointClosedLocus

/-! # Hopf points with the same kernel over a connected ring -/

noncomputable section

open TensorProduct

namespace Langlands.Algebra.HopfPointConnected

open HopfPointExtension HopfPointWeightWindow HopfPointClosedLocus

variable {R : Type*} [CommRing R] {A : Type*} [CommRing A] [Bialgebra R A]
  {D : Type*} [CommRing D] [Algebra R D] {M : Type*} [AddCommGroup M]

theorem coeff_diagMap [DecidableEq M] (y : AddMonoidAlgebra D M) (ψ ψ' : M) :
    (diagMap R D M y).coeff (ψ, ψ') = if ψ = ψ' then y.coeff ψ else 0 := by
  have hinj : Function.Injective ((AddMonoidHom.id M).prod (AddMonoidHom.id M)) := by
    intro a b h
    exact congrArg Prod.fst h
  change (Finsupp.mapDomain ((AddMonoidHom.id M).prod (AddMonoidHom.id M)) y.coeff) (ψ, ψ') = _
  split_ifs with h
  · subst h
    exact Finsupp.mapDomain_apply_of_injective hinj y.coeff ψ
  · apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨a, ha⟩
    apply h
    have h1 := congrArg Prod.fst ha
    have h2 := congrArg Prod.snd ha
    simp only [AddMonoidHom.prod_apply, AddMonoidHom.id_apply] at h1 h2
    rw [← h1, ← h2]

theorem groupCounit_apply (y : AddMonoidAlgebra D M) :
    groupCounit R D M y = y.coeff.sum (fun _ c => c) := by
  induction y using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
    rw [map_add, hx, hy, AddMonoidAlgebra.coeff_add, Finsupp.sum_add_index'] <;> simp
  | single a c => simp [groupCounit, AddMonoidAlgebra.lift_single]

/-- Over a nonzero ring whose only idempotents are `0` and `1`, a group-like element of a
group algebra is a monomial. -/
theorem exists_eq_single_of_grouplike [Nontrivial D]
    (hD : ∀ e : D, IsIdempotentElem e → e = 0 ∨ e = 1) {y : AddMonoidAlgebra D M}
    (hdiag : diagMap R D M y = inlMap R D M y * inrMap R D M y)
    (hcounit : groupCounit R D M y = 1) : ∃ χ, y = AddMonoidAlgebra.single χ 1 := by
  classical
  have key : ∀ ψ ψ', y.coeff ψ * y.coeff ψ' = if ψ = ψ' then y.coeff ψ else 0 := by
    intro ψ ψ'
    rw [← coeff_inlMap_mul_inrMap (R := R), ← hdiag, coeff_diagMap]
  have hidem : ∀ ψ, y.coeff ψ = 0 ∨ y.coeff ψ = 1 := by
    intro ψ
    apply hD
    have := key ψ ψ
    simp only [↓reduceIte] at this
    exact this
  have hne : ∃ χ, y.coeff χ ≠ 0 := by
    by_contra! h
    have hy : y.coeff = 0 := Finsupp.ext h
    rw [groupCounit_apply, hy, Finsupp.sum_zero_index] at hcounit
    exact zero_ne_one hcounit
  obtain ⟨χ, hχ⟩ := hne
  have h1 : y.coeff χ = 1 := (hidem χ).resolve_left hχ
  refine ⟨χ, ?_⟩
  apply AddMonoidAlgebra.coeff_injective
  ext ψ
  rw [AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  split_ifs with h
  · subst h
    exact h1
  · have := key ψ χ
    have h' : ψ ≠ χ := fun e => h e.symm
    simp only [h', ↓reduceIte, h1, mul_one] at this
    exact this

section Smul

theorem inlMap_smul (c : D) (y : AddMonoidAlgebra D M) :
    inlMap R D M (c • y) = c • inlMap R D M y :=
  map_smul (AddMonoidAlgebra.mapDomainAlgHom D D (AddMonoidHom.inl M M)) c y

theorem inrMap_smul (c : D) (y : AddMonoidAlgebra D M) :
    inrMap R D M (c • y) = c • inrMap R D M y :=
  map_smul (AddMonoidAlgebra.mapDomainAlgHom D D (AddMonoidHom.inr M M)) c y

theorem diagMap_smul (c : D) (y : AddMonoidAlgebra D M) :
    diagMap R D M (c • y) = c • diagMap R D M y :=
  map_smul (AddMonoidAlgebra.mapDomainAlgHom D D
    ((AddMonoidHom.id M).prod (AddMonoidHom.id M))) c y

theorem groupCounit_smul (c : D) (y : AddMonoidAlgebra D M) :
    groupCounit R D M (c • y) = c * groupCounit R D M y :=
  map_smul (AddMonoidAlgebra.lift D D M 1) c y

end Smul

section Square

variable {N : Type*} [AddCommGroup N] (τ : AddMonoidAlgebra D M →ₐ[D] AddMonoidAlgebra D N)

variable (R) in
/-- The square `τ ⊠ τ : D[M × M] → D[N × N]` of an algebra map `τ : D[M] → D[N]`. -/
def square : AddMonoidAlgebra D (M × M) →ₐ[D] AddMonoidAlgebra D (N × N) :=
  AddMonoidAlgebra.lift D (AddMonoidAlgebra D (N × N)) (M × M)
    { toFun := fun x =>
        inlMap R D N (τ (AddMonoidAlgebra.single (Multiplicative.toAdd x).1 1)) *
          inrMap R D N (τ (AddMonoidAlgebra.single (Multiplicative.toAdd x).2 1))
      map_one' := by
        simp only [toAdd_one, Prod.fst_zero, Prod.snd_zero]
        rw [← AddMonoidAlgebra.one_def, map_one, map_one, map_one, one_mul]
      map_mul' := fun x y => by
        have e1 : AddMonoidAlgebra.single (Multiplicative.toAdd (x * y)).1 (1 : D) =
            AddMonoidAlgebra.single (Multiplicative.toAdd x).1 1 *
              AddMonoidAlgebra.single (Multiplicative.toAdd y).1 1 := by
          rw [AddMonoidAlgebra.single_mul_single, one_mul]
          rfl
        have e2 : AddMonoidAlgebra.single (Multiplicative.toAdd (x * y)).2 (1 : D) =
            AddMonoidAlgebra.single (Multiplicative.toAdd x).2 1 *
              AddMonoidAlgebra.single (Multiplicative.toAdd y).2 1 := by
          rw [AddMonoidAlgebra.single_mul_single, one_mul]
          rfl
        rw [e1, e2, map_mul, map_mul, map_mul, map_mul]
        ring }

theorem square_single (a b : M) (c : D) :
    square R τ (AddMonoidAlgebra.single (a, b) c) =
      c • (inlMap R D N (τ (AddMonoidAlgebra.single a 1)) *
        inrMap R D N (τ (AddMonoidAlgebra.single b 1))) := by
  rw [square, AddMonoidAlgebra.lift_single]
  rfl

theorem tau_single (χ : M) (c : D) :
    τ (AddMonoidAlgebra.single χ c) = c • τ (AddMonoidAlgebra.single χ 1) := by
  rw [← map_smul, AddMonoidAlgebra.smul_single, smul_eq_mul, mul_one]

theorem square_inlMap (y : AddMonoidAlgebra D M) :
    square R τ (inlMap R D M y) = inlMap R D N (τ y) := by
  induction y using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | single χ c =>
    have h : inlMap R D M (AddMonoidAlgebra.single χ c) = AddMonoidAlgebra.single (χ, 0) c := by
      simp [inlMap]
    rw [h, square_single, tau_single τ χ c, inlMap_smul]
    congr 1
    rw [← AddMonoidAlgebra.one_def, map_one, map_one, mul_one]

theorem square_inrMap (y : AddMonoidAlgebra D M) :
    square R τ (inrMap R D M y) = inrMap R D N (τ y) := by
  induction y using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | single χ c =>
    have h : inrMap R D M (AddMonoidAlgebra.single χ c) = AddMonoidAlgebra.single (0, χ) c := by
      simp [inrMap]
    rw [h, square_single, tau_single τ χ c, inrMap_smul]
    congr 1
    rw [← AddMonoidAlgebra.one_def, map_one, map_one, one_mul]

theorem square_pairMap {α : A →ₐ[R] AddMonoidAlgebra D M} {β : A →ₐ[R] AddMonoidAlgebra D N}
    (hτ : ∀ a, τ (α a) = β a) (t : A ⊗[R] A) : square R τ (pairMap α t) = pairMap β t := by
  induction t with
  | tmul a b =>
    simp only [pairMap, Algebra.TensorProduct.lift_tmul, AlgHom.comp_apply, map_mul,
      square_inlMap, square_inrMap, hτ]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

variable {α : A →ₐ[R] AddMonoidAlgebra D M} {β : A →ₐ[R] AddMonoidAlgebra D N}

/-- A map intertwining two points intertwines their scalar extensions. -/
theorem tau_scalarExt (h : ∀ a, τ (α a) = β a) (x : D ⊗[R] A) :
    τ (scalarExt α x) = scalarExt β x := by
  induction x with
  | tmul d a => rw [scalarExt_tmul, scalarExt_tmul, map_smul, h]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

theorem diagMap_tau (hα : IsHopfPoint α) (hβ : IsHopfPoint β)
    (hs : Function.Surjective (scalarExt α)) (h : ∀ a, τ (α a) = β a)
    (y : AddMonoidAlgebra D M) : diagMap R D N (τ y) = square R τ (diagMap R D M y) := by
  obtain ⟨x, rfl⟩ := hs y
  rw [tau_scalarExt τ h]
  induction x with
  | tmul d a =>
    rw [scalarExt_tmul, scalarExt_tmul, diagMap_smul, diagMap_smul, map_smul]
    congr 1
    have h1 := congrArg (fun F => F a) hβ.comul
    have h2 := congrArg (fun F => F a) hα.comul
    simp only [AlgHom.comp_apply] at h1 h2
    rw [← h1, ← h2, square_pairMap τ h]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add, map_add]

theorem groupCounit_tau (hα : IsHopfPoint α) (hβ : IsHopfPoint β)
    (hs : Function.Surjective (scalarExt α)) (h : ∀ a, τ (α a) = β a)
    (y : AddMonoidAlgebra D M) : groupCounit R D N (τ y) = groupCounit R D M y := by
  obtain ⟨x, rfl⟩ := hs y
  rw [tau_scalarExt τ h]
  induction x with
  | tmul d a =>
    rw [scalarExt_tmul, scalarExt_tmul, groupCounit_smul, groupCounit_smul]
    congr 1
    have h1 := congrArg (fun F => F a) hβ.counit
    have h2 := congrArg (fun F => F a) hα.counit
    simp only [AlgHom.comp_apply] at h1 h2
    rw [h1, h2]
  | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add]

/-- Over a ring with only trivial idempotents, a map intertwining two Hopf points sends
monomials to monomials. -/
theorem exists_tau_single [Nontrivial D] (hD : ∀ e : D, IsIdempotentElem e → e = 0 ∨ e = 1)
    (hα : IsHopfPoint α) (hβ : IsHopfPoint β) (hs : Function.Surjective (scalarExt α))
    (h : ∀ a, τ (α a) = β a) (χ : M) :
    ∃ ψ, τ (AddMonoidAlgebra.single χ 1) = AddMonoidAlgebra.single ψ 1 := by
  apply exists_eq_single_of_grouplike (R := R) hD
  · rw [diagMap_tau τ hα hβ hs h]
    have : diagMap R D M (AddMonoidAlgebra.single χ 1) =
        AddMonoidAlgebra.single (χ, χ) (1 : D) := by
      simp [diagMap]
    rw [this, square_single, one_smul]
  · rw [groupCounit_tau τ hα hβ hs h]
    simp [groupCounit, AddMonoidAlgebra.lift_single]

end Square

/-- Over a nonzero ring with only trivial idempotents, two closed-immersion Hopf points
related by mutually inverse algebra maps of the group algebras differ by an isomorphism of
the character groups. -/
theorem exists_addEquiv_of_comp [Nontrivial D] {N : Type*} [AddCommGroup N]
    (hD : ∀ e : D, IsIdempotentElem e → e = 0 ∨ e = 1) {α : A →ₐ[R] AddMonoidAlgebra D M}
    {β : A →ₐ[R] AddMonoidAlgebra D N}
    (hα : IsHopfPoint α) (hβ : IsHopfPoint β) (hsα : Function.Surjective (scalarExt α))
    (hsβ : Function.Surjective (scalarExt β))
    (τ : AddMonoidAlgebra D M →ₐ[D] AddMonoidAlgebra D N)
    (τ' : AddMonoidAlgebra D N →ₐ[D] AddMonoidAlgebra D M)
    (hτ : ∀ a, τ (α a) = β a) (hτ' : ∀ a, τ' (β a) = α a) :
    ∃ T : M ≃+ N, (AddMonoidAlgebra.mapDomainAlgHom R D T.toAddMonoidHom).comp α = β := by
  classical
  choose T hT using exists_tau_single τ hD hα hβ hsα hτ
  choose T' hT' using exists_tau_single τ' hD hβ hα hsβ hτ'
  have hinv : ∀ y, τ' (τ y) = y := by
    intro y
    obtain ⟨x, rfl⟩ := hsα y
    rw [tau_scalarExt τ hτ, tau_scalarExt τ' hτ']
  have hinv' : ∀ y, τ (τ' y) = y := by
    intro y
    obtain ⟨x, rfl⟩ := hsβ y
    rw [tau_scalarExt τ' hτ', tau_scalarExt τ hτ]
  have hsingleM : ∀ (a b : M),
      AddMonoidAlgebra.single a (1 : D) = AddMonoidAlgebra.single b 1 → a = b :=
    fun a b h => AddMonoidAlgebra.single_left_injective one_ne_zero h
  have hsingleN : ∀ (a b : N),
      AddMonoidAlgebra.single a (1 : D) = AddMonoidAlgebra.single b 1 → a = b :=
    fun a b h => AddMonoidAlgebra.single_left_injective one_ne_zero h
  have hTT : ∀ χ, T' (T χ) = χ := by
    intro χ
    apply hsingleM
    rw [← hT', ← hT, hinv]
  have hTT' : ∀ χ, T (T' χ) = χ := by
    intro χ
    apply hsingleN
    rw [← hT, ← hT', hinv']
  have hadd : ∀ a b, T (a + b) = T a + T b := by
    intro a b
    apply hsingleN
    rw [← hT, ← one_mul (1 : D), ← AddMonoidAlgebra.single_mul_single, map_mul, hT, hT,
      AddMonoidAlgebra.single_mul_single, one_mul]
  let Te : M ≃+ N :=
    { toFun := T
      invFun := T'
      left_inv := hTT
      right_inv := hTT'
      map_add' := hadd }
  refine ⟨Te, ?_⟩
  apply AlgHom.ext
  intro a
  rw [AlgHom.comp_apply, ← hτ a]
  induction α a using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | single χ c =>
    rw [tau_single, hT, AddMonoidAlgebra.smul_single, smul_eq_mul, mul_one]
    simp [Te]

/-- Idempotents of a local ring are trivial. -/
theorem isIdempotentElem_eq_zero_or_one_of_isLocalRing [IsLocalRing D] (e : D)
    (he : IsIdempotentElem e) : e = 0 ∨ e = 1 := by
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self e with h | h
  · right
    exact h.mul_left_cancel (he.eq.trans (mul_one e).symm)
  · left
    have : e * (1 - e) = 0 := by rw [mul_sub, mul_one, he.eq, sub_self]
    exact (h.mul_left_eq_zero).mp this

variable {N : Type*} [AddCommGroup N]

/-- A kernel inclusion between scalar extensions, the first surjective, is realized by an
algebra map of the group algebras. -/
theorem exists_tau_of_ker_le {α : A →ₐ[R] AddMonoidAlgebra D M}
    {β : A →ₐ[R] AddMonoidAlgebra D N}
    (hs : Function.Surjective (scalarExt α))
    (h : RingHom.ker (scalarExt α) ≤ RingHom.ker (scalarExt β)) :
    ∃ τ : AddMonoidAlgebra D M →ₐ[D] AddMonoidAlgebra D N, ∀ a, τ (α a) = β a := by
  have h' : RingHom.ker (scalarExt α).toRingHom ≤ RingHom.ker (scalarExt β).toRingHom := h
  refine ⟨AlgHom.liftOfSurjective (scalarExt α) hs (scalarExt β) h', fun a => ?_⟩
  have h1 : scalarExt α ((1 : D) ⊗ₜ a) = α a := by rw [scalarExt_tmul, one_smul]
  have h2 : scalarExt β ((1 : D) ⊗ₜ a) = β a := by rw [scalarExt_tmul, one_smul]
  rw [← h1, AlgHom.liftOfSurjective_apply, h2]

theorem mapAlgHom_smul {E : Type*} [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E) (c : D)
    (z : AddMonoidAlgebra D M) :
    AddMonoidAlgebra.mapAlgHom M ψ (c • z) = ψ c • AddMonoidAlgebra.mapAlgHom M ψ z := by
  apply AddMonoidAlgebra.coeff_injective
  ext k
  simp [AddMonoidAlgebra.coeff_mapAlgHom, map_mul]

/-- Algebra maps of group algebras change coefficients. -/
theorem exists_baseChange_tau {E : Type*} [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E)
    (τ : AddMonoidAlgebra D M →ₐ[D] AddMonoidAlgebra D N) :
    ∃ τE : AddMonoidAlgebra E M →ₐ[E] AddMonoidAlgebra E N, ∀ y,
      τE (AddMonoidAlgebra.mapAlgHom M ψ y) = AddMonoidAlgebra.mapAlgHom N ψ (τ y) := by
  let φ : Multiplicative M →* AddMonoidAlgebra E N :=
    { toFun := fun x => AddMonoidAlgebra.mapAlgHom N ψ (τ (AddMonoidAlgebra.single
        (Multiplicative.toAdd x) 1))
      map_one' := by
        simp only [toAdd_one]
        rw [← AddMonoidAlgebra.one_def, map_one, map_one]
      map_mul' := fun x y => by
        have e : AddMonoidAlgebra.single (Multiplicative.toAdd (x * y)) (1 : D) =
            AddMonoidAlgebra.single (Multiplicative.toAdd x) 1 *
              AddMonoidAlgebra.single (Multiplicative.toAdd y) 1 := by
          rw [AddMonoidAlgebra.single_mul_single, one_mul]
          rfl
        rw [e, map_mul, map_mul] }
  refine ⟨AddMonoidAlgebra.lift E (AddMonoidAlgebra E N) M φ, fun y => ?_⟩
  induction y using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]
  | single χ c =>
    have h1 : AddMonoidAlgebra.mapAlgHom M ψ (AddMonoidAlgebra.single χ c) =
        AddMonoidAlgebra.single χ (ψ c) := by
      apply AddMonoidAlgebra.coeff_injective
      ext k
      simp
    rw [h1, AddMonoidAlgebra.lift_single, tau_single τ χ c, mapAlgHom_smul]
    rfl

/-- Two closed-immersion Hopf points with the same kernel differ, locally at every maximal
ideal, by an isomorphism of the character groups. -/
theorem exists_addEquiv_localization {α : A →ₐ[R] AddMonoidAlgebra D M}
    {β : A →ₐ[R] AddMonoidAlgebra D N}
    (hα : IsHopfPoint α) (hβ : IsHopfPoint β) (hsα : Function.Surjective (scalarExt α))
    (hsβ : Function.Surjective (scalarExt β))
    (hker : RingHom.ker (scalarExt α) = RingHom.ker (scalarExt β)) (P : Ideal D) [P.IsPrime] :
    ∃ T : M ≃+ N, (AddMonoidAlgebra.mapDomainAlgHom R (Localization.AtPrime P)
        T.toAddMonoidHom).comp ((AddMonoidAlgebra.mapAlgHom M
          (IsScalarTower.toAlgHom R D (Localization.AtPrime P))).comp α) =
      (AddMonoidAlgebra.mapAlgHom N (IsScalarTower.toAlgHom R D (Localization.AtPrime P))).comp β := by
  let loc := IsScalarTower.toAlgHom R D (Localization.AtPrime P)
  obtain ⟨τ, hτ⟩ := exists_tau_of_ker_le hsα hker.le
  obtain ⟨τ', hτ'⟩ := exists_tau_of_ker_le hsβ hker.ge
  obtain ⟨τP, hτP⟩ := exists_baseChange_tau loc τ
  obtain ⟨τP', hτP'⟩ := exists_baseChange_tau loc τ'
  apply exists_addEquiv_of_comp isIdempotentElem_eq_zero_or_one_of_isLocalRing
    (HopfPointWindowExtension.IsHopfPoint.mapAlgHom loc hα)
    (HopfPointWindowExtension.IsHopfPoint.mapAlgHom loc hβ)
    (surjective_scalarExt_mapAlgHom loc hsα) (surjective_scalarExt_mapAlgHom loc hsβ) τP τP'
  · intro a
    simp only [AlgHom.comp_apply]
    rw [hτP, hτ]
  · intro a
    simp only [AlgHom.comp_apply]
    rw [hτP', hτ']

end Langlands.Algebra.HopfPointConnected
