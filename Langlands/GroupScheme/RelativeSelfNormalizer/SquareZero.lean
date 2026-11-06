import Langlands.GroupScheme.CorepresentedNormalizer
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Finiteness.Nakayama
import Mathlib.LinearAlgebra.TensorProduct.Prod

/-! # Self-normalization of flat formally smooth cut-out subgroups from field-valued tests

For a group-valued functor `F` on commutative `R`-algebras, corepresented by `B`, and a family
`H` of subgroups cut out by a finitely generated ideal `I` with `B ⧸ I` flat and formally smooth
over `R`, the normalizer family of `H` is contained in `H` as soon as this holds on every
`R`-algebra whose structure map factors through a field.
-/

noncomputable section

universe u

open CategoryTheory
open scoped TensorProduct

namespace Langlands.GroupScheme.Corepresented

variable {R : CommRingCat.{u}} {F : CommAlgCat.{u} R ⥤ GrpCat.{u}} {B : CommAlgCat.{u} R}
  {e : (F ⋙ forget GrpCat).CorepresentableBy B}
  {H : ∀ A : CommAlgCat.{u} R, Subgroup (F.obj A)} {I : Ideal B}

section Families

variable (H) in
/-- The normalizer family is stable under every algebra map. -/
theorem map_mem_normalizerFamily {A A' : CommAlgCat.{u} R} (f : A ⟶ A') {g : F.obj A}
    (hg : g ∈ normalizerFamily H A) : F.map f g ∈ normalizerFamily H A' := by
  intro A'' f' x hx
  have h := hg A'' (f ≫ f') x hx
  rwa [F.map_comp, ConcreteCategory.comp_apply] at h

/-- A family cut out by an ideal lies in its own normalizer family. -/
theorem le_normalizerFamily (hH : IsCutOutBy e H I) (A : CommAlgCat.{u} R) :
    H A ≤ normalizerFamily H A := by
  intro h hh A' f x hx
  have h' := hH.map_mem f hh
  exact ⟨mul_mem (mul_mem h' hx) (inv_mem h'), mul_mem (mul_mem (inv_mem h') hx) h'⟩

end Families

section TensorMap

variable (I) in
/-- The map `A ⊗[R] (B ⧸ I) ⟶ A' ⊗[R] (B ⧸ I)` induced by an algebra map `f : A ⟶ A'`. -/
abbrev tensorQuotientMapOf {A A' : CommAlgCat.{u} R} (f : A ⟶ A') :
    tensorQuotient I A ⟶ tensorQuotient I A' :=
  CommAlgCat.ofHom (Algebra.TensorProduct.map f.hom (AlgHom.id R (B ⧸ I)))

theorem tensorQuotientMapOf_apply {A A' : CommAlgCat.{u} R} (f : A ⟶ A')
    (z : A ⊗[R] (B ⧸ I)) :
    (tensorQuotientMapOf I f).hom z = f.hom.toLinearMap.rTensor (B ⧸ I) z := by
  induction z with
  | tmul a q => rfl
  | add z z' hz hz' => rw [map_add, map_add, hz, hz']

theorem tensorQuotientLeft_comp_mapOf {A A' : CommAlgCat.{u} R} (f : A ⟶ A') :
    tensorQuotientLeft I A ≫ tensorQuotientMapOf I f = f ≫ tensorQuotientLeft I A' := by
  ext a
  change Algebra.TensorProduct.map f.hom (AlgHom.id R (B ⧸ I)) (a ⊗ₜ 1) = f a ⊗ₜ 1
  simp

theorem map_universalCutPoint_mapOf {A A' : CommAlgCat.{u} R} (f : A ⟶ A') :
    F.map (tensorQuotientMapOf I f) (universalCutPoint e I A) = universalCutPoint e I A' := by
  rw [universalCutPoint, universalCutPoint]
  erw [← e.homEquiv_comp]
  congr 1
  ext b
  change Algebra.TensorProduct.map f.hom (AlgHom.id R (B ⧸ I)) (1 ⊗ₜ Ideal.Quotient.mk I b) =
    1 ⊗ₜ Ideal.Quotient.mk I b
  simp

theorem map_conjugate_mapOf {A A' : CommAlgCat.{u} R} (f : A ⟶ A') (g : F.obj A) :
    F.map (tensorQuotientMapOf I f) (F.map (tensorQuotientLeft I A) g * universalCutPoint e I A *
        (F.map (tensorQuotientLeft I A) g)⁻¹) =
      F.map (tensorQuotientLeft I A') (F.map f g) * universalCutPoint e I A' *
        (F.map (tensorQuotientLeft I A') (F.map f g))⁻¹ := by
  rw [map_mul, map_mul, map_inv, map_universalCutPoint_mapOf, ← ConcreteCategory.comp_apply,
    ← F.map_comp, tensorQuotientLeft_comp_mapOf, F.map_comp, ConcreteCategory.comp_apply]

theorem map_invConjugate_mapOf {A A' : CommAlgCat.{u} R} (f : A ⟶ A') (g : F.obj A) :
    F.map (tensorQuotientMapOf I f) ((F.map (tensorQuotientLeft I A) g)⁻¹ *
        universalCutPoint e I A * F.map (tensorQuotientLeft I A) g) =
      (F.map (tensorQuotientLeft I A') (F.map f g))⁻¹ * universalCutPoint e I A' *
        F.map (tensorQuotientLeft I A') (F.map f g) := by
  rw [map_mul, map_mul, map_inv, map_universalCutPoint_mapOf, ← ConcreteCategory.comp_apply,
    ← F.map_comp, tensorQuotientLeft_comp_mapOf, F.map_comp, ConcreteCategory.comp_apply]

end TensorMap

section Pairs

variable {A : CommAlgCat.{u} R}

/-- The algebra of pairs of elements of `A` that are congruent modulo `J`. -/
abbrev congruencePairs (J : Ideal A) : Subalgebra R (A × A) :=
  AlgHom.equalizer ((Ideal.Quotient.mkₐ R J).comp (AlgHom.fst R A A))
    ((Ideal.Quotient.mkₐ R J).comp (AlgHom.snd R A A))

theorem mem_congruencePairs {J : Ideal A} (x : A × A) :
    x ∈ congruencePairs J ↔ x.1 - x.2 ∈ J := by
  rw [AlgHom.mem_equalizer]
  exact Ideal.Quotient.eq

/-- The first projection from the congruence pairs. -/
abbrev pairFst (J : Ideal A) : CommAlgCat.of R (congruencePairs J) ⟶ A :=
  CommAlgCat.ofHom ((AlgHom.fst R A A).comp (congruencePairs J).val)

/-- The second projection from the congruence pairs. -/
abbrev pairSnd (J : Ideal A) : CommAlgCat.of R (congruencePairs J) ⟶ A :=
  CommAlgCat.ofHom ((AlgHom.snd R A A).comp (congruencePairs J).val)

/-- Two classifying maps that agree modulo `J` define a map into the congruence pairs. -/
def pairMap {J : Ideal A} (η γ : B ⟶ A)
    (h : ∀ b, Ideal.Quotient.mk J (η.hom b) = Ideal.Quotient.mk J (γ.hom b)) :
    B ⟶ CommAlgCat.of R (congruencePairs J) :=
  CommAlgCat.ofHom ((η.hom.prod γ.hom).codRestrict (congruencePairs J) fun b => h b)

theorem pairMap_fst {J : Ideal A} (η γ : B ⟶ A)
    (h : ∀ b, Ideal.Quotient.mk J (η.hom b) = Ideal.Quotient.mk J (γ.hom b)) :
    pairMap η γ h ≫ pairFst J = η := rfl

theorem pairMap_snd {J : Ideal A} (η γ : B ⟶ A)
    (h : ∀ b, Ideal.Quotient.mk J (η.hom b) = Ideal.Quotient.mk J (γ.hom b)) :
    pairMap η γ h ≫ pairSnd J = γ := rfl

/-- Flatness of `B ⧸ I`: an element of `P ⊗[R] (B ⧸ I)` vanishing under both projections is
zero. -/
theorem tensor_eq_zero_of_pair [Module.Flat R (B ⧸ I)] {J : Ideal A}
    (z : congruencePairs J ⊗[R] (B ⧸ I))
    (h₁ : (pairFst J).hom.toLinearMap.rTensor (B ⧸ I) z = 0)
    (h₂ : (pairSnd J).hom.toLinearMap.rTensor (B ⧸ I) z = 0) : z = 0 := by
  let P := congruencePairs J
  let v : P →ₗ[R] A × A := P.val.toLinearMap
  have hinj : Function.Injective (v.rTensor (B ⧸ I)) :=
    Module.Flat.rTensor_preserves_injective_linearMap v Subtype.val_injective
  have key : ∀ w : (A × A) ⊗[R] (B ⧸ I), TensorProduct.prodLeft R R A A (B ⧸ I) w =
      ((LinearMap.fst R A A).rTensor (B ⧸ I) w, (LinearMap.snd R A A).rTensor (B ⧸ I) w) := by
    intro w
    induction w using TensorProduct.inductionOn with
    | tmul x c =>
      obtain ⟨a, a'⟩ := x
      simp
    | add w w' hw hw' => rw [map_add, hw, hw', map_add, map_add, Prod.mk_add_mk]
  have hfst : (pairFst J).hom.toLinearMap = (LinearMap.fst R A A).comp v := rfl
  have hsnd : (pairSnd J).hom.toLinearMap = (LinearMap.snd R A A).comp v := rfl
  apply hinj
  rw [map_zero]
  apply (TensorProduct.prodLeft R R A A (B ⧸ I)).injective
  rw [key, map_zero, ← LinearMap.rTensor_comp_apply, ← LinearMap.rTensor_comp_apply, ← hfst,
    ← hsnd, h₁, h₂]
  rfl

/-- The ideal of diagonal pairs `(a, a)` with `a ∈ m`, when `m * J = 0`. -/
def diagonalIdeal (m J : Ideal A) (hmJ : m * J = ⊥) : Ideal (congruencePairs J) where
  carrier := {x | (x : A × A).1 ∈ m ∧ (x : A × A).1 = (x : A × A).2}
  zero_mem' := ⟨m.zero_mem, rfl⟩
  add_mem' := by
    rintro x y ⟨hx₁, hx₂⟩ ⟨hy₁, hy₂⟩
    refine ⟨m.add_mem hx₁ hy₁, ?_⟩
    change (x : A × A).1 + (y : A × A).1 = (x : A × A).2 + (y : A × A).2
    rw [hx₂, hy₂]
  smul_mem' := by
    rintro c x ⟨hx₁, hx₂⟩
    refine ⟨m.mul_mem_left _ hx₁, ?_⟩
    change (c : A × A).1 * (x : A × A).1 = (c : A × A).2 * (x : A × A).2
    have hc : (c : A × A).1 - (c : A × A).2 ∈ J := (mem_congruencePairs _).1 c.2
    have h0 : (x : A × A).1 * ((c : A × A).1 - (c : A × A).2) = 0 := by
      have := Ideal.mul_mem_mul hx₁ hc
      rwa [hmJ, Ideal.mem_bot] at this
    rw [← hx₂]
    linear_combination h0

theorem mem_diagonalIdeal {m J : Ideal A} {hmJ : m * J = ⊥} (x : congruencePairs J) :
    x ∈ diagonalIdeal m J hmJ ↔ (x : A × A).1 ∈ m ∧ (x : A × A).1 = (x : A × A).2 :=
  Iff.rfl

/-- The diagonal ring map `A → P`. -/
def diagonalMap (J : Ideal A) : A →+* congruencePairs J :=
  ((RingHom.id A).prod (RingHom.id A)).codRestrict (congruencePairs J) fun a => by
    rw [mem_congruencePairs]
    simp

/-- The residue field `A ⧸ m` maps to `P ⧸ diagonalIdeal m J`. -/
def residueMap (m J : Ideal A) (hmJ : m * J = ⊥) :
    A ⧸ m →+* congruencePairs J ⧸ diagonalIdeal m J hmJ :=
  Ideal.Quotient.lift m ((Ideal.Quotient.mk _).comp (diagonalMap J)) fun _ ha =>
    Ideal.Quotient.eq_zero_iff_mem.2 ⟨ha, rfl⟩

theorem residueMap_comp_algebraMap (m J : Ideal A) (hmJ : m * J = ⊥) :
    (residueMap m J hmJ).comp (algebraMap R (A ⧸ m)) =
      algebraMap R (congruencePairs J ⧸ diagonalIdeal m J hmJ) := by
  ext r
  rfl

end Pairs

section Ideals

/-- **Nakayama's lemma**, global form: a finitely generated ideal `J` with `J ≤ m * J` for every
maximal ideal `m` is zero. -/
theorem eq_bot_of_le_mul_maximal {A : Type*} [CommRing A] {J : Ideal A} (hJ : J.FG)
    (h : ∀ m : Ideal A, m.IsMaximal → J ≤ m * J) : J = ⊥ := by
  have hann : Submodule.annihilator J = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨r, hr1, hr⟩ :=
      Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul m J hJ
        (by rw [Ideal.smul_eq_mul]; exact h m hm)
    have hr' : r ∈ m := hle (Submodule.mem_annihilator.2 hr)
    exact hm.ne_top ((Ideal.eq_top_iff_one m).2 (by simpa using m.sub_mem hr' hr1))
  rw [eq_bot_iff]
  intro x hx
  have h1 : (1 : A) ∈ Submodule.annihilator J := hann ▸ Submodule.mem_top
  have h2 := Submodule.mem_annihilator.1 h1 x hx
  rw [one_smul] at h2
  exact (Ideal.mem_bot).2 h2

/-- The image of a maximal ideal `m` in a quotient by an ideal contained in `m` is maximal. -/
theorem isMaximal_map_mk {A : Type*} [CommRing A] (m K : Ideal A) [hm : m.IsMaximal]
    (hK : K ≤ m) : (m.map (Ideal.Quotient.mk K)).IsMaximal := by
  refine (Ideal.map_eq_top_or_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
    hm).resolve_left ?_
  intro htop
  apply hm.ne_top
  have h := Ideal.comap_map_of_surjective (Ideal.Quotient.mk K) Ideal.Quotient.mk_surjective m
  rw [htop, Ideal.comap_top, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_of_le_left hK] at h
  exact h.symm

/-- `m * J` becomes zero in `A ⧸ m * J`. -/
theorem map_mk_mul_map_eq_bot {A : Type*} [CommRing A] (m J : Ideal A) :
    m.map (Ideal.Quotient.mk (m * J)) * J.map (Ideal.Quotient.mk (m * J)) = ⊥ := by
  rw [← Ideal.map_mul, Ideal.map_quotient_self]

end Ideals

section Main

/-- The field hypothesis: on every `R`-algebra whose structure map factors through a field,
the normalizer family of `H` is `H`. -/
def FieldNormalizerCondition (H : ∀ A : CommAlgCat.{u} R, Subgroup (F.obj A)) : Prop :=
  ∀ (E : CommAlgCat.{u} R) (k : Type u) [Field k] (ρ : R →+* k) (φ : k →+* E),
    φ.comp ρ = algebraMap R E → normalizerFamily H E ≤ H E

variable [Module.Flat R (B ⧸ I)] [Algebra.FormallySmooth R (B ⧸ I)]

/-- The square-zero step: if `m * J = 0` for a maximal ideal `m`, where `J` is the ideal
generated by the image of `I` under the classifying map of a normalizing point `g`, then `g`
lies in `H`. -/
theorem mem_of_mul_eq_bot (hH : IsCutOutBy e H I) (hfield : FieldNormalizerCondition H)
    {A : CommAlgCat.{u} R} (m : Ideal A) [hm : m.IsMaximal] {g : F.obj A}
    (hg : g ∈ normalizerFamily H A) (hmJ : m * I.map (e.homEquiv.symm g).hom = ⊥) :
    g ∈ H A := by
  set γ := e.homEquiv.symm g with hγ
  set J := I.map γ.hom with hJ
  let _ : Field (A ⧸ m) := Ideal.Quotient.field m
  -- The residue-field test: `J ≤ m`.
  have hJm : J ≤ m := by
    let E₀ : CommAlgCat.{u} R := CommAlgCat.of R (A ⧸ m)
    let q : A ⟶ E₀ := CommAlgCat.ofHom (Ideal.Quotient.mkₐ R m)
    have h0 : F.map q g ∈ H E₀ :=
      hfield E₀ (A ⧸ m) (algebraMap R (A ⧸ m)) (RingHom.id _) rfl
        (map_mem_normalizerFamily H q hg)
    rw [hH] at h0
    rw [Ideal.map_le_iff_le_comap]
    intro b hb
    have h1 := h0 b hb
    rw [homEquiv_symm_map] at h1
    change Ideal.Quotient.mk m (γ.hom b) = 0 at h1
    exact Ideal.mem_comap.2 (Ideal.Quotient.eq_zero_iff_mem.1 h1)
  have hJJ : J ^ 2 = ⊥ := by
    rw [pow_two, eq_bot_iff, ← hmJ]
    exact Ideal.mul_mono_left hJm
  have hnil : IsNilpotent J := ⟨2, hJJ⟩
  -- Lift the reduction of `g` modulo `J` to a point of `H`.
  have hγJ : ∀ b ∈ I, (Ideal.Quotient.mkₐ R J).comp γ.hom b = 0 := fun b hb =>
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ hb)
  let γbar : B ⧸ I →ₐ[R] A ⧸ J := Ideal.Quotient.liftₐ I ((Ideal.Quotient.mkₐ R J).comp γ.hom) hγJ
  let θ : B ⧸ I →ₐ[R] A := Algebra.FormallySmooth.lift J hnil γbar
  let η : B ⟶ A := CommAlgCat.ofHom (θ.comp (Ideal.Quotient.mkₐ R I))
  have hη : ∀ b ∈ I, η.hom b = 0 := by
    intro b hb
    change θ (Ideal.Quotient.mk I b) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.2 hb, map_zero]
  have hηγ : ∀ b, Ideal.Quotient.mk J (η.hom b) = Ideal.Quotient.mk J (γ.hom b) := by
    intro b
    change Ideal.Quotient.mk J (θ (Ideal.Quotient.mk I b)) = _
    rw [Algebra.FormallySmooth.mk_lift]
    rfl
  -- The pair `(η, γ)` over the congruence pairs normalizes `H`.
  let P : CommAlgCat.{u} R := CommAlgCat.of R (congruencePairs J)
  let δ : B ⟶ P := pairMap η γ hηγ
  let pt : F.obj P := e.homEquiv δ
  have hpt₁ : F.map (pairFst J) pt = e.homEquiv η := by
    rw [← pairMap_fst η γ hηγ]
    exact (e.homEquiv_comp (pairFst J) δ).symm
  have hpt₂ : F.map (pairSnd J) pt = g := by
    have h := (e.homEquiv_comp (pairSnd J) δ).symm
    rw [pairMap_snd] at h
    exact h.trans (e.homEquiv.apply_symm_apply g)
  have hηH : e.homEquiv η ∈ H A := by
    rw [hH, Equiv.symm_apply_apply]
    exact hη
  have hmem : ∀ y : F.obj (tensorQuotient I P),
      F.map (tensorQuotientMapOf I (pairFst J)) y ∈ H (tensorQuotient I A) →
      F.map (tensorQuotientMapOf I (pairSnd J)) y ∈ H (tensorQuotient I A) →
      y ∈ H (tensorQuotient I P) := by
    intro y hy₁ hy₂
    rw [hH] at hy₁ hy₂ ⊢
    intro b hb
    apply tensor_eq_zero_of_pair
    · have h := hy₁ b hb
      rwa [homEquiv_symm_map, CommAlgCat.hom_comp, AlgHom.comp_apply,
        tensorQuotientMapOf_apply] at h
    · have h := hy₂ b hb
      rwa [homEquiv_symm_map, CommAlgCat.hom_comp, AlgHom.comp_apply,
        tensorQuotientMapOf_apply] at h
  have hptN : pt ∈ normalizerFamily H P := by
    rw [mem_normalizerFamily_iff hH]
    have hN₁ := (mem_normalizerFamily_iff hH (e.homEquiv η)).1 (le_normalizerFamily hH A hηH)
    have hN₂ := (mem_normalizerFamily_iff hH g).1 hg
    constructor
    · apply hmem
      · rw [map_conjugate_mapOf, hpt₁]
        exact hN₁.1
      · rw [map_conjugate_mapOf, hpt₂]
        exact hN₂.1
    · apply hmem
      · rw [map_invConjugate_mapOf, hpt₁]
        exact hN₁.2
      · rw [map_invConjugate_mapOf, hpt₂]
        exact hN₂.2
  -- Push the pair to the algebra `P ⧸ K` over the residue field.
  let K := diagonalIdeal m J hmJ
  let E : CommAlgCat.{u} R := CommAlgCat.of R (congruencePairs J ⧸ K)
  let ψ : P ⟶ E := CommAlgCat.ofHom (Ideal.Quotient.mkₐ R K)
  have hD : F.map ψ pt ∈ H E :=
    hfield E (A ⧸ m) (algebraMap R (A ⧸ m)) (residueMap m J hmJ)
      (residueMap_comp_algebraMap m J hmJ) (map_mem_normalizerFamily H ψ hptN)
  rw [hH] at hD
  rw [hH]
  intro b hb
  have h1 := hD b hb
  rw [homEquiv_symm_map, Equiv.symm_apply_apply] at h1
  have h2 : δ.hom b ∈ K := Ideal.Quotient.eq_zero_iff_mem.1 h1
  have h3 : η.hom b = γ.hom b := h2.2
  rw [← h3]
  exact hη b hb

/-- For a normalizing point `g` with classifying ideal `J = I.map γ` and a maximal ideal `m`,
the square-zero step over `A ⧸ m * J` gives `J ≤ m * J`. -/
theorem le_mul_of_isMaximal (hH : IsCutOutBy e H I) (hfield : FieldNormalizerCondition H)
    {A : CommAlgCat.{u} R} {g : F.obj A} (hg : g ∈ normalizerFamily H A) (m : Ideal A)
    [m.IsMaximal] :
    I.map (e.homEquiv.symm g).hom ≤ m * I.map (e.homEquiv.symm g).hom := by
  let K : Ideal A := m * I.map (e.homEquiv.symm g).hom
  let A₁ : CommAlgCat.{u} R := CommAlgCat.of R (A ⧸ K)
  let π : A ⟶ A₁ := CommAlgCat.ofHom (Ideal.Quotient.mkₐ R K)
  let m₁ : Ideal A₁ := m.map π.hom
  have hm₁ : m₁.IsMaximal := isMaximal_map_mk m K Ideal.mul_le_left
  have h3 :
      I.map (e.homEquiv.symm (F.map π g)).hom ≤ (I.map (e.homEquiv.symm g).hom).map π.hom := by
    rw [Ideal.map_le_iff_le_comap]
    intro b hb
    rw [Ideal.mem_comap, homEquiv_symm_map]
    exact Ideal.mem_map_of_mem π.hom (Ideal.mem_map_of_mem _ hb)
  have h0 : m₁ * (I.map (e.homEquiv.symm g).hom).map π.hom = ⊥ := map_mk_mul_map_eq_bot m _
  have h1 : F.map π g ∈ H A₁ := by
    refine mem_of_mul_eq_bot (hm := hm₁) hH hfield m₁ (map_mem_normalizerFamily H π hg) ?_
    rw [eq_bot_iff, ← h0]
    exact Ideal.mul_mono_right h3
  rw [hH] at h1
  rw [Ideal.map_le_iff_le_comap]
  intro b hb
  have h2 := h1 b hb
  rw [homEquiv_symm_map] at h2
  change Ideal.Quotient.mk K ((e.homEquiv.symm g).hom b) = 0 at h2
  exact Ideal.mem_comap.2 (Ideal.Quotient.eq_zero_iff_mem.1 h2)

/-- **Detection on field-valued tests.** If `H` is cut out by a finitely generated ideal `I`
with `B ⧸ I` flat and formally smooth, and the normalizer family of `H` is contained in `H` on
every algebra over a field, then it is contained in `H` on every algebra. -/
theorem normalizerFamily_le_of_field (hH : IsCutOutBy e H I) (hI : I.FG)
    (hfield : FieldNormalizerCondition H) (A : CommAlgCat.{u} R) :
    normalizerFamily H A ≤ H A := by
  intro g hg
  have hJ0 : I.map (e.homEquiv.symm g).hom = ⊥ :=
    eq_bot_of_le_mul_maximal (hI.map _) fun m _ => le_mul_of_isMaximal hH hfield hg m
  rw [hH]
  intro b hb
  have h := Ideal.mem_map_of_mem (e.homEquiv.symm g).hom hb
  rw [hJ0] at h
  exact (Ideal.mem_bot).1 h

end Main

end Langlands.GroupScheme.Corepresented
