import Langlands.GroupScheme.Torus.TorsionDetermination.Algebra
import Langlands.GroupScheme.Torus.TorsionDetermination.FieldPointLift
import Langlands.GroupScheme.Torus.Diagonalizable
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.RingTheory.Localization.FractionRing

/-! # Torsion determination for diagonalizable groups over an affine base -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.TorsionDetermination

/-- The points of `G` that factor through `i : Z ⟶ G.X` are closed under multiplication and
contain every torsion point, over every test scheme. -/
structure TorsionClosed {S : Scheme.{u}} {G : GroupScheme S} {Z : Over S} (i : Z ⟶ G.X) :
    Prop where
  mul : ∀ (T : Over S) (x y : T ⟶ G.X), (∃ a, a ≫ i = x) → (∃ b, b ≫ i = y) →
    ∃ c, c ≫ i = x * y
  torsion : ∀ n : ℕ, 0 < n → ∀ (T : Over S) (x : T ⟶ G.X), x ^ n = 1 → ∃ a, a ≫ i = x

/-! ### The generic point of `K[ℤ^I]` -/

/-- A locally closed subset of `Spec K[ℤ^I]` containing the images of all points of the
`Spec K[(ℤ/n)^I]` (`n > 0` invertible in `K`) contains the generic point. -/
theorem bot_mem_of_isLocallyClosed {K : Type u} [Field K] {I : Type u} [Fintype I]
    {s : Set (PrimeSpectrum (AddMonoidAlgebra K (I → ℤ)))} (hs : IsLocallyClosed s)
    (h : ∀ n : ℕ, 0 < n → (n : K) ≠ 0 →
      ∀ q : PrimeSpectrum (AddMonoidAlgebra K (I → ZMod n)),
        PrimeSpectrum.comap (AddMonoidAlgebra.mapDomainRingHom K (castPi I n)) q ∈ s) :
    (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (AddMonoidAlgebra K (I → ℤ))) ∈ s := by
  obtain ⟨U, C, hU, hC, rfl⟩ := hs
  obtain ⟨q⟩ : Nonempty (PrimeSpectrum (AddMonoidAlgebra K (I → ZMod 1))) := inferInstance
  have h1 := h 1 one_pos (by simp) q
  refine ⟨?_, ?_⟩
  · exact Specializes.mem_open ((PrimeSpectrum.le_iff_specializes _ _).mp bot_le) hU h1.1
  · rw [← hC.closure_eq, ← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure,
      PrimeSpectrum.mem_zeroLocus]
    intro a ha
    change a ∈ (⊥ : Ideal _)
    rw [Ideal.mem_bot]
    by_contra hne
    obtain ⟨n, hn, hnK, hnil⟩ := exists_not_isNilpotent_mapDomain_castPi hne
    rw [nilpotent_iff_mem_prime] at hnil
    push Not at hnil
    obtain ⟨J, hJ, haJ⟩ := hnil
    have hmem := (h n hn hnK ⟨J, hJ⟩).2
    exact haJ ((PrimeSpectrum.mem_vanishingIdeal _ _).mp ha _ hmem)

section Points

variable {R : CommRingCat.{u}} {Λ : Type u} [AddCommGroup Λ]

/-- Points of `D(Λ)` over `Spec S` are the characters `Λ → Sˣ`. -/
def affineCharEquiv (S : CommAlgCat.{u} R) :
    ((algSpec R).obj (op S) ⟶ (Diagonalizable.groupScheme R Λ).X) ≃*
      (Multiplicative Λ →* Sˣ) :=
  Corepresented.affinePointsEquiv (Diagonalizable.functor R Λ)
    (Diagonalizable.grpCorepresentation R Λ) S

/-- The point of `D(Λ)` over `Spec S` classified by a character `χ : Λ → Sˣ`. -/
abbrev charPoint {S : CommAlgCat.{u} R} (χ : Multiplicative Λ →* Sˣ) :
    (algSpec R).obj (op S) ⟶ (Diagonalizable.groupScheme R Λ).X :=
  (affineCharEquiv S).symm χ

/-- Push a character forward along an algebra map. -/
abbrev charMap {S S' : CommAlgCat.{u} R} (g : S ⟶ S') (χ : Multiplicative Λ →* Sˣ) :
    Multiplicative Λ →* S'ˣ :=
  (Units.map g.hom.toRingHom.toMonoidHom).comp χ

theorem charPoint_eq {S : CommAlgCat.{u} R} (χ : Multiplicative Λ →* Sˣ) :
    charPoint χ = (algSpec R).map (Diagonalizable.lift R Λ χ).op := by
  apply (affineCharEquiv S).injective
  rw [MulEquiv.apply_symm_apply]
  refine Eq.trans ?_ (Corepresented.affinePointsEquiv_map (Diagonalizable.functor R Λ)
    (Diagonalizable.grpCorepresentation R Λ) S (Diagonalizable.lift R Λ χ)).symm
  exact ((Diagonalizable.corepresentation R Λ).homEquiv.apply_symm_apply χ).symm

theorem charPoint_left_apply {S : CommAlgCat.{u} R} (χ : Multiplicative Λ →* Sˣ)
    (q : PrimeSpectrum S) :
    (charPoint χ).left q =
      PrimeSpectrum.comap (Diagonalizable.lift R Λ χ).hom.toRingHom q := by
  rw [charPoint_eq]
  rfl

theorem lift_charMap {S S' : CommAlgCat.{u} R} (g : S ⟶ S') (χ : Multiplicative Λ →* Sˣ) :
    Diagonalizable.lift R Λ (charMap g χ) = Diagonalizable.lift R Λ χ ≫ g := by
  apply CommAlgCat.hom_ext
  apply AddMonoidAlgebra.algHom_ext
  · intro character
    simp
  · exact Subsingleton.elim _ _

theorem comp_charPoint {S S' : CommAlgCat.{u} R} (g : S ⟶ S') (χ : Multiplicative Λ →* Sˣ) :
    (algSpec R).map g.op ≫ charPoint χ = charPoint (charMap g χ) := by
  rw [charPoint_eq, charPoint_eq, lift_charMap, ← Functor.map_comp]
  rfl

theorem charPoint_mul {S : CommAlgCat.{u} R} (χ ψ : Multiplicative Λ →* Sˣ) :
    charPoint (χ * ψ) = charPoint χ * charPoint ψ :=
  map_mul (affineCharEquiv S).symm χ ψ

theorem charPoint_pow {S : CommAlgCat.{u} R} (χ : Multiplicative Λ →* Sˣ) (n : ℕ) :
    charPoint (χ ^ n) = charPoint χ ^ n :=
  map_pow (affineCharEquiv S).symm χ n

theorem charPoint_one {S : CommAlgCat.{u} R} :
    charPoint (1 : Multiplicative Λ →* Sˣ) = 1 :=
  map_one (affineCharEquiv S).symm

variable {Z : Over (Spec R)} (i : Z ⟶ (Diagonalizable.groupScheme R Λ).X)

/-- A character lifts through `i` if the point it classifies factors through `i`. -/
def Lifts {S : CommAlgCat.{u} R} (χ : Multiplicative Λ →* Sˣ) : Prop :=
  ∃ a : (algSpec R).obj (op S) ⟶ Z, a ≫ i = charPoint χ

variable {i}

theorem Lifts.map {S S' : CommAlgCat.{u} R} {χ : Multiplicative Λ →* Sˣ} (h : Lifts i χ)
    (g : S ⟶ S') : Lifts i (charMap g χ) := by
  obtain ⟨a, ha⟩ := h
  exact ⟨(algSpec R).map g.op ≫ a, by rw [Category.assoc, ha, comp_charPoint]⟩

theorem Lifts.mem_range {S : CommAlgCat.{u} R} {χ : Multiplicative Λ →* Sˣ} (h : Lifts i χ)
    (q : PrimeSpectrum S) :
    PrimeSpectrum.comap (Diagonalizable.lift R Λ χ).hom.toRingHom q ∈ Set.range i.left := by
  obtain ⟨a, ha⟩ := h
  refine ⟨a.left q, ?_⟩
  rw [← charPoint_left_apply, ← ha]
  rfl

/-- A field-valued character lifts as soon as the image of its point lies in the image of the
immersion `i`. -/
theorem lifts_of_mem_range [IsImmersion i.left] {F : Type u} [Field F] [Algebra R F]
    {χ : Multiplicative Λ →* Fˣ}
    (h : PrimeSpectrum.comap
      (Diagonalizable.lift R Λ (B := CommAlgCat.of R F) χ).hom.toRingHom
        (IsLocalRing.closedPoint F) ∈ Set.range i.left) :
    Lifts i (S := CommAlgCat.of R F) χ := by
  obtain ⟨z, hz⟩ := h
  obtain ⟨q, hq⟩ := exists_lift_of_mem_range i.left
    (charPoint (S := CommAlgCat.of R F) χ).left (x := z)
    (hz.trans (charPoint_left_apply (S := CommAlgCat.of R F) χ _).symm)
  refine ⟨Over.homMk q ?_, ?_⟩
  · rw [← Over.w i, ← Category.assoc, hq, Over.w]
  · ext1
    exact hq

/-- A character with values in a field `K` lifts if its push-forward to some nonzero algebra
lifts. -/
theorem Lifts.of_map [IsImmersion i.left] {K : Type u} [Field K] [Algebra R K]
    {S' : CommAlgCat.{u} R} (g : CommAlgCat.of R K ⟶ S') (q : PrimeSpectrum S')
    {χ : Multiplicative Λ →* Kˣ} (h : Lifts i (charMap g χ)) :
    Lifts i (S := CommAlgCat.of R K) χ := by
  apply lifts_of_mem_range
  have hm := h.mem_range q
  rw [lift_charMap] at hm
  convert hm using 1
  change _ = PrimeSpectrum.comap (Diagonalizable.lift R Λ (B := CommAlgCat.of R K) χ).hom.toRingHom
    (PrimeSpectrum.comap g.hom.toRingHom q)
  congr 1
  ext1
  rw [Ideal.eq_bot_of_prime (IsLocalRing.closedPoint K).asIdeal,
    Ideal.eq_bot_of_prime (PrimeSpectrum.comap g.hom.toRingHom q).asIdeal]

variable (hi : TorsionClosed (G := (Diagonalizable.groupScheme R Λ).toGrp) i)
include hi

theorem lifts_of_pow_eq_one {S : CommAlgCat.{u} R} {χ : Multiplicative Λ →* Sˣ} {n : ℕ}
    (hn : 0 < n) (h : χ ^ n = 1) : Lifts i χ :=
  hi.torsion n hn _ (charPoint χ) (by rw [← charPoint_pow, h, charPoint_one])

theorem Lifts.mul {S : CommAlgCat.{u} R} {χ ψ : Multiplicative Λ →* Sˣ} (h₁ : Lifts i χ)
    (h₂ : Lifts i ψ) : Lifts i (χ * ψ) := by
  obtain ⟨c, hc⟩ := hi.mul _ _ _ h₁ h₂
  exact ⟨c, hc.trans (charPoint_mul χ ψ).symm⟩

omit hi in
/-- The `n`-torsion character `Λ → R[Λ/nΛ]ˣ`. -/
theorem quotientChar_pow (n : ℕ) :
    ((Diagonalizable.monomialUnits R (Λ ⧸ TorsionDensity.multiples Λ n)).comp
      (AddMonoidHom.toMultiplicative (QuotientAddGroup.mk' (TorsionDensity.multiples Λ n)))) ^ n = 1 := by
  apply MonoidHom.ext
  intro m
  apply Units.ext
  rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val, MonoidHom.one_apply, Units.val_one]
  change (AddMonoidAlgebra.single (QuotientAddGroup.mk' (TorsionDensity.multiples Λ n) m.toAdd) (1 : R)) ^ n
    = 1
  have h0 : QuotientAddGroup.mk' (TorsionDensity.multiples Λ n) (n • m.toAdd) = 0 :=
    (QuotientAddGroup.eq_zero_iff _).mpr (AddMonoidHom.mem_range.mpr ⟨m.toAdd, rfl⟩)
  rw [AddMonoidAlgebra.single_pow, one_pow, ← map_nsmul, h0, ← AddMonoidAlgebra.one_def]

/-! ### Characters factoring through a free quotient -/

section Torus

variable {K : Type u} [Field K] [Algebra R K] {I : Type u} [Fintype I] (π : Λ →+ (I → ℤ))

omit hi in
variable (K) in
/-- The universal character `Λ → ℤ^I → K[ℤ^I]ˣ` through `π`. -/
abbrev univChar : Multiplicative Λ →* (CommAlgCat.of R (AddMonoidAlgebra K (I → ℤ)))ˣ :=
  (AddMonoidAlgebra.of K (I → ℤ)).toHomUnits.comp (AddMonoidHom.toMultiplicative π)

omit hi [Fintype I] in
theorem charMap_castPi_pow (n : ℕ) :
    charMap (CommAlgCat.ofHom (AddMonoidAlgebra.mapDomainAlgHom R K (castPi I n)) :
      CommAlgCat.of R (AddMonoidAlgebra K (I → ℤ)) ⟶
        CommAlgCat.of R (AddMonoidAlgebra K (I → ZMod n))) (univChar K π) ^ n = 1 := by
  apply MonoidHom.ext
  intro m
  apply Units.ext
  rw [MonoidHom.pow_apply, Units.val_pow_eq_pow_val, MonoidHom.one_apply, Units.val_one]
  change (AddMonoidAlgebra.mapDomain (castPi I n)
    (AddMonoidAlgebra.single (π m.toAdd) (1 : K))) ^ n = 1
  rw [AddMonoidAlgebra.mapDomain_single, AddMonoidAlgebra.single_pow, one_pow]
  have h : n • castPi I n (π m.toAdd) = 0 := by
    funext k
    simp
  rw [h, ← AddMonoidAlgebra.one_def]

/-- **Generic points lift.** The universal character through `π`, pushed into any field by
an injective map, lifts through `i`. -/
theorem lifts_univChar [IsImmersion i.left] {F : Type u} [Field F] [Algebra R F]
    (j : CommAlgCat.of R (AddMonoidAlgebra K (I → ℤ)) ⟶ CommAlgCat.of R F)
    (hj : Function.Injective j.hom) : Lifts i (charMap j (univChar K π)) := by
  apply lifts_of_mem_range
  rw [lift_charMap]
  have hcp : PrimeSpectrum.comap j.hom.toRingHom (IsLocalRing.closedPoint F) =
      ⟨⊥, Ideal.isPrime_bot⟩ := by
    ext1
    change Ideal.comap j.hom.toRingHom (IsLocalRing.closedPoint F).asIdeal = ⊥
    rw [Ideal.eq_bot_of_prime (IsLocalRing.closedPoint F).asIdeal]
    exact Ideal.comap_bot_of_injective _ hj
  change PrimeSpectrum.comap (Diagonalizable.lift R Λ (univChar K π)).hom.toRingHom
    (PrimeSpectrum.comap j.hom.toRingHom (IsLocalRing.closedPoint F)) ∈ _
  rw [hcp]
  refine bot_mem_of_isLocallyClosed
    (s := PrimeSpectrum.comap (Diagonalizable.lift R Λ (univChar K π)).hom.toRingHom ⁻¹'
      Set.range i.left)
    (i.left.isLocallyClosed_range.preimage (PrimeSpectrum.continuous_comap _)) ?_
  intro n hn _ q
  have hm := (lifts_of_pow_eq_one hi hn (charMap_castPi_pow π n)).mem_range q
  rw [lift_charMap] at hm
  exact hm

omit hi in
variable (I) in
/-- Twisting monomials by a character: `e^μ ↦ ψ(μ) e^μ`. -/
def twistHom (ψ : Multiplicative (I → ℤ) →* Kˣ) :
    Multiplicative (I → ℤ) →* AddMonoidAlgebra K (I → ℤ) where
  toFun m := AddMonoidAlgebra.single m.toAdd (ψ m : K)
  map_one' := by
    change AddMonoidAlgebra.single (0 : I → ℤ) ((ψ 1 : Kˣ) : K) = 1
    rw [map_one, Units.val_one, ← AddMonoidAlgebra.one_def]
  map_mul' a b := by
    change AddMonoidAlgebra.single (a.toAdd + b.toAdd) ((ψ (a * b) : Kˣ) : K) =
      AddMonoidAlgebra.single a.toAdd (ψ a : K) * AddMonoidAlgebra.single b.toAdd (ψ b : K)
    rw [AddMonoidAlgebra.single_mul_single, map_mul, Units.val_mul]

omit hi in
variable (R) in
/-- The twisting automorphism of `K[ℤ^I]` as an `R`-algebra map. -/
def twist (ψ : Multiplicative (I → ℤ) →* Kˣ) :
    CommAlgCat.of R (AddMonoidAlgebra K (I → ℤ)) ⟶ CommAlgCat.of R (AddMonoidAlgebra K (I → ℤ)) :=
  CommAlgCat.ofHom ((AddMonoidAlgebra.lift K (AddMonoidAlgebra K (I → ℤ)) (I → ℤ)
    (twistHom I ψ)).restrictScalars R)

omit hi [Fintype I] in
theorem twist_single (ψ : Multiplicative (I → ℤ) →* Kˣ) (d : I → ℤ) (c : K) :
    (twist R ψ).hom (AddMonoidAlgebra.single d c) =
      AddMonoidAlgebra.single d (c * ψ (Multiplicative.ofAdd d)) := by
  change AddMonoidAlgebra.lift K (AddMonoidAlgebra K (I → ℤ)) (I → ℤ) (twistHom I ψ)
    (AddMonoidAlgebra.single d c) = _
  rw [AddMonoidAlgebra.lift_single]
  change c • AddMonoidAlgebra.single d (ψ (Multiplicative.ofAdd d) : K) = _
  rw [AddMonoidAlgebra.smul_single, smul_eq_mul]

omit hi [Fintype I] in
theorem twist_injective (ψ : Multiplicative (I → ℤ) →* Kˣ) :
    Function.Injective (twist R ψ).hom := by
  have h : ∀ x, (twist R ψ⁻¹).hom ((twist R ψ).hom x) = x := by
    intro x
    induction x using AddMonoidAlgebra.induction_linear with
    | zero => rw [map_zero, map_zero]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
    | single d c =>
      rw [twist_single, twist_single, mul_assoc]
      congr 1
      simp
  exact Function.LeftInverse.injective h

omit hi in
variable (R K I) in
/-- Inversion `e^μ ↦ e^{-μ}` on `K[ℤ^I]`. -/
abbrev invMap :
    CommAlgCat.of R (AddMonoidAlgebra K (I → ℤ)) ⟶ CommAlgCat.of R (AddMonoidAlgebra K (I → ℤ)) :=
  CommAlgCat.ofHom (AddMonoidAlgebra.mapDomainAlgHom R K (negAddMonoidHom : (I → ℤ) →+ (I → ℤ)))

omit hi [Fintype I] in
theorem invMap_injective : Function.Injective (invMap R K I).hom :=
  AddMonoidAlgebra.mapDomain_injective neg_injective

omit hi [Fintype I] in
/-- `ψ ∘ π` is the product of two generic characters. -/
theorem charMap_twist_mul {F : Type u} [Field F] [Algebra R F]
    (j : CommAlgCat.of R (AddMonoidAlgebra K (I → ℤ)) ⟶ CommAlgCat.of R F)
    (ψ : Multiplicative (I → ℤ) →* Kˣ) :
    charMap (CommAlgCat.ofHom (IsScalarTower.toAlgHom R K (AddMonoidAlgebra K (I → ℤ))) ≫ j)
        (ψ.comp (AddMonoidHom.toMultiplicative π)) =
      charMap (twist R ψ ≫ j) (univChar K π) * charMap (invMap R K I ≫ j) (univChar K π) := by
  apply MonoidHom.ext
  intro m
  apply Units.ext
  rw [MonoidHom.mul_apply, Units.val_mul]
  change j.hom (algebraMap K (AddMonoidAlgebra K (I → ℤ)) (ψ (.ofAdd (π m.toAdd)))) =
    j.hom ((twist R ψ).hom (AddMonoidAlgebra.single (π m.toAdd) 1)) *
      j.hom (AddMonoidAlgebra.mapDomain (negAddMonoidHom : (I → ℤ) →+ (I → ℤ))
        (AddMonoidAlgebra.single (π m.toAdd) 1))
  rw [← map_mul, twist_single, AddMonoidAlgebra.mapDomain_single,
    AddMonoidAlgebra.single_mul_single, one_mul, mul_one]
  congr 1
  simp [AddMonoidAlgebra.coe_algebraMap]

/-- **Characters through a free quotient lift.** -/
theorem lifts_comp_free [IsImmersion i.left] (ψ : Multiplicative (I → ℤ) →* Kˣ) :
    Lifts i (S := CommAlgCat.of R K) (ψ.comp (AddMonoidHom.toMultiplicative π)) := by
  let j : CommAlgCat.of R (AddMonoidAlgebra K (I → ℤ)) ⟶
      CommAlgCat.of R (FractionRing (AddMonoidAlgebra K (I → ℤ))) :=
    CommAlgCat.ofHom (IsScalarTower.toAlgHom R (AddMonoidAlgebra K (I → ℤ))
      (FractionRing (AddMonoidAlgebra K (I → ℤ))))
  have hj : Function.Injective j.hom := IsFractionRing.injective _ _
  have h1 := lifts_univChar hi π (twist R ψ ≫ j) (hj.comp (twist_injective ψ))
  have h2 := lifts_univChar hi π (invMap R K I ≫ j) (hj.comp invMap_injective)
  have h3 := h1.mul hi h2
  rw [← charMap_twist_mul] at h3
  exact h3.of_map _ (IsLocalRing.closedPoint _)

end Torus

/-- **Field-valued points lift.** Every character with values in a field lifts through `i`. -/
theorem lifts_field [AddGroup.FG Λ] [IsImmersion i.left] {K : Type u} [Field K] [Algebra R K]
    (χ : Multiplicative Λ →* Kˣ) : Lifts i (S := CommAlgCat.of R K) χ := by
  obtain ⟨I, A, _, _, _, ⟨e⟩⟩ := Diagonalizable.exists_freeFiniteEquiv Λ
  let π : Λ →+ (I → ℤ) := (AddMonoidHom.fst _ _).comp e.toAddMonoidHom
  let s : (I → ℤ) →+ Λ := e.symm.toAddMonoidHom.comp (AddMonoidHom.inl _ _)
  let ψ : Multiplicative (I → ℤ) →* Kˣ := χ.comp (AddMonoidHom.toMultiplicative s)
  let χ₁ : Multiplicative Λ →* Kˣ := χ * (ψ.comp (AddMonoidHom.toMultiplicative π))⁻¹
  have hs : ∀ x : Λ, (e x).2 = 0 → s (π x) = x := by
    intro x hx
    apply e.injective
    change e (e.symm ((e x).1, 0)) = e x
    rw [AddEquiv.apply_symm_apply, ← hx]
  have key : ∀ x : Λ, (e x).2 = 0 → χ₁ (Multiplicative.ofAdd x) = 1 := by
    intro x hx
    change χ (Multiplicative.ofAdd x) * (χ (Multiplicative.ofAdd (s (π x))))⁻¹ = 1
    rw [hs x hx, mul_inv_cancel]
  have hN : χ₁ ^ Nat.card A = 1 := by
    apply MonoidHom.ext
    intro m
    rw [MonoidHom.pow_apply, MonoidHom.one_apply, ← map_pow]
    apply key
    rw [map_nsmul, Prod.smul_snd, card_nsmul_eq_zero']
  have h := (lifts_of_pow_eq_one hi Nat.card_pos hN).mul hi (lifts_comp_free hi π ψ)
  have hχ : χ₁ * ψ.comp (AddMonoidHom.toMultiplicative π) = χ :=
    inv_mul_cancel_right χ (ψ.comp (AddMonoidHom.toMultiplicative π))
  rwa [hχ] at h

/-- **Step A.** The immersion `i` is surjective. -/
theorem surjective_left [AddGroup.FG Λ] [IsImmersion i.left] : Function.Surjective i.left := by
  intro 𝔭
  change PrimeSpectrum (AddMonoidAlgebra R Λ) at 𝔭
  let K := 𝔭.asIdeal.ResidueField
  let _ : Algebra R K := ((algebraMap (AddMonoidAlgebra R Λ) K).comp
    (algebraMap R (AddMonoidAlgebra R Λ))).toAlgebra
  let φ : Diagonalizable.algebra R Λ ⟶ CommAlgCat.of R K :=
    CommAlgCat.ofHom { algebraMap (AddMonoidAlgebra R Λ) K with commutes' := fun _ => rfl }
  have h := (lifts_field hi (K := K)
    ((Diagonalizable.corepresentation R Λ).homEquiv φ)).mem_range (IsLocalRing.closedPoint K)
  have hφ : Diagonalizable.lift R Λ ((Diagonalizable.corepresentation R Λ).homEquiv φ) = φ :=
    (Diagonalizable.corepresentation R Λ).homEquiv.symm_apply_apply φ
  rw [hφ] at h
  obtain ⟨z, hz⟩ := h
  refine ⟨z, hz.trans (PrimeSpectrum.ext (R := AddMonoidAlgebra R Λ) ?_)⟩
  change Ideal.comap (algebraMap (AddMonoidAlgebra R Λ) K) (IsLocalRing.closedPoint K).asIdeal =
    𝔭.asIdeal
  rw [Ideal.eq_bot_of_prime (IsLocalRing.closedPoint K).asIdeal, ← RingHom.ker_eq_comap_bot,
    Ideal.ker_algebraMap_residueField]

/-- **Torsion determination for `D_R(Λ)`.** An immersion into `D_R(Λ)` (with `Λ` finitely
generated) whose points are closed under multiplication and contain all torsion points is an
isomorphism. -/
theorem isIso_left [AddGroup.FG Λ] [IsImmersion i.left] : IsIso i.left := by
  have hsurj := surjective_left hi
  have : IsClosedImmersion i.left :=
    IsClosedImmersion.of_isPreimmersion _ (by rw [hsurj.range_eq]; exact isClosed_univ)
  have : IsAffine (Diagonalizable.groupScheme R Λ).X.left :=
    inferInstanceAs (IsAffine (Spec (CommRingCat.of (AddMonoidAlgebra R Λ))))
  apply IsClosedImmersion.isIso_of_injective_of_isAffine
  refine (injective_iff_map_eq_zero i.left.appTop.hom).mpr ?_
  intro a ha
  let A := CommRingCat.of (AddMonoidAlgebra R Λ)
  suffices h : (Scheme.ΓSpecIso A).hom a = 0 by
    have := congrArg (Scheme.ΓSpecIso A).inv.hom h
    rwa [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply, map_zero] at this
  by_contra hne
  obtain ⟨n, hn, hne'⟩ := exists_mapDomain_mk_ne_zero hne
  apply hne'
  obtain ⟨b, hb⟩ := lifts_of_pow_eq_one hi
    (S := Diagonalizable.algebra R (Λ ⧸ TorsionDensity.multiples Λ n)) hn
    (quotientChar_pow (R := R) (Λ := Λ) n)
  have hb' : b.left ≫ i.left =
      Spec.map (CommRingCat.ofHom
        (Diagonalizable.incl R (QuotientAddGroup.mk' (TorsionDensity.multiples Λ n))).hom.toRingHom) := by
    rw [← Over.comp_left, hb, charPoint_eq]
    rfl
  have h2 := congrArg (fun f => (f.appTop).hom a) hb'
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, ha, map_zero] at h2
  have key := congrArg (fun g => g.hom a) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom
    (Diagonalizable.incl R (QuotientAddGroup.mk' (TorsionDensity.multiples Λ n))).hom.toRingHom))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at key
  rw [← Diagonalizable.incl_apply]
  exact key.symm.trans ((congrArg (Scheme.ΓSpecIso _).hom.hom h2.symm).trans (map_zero _))

end Points

/-- **Torsion determination for `D_R(Λ)`**, with the hypotheses spelled out: an immersion into
`D_R(Λ)` (with `Λ` finitely generated) whose points are closed under multiplication and contain
all torsion points is an isomorphism. -/
theorem isIso_left_of_diagonalizable {R : CommRingCat.{u}} {Λ : Type u} [AddCommGroup Λ]
    [AddGroup.FG Λ] {Z : Over (Spec R)} (i : Z ⟶ (Diagonalizable.groupScheme R Λ).X)
    [IsImmersion i.left]
    (hmul : ∀ (T : Over (Spec R)) (x y : T ⟶ (Diagonalizable.groupScheme R Λ).X),
      (∃ a, a ≫ i = x) → (∃ b, b ≫ i = y) → ∃ c, c ≫ i = x * y)
    (htors : ∀ n : ℕ, 0 < n → ∀ (T : Over (Spec R)) (x : T ⟶ (Diagonalizable.groupScheme R Λ).X),
      x ^ n = 1 → ∃ a, a ≫ i = x) :
    IsIso i.left :=
  isIso_left ⟨hmul, htors⟩

end Langlands.GroupScheme.TorsionDetermination
