import Langlands.ClassField.Global.IdeleCohomology
import Langlands.Global.AdelicFunctoriality.LocalDegree
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.NumberTheory.Cyclotomic.Basic

/-! # Local invariants of global classes and the reciprocity law

For a finite Galois extension `E / F` of number fields, a class in the actual
`H²(Gal(E/F), Eˣ)` has a local invariant at every place of `F`, computed at a chosen place
`w` of `E` above it:

* at a finite place `w | v`, the local component `unitsLocalMap v w 2` (restriction along
  `decompositionHom v w` with coefficients `Eˣ → E_wˣ`) followed by the supplied abstract
  relative invariant map of `E_w / F_v`;
* at an infinite place `w`, the archimedean invariant in `½ℤ/ℤ`: it is `0` unless some
  nontrivial `c ∈ Gal(E/F)` fixes `w` (then `w` is complex over a real place and `c` is its
  complex conjugation), in which case it is `1/2` exactly when `w(f(c,c) · f(1,1))`, which is
  a nonzero real number, is negative, for a `2`-cocycle `f` representing the class.

The reciprocity law states that, for every choice of places above, only finitely many finite
local invariants are nonzero and the sum of all local invariants is zero; it is stated for
cyclic subextensions of cyclotomic extensions and for all finite Galois extensions.
-/

noncomputable section

namespace Langlands.ClassField.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField Langlands.Global.AdelicFunctoriality.FiniteExtension
open Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic
open Langlands.ClassFieldTheory.Local
open CategoryTheory FundamentalClass

universe u

namespace Reciprocity

section Lift

variable {k G : Type u} [CommRing k] [Group G] {A : Rep.{u} k G} {B : Type*} [AddCommGroup B]

theorem H2π_surjective : Function.Surjective (groupCohomology.H2π A) := fun x =>
  groupCohomology.H2_induction_on x fun y => ⟨y, rfl⟩

/-- An additive map on `2`-cocycles which vanishes on coboundaries, as a map on `H²`. -/
def H2Lift (φ : groupCohomology.cocycles₂ A →+ B)
    (hφ : ∀ x : groupCohomology.cocycles₂ A, ⇑x ∈ groupCohomology.coboundaries₂ A → φ x = 0) :
    groupCohomology.H2 A →+ B where
  toFun y := φ (Function.surjInv H2π_surjective y)
  map_zero' := by
    apply hφ
    rw [← groupCohomology.H2π_eq_zero_iff, Function.surjInv_eq H2π_surjective]
  map_add' y z := by
    rw [← sub_eq_zero, ← map_add, ← map_sub]
    apply hφ
    rw [← groupCohomology.H2π_eq_zero_iff, map_sub, map_add,
      Function.surjInv_eq H2π_surjective, Function.surjInv_eq H2π_surjective,
      Function.surjInv_eq H2π_surjective, sub_self]

theorem H2Lift_H2π (φ : groupCohomology.cocycles₂ A →+ B)
    (hφ : ∀ x : groupCohomology.cocycles₂ A, ⇑x ∈ groupCohomology.coboundaries₂ A → φ x = 0)
    (x : groupCohomology.cocycles₂ A) :
    H2Lift φ hφ (groupCohomology.H2π A x) = φ x := by
  change φ (Function.surjInv H2π_surjective _) = φ x
  rw [← sub_eq_zero, ← map_sub]
  apply hφ
  rw [← groupCohomology.H2π_eq_zero_iff, map_sub, Function.surjInv_eq H2π_surjective, sub_self]

end Lift

section Finite

variable {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [IsGalois F E] (v : HeightOneSpectrum (𝓞 F)) (w : HeightOneSpectrum (𝓞 E))
  [w.asIdeal.LiesOver v.asIdeal]

/-- The local invariant at the finite place `w | v` of a global class in `H²(Gal(E/F), Eˣ)`:
its local component `unitsLocalMap v w 2` measured by the supplied relative invariant map of
`E_w / F_v` at the residue prime of `v`. -/
def finiteLocalInvariant (I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p) :
    relativeCohomology F E 2 →+ RationalModIntegers :=
  haveI : IsGalois (padicField v).Carrier (w.adicCompletion E) :=
    isGalois_adicCompletion v w
  haveI : FiniteDimensional (padicField v).Carrier (w.adicCompletion E) :=
    FiniteExtension.local_finite v w
  ((I (residuePrime v)).relative (padicField v) (w.adicCompletion E)).comp
    (unitsLocalMap v w 2).hom.toAddMonoidHom

end Finite

section Sign

/-- The class in `ℚ/ℤ` of the sign of a complex number on the real line: `1/2` for a negative
real part, `0` otherwise. -/
def signClass (z : ℂ) : RationalModIntegers :=
  if z.re < 0 then rationalClass (1 / 2) else 0

theorem rationalClass_half_add_half : rationalClass (1 / 2) + rationalClass (1 / 2) = 0 := by
  rw [← map_add, show (1 / 2 : ℚ) + 1 / 2 = 1 by norm_num]
  exact (QuotientAddGroup.eq_zero_iff _).2 (AddSubgroup.mem_zmultiples _)

theorem signClass_mul {a b : ℂ} (ha : a.im = 0) (hb : b.im = 0) (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
    signClass (a * b) = signClass a + signClass b := by
  have hre : (a * b).re = a.re * b.re := by simp [Complex.mul_re, ha, hb]
  have ha' : a.re ≠ 0 := fun h => ha0 (Complex.ext (by simpa using h) (by simpa using ha))
  have hb' : b.re ≠ 0 := fun h => hb0 (Complex.ext (by simpa using h) (by simpa using hb))
  unfold signClass
  rw [hre]
  rcases ha'.lt_or_gt with h1 | h1 <;> rcases hb'.lt_or_gt with h2 | h2
  · simp only [lt_asymm (mul_pos_of_neg_of_neg h1 h2), h1, h2, ↓reduceIte,
      rationalClass_half_add_half]
  · simp only [mul_neg_of_neg_of_pos h1 h2, h1, lt_asymm h2, ↓reduceIte, add_zero]
  · simp only [mul_neg_of_pos_of_neg h1 h2, lt_asymm h1, h2, ↓reduceIte, zero_add]
  · simp only [lt_asymm (mul_pos h1 h2), lt_asymm h1, lt_asymm h2, ↓reduceIte, add_zero]

theorem signClass_star_mul_self (z : ℂ) : signClass (star z * z) = 0 := by
  have h : (star z * z).re = z.re * z.re + z.im * z.im := by
    simp [Complex.mul_re]
  unfold signClass
  simp only [not_lt.2 (h ▸ add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)), ↓reduceIte]

end Sign

section Infinite

variable {F E : Type u} [Field F] [Field E] [Algebra F E] (w : InfinitePlace E)

/-- The unit `f(c,c) · f(1,1)`, in multiplicative notation, of a `2`-cochain. -/
def conjugationValue (c : E ≃ₐ[F] E)
    (f : (E ≃ₐ[F] E) × (E ≃ₐ[F] E) → (unitsRepresentation F E).V) : Eˣ :=
  Additive.toMul (f (c, c) + f (1, 1))

theorem conjugationValue_add (c : E ≃ₐ[F] E)
    (f g : (E ≃ₐ[F] E) × (E ≃ₐ[F] E) → (unitsRepresentation F E).V) :
    conjugationValue c (f + g) = conjugationValue c f * conjugationValue c g := by
  unfold conjugationValue
  rw [Pi.add_apply, Pi.add_apply, add_add_add_comm]
  rfl

/-- For an involution `c`, the value `f(c,c) · f(1,1)` of a `2`-cocycle is fixed by `c`. -/
theorem conjugationValue_fixed (f : groupCohomology.cocycles₂ (unitsRepresentation F E))
    {c : E ≃ₐ[F] E} (hc : c * c = 1) :
    c (conjugationValue c f : E) = conjugationValue c f := by
  have h := (groupCohomology.mem_cocycles₂_iff f).1 f.2 c c c
  rw [hc, groupCohomology.cocycles₂_map_one_fst f c, groupCohomology.cocycles₂_map_one_snd f c,
    ← map_add ((unitsRepresentation F E).ρ c), add_comm (f (1, 1))] at h
  exact (congrArg (fun y : (unitsRepresentation F E).V => ((Additive.toMul y : Eˣ) : E)) h).symm

/-- A nontrivial element of `Gal(E/F)` fixing `w` is the complex conjugation of `w`. -/
theorem isConj_of_mem_stabilizer {c : E ≃ₐ[F] E}
    (hc : c ∈ MulAction.stabilizer (E ≃ₐ[F] E) w) (h1 : c ≠ 1) :
    ComplexEmbedding.IsConj w.embedding c := by
  rw [← w.mk_embedding, InfinitePlace.mem_stabilizer_mk_iff] at hc
  exact hc.resolve_left h1

theorem conjugation_mul_self {c : E ≃ₐ[F] E} (hc : ComplexEmbedding.IsConj w.embedding c) :
    c * c = 1 :=
  AlgEquiv.ext fun x => ComplexEmbedding.isConj_apply_apply hc x

/-- At the complex conjugation `c` of `w`, `w(f(c,c) · f(1,1))` is real for a `2`-cocycle. -/
theorem embedding_conjugationValue_im (f : groupCohomology.cocycles₂ (unitsRepresentation F E))
    {c : E ≃ₐ[F] E} (hc : ComplexEmbedding.IsConj w.embedding c) :
    (w.embedding (conjugationValue c f : E)).im = 0 := by
  have h := hc.eq (conjugationValue c f : E)
  rw [conjugationValue_fixed f (conjugation_mul_self w hc)] at h
  have h2 := congrArg Complex.im h
  rw [Complex.star_def, Complex.conj_im] at h2
  linarith

open Classical in
/-- The archimedean invariant of a `2`-cocycle at the infinite place `w`: `0` unless some
nontrivial `c ∈ Gal(E/F)` fixes `w`, in which case it is the sign class of
`w(f(c,c) · f(1,1))` for the chosen such `c` (the complex conjugation of `w`). -/
def archimedeanCocycleHom :
    groupCohomology.cocycles₂ (unitsRepresentation F E) →+ RationalModIntegers where
  toFun f :=
    if h : ∃ c : E ≃ₐ[F] E, c ∈ MulAction.stabilizer (E ≃ₐ[F] E) w ∧ c ≠ 1 then
      signClass (w.embedding (conjugationValue h.choose f : E))
    else 0
  map_zero' := by
    split_ifs with h
    · have : conjugationValue h.choose
          ⇑(0 : groupCohomology.cocycles₂ (unitsRepresentation F E)) = 1 := by
        unfold conjugationValue
        rw [show ⇑(0 : groupCohomology.cocycles₂ (unitsRepresentation F E)) = 0 from rfl,
          Pi.zero_apply, Pi.zero_apply, add_zero]
        rfl
      rw [this, Units.val_one, map_one]
      simp [signClass]
    · rfl
  map_add' f g := by
    split_ifs with h
    · have hc := isConj_of_mem_stabilizer w h.choose_spec.1 h.choose_spec.2
      rw [show ⇑(f + g) = ⇑f + ⇑g from rfl, conjugationValue_add, Units.val_mul, map_mul]
      exact signClass_mul (embedding_conjugationValue_im w f hc)
        (embedding_conjugationValue_im w g hc) (by simp) (by simp)
    · rw [add_zero]

open Classical in
theorem archimedeanCocycleHom_coboundary
    (f : groupCohomology.cocycles₂ (unitsRepresentation F E))
    (hf : ⇑f ∈ groupCohomology.coboundaries₂ (unitsRepresentation F E)) :
    archimedeanCocycleHom w f = 0 := by
  obtain ⟨b, hb⟩ := hf
  change (if h : ∃ c : E ≃ₐ[F] E, c ∈ MulAction.stabilizer (E ≃ₐ[F] E) w ∧ c ≠ 1 then
      signClass (w.embedding (conjugationValue h.choose f : E)) else 0) = 0
  split_ifs with h
  · have hc := isConj_of_mem_stabilizer w h.choose_spec.1 h.choose_spec.2
    have hcc := conjugation_mul_self w hc
    have hsum : f (h.choose, h.choose) + f (1, 1) =
        (unitsRepresentation F E).ρ h.choose (b h.choose) + b h.choose := by
      rw [← congrFun hb (h.choose, h.choose), ← congrFun hb (1, 1)]
      change ((unitsRepresentation F E).ρ h.choose (b h.choose) - b (h.choose * h.choose) +
          b h.choose) + ((unitsRepresentation F E).ρ 1 (b 1) - b (1 * 1) + b 1) = _
      rw [hcc, mul_one, map_one, Module.End.one_apply]
      abel
    have hval : (conjugationValue h.choose f : E) =
        h.choose ((Additive.toMul (b h.choose) : Eˣ) : E) *
          ((Additive.toMul (b h.choose) : Eˣ) : E) := by
      unfold conjugationValue
      rw [hsum]
      rfl
    rw [hval, map_mul, hc.eq]
    exact signClass_star_mul_self _
  · rfl

/-- The archimedean local invariant at `w` of a class in `H²(Gal(E/F), Eˣ)`. -/
def archimedeanInvariant : relativeCohomology F E 2 →+ RationalModIntegers :=
  H2Lift (archimedeanCocycleHom w) (archimedeanCocycleHom_coboundary w)

end Infinite

section Sum

variable (I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p)
  {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [IsGalois F E]

/-- The reciprocity law for one class `x ∈ H²(Gal(E/F), Eˣ)`: for every choice of a finite place
`wf v` of `E` above each finite place `v` of `F` and an infinite place `wi v` of `E` above each
infinite place `v` of `F`, only finitely many finite local invariants are nonzero and the sum
of all finite and archimedean local invariants is zero. -/
def SumOfInvariantsVanishes (x : relativeCohomology F E 2) : Prop :=
  ∀ (wf : ∀ v : HeightOneSpectrum (𝓞 F), FinitePlacesAbove E v)
    (wi : ∀ v : InfinitePlace F, InfinitePlacesAbove E v),
    (Function.support fun v =>
        haveI := (wf v).2
        finiteLocalInvariant v (wf v).1 I x).Finite ∧
      (∑ᶠ v, haveI := (wf v).2; finiteLocalInvariant v (wf v).1 I x) +
          ∑ v, archimedeanInvariant (wi v).1 x = 0

end Sum

end Reciprocity

open Reciprocity

/-- The reciprocity law for cyclic subextensions of cyclotomic extensions (Artin–Tate VII §3,
Case 1 of the proof of Theorem 6, over an arbitrary base field): for local invariant maps
forming a class formation with the arithmetic normalization, every class of
`H²(Gal(E/F), Eˣ)` satisfies `SumOfInvariantsVanishes` whenever `E / F` is cyclic and `E`
embeds over `F` into a cyclotomic field `F(μ_m)`. -/
def CyclicCyclotomicReciprocity : Prop :=
  ∀ I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p,
    (∀ (p : ℕ) [Fact p.Prime],
      (I p).RelativeClassFormation ∧ (I p).ArithmeticNormalization) →
    ∀ (F : Type u) [Field F] [NumberField F] (E : Type u) [Field E] [NumberField E]
      [Algebra F E] [IsGalois F E],
      IsCyclic (E ≃ₐ[F] E) → (∃ m : ℕ, 0 < m ∧ Nonempty (E →ₐ[F] CyclotomicField m F)) →
      ∀ x : relativeCohomology F E 2, SumOfInvariantsVanishes I x

/-- The global reciprocity law (Artin–Tate VII §3 Theorem 6): for local invariant maps forming
a class formation with the arithmetic normalization, every class of `H²(Gal(E/F), Eˣ)`, for
every finite Galois extension `E / F` of number fields, satisfies `SumOfInvariantsVanishes`. -/
def GlobalReciprocity : Prop :=
  ∀ I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p,
    (∀ (p : ℕ) [Fact p.Prime],
      (I p).RelativeClassFormation ∧ (I p).ArithmeticNormalization) →
    ∀ (F : Type u) [Field F] [NumberField F] (E : Type u) [Field E] [NumberField E]
      [Algebra F E] [IsGalois F E] (x : relativeCohomology F E 2),
      SumOfInvariantsVanishes I x

end Langlands.ClassField.Global
