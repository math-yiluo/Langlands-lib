import Langlands.AlgebraicGeometry.FiniteEtale.KummerFactorizationStatement
import Langlands.CommutativeAlgebra.StrictlyHenselianKummerUnits
import WeilConjectures.Mathlib.RingTheory.Etale.StandardEtale

/-! # Kummer covers and the Kummer character

For a commutative ring `A`, a unit `a` of `A` and a positive integer `m` invertible in `A`, the
algebra `A[X]/(X^m - a)` is finite étale over `A`. Its spectrum is a finite étale cover of
`Spec A`. An `m`-th root of unity `ζ` of a ring `R` mapping to `A` acts on it by `X ↦ ζ X`.
When `R` is local with `m` invertible and contains `m` distinct `m`-th roots of unity, the
geometric fibre over a geometric point with algebraically closed residue field is a torsor
under the `m`-th roots of unity of `R`. The fundamental group then acts on this fibre through
a homomorphism to the roots of unity, the Kummer character, which is compatible with the maps
`X ↦ X^d` between levels and trivial when `a = 1`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry Polynomial

namespace Langlands.AlgebraicGeometry.FiniteEtale

section Algebra

variable {A : Type u} [CommRing A]

/-- The Kummer algebra `A[X]/(X^m - a)` with an arbitrary parameter `a ∈ A`. -/
abbrev KummerRootAlgebra (a : A) (m : ℕ) : Type u := AdjoinRoot (X ^ m - C a)

theorem kummerRoot_pow (a : A) (m : ℕ) :
    AdjoinRoot.root (X ^ m - C a) ^ m = algebraMap A (KummerRootAlgebra a m) a := by
  have h := AdjoinRoot.eval₂_root (X ^ m - C a)
  simp only [eval₂_sub, eval₂_X_pow, eval₂_C] at h
  rw [sub_eq_zero] at h
  exact h

/-- The structure morphism of the spectrum of a Kummer algebra. -/
abbrev kummerRootMorphism (a : A) (m : ℕ) :
    Spec (.of (KummerRootAlgebra a m)) ⟶ Spec (.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A (KummerRootAlgebra a m)))

theorem kummerRoot_isFinite (a : A) {m : ℕ} (hm0 : m ≠ 0) :
    IsFinite (kummerRootMorphism a m) := by
  rw [IsFinite.SpecMap_iff]
  have : Module.Finite A (KummerRootAlgebra a m) :=
    (monic_X_pow_sub_C a hm0).finite_adjoinRoot
  exact RingHom.finite_algebraMap.mpr this

theorem kummerRoot_etale (a : A) {m : ℕ} (hm0 : m ≠ 0) (hm : IsUnit (m : A)) (ha : IsUnit a) :
    Etale (kummerRootMorphism a m) := by
  rw [HasRingHomProperty.Spec_iff (P := @Etale)]
  exact RingHom.etale_algebraMap.mpr (AdjoinRoot.etale_X_pow_sub_C hm0 hm ha)

/-- The finite étale Kummer cover `Spec A[X]/(X^m - a) → Spec A`. -/
def kummerRootCover (a : A) (m : ℕ) (hm0 : m ≠ 0) (hm : IsUnit (m : A)) (ha : IsUnit a) :
    Cover (Spec (.of A)) :=
  haveI := kummerRoot_isFinite a hm0
  haveI := kummerRoot_etale a hm0 hm ha
  cover (kummerRootMorphism a m)

@[simp]
theorem kummerRootCover_hom (a : A) (m : ℕ) (hm0 : m ≠ 0) (hm : IsUnit (m : A))
    (ha : IsUnit a) : (kummerRootCover a m hm0 hm ha).obj.hom = kummerRootMorphism a m :=
  rfl

variable (R : Type*) [CommRing R] [Algebra R A]

/-- The `A`-algebra endomorphism `X ↦ ζ X` of `A[X]/(X^m - a)` for an `m`-th root of unity
`ζ` of `R`. -/
def kummerScale (a : A) (m : ℕ) (ζ : rootsOfUnity m R) :
    KummerRootAlgebra a m →ₐ[A] KummerRootAlgebra a m :=
  AdjoinRoot.liftAlgHom (X ^ m - C a) (Algebra.ofId A _)
    (algebraMap A (KummerRootAlgebra a m) (algebraMap R A ((ζ : Rˣ) : R)) *
      AdjoinRoot.root (X ^ m - C a)) (by
      have hζ : ((ζ : Rˣ) : R) ^ m = 1 := by
        rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity m (ζ : Rˣ)).mp ζ.2, Units.val_one]
      simp only [eval₂_sub, eval₂_X_pow, eval₂_C, mul_pow, ← map_pow, hζ, map_one, one_mul,
        kummerRoot_pow]
      simp)

@[simp]
theorem kummerScale_root (a : A) (m : ℕ) (ζ : rootsOfUnity m R) :
    kummerScale R a m ζ (AdjoinRoot.root _) =
      algebraMap A (KummerRootAlgebra a m) (algebraMap R A ((ζ : Rˣ) : R)) *
        AdjoinRoot.root (X ^ m - C a) := by
  simp [kummerScale]

/-- The `A`-algebra map `A[X]/(X^m - a) → A[X]/(X^n - a)`, `X ↦ X^d`, for `m * d = n`. -/
def kummerLevel (a : A) {m d n : ℕ} (hmn : m * d = n) :
    KummerRootAlgebra a m →ₐ[A] KummerRootAlgebra a n :=
  AdjoinRoot.liftAlgHom (X ^ m - C a) (Algebra.ofId A _)
    (AdjoinRoot.root (X ^ n - C a) ^ d) (by
      simp only [eval₂_sub, eval₂_X_pow, eval₂_C, ← pow_mul, mul_comm d m, hmn, kummerRoot_pow]
      simp)

@[simp]
theorem kummerLevel_root (a : A) {m d n : ℕ} (hmn : m * d = n) :
    kummerLevel a hmn (AdjoinRoot.root _) = AdjoinRoot.root (X ^ n - C a) ^ d := by
  simp [kummerLevel]

/-- The `A`-algebra map `A[X]/(X^m - 1) → A`, `X ↦ 1`. -/
def kummerUnitSection (m : ℕ) : KummerRootAlgebra (1 : A) m →ₐ[A] A :=
  AdjoinRoot.liftAlgHom (X ^ m - C 1) (Algebra.ofId A A) 1 (by simp)

end Algebra

section Fiber

variable {A : Type u} [CommRing A] (a : A) (m : ℕ) (hm0 : m ≠ 0) (hm : IsUnit (m : A))
  (ha : IsUnit a) {Ω : Type u} [Field Ω] (x : Spec (.of Ω) ⟶ Spec (.of A))

/-- The ring homomorphism `A[X]/(X^m - a) → Ω` of a geometric point of the Kummer cover. -/
def kummerPointHom (p : Fiber x (kummerRootCover a m hm0 hm ha)) :
    CommRingCat.of (KummerRootAlgebra a m) ⟶ CommRingCat.of Ω :=
  Spec.preimage p.left

theorem kummerPointHom_spec (p : Fiber x (kummerRootCover a m hm0 hm ha)) :
    Spec.map (kummerPointHom a m hm0 hm ha x p) = p.left :=
  Spec.map_preimage _

theorem algebraMap_comp_kummerPointHom (p : Fiber x (kummerRootCover a m hm0 hm ha)) :
    CommRingCat.ofHom (algebraMap A (KummerRootAlgebra a m)) ≫
        kummerPointHom a m hm0 hm ha x p = Spec.preimage x := by
  apply Spec.map_injective
  rw [Spec.map_comp, kummerPointHom_spec, Spec.map_preimage]
  exact Over.w p

theorem kummerPointHom_algebraMap (p : Fiber x (kummerRootCover a m hm0 hm ha)) (c : A) :
    kummerPointHom a m hm0 hm ha x p (algebraMap A _ c) = Spec.preimage x c := by
  rw [← algebraMap_comp_kummerPointHom a m hm0 hm ha x p]
  rfl

/-- The value of a geometric point of the Kummer cover at the root `X`. -/
def kummerRootValue (p : Fiber x (kummerRootCover a m hm0 hm ha)) : Ω :=
  kummerPointHom a m hm0 hm ha x p (AdjoinRoot.root _)

theorem kummerRootValue_pow (p : Fiber x (kummerRootCover a m hm0 hm ha)) :
    kummerRootValue a m hm0 hm ha x p ^ m = Spec.preimage x a := by
  rw [kummerRootValue, ← map_pow, kummerRoot_pow, kummerPointHom_algebraMap]

theorem kummerRootValue_ne_zero (p : Fiber x (kummerRootCover a m hm0 hm ha)) :
    kummerRootValue a m hm0 hm ha x p ≠ 0 := by
  intro h
  have h1 := kummerRootValue_pow a m hm0 hm ha x p
  rw [h, zero_pow hm0] at h1
  exact (ha.map (Spec.preimage x).hom).ne_zero h1.symm

theorem kummerRootValue_injective : Function.Injective (kummerRootValue a m hm0 hm ha x) := by
  intro p q h
  have hφ : kummerPointHom a m hm0 hm ha x p = kummerPointHom a m hm0 hm ha x q := by
    ext1
    apply AdjoinRoot.ringHom_ext
    · ext c
      exact (kummerPointHom_algebraMap a m hm0 hm ha x p c).trans
        (kummerPointHom_algebraMap a m hm0 hm ha x q c).symm
    · exact h
  apply Over.OverMorphism.ext
  rw [← kummerPointHom_spec a m hm0 hm ha x p, ← kummerPointHom_spec a m hm0 hm ha x q, hφ]

/-- The geometric point of the Kummer cover sending `X` to a given `m`-th root of the image
of `a`. -/
def kummerPointOfRoot (r : Ω) (hr : r ^ m = Spec.preimage x a) :
    Fiber x (kummerRootCover a m hm0 hm ha) :=
  Over.homMk (Spec.map (CommRingCat.ofHom
    (AdjoinRoot.lift (Spec.preimage x).hom r (by simp [hr])))) (by
    change Spec.map _ ≫ Spec.map _ = x
    rw [← Spec.map_comp]
    conv_rhs => rw [← Spec.map_preimage x]
    congr 1
    ext c
    simp)

theorem kummerRootValue_pointOfRoot (r : Ω) (hr : r ^ m = Spec.preimage x a) :
    kummerRootValue a m hm0 hm ha x (kummerPointOfRoot a m hm0 hm ha x r hr) = r := by
  simp [kummerRootValue, kummerPointHom, kummerPointOfRoot]

theorem kummerFiber_nonempty [IsAlgClosed Ω] :
    Nonempty (Fiber x (kummerRootCover a m hm0 hm ha)) := by
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (Spec.preimage x a) (Nat.pos_of_ne_zero hm0)
  exact ⟨kummerPointOfRoot a m hm0 hm ha x r hr⟩

theorem kummerFiber_finite_and_card_le :
    Finite (Fiber x (kummerRootCover a m hm0 hm ha)) ∧
      Nat.card (Fiber x (kummerRootCover a m hm0 hm ha)) ≤ m := by
  classical
  set c := Spec.preimage x a
  let f : Fiber x (kummerRootCover a m hm0 hm ha) → (nthRoots m c).toFinset := fun p =>
    ⟨kummerRootValue a m hm0 hm ha x p, by
      rw [Multiset.mem_toFinset, mem_nthRoots (Nat.pos_of_ne_zero hm0)]
      exact kummerRootValue_pow a m hm0 hm ha x p⟩
  have hinj : Function.Injective f := fun p q h =>
    kummerRootValue_injective a m hm0 hm ha x (congrArg Subtype.val h)
  refine ⟨Finite.of_injective f hinj, ?_⟩
  calc Nat.card _ ≤ Nat.card (nthRoots m c).toFinset := Nat.card_le_card_of_injective f hinj
    _ = (nthRoots m c).toFinset.card := Nat.card_eq_finsetCard _
    _ ≤ Multiset.card (nthRoots m c) := Multiset.toFinset_card_le _
    _ ≤ m := card_nthRoots m c

variable (R : Type*) [CommRing R] [Algebra R A]

/-- The cover automorphism `X ↦ ζ X` of the Kummer cover for an `m`-th root of unity `ζ` of
`R`. -/
def kummerScaleHom (ζ : rootsOfUnity m R) :
    kummerRootCover a m hm0 hm ha ⟶ kummerRootCover a m hm0 hm ha :=
  ObjectProperty.homMk (Over.homMk
    (Spec.map (CommRingCat.ofHom (kummerScale R a m ζ).toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext c
    exact (kummerScale R a m ζ).commutes c))

theorem kummerRootValue_scale (p : Fiber x (kummerRootCover a m hm0 hm ha))
    (ζ : rootsOfUnity m R) :
    kummerRootValue a m hm0 hm ha x (p ≫ (kummerScaleHom a m hm0 hm ha R ζ).hom) =
      Spec.preimage x (algebraMap R A ((ζ : Rˣ) : R)) * kummerRootValue a m hm0 hm ha x p := by
  have hφ : kummerPointHom a m hm0 hm ha x (p ≫ (kummerScaleHom a m hm0 hm ha R ζ).hom) =
      CommRingCat.ofHom (kummerScale R a m ζ).toRingHom ≫ kummerPointHom a m hm0 hm ha x p := by
    apply Spec.map_injective
    rw [kummerPointHom_spec, Spec.map_comp, kummerPointHom_spec]
    rfl
  rw [kummerRootValue, hφ]
  change kummerPointHom a m hm0 hm ha x p (kummerScale R a m ζ (AdjoinRoot.root _)) = _
  rw [kummerScale_root, map_mul, kummerPointHom_algebraMap]
  rfl

theorem kummerScale_comp (p : Fiber x (kummerRootCover a m hm0 hm ha))
    (ζ η : rootsOfUnity m R) :
    (p ≫ (kummerScaleHom a m hm0 hm ha R ζ).hom) ≫ (kummerScaleHom a m hm0 hm ha R η).hom =
      p ≫ (kummerScaleHom a m hm0 hm ha R (ζ * η)).hom := by
  apply kummerRootValue_injective a m hm0 hm ha x
  rw [kummerRootValue_scale, kummerRootValue_scale, kummerRootValue_scale]
  simp only [Subgroup.coe_mul, Units.val_mul, map_mul]
  ring

theorem kummerScale_one (p : Fiber x (kummerRootCover a m hm0 hm ha)) :
    p ≫ (kummerScaleHom a m hm0 hm ha R 1).hom = p := by
  apply kummerRootValue_injective a m hm0 hm ha x
  rw [kummerRootValue_scale]
  simp

section Torsor

variable [IsLocalRing R] (hmR : IsUnit (m : R))

include hmR in
/-- Distinct `m`-th roots of unity of a local ring with `m` invertible stay distinct in every
nonzero ring. -/
theorem rootsOfUnity_eq_of_map_eq {S : Type*} [CommRing S] [Nontrivial S] (ψ : R →+* S)
    {ζ η : rootsOfUnity m R} (h : ψ ((ζ : Rˣ) : R) = ψ ((η : Rˣ) : R)) : ζ = η := by
  set θ : rootsOfUnity m R := ζ * η⁻¹
  have hθ : ((θ : Rˣ) : R) ^ m = 1 := by
    rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity m (θ : Rˣ)).mp θ.2, Units.val_one]
  have hψ : ψ ((θ : Rˣ) : R) = 1 := by
    have h1 : ψ ((η : Rˣ) : R) * ψ (((η⁻¹ : rootsOfUnity m R) : Rˣ) : R) = 1 := by
      rw [← map_mul, ← Units.val_mul, ← Subgroup.coe_mul, mul_inv_cancel]
      simp
    simp only [θ, Subgroup.coe_mul, Units.val_mul, map_mul, h, h1]
  have h1 := Langlands.CommutativeAlgebra.StrictlyHenselianKummerUnits.eq_one_of_pow_eq_one_of_map_eq_one
    ψ hmR hθ hψ
  have hθ1 : θ = 1 := Subtype.ext (Units.ext h1)
  rw [mul_inv_eq_one] at hθ1
  exact hθ1

include hmR in
theorem kummerScale_injective (p : Fiber x (kummerRootCover a m hm0 hm ha)) :
    Function.Injective (fun ζ : rootsOfUnity m R => p ≫ (kummerScaleHom a m hm0 hm ha R ζ).hom) := by
  intro ζ η h
  have h1 := congrArg (kummerRootValue a m hm0 hm ha x) h
  simp only [kummerRootValue_scale] at h1
  have h2 := mul_right_cancel₀ (kummerRootValue_ne_zero a m hm0 hm ha x p) h1
  exact rootsOfUnity_eq_of_map_eq m R hmR ((Spec.preimage x).hom.comp (algebraMap R A)) h2

include hmR in
theorem kummerScale_bijective (hcardR : Nat.card (rootsOfUnity m R) = m)
    (p : Fiber x (kummerRootCover a m hm0 hm ha)) :
    Function.Bijective
      (fun ζ : rootsOfUnity m R => p ≫ (kummerScaleHom a m hm0 hm ha R ζ).hom) := by
  obtain ⟨hfin, hcard⟩ := kummerFiber_finite_and_card_le a m hm0 hm ha x
  refine (kummerScale_injective a m hm0 hm ha x R hmR p).bijective_of_nat_card_le ?_
  rw [hcardR]
  exact hcard

include hmR in
theorem kummerScale_eq_self_iff (p : Fiber x (kummerRootCover a m hm0 hm ha))
    (ζ : rootsOfUnity m R) : p ≫ (kummerScaleHom a m hm0 hm ha R ζ).hom = p ↔ ζ = 1 := by
  constructor
  · intro h
    apply kummerScale_injective a m hm0 hm ha x R hmR p
    simp only
    rw [h, kummerScale_one]
  · rintro rfl
    exact kummerScale_one a m hm0 hm ha x R p

end Torsor

end Fiber

section Character

variable {A : Type u} [CommRing A] (a : A) (m : ℕ) (hm0 : m ≠ 0) (hm : IsUnit (m : A))
  (ha : IsUnit a) {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ Spec (.of A))
  (hx : ∀ Y : Cover (Spec (.of A)), Finite (Fiber x Y))
  (R : Type*) [CommRing R] [Algebra R A] [IsLocalRing R] (hmR : IsUnit (m : R))
  (hcardR : Nat.card (rootsOfUnity m R) = m)

/-- The base point used to define the Kummer character. -/
def kummerBasePoint : Fiber x (kummerRootCover a m hm0 hm ha) :=
  (kummerFiber_nonempty a m hm0 hm ha x).some

/-- The Kummer character as a function: the root of unity carrying the base point to its
translate by an element of the fundamental group. -/
def kummerCharacterFun (g : FundamentalGroup x hx) : rootsOfUnity m R :=
  (Equiv.ofBijective _ (kummerScale_bijective a m hm0 hm ha x R hmR hcardR
    (kummerBasePoint a m hm0 hm ha x))).symm (g • kummerBasePoint a m hm0 hm ha x)

theorem smul_kummerBasePoint (g : FundamentalGroup x hx) :
    g • kummerBasePoint a m hm0 hm ha x = kummerBasePoint a m hm0 hm ha x ≫
      (kummerScaleHom a m hm0 hm ha R (kummerCharacterFun a m hm0 hm ha x hx R hmR hcardR g)).hom :=
  (Equiv.ofBijective_apply_symm_apply
    (fun ζ : rootsOfUnity m R => kummerBasePoint a m hm0 hm ha x ≫
      (kummerScaleHom a m hm0 hm ha R ζ).hom)
    (kummerScale_bijective a m hm0 hm ha x R hmR hcardR (kummerBasePoint a m hm0 hm ha x))
    (g • kummerBasePoint a m hm0 hm ha x)).symm

theorem smul_eq_comp_kummerScale (g : FundamentalGroup x hx)
    (p : Fiber x (kummerRootCover a m hm0 hm ha)) :
    g • p = p ≫
      (kummerScaleHom a m hm0 hm ha R (kummerCharacterFun a m hm0 hm ha x hx R hmR hcardR g)).hom := by
  obtain ⟨η, rfl⟩ := (kummerScale_bijective a m hm0 hm ha x R hmR hcardR
    (kummerBasePoint a m hm0 hm ha x)).2 p
  simp only
  rw [smul_naturality, smul_kummerBasePoint a m hm0 hm ha x hx R hmR hcardR, kummerScale_comp,
    kummerScale_comp, mul_comm]

/-- **The Kummer character.** The fundamental group acts on the geometric fibre of the Kummer
cover `Spec A[X]/(X^m - a)` through the `m`-th roots of unity of `R` acting by `X ↦ ζ X`. -/
def kummerCharacter : FundamentalGroup x hx →* rootsOfUnity m R where
  toFun := kummerCharacterFun a m hm0 hm ha x hx R hmR hcardR
  map_one' := by
    apply kummerScale_injective a m hm0 hm ha x R hmR (kummerBasePoint a m hm0 hm ha x)
    simp only
    rw [← smul_kummerBasePoint, one_smul, kummerScale_one]
  map_mul' g h := by
    apply kummerScale_injective a m hm0 hm ha x R hmR (kummerBasePoint a m hm0 hm ha x)
    simp only
    rw [← smul_kummerBasePoint, ← kummerScale_comp, mul_smul, smul_kummerBasePoint a m hm0 hm ha x hx R hmR hcardR h,
      smul_naturality, smul_kummerBasePoint a m hm0 hm ha x hx R hmR hcardR g]

theorem smul_eq_comp_kummerCharacter (g : FundamentalGroup x hx)
    (p : Fiber x (kummerRootCover a m hm0 hm ha)) :
    g • p = p ≫
      (kummerScaleHom a m hm0 hm ha R (kummerCharacter a m hm0 hm ha x hx R hmR hcardR g)).hom :=
  smul_eq_comp_kummerScale a m hm0 hm ha x hx R hmR hcardR g p

theorem smul_eq_self_iff_kummerCharacter (g : FundamentalGroup x hx)
    (p : Fiber x (kummerRootCover a m hm0 hm ha)) :
    g • p = p ↔ kummerCharacter a m hm0 hm ha x hx R hmR hcardR g = 1 := by
  rw [smul_eq_comp_kummerCharacter a m hm0 hm ha x hx R hmR hcardR g p,
    kummerScale_eq_self_iff a m hm0 hm ha x R hmR]

/-- The kernel of the Kummer character is the stabilizer of any geometric point. -/
theorem ker_kummerCharacter (p : Fiber x (kummerRootCover a m hm0 hm ha)) :
    (kummerCharacter a m hm0 hm ha x hx R hmR hcardR).ker =
      MulAction.stabilizer (FundamentalGroup x hx) p := by
  ext g
  rw [MonoidHom.mem_ker, MulAction.mem_stabilizer_iff,
    smul_eq_self_iff_kummerCharacter a m hm0 hm ha x hx R hmR hcardR]

/-- The kernel of the Kummer character is open. -/
theorem isOpen_ker_kummerCharacter :
    IsOpen ((kummerCharacter a m hm0 hm ha x hx R hmR hcardR).ker : Set (FundamentalGroup x hx)) := by
  rw [ker_kummerCharacter a m hm0 hm ha x hx R hmR hcardR (kummerBasePoint a m hm0 hm ha x)]
  exact (continuous_evaluation x hx _ (kummerBasePoint a m hm0 hm ha x)).isOpen_preimage
    {kummerBasePoint a m hm0 hm ha x} (isOpen_discrete _)

end Character

section Level

variable {A : Type u} [CommRing A] (a : A) (ha : IsUnit a) {m d n : ℕ} (hmn : m * d = n)
  (hm0 : m ≠ 0) (hm : IsUnit (m : A)) (hn0 : n ≠ 0) (hn : IsUnit (n : A))
  {Ω : Type u} [Field Ω] (x : Spec (.of Ω) ⟶ Spec (.of A))

/-- The cover map `Spec A[X]/(X^n - a) → Spec A[X]/(X^m - a)` given by `X ↦ X^d`, where
`m * d = n`. -/
def kummerLevelHom : kummerRootCover a n hn0 hn ha ⟶ kummerRootCover a m hm0 hm ha :=
  ObjectProperty.homMk (Over.homMk
    (Spec.map (CommRingCat.ofHom (kummerLevel a hmn).toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp]
    congr 1
    ext c
    exact (kummerLevel a hmn).commutes c))

theorem kummerRootValue_level (p : Fiber x (kummerRootCover a n hn0 hn ha)) :
    kummerRootValue a m hm0 hm ha x (p ≫ (kummerLevelHom a ha hmn hm0 hm hn0 hn).hom) =
      kummerRootValue a n hn0 hn ha x p ^ d := by
  have hφ : kummerPointHom a m hm0 hm ha x (p ≫ (kummerLevelHom a ha hmn hm0 hm hn0 hn).hom) =
      CommRingCat.ofHom (kummerLevel a hmn).toRingHom ≫ kummerPointHom a n hn0 hn ha x p := by
    apply Spec.map_injective
    rw [kummerPointHom_spec, Spec.map_comp, kummerPointHom_spec]
    rfl
  rw [kummerRootValue, hφ]
  change kummerPointHom a n hn0 hn ha x p (kummerLevel a hmn (AdjoinRoot.root _)) = _
  rw [kummerLevel_root, map_pow]
  rfl

variable [IsAlgClosed Ω] (hx : ∀ Y : Cover (Spec (.of A)), Finite (Fiber x Y))
  (R : Type*) [CommRing R] [Algebra R A] [IsLocalRing R] (hmR : IsUnit (m : R))
  (hnR : IsUnit (n : R)) (hcardm : Nat.card (rootsOfUnity m R) = m)
  (hcardn : Nat.card (rootsOfUnity n R) = n)

include hmn in
/-- **Compatibility of Kummer characters between levels.** If `m * d = n`, the Kummer character
of level `m` is the `d`-th power of the Kummer character of level `n`. -/
theorem kummerCharacter_level (g : FundamentalGroup x hx) :
    ((kummerCharacter a m hm0 hm ha x hx R hmR hcardm g : Rˣ) : R) =
      ((kummerCharacter a n hn0 hn ha x hx R hnR hcardn g : Rˣ) : R) ^ d := by
  obtain ⟨p⟩ := kummerFiber_nonempty a n hn0 hn ha x
  set κm := kummerCharacter a m hm0 hm ha x hx R hmR hcardm g
  set κn := kummerCharacter a n hn0 hn ha x hx R hnR hcardn g
  have h1 := smul_eq_comp_kummerCharacter a m hm0 hm ha x hx R hmR hcardm g
    (p ≫ (kummerLevelHom a ha hmn hm0 hm hn0 hn).hom)
  rw [smul_naturality, smul_eq_comp_kummerCharacter a n hn0 hn ha x hx R hnR hcardn g p] at h1
  have h2 := congrArg (kummerRootValue a m hm0 hm ha x) h1
  rw [kummerRootValue_level, kummerRootValue_scale, kummerRootValue_scale, kummerRootValue_level,
    mul_pow] at h2
  have h3 := mul_right_cancel₀ (pow_ne_zero d (kummerRootValue_ne_zero a n hn0 hn ha x p)) h2
  have hpow : ((κn : Rˣ) ^ d) ∈ rootsOfUnity m R := by
    rw [mem_rootsOfUnity, ← pow_mul, mul_comm, hmn]
    exact (mem_rootsOfUnity n (κn : Rˣ)).mp κn.2
  have h4 := rootsOfUnity_eq_of_map_eq m R hmR ((Spec.preimage x).hom.comp (algebraMap R A))
    (ζ := ⟨(κn : Rˣ) ^ d, hpow⟩) (η := κm) (by
      simp only [RingHom.coe_comp, Function.comp_apply, Units.val_pow_eq_pow_val, map_pow]
      exact h3)
  rw [← h4]
  simp

end Level

section UnitParameter

variable {A : Type u} [CommRing A] (m : ℕ) (hm0 : m ≠ 0) (hm : IsUnit (m : A))
  {Ω : Type u} [Field Ω] (x : Spec (.of Ω) ⟶ Spec (.of A))

/-- The cover map from the identity cover to `Spec A[X]/(X^m - 1)` given by `X ↦ 1`. -/
def kummerUnitSectionHom :
    cover (𝟙 (Spec (.of A))) ⟶ kummerRootCover (1 : A) m hm0 hm isUnit_one :=
  ObjectProperty.homMk (Over.homMk
    (Spec.map (CommRingCat.ofHom (kummerUnitSection (A := A) m).toRingHom)) (by
    change Spec.map _ ≫ Spec.map _ = 𝟙 _
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext c
    exact (kummerUnitSection (A := A) m).commutes c))

/-- The unique geometric point of the identity cover. -/
def identityCoverPoint : Fiber x (cover (𝟙 (Spec (.of A)))) :=
  Over.homMk x (by simp [cover])

theorem identityCover_subsingleton : Subsingleton (Fiber x (cover (𝟙 (Spec (.of A))))) := by
  constructor
  intro p q
  apply Over.OverMorphism.ext
  have hp : p.left ≫ 𝟙 _ = x := Over.w p
  have hq : q.left ≫ 𝟙 _ = x := Over.w q
  exact (Category.comp_id _).symm.trans (hp.trans (hq.symm.trans (Category.comp_id _)))

/-- The geometric point `X ↦ 1` of `Spec A[X]/(X^m - 1)`. -/
def kummerUnitPoint : Fiber x (kummerRootCover (1 : A) m hm0 hm isUnit_one) :=
  identityCoverPoint x ≫ (kummerUnitSectionHom m hm0 hm).hom

theorem smul_kummerUnitPoint (hx : ∀ Y : Cover (Spec (.of A)), Finite (Fiber x Y))
    (g : FundamentalGroup x hx) :
    g • kummerUnitPoint m hm0 hm x = kummerUnitPoint m hm0 hm x := by
  rw [kummerUnitPoint, smul_naturality]
  congr 1
  have := identityCover_subsingleton x
  exact Subsingleton.elim _ _

/-- The Kummer character of `Spec A[X]/(X^m - 1)` is trivial. -/
theorem kummerCharacter_one_eq_one [IsAlgClosed Ω]
    (hx : ∀ Y : Cover (Spec (.of A)), Finite (Fiber x Y))
    (R : Type*) [CommRing R] [Algebra R A] [IsLocalRing R] (hmR : IsUnit (m : R))
    (hcardR : Nat.card (rootsOfUnity m R) = m) :
    kummerCharacter (1 : A) m hm0 hm isUnit_one x hx R hmR hcardR = 1 := by
  ext1 g
  rw [MonoidHom.one_apply, ← smul_eq_self_iff_kummerCharacter (1 : A) m hm0 hm isUnit_one x hx R
    hmR hcardR g (kummerUnitPoint m hm0 hm x)]
  exact smul_kummerUnitPoint m hm0 hm x hx g

end UnitParameter

end Langlands.AlgebraicGeometry.FiniteEtale
