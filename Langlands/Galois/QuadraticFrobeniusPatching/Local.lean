import Langlands.Galois.ClosureRestriction
import Langlands.Galois.FrobeniusLift
import Langlands.Global.AdelicFunctoriality.CompletedRamification
import Langlands.Global.AdelicFunctoriality.Finite
import Langlands.Global.AdelicFunctoriality.LocalDegree
import Langlands.Galois.QuadraticPatchingStatement

/-! # Geometric Frobenius and a square of completion embeddings -/

noncomputable section

open Polynomial IsLocalRing Langlands.Global Langlands.Global.AdelicFunctoriality
open Langlands.Global.AdelicFunctoriality.FiniteExtension
open scoped Valued NumberField

namespace Langlands.GaloisRepresentation.QuadraticFrobeniusPatching

section Closure

variable {K E : Type*} [Field K] [Field E] (f : K →+* E)

theorem chosenClosureEmbedding_commutes (x : K) :
    chosenClosureEmbedding f (algebraMap K (AlgebraicClosure K) x) =
      algebraMap E (AlgebraicClosure E) (f x) := by
  let : Algebra K E := f.toAlgebra
  exact (chosenClosureEmbedding f).commutes x

theorem map_commutes (g : Field.absoluteGaloisGroup E) (x : AlgebraicClosure K) :
    chosenClosureEmbedding f (AlgEquiv.toRingEquiv (Field.absoluteGaloisGroup.map f g) x) =
      AlgEquiv.toRingEquiv g (chosenClosureEmbedding f x) := by
  let : Algebra K E := f.toAlgebra
  exact restrictionAlongClosure_commutes (chosenClosureEmbedding f) g x

theorem chosenClosureEmbedding_bijective
    (hf : letI : Algebra K E := f.toAlgebra; Algebra.IsAlgebraic K E) :
    Function.Bijective (chosenClosureEmbedding f) := by
  let : Algebra K E := f.toAlgebra
  let : Algebra.IsAlgebraic K E := hf
  let : Algebra.IsAlgebraic K (AlgebraicClosure E) :=
    Algebra.IsAlgebraic.trans K E (AlgebraicClosure E)
  exact (Algebra.IsAlgebraic.algHom_bijective₂
    (IsAlgClosed.lift : AlgebraicClosure E →ₐ[K] AlgebraicClosure K)
    (chosenClosureEmbedding f)).2

theorem isAlgebraic_of_surjective (hf : Function.Surjective f) :
    letI : Algebra K E := f.toAlgebra; Algebra.IsAlgebraic K E := by
  let : Algebra K E := f.toAlgebra
  constructor
  intro x
  obtain ⟨y, rfl⟩ := hf x
  exact (isIntegral_algebraMap (R := K) (A := E) (x := y)).isAlgebraic

/-- When the chosen closure embedding is an isomorphism, the image of the
absolute restriction is the group fixing the transported copy of the larger field. -/
theorem mem_map_range_iff (e : AlgebraicClosure K ≃+* AlgebraicClosure E)
    (he : ∀ x, e x = chosenClosureEmbedding f x) (g : Field.absoluteGaloisGroup K) :
    g ∈ (Field.absoluteGaloisGroup.map f).toMonoidHom.range ↔
      ∀ x : E, AlgEquiv.toRingEquiv g (e.symm (algebraMap E (AlgebraicClosure E) x)) =
        e.symm (algebraMap E (AlgebraicClosure E) x) := by
  rw [MonoidHom.mem_range]
  constructor
  · rintro ⟨σ, rfl⟩ x
    apply e.injective
    rw [e.apply_symm_apply]
    have h := map_commutes f σ (e.symm (algebraMap E (AlgebraicClosure E) x))
    simp only [← he, e.apply_symm_apply] at h
    exact h.trans (σ.commutes x)
  · intro hg
    let t := (e.symm.trans (AlgEquiv.toRingEquiv g)).trans e
    have ht (x : E) : t (algebraMap E (AlgebraicClosure E) x) =
        algebraMap E (AlgebraicClosure E) x :=
      (congrArg e (hg x)).trans (e.apply_symm_apply _)
    let σ : Field.absoluteGaloisGroup E := AlgEquiv.ofRingEquiv (f := t) ht
    refine ⟨σ, ?_⟩
    apply AlgEquiv.ext
    intro x
    apply e.injective
    calc
      e (AlgEquiv.toRingEquiv (Field.absoluteGaloisGroup.map f σ) x) =
          AlgEquiv.toRingEquiv σ (e x) := by simpa only [← he] using map_commutes f σ x
      _ = e (AlgEquiv.toRingEquiv g x) := by
        change e (AlgEquiv.toRingEquiv g (e.symm (e x))) = e (AlgEquiv.toRingEquiv g x)
        rw [e.symm_apply_apply]

theorem map_surjective (hf : Function.Surjective f) :
    Function.Surjective (Field.absoluteGaloisGroup.map f) := by
  let : Algebra K E := f.toAlgebra
  let e := RingEquiv.ofBijective (chosenClosureEmbedding f).toRingHom
    (chosenClosureEmbedding_bijective f (isAlgebraic_of_surjective f hf))
  intro g
  apply MonoidHom.mem_range.mp
  apply (mem_map_range_iff f e (fun _ => rfl) g).mpr
  intro x
  obtain ⟨y, rfl⟩ := hf x
  rw [← chosenClosureEmbedding_commutes f y]
  change AlgEquiv.toRingEquiv g (e.symm (e _)) = e.symm (e _)
  rw [e.symm_apply_apply]
  exact g.commutes y

variable {T C : Type*} [Field T] [Field C] [TopologicalSpace C]

/-- The two chosen restrictions compose up to conjugation by a closure automorphism. -/
def pullbackCompEquiv (g : E →+* T) (A : Objects K C) :
    FiniteRepresentation.Equiv (pullback g (pullback f A)).val (pullback (g.comp f) A).val := by
  let : Algebra K E := f.toAlgebra
  let : Algebra E T := g.toAlgebra
  let : Algebra K T := (g.comp f).toAlgebra
  let ι : ClosureEmbedding (g.comp f) :=
    { toRingHom := (chosenClosureEmbedding g).toRingHom.comp (chosenClosureEmbedding f).toRingHom
      commutes' := fun x => by
        change chosenClosureEmbedding g (chosenClosureEmbedding f (algebraMap K _ x)) =
          algebraMap T (AlgebraicClosure T) (g (f x))
        rw [chosenClosureEmbedding_commutes, chosenClosureEmbedding_commutes] }
  have h (a : Field.absoluteGaloisGroup T) :
      Field.absoluteGaloisGroup.map f (Field.absoluteGaloisGroup.map g a) =
        restrictionAlongClosure ι a := by
    apply AlgEquiv.ext
    intro x
    apply ι.injective
    calc
      ι (AlgEquiv.toRingEquiv
        (Field.absoluteGaloisGroup.map f (Field.absoluteGaloisGroup.map g a)) x) =
          chosenClosureEmbedding g (AlgEquiv.toRingEquiv (Field.absoluteGaloisGroup.map g a)
            (chosenClosureEmbedding f x)) :=
        congrArg (fun y : AlgebraicClosure E => chosenClosureEmbedding g y)
          (map_commutes f (Field.absoluteGaloisGroup.map g a) x)
      _ = AlgEquiv.toRingEquiv a (ι x) := map_commutes g _ _
      _ = ι (AlgEquiv.toRingEquiv (restrictionAlongClosure ι a) x) :=
        (restrictionAlongClosure_commutes ι a x).symm
  let e : FiniteRepresentation.Equiv (pullback g (pullback f A)).val
      (pullbackAlongClosure ι A).val :=
    Representation.Equiv.mk (LinearEquiv.refl C A.val) (fun a => by
      change 1 * A.val.representation
        (Field.absoluteGaloisGroup.map f (Field.absoluteGaloisGroup.map g a)) =
          A.val.representation (restrictionAlongClosure ι a) * 1
      rw [one_mul, mul_one, h])
  exact e.trans (pullbackAlongClosureEquiv (chosenClosureEmbedding (g.comp f)) ι A)

theorem action_eq_one_iff {K C : Type*} [Field K] [Field C] [TopologicalSpace C]
    {A B : Objects K C} (e : FiniteRepresentation.Equiv A.val B.val)
    (a : Field.absoluteGaloisGroup K) :
    A.val.representation a = 1 ↔ B.val.representation a = 1 := by
  have h1 : e.conj (1 : Module.End C A.val) = 1 := e.toLinearEquiv.conj_id
  rw [← Representation.Equiv.conj_apply_self a e, ← h1, e.conj.injective.eq_iff]

end Closure

section Residue

open LocalGalois

variable {K E : Type*} [NontriviallyNormedField K] [NontriviallyNormedField E]
  [IsUltrametricDist K] [IsUltrametricDist E] [CompleteSpace K] [CompleteSpace E]
  (f : K →+* E)

private theorem closureInteger_mem
    (hf : ∀ x, ‖f x‖ ≤ 1 ↔ ‖x‖ ≤ 1)
    (x : AlgebraicClosure K) (hx : x ∈ extensionIntegers K (AlgebraicClosure K)) :
    chosenClosureEmbedding f x ∈ extensionIntegers E (AlgebraicClosure E) := by
  let : Algebra K E := f.toAlgebra
  let f₀ : baseIntegers K →+* baseIntegers E :=
    f.restrict (baseIntegers K).toSubring (baseIntegers E).toSubring
      (fun y hy => (hf y).2 hy)
  let ι := chosenClosureEmbedding f
  apply (integral_iff_mem_spectralIntegers E (AlgebraicClosure E) _).mp
  refine IsIntegral.map_of_comp_eq f₀ ι.toRingHom ?_ (spectral_integral K (AlgebraicClosure K) ⟨x, hx⟩)
  apply RingHom.ext
  intro y
  exact (chosenClosureEmbedding_commutes f (y : K)).symm

private theorem closureNorm_lt_one
    (hf : ∀ x, ‖f x‖ ≤ 1 ↔ ‖x‖ ≤ 1) (x : AlgebraicClosure K)
    (hx : spectralNorm K (AlgebraicClosure K) x < 1) :
    spectralNorm E (AlgebraicClosure E) (chosenClosureEmbedding f x) < 1 := by
  let := spectralNorm.nontriviallyNormedField K (AlgebraicClosure K)
  let := spectralNorm.nontriviallyNormedField E (AlgebraicClosure E)
  obtain ⟨a, ha, ha₁⟩ := NormedField.exists_norm_lt K zero_lt_one
  have hfa : ‖f a‖ < 1 := by
    by_contra! hn
    have hi : ‖f (a⁻¹)‖ ≤ 1 := by simpa only [map_inv₀, norm_inv] using inv_le_one_of_one_le₀ hn
    have hi' := (hf _).1 hi
    rw [norm_inv, inv_le_one₀ ha] at hi'
    exact ha₁.not_ge hi'
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one ha hx
  have hn' : ‖x ^ n / algebraMap K (AlgebraicClosure K) a‖ ≤ 1 := by
    rw [norm_div, norm_pow]
    change spectralNorm K _ x ^ n / spectralNorm K _ (algebraMap K _ a) ≤ 1
    rw [spectralNorm_extends]
    exact (div_le_one ha).mpr hn.le
  have hb := closureInteger_mem f hf _ hn'
  change ‖chosenClosureEmbedding f (x ^ n / algebraMap K (AlgebraicClosure K) a)‖ ≤ 1 at hb
  rw [map_div₀, map_pow, chosenClosureEmbedding_commutes, norm_div, norm_pow] at hb
  change spectralNorm E _ (chosenClosureEmbedding f x) ^ n /
    spectralNorm E _ (algebraMap E _ (f a)) ≤ 1 at hb
  rw [spectralNorm_extends] at hb
  have hfaPos : 0 < ‖f a‖ := norm_pos_iff.mpr ((_root_.map_ne_zero f).2 (norm_pos_iff.mp ha))
  have hpow := (div_le_one hfaPos).mp hb
  exact lt_of_not_ge fun h => hfa.not_ge ((one_le_pow₀ h).trans hpow)

private theorem closureInteger_mem_iff
    (hf : ∀ x, ‖f x‖ ≤ 1 ↔ ‖x‖ ≤ 1) (x : AlgebraicClosure K) :
    chosenClosureEmbedding f x ∈ extensionIntegers E (AlgebraicClosure E) ↔
      x ∈ extensionIntegers K (AlgebraicClosure K) := by
  refine ⟨fun hx => ?_, closureInteger_mem f hf x⟩
  let := spectralNorm.nontriviallyNormedField K (AlgebraicClosure K)
  let := spectralNorm.nontriviallyNormedField E (AlgebraicClosure E)
  change ‖chosenClosureEmbedding f x‖ ≤ 1 at hx
  change ‖x‖ ≤ 1
  by_contra! h
  have hi : ‖x⁻¹‖ < 1 := by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ h
  have hlt : ‖chosenClosureEmbedding f (x⁻¹)‖ < 1 := closureNorm_lt_one f hf _ hi
  let : Algebra K E := f.toAlgebra
  have hfx : 0 < ‖chosenClosureEmbedding f x‖ :=
    norm_pos_iff.mpr ((_root_.map_ne_zero (chosenClosureEmbedding f)).2 (norm_pos_iff.mp (zero_lt_one.trans h)))
  rw [map_inv₀, norm_inv, inv_lt_one₀ hfx] at hlt
  exact hlt.not_ge hx

/-- The chosen closure map induces an isomorphism of spectral integer rings for an algebraic
embedding that preserves and reflects the unit ball. -/
def closureIntegerEquiv
    (hf : ∀ x, ‖f x‖ ≤ 1 ↔ ‖x‖ ≤ 1)
    (hAlg : letI : Algebra K E := f.toAlgebra; Algebra.IsAlgebraic K E) :
    extensionIntegers K (AlgebraicClosure K) ≃+*
      extensionIntegers E (AlgebraicClosure E) := by
  let : Algebra K E := f.toAlgebra
  let ι := chosenClosureEmbedding f
  let F := ι.toRingHom.restrict (extensionIntegers K (AlgebraicClosure K)).toSubring
    (extensionIntegers E (AlgebraicClosure E)).toSubring (closureInteger_mem f hf)
  have hι := chosenClosureEmbedding_bijective f hAlg
  refine RingEquiv.ofBijective F ⟨fun x y h => Subtype.ext (hι.1 (congrArg Subtype.val h)), ?_⟩
  intro y
  obtain ⟨x, hx⟩ := hι.2 (y : AlgebraicClosure E)
  exact ⟨⟨x, (closureInteger_mem_iff f hf x).1 (hx ▸ y.property)⟩, Subtype.ext hx⟩

def closureResidueEquiv
    (hf : ∀ x, ‖f x‖ ≤ 1 ↔ ‖x‖ ≤ 1)
    (hAlg : letI : Algebra K E := f.toAlgebra; Algebra.IsAlgebraic K E) :
    ResidueField (extensionIntegers K (AlgebraicClosure K)) ≃+*
      ResidueField (extensionIntegers E (AlgebraicClosure E)) :=
  ResidueField.mapEquiv (closureIntegerEquiv f hf hAlg)

theorem closureResidueEquiv_action
    (hf : ∀ x, ‖f x‖ ≤ 1 ↔ ‖x‖ ≤ 1)
    (hAlg : letI : Algebra K E := f.toAlgebra; Algebra.IsAlgebraic K E)
    (g : Field.absoluteGaloisGroup E)
    (x : ResidueField (extensionIntegers K (AlgebraicClosure K))) :
    closureResidueEquiv f hf hAlg (residueHom K (AlgebraicClosure K)
      (Field.absoluteGaloisGroup.map f g) x) =
    residueHom E (AlgebraicClosure E) g (closureResidueEquiv f hf hAlg x) := by
  obtain ⟨y, rfl⟩ := residue_surjective x
  let gK : Gal(AlgebraicClosure K/K) := Field.absoluteGaloisGroup.map f g
  let gE : Gal(AlgebraicClosure E/E) := g
  change closureResidueEquiv f hf hAlg (residueHom K (AlgebraicClosure K) gK (residue _ y)) =
    residueHom E (AlgebraicClosure E) gE (closureResidueEquiv f hf hAlg (residue _ y))
  simp only [closureResidueEquiv, ResidueField.mapEquiv_apply, ResidueField.map_residue, residueHom_apply]
  exact congrArg (residue _) (Subtype.ext (map_commutes f g y))

end Residue

section CompletionSquare

open scoped FiniteExtension

variable {K E C : Type*} [Field K] [NumberField K] [Field E] [NumberField E]
  [Field C] [TopologicalSpace C]
  {v : FinitePlace K} {w : FinitePlace E}
  (g : FiniteCompletion K v →+* FiniteCompletion E w)

include g in
/-- Under restriction along the local embedding, the upstairs inertia group is
exactly the inverse image of the downstairs inertia group. -/
theorem map_mem_inertia_iff
    (hg : ∀ x, ‖g x‖ ≤ 1 ↔ ‖x‖ ≤ 1)
    (hAlg : letI : Algebra (FiniteCompletion K v) (FiniteCompletion E w) := g.toAlgebra
      Algebra.IsAlgebraic (FiniteCompletion K v) (FiniteCompletion E w))
    (a : LocalGroup w) :
    Field.absoluteGaloisGroup.map g a ∈ localInertia v ↔ a ∈ localInertia w := by
  let e := closureResidueEquiv g hg hAlg
  have he (x : LocalResidueClosure v) :
      e (localResidueAction v (Field.absoluteGaloisGroup.map g a) x) =
        localResidueAction w a (e x) := closureResidueEquiv_action g hg hAlg a x
  constructor
  · intro h
    change localResidueAction v (Field.absoluteGaloisGroup.map g a) = 1 at h
    change localResidueAction w a = 1
    ext z
    obtain ⟨x, rfl⟩ := e.surjective z
    rw [← he, h]
    rfl
  · intro h
    change localResidueAction w a = 1 at h
    change localResidueAction v (Field.absoluteGaloisGroup.map g a) = 1
    ext x
    apply e.injective
    rw [he, h]
    rfl

private theorem arithmetic_power_apply {b : LocalGroup v}
    (hb : IsGeometricFrobeniusLift v b) (d : ℕ) (x : LocalResidueClosure v) :
    localResidueAction v ((b⁻¹) ^ d) x = x ^ (residueCardinality v ^ d) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [pow_succ', map_mul, AlgEquiv.mul_apply, hb, ih, ← pow_mul, pow_succ]

/-- Restricting a geometric lift induces the residue-degree power of geometric
Frobenius. The arithmetic cardinality formula is applied to the inverses. -/
theorem residueAction_map_eq_pow
    (hg : ∀ x, ‖g x‖ ≤ 1 ↔ ‖x‖ ≤ 1)
    (hAlg : letI : Algebra (FiniteCompletion K v) (FiniteCompletion E w) := g.toAlgebra
      Algebra.IsAlgebraic (FiniteCompletion K v) (FiniteCompletion E w))
    (d : ℕ) (hd : residueCardinality w = residueCardinality v ^ d)
    {a : LocalGroup w} {b : LocalGroup v}
    (ha : IsGeometricFrobeniusLift w a) (hb : IsGeometricFrobeniusLift v b) :
    localResidueAction v (Field.absoluteGaloisGroup.map g a) = localResidueAction v (b ^ d) := by
  apply inv_injective
  rw [← map_inv, ← map_inv, ← map_inv, ← inv_pow]
  ext x
  apply (closureResidueEquiv g hg hAlg).injective
  change closureResidueEquiv g hg hAlg
      (localResidueAction v (Field.absoluteGaloisGroup.map g (a⁻¹)) x) =
    closureResidueEquiv g hg hAlg (localResidueAction v ((b⁻¹) ^ d) x)
  have he : closureResidueEquiv g hg hAlg
      (localResidueAction v (Field.absoluteGaloisGroup.map g (a⁻¹)) x) =
        localResidueAction w (a⁻¹) (closureResidueEquiv g hg hAlg x) :=
    closureResidueEquiv_action g hg hAlg a⁻¹ x
  rw [he, ha, arithmetic_power_apply hb, map_pow, hd]

/-- The commuting square of field embeddings induces a commuting square of
restrictions up to an actual linear intertwiner. -/
def completionSquareEquiv (f : K →+* E)
    (h : ∀ x, g (NumberField.FinitePlace.embedding v x) =
      NumberField.FinitePlace.embedding w (f x)) (A : Objects K C) :
    FiniteRepresentation.Equiv (atFinitePlace w (pullback f A)).val
      (pullback g (atFinitePlace v A)).val := by
  have hcomp : (NumberField.FinitePlace.embedding w).comp f =
      g.comp (NumberField.FinitePlace.embedding v) := RingHom.ext fun x => (h x).symm
  have e := pullbackCompEquiv f (NumberField.FinitePlace.embedding w) A
  rw [hcomp] at e
  exact e.trans (pullbackCompEquiv (NumberField.FinitePlace.embedding v) g A).symm

theorem hasEulerPolynomialAt_equiv {A B : Objects E C}
    (e : FiniteRepresentation.Equiv A.val B.val) (w : FinitePlace E) (P : C[X]) :
    HasEulerPolynomialAt A w P ↔ HasEulerPolynomialAt B w P := by
  let e' : FiniteRepresentation.Equiv (atFinitePlace w A).val (atFinitePlace w B).val :=
    Representation.Equiv.mk e.toLinearEquiv fun a =>
      e.toIntertwiningMap.isIntertwining'
        (Field.absoluteGaloisGroup.map (NumberField.FinitePlace.embedding w) a)
  rw [hasEulerPolynomialAt_iff, hasEulerPolynomialAt_iff]
  change (IsUnramifiedAt A w ∧ eulerPolynomial (atFinitePlace w A) _ = P) ↔
    (IsUnramifiedAt B w ∧ eulerPolynomial (atFinitePlace w B) _ = P)
  rw [eulerPolynomial_eq_of_equiv e']
  exact and_congr_left' (forall_congr' fun i => action_eq_one_iff e' i.val)

variable (f : K →+* E)
    (h : ∀ x, g (NumberField.FinitePlace.embedding v x) =
      NumberField.FinitePlace.embedding w (f x))
    (hg : ∀ x, ‖g x‖ ≤ 1 ↔ ‖x‖ ≤ 1)
    (hAlg : letI : Algebra (FiniteCompletion K v) (FiniteCompletion E w) := g.toAlgebra
      Algebra.IsAlgebraic (FiniteCompletion K v) (FiniteCompletion E w))
    {A : Objects K C}

include g h hg hAlg

theorem isUnramifiedAt_pullback (hA : IsUnramifiedAt A v) :
    IsUnramifiedAt (pullback f A) w := by
  intro i
  exact (action_eq_one_iff (completionSquareEquiv g f h A) i.val).2
    (hA ⟨Field.absoluteGaloisGroup.map g i.val, (map_mem_inertia_iff g hg hAlg i.val).2 i.prop⟩)

theorem eulerPolynomial_pullback_pow (hA : IsUnramifiedAt A v)
    (d : ℕ) (hd : residueCardinality w = residueCardinality v ^ d)
    {a : LocalGroup w} {b : LocalGroup v}
    (ha : IsGeometricFrobeniusLift w a) (hb : IsGeometricFrobeniusLift v b) :
    eulerPolynomial (atFinitePlace w (pullback f A)) a = eulerPolynomial (atFinitePlace v A) (b ^ d) := by
  rw [eulerPolynomial_eq_of_equiv (completionSquareEquiv g f h A), eulerPolynomial_pullback,
    eulerPolynomial, eulerPolynomial, characteristicPolynomial, characteristicPolynomial,
    action_eq_of_residueAction_eq hA (residueAction_map_eq_pow g hg hAlg d hd ha hb)]

/-- Along an isomorphism of completions with the same residue cardinality, both
inertia triviality and the geometric Euler polynomial descend. -/
theorem hasEulerPolynomialAt_of_local_surjective (hSurj : Function.Surjective g)
    (hd : residueCardinality w = residueCardinality v) {P : C[X]}
    (hA : HasEulerPolynomialAt (pullback f A) w P) : HasEulerPolynomialAt A v P := by
  have hInertia : IsUnramifiedAt A v := by
    intro i
    obtain ⟨a, ha⟩ := map_surjective g hSurj i.val
    have hai : a ∈ localInertia w := (map_mem_inertia_iff g hg hAlg a).1 (ha ▸ i.prop)
    have he := (action_eq_one_iff (completionSquareEquiv g f h A) a).1 (hA.1 ⟨a, hai⟩)
    change (atFinitePlace v A).val.representation (Field.absoluteGaloisGroup.map g a) = 1 at he
    simpa only [ha] using he
  obtain ⟨_, a, ha, hp⟩ := hA
  let b := geometricFrobeniusLift v
  refine ⟨hInertia, b, geometricFrobeniusLift_spec v, ?_⟩
  have he := eulerPolynomial_pullback_pow g f h hg hAlg hInertia 1 (by simpa using hd)
    ha (geometricFrobeniusLift_spec v)
  simpa only [pow_one] using he.symm.trans hp

end CompletionSquare

end Langlands.GaloisRepresentation.QuadraticFrobeniusPatching
