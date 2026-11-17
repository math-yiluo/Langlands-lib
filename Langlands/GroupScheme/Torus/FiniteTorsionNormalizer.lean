import Langlands.GroupScheme.Torus.FiniteTorsionNormalizerDetection

/-! # Finite torsion subgroups detecting diagonalizable normalizers -/

noncomputable section

universe u

open CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme.CharacterAction

open Corepresented FiniteCharacterSeparation

variable {R : CommRingCat.{u}} {M N : Type u} [AddCommGroup M] [AddCommGroup N]
  {F : CommAlgCat.{u} R ⥤ GrpCat.{u}} (emb : CharacterEmbedding F M)

/-- The subgroup of characters induced by a quotient character group. -/
def quotientEmbedding (emb : CharacterEmbedding F M) (q : M →+ N) (hq : Function.Surjective q) : CharacterEmbedding F N where
  hom A :=
    { toFun := fun t => emb.hom A (t.comp (AddMonoidHom.toMultiplicative q))
      map_one' := (emb.hom A).map_one
      map_mul' := by
        intro t s
        have h : (t * s).comp (AddMonoidHom.toMultiplicative q) =
            t.comp (AddMonoidHom.toMultiplicative q) * s.comp (AddMonoidHom.toMultiplicative q) := by
          ext m
          rfl
        rw [h, map_mul] }
  naturality f t := by
    change F.map f (emb.hom _ (t.comp (AddMonoidHom.toMultiplicative q))) = _
    rw [emb.naturality]
    rfl
  injective A t s h := by
    have h' := emb.injective A h
    apply MonoidHom.ext
    intro n
    obtain ⟨m, hm⟩ := hq n.toAdd
    have hx := DFunLike.congr_fun h' (Multiplicative.ofAdd m)
    change t (Multiplicative.ofAdd (q m)) = s (Multiplicative.ofAdd (q m)) at hx
    rw [hm] at hx
    exact hx

/-- The characteristic integer quotient embedding. -/
abbrev integerTorsionEmbedding (emb : CharacterEmbedding F M) (n : ℕ) : CharacterEmbedding F (M ⧸ multiples n) :=
  quotientEmbedding emb (QuotientAddGroup.mk' (multiples n)) QuotientAddGroup.mk_surjective

/-- Integer multiples vanish in the characteristic integer quotient. -/
theorem quotient_nsmul_eq_zero (n : ℕ) (m : M) :
    n • (QuotientAddGroup.mk' (multiples n)) m = 0 := by
  rw [← map_nsmul]
  apply (QuotientAddGroup.eq_zero_iff _).mpr
  exact ⟨m, rfl⟩

/-- Its embedded points are precisely the n-torsion points of the full
embedded character group. -/
theorem integerTorsionEmbedding_mem_iff (n : ℕ) (A : CommAlgCat.{u} R) (x : F.obj A) :
    x ∈ (integerTorsionEmbedding emb n).range A ↔ x ∈ emb.range A ∧ x ^ n = 1 := by
  let q : M →+ M ⧸ multiples n := QuotientAddGroup.mk' (multiples n)
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨⟨t.comp (AddMonoidHom.toMultiplicative q), rfl⟩, ?_⟩
    change (emb.hom A (t.comp (AddMonoidHom.toMultiplicative q))) ^ n = 1
    rw [← map_pow, ← (emb.hom A).map_one]
    congr 1
    apply MonoidHom.ext
    intro m
    change t (Multiplicative.ofAdd (q m.toAdd)) ^ n = 1
    rw [← map_pow]
    change t (Multiplicative.ofAdd (n • q m.toAdd)) = 1
    rw [quotient_nsmul_eq_zero]
    exact t.map_one
  · rintro ⟨⟨t, rfl⟩, ht⟩
    have htn : t ^ n = 1 := emb.injective A
      (((emb.hom A).map_pow t n).trans (ht.trans (emb.hom A).map_one.symm))
    let ψ : M →+ Additive Aˣ :=
      { toFun := fun m => Additive.ofMul (t (Multiplicative.ofAdd m))
        map_zero' := t.map_one
        map_add' := fun m m' => t.map_mul _ _ }
    have hker : multiples n ≤ ψ.ker := by
      rintro m ⟨a, rfl⟩
      change t (Multiplicative.ofAdd (n • a)) = 1
      change t ((Multiplicative.ofAdd a) ^ n) = 1
      rw [map_pow]
      exact DFunLike.congr_fun htn (Multiplicative.ofAdd a)
    let ψq := QuotientAddGroup.lift (multiples n) ψ hker
    let tq : Multiplicative (M ⧸ multiples n) →* Aˣ :=
      { toFun := fun m => (ψq m.toAdd).toMul
        map_one' := ψq.map_zero
        map_mul' := fun m m' => ψq.map_add _ _ }
    refine ⟨tq, ?_⟩
    change emb.hom A (tq.comp (AddMonoidHom.toMultiplicative q)) = emb.hom A t
    congr 1

/-- Normalization preserves the characteristic n-torsion subgroup. -/
theorem normalizerFamily_le_integerTorsion (n : ℕ) (A : CommAlgCat.{u} R) :
    normalizerFamily emb.range A ≤ normalizerFamily (integerTorsionEmbedding emb n).range A := by
  intro g hg D f x hx
  have hx' := (integerTorsionEmbedding_mem_iff emb n D x).mp hx
  have hpow (a : F.obj D) : (a * x * a⁻¹) ^ n = 1 := by
    rw [conj_pow, hx'.2, mul_one, mul_inv_cancel]
  constructor
  · apply (integerTorsionEmbedding_mem_iff emb n D _).mpr
    exact ⟨(hg D f x hx'.1).1, hpow _⟩
  · apply (integerTorsionEmbedding_mem_iff emb n D _).mpr
    exact ⟨(hg D f x hx'.1).2, by simpa only [inv_inv] using hpow (F.map f g)⁻¹⟩

/-- Reduction of the universal conjugate is the universal conjugate for the
finite torsion embedding. -/
theorem degreeMap_universalEmbeddedConjugate (n : ℕ) {A : CommAlgCat.{u} R} (g : F.obj A) :
    F.map (degreeMap (QuotientAddGroup.mk' (multiples n)) A)
        (universalEmbeddedConjugate emb g) =
      universalEmbeddedConjugate (integerTorsionEmbedding emb n) g := by
  let q : M →+ M ⧸ multiples n := QuotientAddGroup.mk' (multiples n)
  have hc : constant (M := M) A ≫ degreeMap q A = constant (M := M ⧸ multiples n) A :=
    constant_evaluate _ _
  have ht : mapCharacter (degreeMap q A) (universal (M := M) A) =
      (universal (M := M ⧸ multiples n) A).comp (AddMonoidHom.toMultiplicative q) :=
    mapCharacter_evaluate_universal _ _
  dsimp only [q] at hc ht
  simp only [universalEmbeddedConjugate, map_mul, map_inv, emb.naturality, ht,
    ← ConcreteCategory.comp_apply, ← F.map_comp, hc]
  rfl

/-- Some finite characteristic torsion subgroup has exactly the full
normalizer of the embedded diagonalizable group, over every coefficient algebra. -/
theorem exists_integerTorsion_same_normalizer [AddGroup.FG M]
    {B : CommAlgCat.{u} R} (e : (F ⋙ forget GrpCat).CorepresentableBy B)
    {I : Ideal B} (hI : IsCutOutBy e emb.range I) (hIfg : I.FG) :
    ∃ n : ℕ, 0 < n ∧ ∀ A : CommAlgCat.{u} R,
      normalizerFamily (integerTorsionEmbedding emb n).range A = normalizerFamily emb.range A := by
  obtain ⟨n, hn, hdet⟩ := exists_finiteDegreeDetectsNormalizer emb e hI hIfg
  refine ⟨n, hn, fun A => le_antisymm ?_ (normalizerFamily_le_integerTorsion emb n A)⟩
  intro g hg
  apply (hdet A g).mpr
  have h := (mem_normalizerFamily_iff_universalEmbedded (integerTorsionEmbedding emb n) g).mp hg
  constructor
  · rw [degreeMap_universalEmbeddedConjugate]
    exact ((integerTorsionEmbedding_mem_iff emb n _ _).mp h.1).1
  · rw [degreeMap_universalEmbeddedConjugate]
    exact ((integerTorsionEmbedding_mem_iff emb n _ _).mp h.2).1

/-- Choose a positive integer whose characteristic torsion embedding has
the same normalizer over every coefficient algebra. -/
def finiteTorsionNormalizerModel [AddGroup.FG M]
    {B : CommAlgCat.{u} R} (e : (F ⋙ forget GrpCat).CorepresentableBy B)
    {I : Ideal B} (hI : IsCutOutBy e emb.range I) (hIfg : I.FG) :
    Σ n : ℕ, {_hn : 0 < n // ∀ A : CommAlgCat.{u} R,
      normalizerFamily (integerTorsionEmbedding emb n).range A = normalizerFamily emb.range A} := by
  let h := exists_integerTorsion_same_normalizer emb e hI hIfg
  exact ⟨h.choose, h.choose_spec.1, h.choose_spec.2⟩

end Langlands.GroupScheme.CharacterAction
