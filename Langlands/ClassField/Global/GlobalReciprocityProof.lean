import Langlands.ClassField.Global.ReciprocityTower
import Langlands.ClassField.Global.CyclicReciprocityProof
import Langlands.ClassField.Global.UnramifiedCyclotomicProof
import Langlands.ClassField.Global.IdeleInvariantDenominator
import Langlands.ClassFieldTheory.Local.RelativeH2InflationProof
import Langlands.Global.Arithmetic.CyclotomicSplitting

/-! # The global reciprocity law

Assuming `H¹(Gal(E/F), C_E) = 0` for all finite Galois extensions of number fields, every class
of `H²(Gal(E/F), Eˣ)` satisfies the reciprocity law `SumOfInvariantsVanishes` (Artin–Tate VII §3,
Theorem 6). The proof reduces to classes killed by a prime power `ℓ ^ a`, splits such a class by a
cyclic cyclotomic extension `K / F` whose local degrees at the support of the class are divisible
by `ℓ ^ a`, and descends it to `H²(Gal(K/F), Kˣ)` by the Hasse principle and inflation–restriction,
where cyclic cyclotomic reciprocity applies.
-/

noncomputable section

namespace Langlands.ClassField.Global

open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped NumberField Langlands.Global.AdelicFunctoriality.FiniteExtension
open Langlands.Global.AdelicFunctoriality Langlands.Global.CompletionPadic
open Langlands.ClassFieldTheory.Local
open CategoryTheory FundamentalClass

universe u

/-- **Reciprocity for cyclic subextensions of cyclotomic extensions**, unconditionally: the
cyclic cyclotomic reciprocity law with the unramified cyclotomic Frobenius data supplied. -/
theorem cyclicCyclotomicReciprocity : CyclicCyclotomicReciprocity.{u} :=
  CyclicReciprocity.cyclicCyclotomicReciprocity_of UnramifiedCyclotomic.unramifiedCyclotomicFrobenius

namespace Reciprocity

section Subgroup

variable (I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p)
  (hI : ∀ (p : ℕ) [Fact p.Prime], (I p).RelativeImages)
  {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  [IsGalois F E]

include hI in
/-- Under the local image laws, the reciprocity law for `x` says exactly that the total idele
invariant of its principal image vanishes for every choice of places (the finiteness of the
support is automatic). -/
theorem sumOfInvariantsVanishes_iff (x : relativeCohomology F E 2) :
    SumOfInvariantsVanishes I x ↔
      ∀ (wf : ∀ v : HeightOneSpectrum (𝓞 F), FinitePlacesAbove E v)
        (wi : ∀ v : InfinitePlace F, InfinitePlacesAbove E v),
        totalIdeleInvariant I hI wf wi (principalIdeleCohomologyMap F E 2 x) = 0 := by
  refine ⟨fun h wf wi => totalIdeleInvariant_principal_eq_zero I hI wf wi x h,
    fun h wf wi => ⟨?_, ?_⟩⟩
  · refine (finite_support_finiteIdeleInvariant I hI wf
      (principalIdeleCohomologyMap F E 2 x)).subset ?_
    intro v hv
    have := (wf v).2
    rw [Function.mem_support] at hv ⊢
    rwa [finiteIdeleInvariant_principal I v (wf v).1 x]
  · rw [← totalIdeleInvariant_principal I hI]
    exact h wf wi

include hI in
theorem sumOfInvariantsVanishes_zero : SumOfInvariantsVanishes I (0 : relativeCohomology F E 2) := by
  rw [sumOfInvariantsVanishes_iff I hI]
  intro wf wi
  rw [map_zero, map_zero]

include hI in
theorem sumOfInvariantsVanishes_add {x y : relativeCohomology F E 2}
    (hx : SumOfInvariantsVanishes I x) (hy : SumOfInvariantsVanishes I y) :
    SumOfInvariantsVanishes I (x + y) := by
  rw [sumOfInvariantsVanishes_iff I hI] at hx hy ⊢
  intro wf wi
  rw [map_add, map_add, hx wf wi, hy wf wi, add_zero]

include hI in
theorem sumOfInvariantsVanishes_zsmul (n : ℤ) {x : relativeCohomology F E 2}
    (hx : SumOfInvariantsVanishes I x) : SumOfInvariantsVanishes I (n • x) := by
  rw [sumOfInvariantsVanishes_iff I hI] at hx ⊢
  intro wf wi
  rw [map_zsmul, map_zsmul, hx wf wi, smul_zero]

variable (F E) in
/-- The classes of `H²(Gal(E/F), Eˣ)` satisfying the reciprocity law `SumOfInvariantsVanishes I`.
Under the local image laws they form a subgroup, because the law says that the additive total
idele invariant of the principal image vanishes. -/
def reciprocitySubgroup : AddSubgroup (relativeCohomology F E 2) where
  carrier := {x | SumOfInvariantsVanishes I x}
  zero_mem' := sumOfInvariantsVanishes_zero I hI
  add_mem' := sumOfInvariantsVanishes_add I hI
  neg_mem' := fun {x} hx => by
    have := sumOfInvariantsVanishes_zsmul I hI (-1) hx
    rwa [neg_one_zsmul] at this

theorem mem_reciprocitySubgroup {x : relativeCohomology F E 2} :
    x ∈ reciprocitySubgroup I hI F E ↔ SumOfInvariantsVanishes I x := Iff.rfl

include hI in
/-- **Reduction to prime-power torsion.** If the reciprocity law holds for every class of
`H²(Gal(E/F), Eˣ)` killed by a prime power, it holds for every class. -/
theorem sumOfInvariantsVanishes_of_primary
    (h : ∀ (ℓ a : ℕ), ℓ.Prime → ∀ x : relativeCohomology F E 2, ℓ ^ a • x = 0 →
      SumOfInvariantsVanishes I x)
    (x : relativeCohomology F E 2) : SumOfInvariantsVanishes I x := by
  have key : ∀ n : ℕ, n ≠ 0 → ∀ x : relativeCohomology F E 2, n • x = 0 →
      SumOfInvariantsVanishes I x := by
    intro n
    induction n using Nat.recOnPrimeCoprime with
    | zero => intro h0; exact absurd rfl h0
    | prime_pow p k hp => intro _ x hx; exact h p k hp x hx
    | coprime a b _ _ hab ha hb =>
      intro hab0 x hx
      obtain ⟨s, t, hst⟩ := Nat.isCoprime_iff_coprime.2 hab
      have hxa : SumOfInvariantsVanishes I (a • x) := by
        refine hb (right_ne_zero_of_mul hab0) _ ?_
        rw [smul_smul, mul_comm, hx]
      have hxb : SumOfInvariantsVanishes I (b • x) := by
        refine ha (left_ne_zero_of_mul hab0) _ ?_
        rw [smul_smul, hx]
      have hx' : x = s • (a • x) + t • (b • x) := by
        rw [← Nat.cast_smul_eq_nsmul ℤ a x, ← Nat.cast_smul_eq_nsmul ℤ b x, smul_smul, smul_smul, ← add_smul, hst,
          one_smul]
      rw [hx', ← mem_reciprocitySubgroup I hI]
      exact (reciprocitySubgroup I hI F E).add_mem
        ((reciprocitySubgroup I hI F E).zsmul_mem hxa s)
        ((reciprocitySubgroup I hI F E).zsmul_mem hxb t)
  refine key (Nat.card (E ≃ₐ[F] E)) Nat.card_pos.ne' x ?_
  exact card_nsmul_H2_eq_zero _ x

end Subgroup

section LocalRestriction

/-- **Local vanishing after restriction.** For a tower `F ⊆ K ⊆ M` of `p`-adic fields with `M / F`
Galois and local invariant maps forming a class formation, a class `t ∈ H²(Gal(M/F), Mˣ)` whose
invariant is killed by `n` restricts to zero in `H²(Gal(M/K), Mˣ)` as soon as `n ∣ [K : F]`: the
restriction multiplies the invariant by `[K : F]`, and invariants are injective. -/
theorem relativeRestriction_eq_zero_of_dvd {p : ℕ} [Fact p.Prime]
    (I : InvariantFamily.{u, u} p) (hI : I.RelativeClassFormation) (F : PadicField.{u} p)
    (K M : Type u) [Field K] [Field M] [Algebra F.Carrier K] [Algebra K M] [Algebra F.Carrier M]
    [IsScalarTower F.Carrier K M] [FiniteDimensional F.Carrier K] [FiniteDimensional F.Carrier M]
    [FiniteDimensional K M] [IsGalois F.Carrier M] [IsGalois K M] {n : ℕ}
    (t : relativeCohomology F.Carrier M 2) (ht : n • I.relative F M t = 0)
    (hn : n ∣ Module.finrank F.Carrier K) :
    (relativeRestriction F.Carrier K M 2).hom t = 0 := by
  let : Algebra (Padic p) K :=
    ((algebraMap F.Carrier K).comp (algebraMap (Padic p) F.Carrier)).toAlgebra
  have : IsScalarTower (Padic p) F.Carrier K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : FiniteDimensional (Padic p) K := Module.Finite.trans F.Carrier K
  have h := hI.2.2.2 F ⟨K⟩ M t
  apply (hI.2.1 ⟨K⟩ M).1
  rw [map_zero]
  refine h.trans ?_
  change Module.finrank F.Carrier K • I.relative F M t = 0
  obtain ⟨c, hc⟩ := hn
  rw [hc, mul_comm, mul_smul, ht, smul_zero]

end LocalRestriction

section Compositum

variable (F E : Type u) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (m : ℕ) [NeZero m]

/-- If `E / F` is Galois, so is `E(μ_m) / F`: it is the splitting field over `F` of the product
of a polynomial with splitting field `E` and the `m`-th cyclotomic polynomial. -/
theorem isGalois_cyclotomicField [IsGalois F E] : IsGalois F (CyclotomicField m E) := by
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  obtain ⟨p, hp, _⟩ := IsGalois.is_separable_splitting_field F E
  have : Polynomial.IsSplittingField E (CyclotomicField m E)
      ((Polynomial.cyclotomic m F).map (algebraMap F E)) := by
    rw [Polynomial.map_cyclotomic]
    exact IsCyclotomicExtension.splitting_field_cyclotomic m E (CyclotomicField m E)
  have := Polynomial.IsSplittingField.mul (K := E) (CyclotomicField m E) p
    (Polynomial.cyclotomic m F) hp.ne_zero (Polynomial.cyclotomic_ne_zero m F)
  have := Normal.of_isSplittingField (F := F) (E := CyclotomicField m E)
    (p * Polynomial.cyclotomic m F)
  exact IsGalois.mk

/-- `F(μ_m)` embeds over `F` into `E(μ_m)`. -/
theorem nonempty_algHom_cyclotomicField :
    Nonempty (CyclotomicField m F →ₐ[F] CyclotomicField m E) := by
  have := IsCyclotomicExtension.splitting_field_cyclotomic m F (CyclotomicField m F)
  refine ⟨Polynomial.IsSplittingField.lift (CyclotomicField m F) (Polynomial.cyclotomic m F) ?_⟩
  rw [IsScalarTower.algebraMap_eq F E (CyclotomicField m E), ← Polynomial.map_map,
    Polynomial.map_cyclotomic]
  have := IsCyclotomicExtension.splitting_field_cyclotomic m E (CyclotomicField m E)
  exact Polynomial.IsSplittingField.splits (CyclotomicField m E) (Polynomial.cyclotomic m E)

end Compositum

section Main

/-- **Reciprocity for prime-power torsion.** Assume `H¹(Gal(E/F), C_E) = 0` for all finite
Galois extensions of number fields. For local invariant maps forming a class formation with the
arithmetic normalization, every class `x ∈ H²(Gal(E/F), Eˣ)` with `ℓ ^ a • x = 0` satisfies the
reciprocity law. A cyclic cyclotomic `K / F` whose local degrees at the finite support `S` of `x`
are divisible by `ℓ ^ a` and whose infinite places are complex kills the restriction of the
inflation `y` of `x` to `E(μ_m)` locally everywhere, so by the Hasse principle `y` is inflated
from `H²(Gal(K/F), Kˣ)`, where cyclic cyclotomic reciprocity applies. -/
theorem sumOfInvariantsVanishes_of_pow_nsmul_eq_zero (hH1 : IdeleClassH1Vanishing.{u})
    (I : ∀ (p : ℕ) [Fact p.Prime], InvariantFamily.{u, u} p)
    (hI : ∀ (p : ℕ) [Fact p.Prime],
      (I p).RelativeClassFormation ∧ (I p).ArithmeticNormalization)
    {F E : Type u} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [IsGalois F E] (ℓ a : ℕ) [Fact ℓ.Prime] (x : relativeCohomology F E 2)
    (hx : ℓ ^ a • x = 0) : SumOfInvariantsVanishes I x := by
  have hRI : ∀ (p : ℕ) [Fact p.Prime], (I p).RelativeImages := fun p _ => (hI p).1.2.1
  have hIC : ∀ (p : ℕ) [Fact p.Prime], (I p).InflationCompatibility :=
    fun p _ => (hI p).1.2.2.1
  have hS := finite_ideleLocalSupport I hRI ((principalIdeleCohomologyMap F E 2).hom x)
  obtain ⟨K, _, _, _, hKgal, hKcyc, ⟨m, hm, ⟨φ⟩⟩, hKloc, hKinf⟩ :=
    Langlands.Global.CyclotomicSplitting.exists_cyclic_splitting F ℓ a hS.toFinset
  have : NeZero m := ⟨hm.ne'⟩
  have : IsGalois F (CyclotomicField m E) := isGalois_cyclotomicField F E m
  obtain ⟨ι⟩ := nonempty_algHom_cyclotomicField F E m
  let ψ : K →ₐ[F] CyclotomicField m E := ι.comp φ
  let : Algebra K (CyclotomicField m E) := ψ.toRingHom.toAlgebra
  have : IsScalarTower F K (CyclotomicField m E) :=
    IsScalarTower.of_algebraMap_eq fun c => (ψ.commutes c).symm
  have : IsGalois K (CyclotomicField m E) :=
    IsGalois.tower_top_of_isGalois F K (CyclotomicField m E)
  have : FiniteDimensional F K := Module.Finite.of_restrictScalars_finite ℚ F K
  have : FiniteDimensional F (CyclotomicField m E) :=
    Module.Finite.of_restrictScalars_finite ℚ F (CyclotomicField m E)
  set y := (relativeInflation F E (CyclotomicField m E) 2).hom x with hy
  have hz : (relativeRestriction F K (CyclotomicField m E) 2).hom y = 0 := by
    refine eq_zero_of_local_eq_zero hH1 I hRI _ ?_ fun u' =>
      CyclicReciprocity.archimedeanInvariant_eq_zero_of_isComplex u' (hKinf _) _
    intro w' u _
    have : u.asIdeal.LiesOver (placeBelow F w').asIdeal :=
      Ideal.LiesOver.trans u.asIdeal w'.asIdeal (placeBelow F w').asIdeal
    have : (placeBelow E u).asIdeal.LiesOver (placeBelow F w').asIdeal :=
      Ideal.LiesOver.tower_bot u.asIdeal (placeBelow E u).asIdeal (placeBelow F w').asIdeal
    rw [unitsLocalMap_relativeRestriction (placeBelow F w') w' u y]
    by_cases hv : placeBelow F w' ∈ hS.toFinset
    · have := isGalois_adicCompletion (placeBelow F w') u
      have := isGalois_adicCompletion w' u
      have := FiniteExtension.local_finite (placeBelow F w') w'
      have := FiniteExtension.local_finite (placeBelow F w') u
      have := FiniteExtension.local_finite w' u
      refine relativeRestriction_eq_zero_of_dvd (I (residuePrime (placeBelow F w')))
        (hI _).1 (padicField (placeBelow F w')) _ _ (n := ℓ ^ a) _ ?_
        (hKloc _ hv w')
      change ℓ ^ a • finiteLocalInvariant (placeBelow F w') u I y = 0
      rw [hy, finiteLocalInvariant_relativeInflation (placeBelow F w') (placeBelow E u) u I hIC x,
        ← map_nsmul, hx, map_zero]
    · have hs : (unitsLocalMap (placeBelow F w') (placeBelow E u) 2).hom x = 0 := by
        by_contra hne
        apply hv
        rw [Set.Finite.mem_toFinset]
        refine ⟨placeBelow E u, inferInstance, fun h0 => hne ?_⟩
        rw [← principalIdeleCohomologyMap_comp_ideleLocalMap]
        exact h0
      rw [hy, unitsLocalMap_relativeInflation (placeBelow F w') (placeBelow E u) u x, hs,
        map_zero, map_zero]
  obtain ⟨c, hc⟩ : y ∈ LinearMap.range (relativeInflation F K (CyclotomicField m E) 2).hom := by
    rw [(finiteRelativeH2InflationExactness F K (CyclotomicField m E)).2]
    exact hz
  rw [← sumOfInvariantsVanishes_relativeInflation_iff (L := CyclotomicField m E) I hIC x, ← hy,
    ← hc, sumOfInvariantsVanishes_relativeInflation_iff I hIC c]
  exact cyclicCyclotomicReciprocity I hI F K hKcyc ⟨m, hm, ⟨φ⟩⟩ c

end Main

end Reciprocity

open Reciprocity in
/-- **The global reciprocity law from `H¹(C_E) = 0`** (Artin–Tate VII §3, Theorem 6): if the
first cohomology of the idele class group vanishes in every finite Galois extension of number
fields, then `GlobalReciprocity` holds. Every class of `H²(Gal(E/F), Eˣ)` is a sum of classes
killed by prime powers, and these satisfy the reciprocity law by
`sumOfInvariantsVanishes_of_pow_nsmul_eq_zero`. -/
theorem globalReciprocity_of (hH1 : IdeleClassH1Vanishing.{u}) : GlobalReciprocity.{u} := by
  intro I hI F _ _ E _ _ _ _ x
  have hRI : ∀ (p : ℕ) [Fact p.Prime], (I p).RelativeImages := fun p _ => (hI p).1.2.1
  refine sumOfInvariantsVanishes_of_primary I hRI (fun ℓ a hℓ y hy => ?_) x
  have := Fact.mk hℓ
  exact sumOfInvariantsVanishes_of_pow_nsmul_eq_zero hH1 I hI ℓ a y hy

end Langlands.ClassField.Global
