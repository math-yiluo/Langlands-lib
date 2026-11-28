import Langlands.GroupScheme.Rational.NumberFieldTypeE7HasseInputs
import Langlands.GroupScheme.Rational.NumberFieldTotallyComplexTypeE7Inputs
import Langlands.GroupScheme.Rational.NumberFieldTorusCyclotomicSplitting
import Langlands.GroupScheme.GaloisCocycleInflationRestriction
import Langlands.GroupScheme.Rational.QuasiSplitCocycleTorusReductionProof
import Langlands.GroupScheme.Rational.SteinbergAssembly
import Langlands.GroupScheme.Rational.MaximalTorusFiniteType
import Langlands.GroupScheme.Rational.QuasiSplitInnerFormBaseChange
import Langlands.GroupScheme.Rational.QuasiSplitSplittingReduction
import Langlands.GroupScheme.Reductive.TitsIndexSeparableScalarExtension
import Langlands.GroupScheme.Reductive.GeometricSimplyConnected
import Langlands.GroupScheme.Reductive.AlgebraicExtensionAscent
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! # Reduction of `H¹ = 1` for quasi-split `E_7` over totally complex fields

This module states and proves that `NumberFieldTotallyComplexTypeE7Statement` follows from
three inputs: the order bound for maximal-torus cocycles
(`TypeE7MaximalTorusCocycleOrderStatement`), the cyclotomic splitting of torsion torus
cocycles over number fields (`NumberFieldTorusCocycleCyclotomicSplittingStatement`), and the
vanishing on Galois covers of degree `2` and `3`
(`NumberFieldTotallyComplexTypeE7CyclicStatement`).
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry IntermediateField
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- `NumberFieldTotallyComplexTypeE7Statement` follows from the maximal-torus order bound in
type `E_7`, the cyclotomic splitting of torsion torus cocycles over number fields, and the
vanishing of cocycles of quasi-split simply connected groups of type `E_7` on Galois covers of
degree `2` and `3` over totally complex number fields. -/
def NumberFieldTotallyComplexTypeE7ReductionStatement : Prop :=
  TypeE7MaximalTorusCocycleOrderStatement.{u} →
    NumberFieldTorusCocycleCyclotomicSplittingStatement.{u} →
      NumberFieldTotallyComplexTypeE7CyclicStatement.{u} →
        NumberFieldTotallyComplexTypeE7Statement.{u}

section TypeE7

variable {K : Type u} [Field K] {G : GroupScheme (Spec (CommRingCat.of K))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]

private instance typeE7BaseChangeAffine (E : Type u) [Field E] [Algebra K E] :
    IsAffineHom ((GroupScheme.baseChange (algebraBaseMap K E)).obj G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom _)
  infer_instance

private instance typeE7BaseChangeFiniteType (E : Type u) [Field E] [Algebra K E] :
    LocallyOfFiniteType ((GroupScheme.baseChange (algebraBaseMap K E)).obj G).X.hom := by
  change LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd G.X.hom _)
  infer_instance

/-- The cyclic input applies to the base change of the group to every finite intermediate
field `F` of the separable closure: the Tits index data and its `E_7` numbering are carried to
`G_F`, and simple connectedness, absolute almost-simplicity and quasi-splitness persist. -/
theorem typeE7Cyclic_intermediateField
    (h3 : NumberFieldTotallyComplexTypeE7CyclicStatement.{u})
    [NumberField K] [NumberField.IsTotallyComplex K]
    (d : TitsIndexData G) (e : d.Vertex ≃ Fin 7) (hsc : IsSimplyConnected G)
    (habs : IsAbsolutelyAlmostSimple G) (hE7 : ∀ a b, d.cartan a b = CartanMatrix.E 7 (e a) (e b))
    (hqs : IsQuasiSplit G) (F : IntermediateField K (SeparableClosure K)) [FiniteDimensional K F]
    (F₁ : Type u) [Field F₁] [Algebra F F₁] [FiniteDimensional F F₁] [IsGalois F F₁]
    (hdeg : Module.finrank F F₁ = 2 ∨ Module.finrank F F₁ = 3)
    (ζ : Cocycle ((GroupScheme.baseChange (algebraBaseMap K F)).obj G)
      (GaloisCocycle.cover F F₁)) : ζ.IsTrivial := by
  have : NumberField F := NumberField.of_module_finite K F
  have : NumberField.IsTotallyComplex F := NumberField.isTotallyComplex_of_algebra K F
  have : Algebra.IsSeparable F (SeparableClosure K) :=
    Algebra.isSeparable_tower_top_of_isSeparable K F (SeparableClosure K)
  have : IsSepClosure F (SeparableClosure K) := ⟨inferInstance, inferInstance⟩
  let : Algebra F (SeparableClosure F) := (separableClosure F (AlgebraicClosure F)).algebra
  let c : SeparableClosure F ≃ₐ[F] SeparableClosure K :=
    IsSepClosure.equiv F (SeparableClosure F) (SeparableClosure K)
  let X := d.separableScalarExtension F c
  let GF := (GroupScheme.baseChange (algebraBaseMap K F)).obj G
  have hscF : IsSimplyConnected GF := (isSimplyConnected_fieldExtension_iff G).mpr hsc
  have habsF : IsAbsolutelyAlmostSimple GF :=
    IsAbsolutelyAlmostSimple.baseChange_of_algebraicExtension habs
  have hE7F : ∀ a b, X.index.cartan a b =
      CartanMatrix.E 7 ((X.vertices.symm.trans e) a) ((X.vertices.symm.trans e) b) := by
    intro a b
    have h := X.cartan_eq (X.vertices.symm a) (X.vertices.symm b)
    simp only [Equiv.apply_symm_apply] at h
    rw [h, hE7]
    rfl
  exact h3 F GF X.index (X.vertices.symm.trans e) hscF habsF hE7F
    hqs.baseChange_of_algebraicExtension F₁ hdeg ζ

end TypeE7

section Descent

variable {K : Type u} [Field K] {G : GroupScheme (Spec (CommRingCat.of K))}

/-- The Galois values of a cocycle `ν` on `Spec M → Spec K` form the coboundary of one point
on the automorphisms of `M/K` that fix the intermediate field `F` of the separable closure
pointwise. -/
private def FixedCoboundary (M : IntermediateField K (SeparableClosure K))
    (ν : Cocycle G (GaloisCocycle.cover K M)) (F : IntermediateField K (SeparableClosure K)) :
    Prop :=
  ∃ f : G.affinePoints (CommAlgCat.of K M), ∀ σ : M ≃ₐ[K] M,
    (∀ x : M, (x : SeparableClosure K) ∈ F → σ x = x) →
      GaloisCocycle.value ν σ = f * (GaloisPoint.conjugate K M G σ f)⁻¹

private theorem fixedCoboundary_of_relative (M : IntermediateField K (SeparableClosure K))
    (ν : Cocycle G (GaloisCocycle.cover K M)) (F : IntermediateField K (SeparableClosure K))
    [Algebra F M] [IsScalarTower K F M]
    (hFM : ∀ x : F, ((algebraMap F M x : M) : SeparableClosure K) = x)
    (f : G.affinePoints (CommAlgCat.of K M))
    (hf : ∀ τ : M ≃ₐ[F] M, GaloisCocycle.value ν (τ.restrictScalars K) =
      f * (GaloisPoint.conjugate K M G (τ.restrictScalars K) f)⁻¹) :
    FixedCoboundary M ν F := by
  refine ⟨f, fun σ hσ => ?_⟩
  let τ : M ≃ₐ[F] M := AlgEquiv.ofRingEquiv (f := σ.toRingEquiv) (fun c =>
    hσ (algebraMap F M c) (by rw [hFM]; exact c.2))
  have hτ : τ.restrictScalars K = σ := AlgEquiv.ext fun _ => rfl
  rw [← hτ]
  exact hf τ

private theorem relative_of_fixedCoboundary (M : IntermediateField K (SeparableClosure K))
    (ν : Cocycle G (GaloisCocycle.cover K M)) (F : IntermediateField K (SeparableClosure K))
    [Algebra F M] [IsScalarTower K F M]
    (hFM : ∀ x : F, ((algebraMap F M x : M) : SeparableClosure K) = x)
    (h : FixedCoboundary M ν F) :
    ∃ f : G.affinePoints (CommAlgCat.of K M), ∀ τ : M ≃ₐ[F] M,
      GaloisCocycle.value ν (τ.restrictScalars K) =
        f * (GaloisPoint.conjugate K M G (τ.restrictScalars K) f)⁻¹ := by
  obtain ⟨f, hf⟩ := h
  refine ⟨f, fun τ => hf _ fun x hx => ?_⟩
  have hx' : x = algebraMap F M ⟨x, hx⟩ := Subtype.ext (hFM ⟨x, hx⟩).symm
  rw [hx']
  exact τ.commutes _

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- One step of the cyclotomic descent: if `β ^ q = α` with `q = 2` or `q = 3` and `K⟮β⟯` is
Galois over `K`, a coboundary on the automorphisms fixing `K⟮β⟯` gives one on the
automorphisms fixing `K⟮α⟯`, provided the base change of `G` to `K⟮α⟯` has trivial cocycles
on Galois covers of degree `2` and `3`. -/
private theorem fixedCoboundary_adjoin_pow [IsAffineHom G.X.hom]
    (hcyc : ∀ (F : IntermediateField K (SeparableClosure K)) [FiniteDimensional K F]
      (F₁ : Type u) [Field F₁] [Algebra F F₁] [FiniteDimensional F F₁] [IsGalois F F₁],
      (Module.finrank F F₁ = 2 ∨ Module.finrank F F₁ = 3) →
      ∀ ζ : Cocycle ((GroupScheme.baseChange (algebraBaseMap K F)).obj G)
        (GaloisCocycle.cover F F₁), ζ.IsTrivial)
    (M : IntermediateField K (SeparableClosure K)) [FiniteDimensional K M] [IsGalois K M]
    (M₀ : Type u) [Field M₀] [Algebra K M₀] [Algebra M₀ M] [IsScalarTower K M₀ M] [Normal K M₀]
    (ξ : Cocycle G (GaloisCocycle.cover K M₀))
    {α β : SeparableClosure K} {q : ℕ} (hq : q = 2 ∨ q = 3) (hβq : β ^ q = α) (hβM : β ∈ M)
    [IsGalois K K⟮β⟯]
    (h : FixedCoboundary M (ξ.refine (GaloisCocycle.coverMap K M₀ M)) K⟮β⟯) :
    FixedCoboundary M (ξ.refine (GaloisCocycle.coverMap K M₀ M)) K⟮α⟯ := by
  have hβ : IsIntegral K β := Algebra.IsIntegral.isIntegral β
  have hα : IsIntegral K α := Algebra.IsIntegral.isIntegral α
  have hαβ : K⟮α⟯ ≤ K⟮β⟯ :=
    adjoin_simple_le_iff.mpr (hβq ▸ pow_mem (mem_adjoin_simple_self K β) q)
  have hβM' : K⟮β⟯ ≤ M := adjoin_simple_le_iff.mpr hβM
  let : Algebra K⟮α⟯ K⟮β⟯ := (IntermediateField.inclusion hαβ).toAlgebra
  let : Algebra K⟮β⟯ M := (IntermediateField.inclusion hβM').toAlgebra
  let : Algebra K⟮α⟯ M := (IntermediateField.inclusion (hαβ.trans hβM')).toAlgebra
  have : IsScalarTower K K⟮α⟯ K⟮β⟯ := .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower K K⟮β⟯ M := .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower K K⟮α⟯ M := .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower K⟮α⟯ K⟮β⟯ M := .of_algebraMap_eq fun _ => rfl
  have : FiniteDimensional K K⟮β⟯ := adjoin.finiteDimensional hβ
  have : FiniteDimensional K K⟮α⟯ := adjoin.finiteDimensional hα
  have : FiniteDimensional K⟮α⟯ K⟮β⟯ := Module.Finite.of_restrictScalars_finite K _ _
  have : IsGalois K⟮α⟯ K⟮β⟯ := IsGalois.tower_top_of_isGalois K K⟮α⟯ K⟮β⟯
  -- The degree of `K⟮β⟯` over `K⟮α⟯` is at most `q`.
  have hdeg : Module.finrank K⟮α⟯ K⟮β⟯ ≤ q := by
    let b : K⟮β⟯ := AdjoinSimple.gen K β
    let a : K⟮α⟯ := AdjoinSimple.gen K α
    have htop : K⟮α⟯⟮b⟯ = ⊤ := by
      rw [← restrictScalars_eq_top_iff (K := K), eq_top_iff]
      have hle : K⟮β⟯ ≤ (K⟮α⟯⟮b⟯.restrictScalars K).map K⟮β⟯.val :=
        adjoin_simple_le_iff.mpr ⟨b, mem_adjoin_simple_self _ b, rfl⟩
      intro x _
      obtain ⟨y, hy, hyx⟩ := hle x.2
      rwa [show y = x from Subtype.ext hyx] at hy
    have hb : IsIntegral K⟮α⟯ b := Algebra.IsIntegral.isIntegral b
    have hdvd : minpoly K⟮α⟯ b ∣ Polynomial.X ^ q - Polynomial.C a := by
      apply minpoly.dvd
      rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
      apply Subtype.ext
      change (b : SeparableClosure K) ^ q - (a : SeparableClosure K) = 0
      rw [AdjoinSimple.coe_gen, AdjoinSimple.coe_gen, hβq, sub_self]
    have hq0 : 0 < q := by omega
    calc Module.finrank K⟮α⟯ K⟮β⟯ = Module.finrank K⟮α⟯ K⟮α⟯⟮b⟯ := by rw [htop, finrank_top']
      _ = (minpoly K⟮α⟯ b).natDegree := adjoin.finrank hb
      _ ≤ (Polynomial.X ^ q - Polynomial.C a).natDegree :=
          Polynomial.natDegree_le_of_dvd hdvd (Polynomial.X_pow_sub_C_ne_zero hq0 a)
      _ = q := Polynomial.natDegree_X_pow_sub_C
  have hpos : 0 < Module.finrank K⟮α⟯ K⟮β⟯ := Module.finrank_pos
  rcases (show Module.finrank K⟮α⟯ K⟮β⟯ = 1 ∨
      (Module.finrank K⟮α⟯ K⟮β⟯ = 2 ∨ Module.finrank K⟮α⟯ K⟮β⟯ = 3) by omega) with h1 | h23
  · have : Module.Free K K⟮α⟯ := Module.Free.of_divisionRing _ _
    have : Module.Free K⟮α⟯ K⟮β⟯ := Module.Free.of_divisionRing _ _
    have hmul := Module.finrank_mul_finrank K K⟮α⟯ K⟮β⟯
    rw [h1, mul_one] at hmul
    rw [IntermediateField.eq_of_le_of_finrank_eq hαβ hmul]
    exact h
  · obtain ⟨f, hf⟩ := relative_of_fixedCoboundary M _ K⟮β⟯ (fun _ => rfl) h
    obtain ⟨f', hf'⟩ :=
      GaloisCocycle.exists_value_refine_of_restrict ξ (hcyc K⟮α⟯ K⟮β⟯ h23) f hf
    exact fixedCoboundary_of_relative M _ K⟮α⟯ (fun _ => rfl) f' hf'

/-- The descent along the cyclotomic tower: for `t ∣ N`, the coboundary property on the
automorphisms fixing `K⟮ζ⟯` passes to the automorphisms fixing `K⟮ζ ^ t⟯`, one prime factor
`2` or `3` of `t` at a time. -/
private theorem fixedCoboundary_pow_of_dvd [CharZero K] [IsAffineHom G.X.hom]
    (hcyc : ∀ (F : IntermediateField K (SeparableClosure K)) [FiniteDimensional K F]
      (F₁ : Type u) [Field F₁] [Algebra F F₁] [FiniteDimensional F F₁] [IsGalois F F₁],
      (Module.finrank F F₁ = 2 ∨ Module.finrank F F₁ = 3) →
      ∀ ζ : Cocycle ((GroupScheme.baseChange (algebraBaseMap K F)).obj G)
        (GaloisCocycle.cover F F₁), ζ.IsTrivial)
    (M : IntermediateField K (SeparableClosure K)) [FiniteDimensional K M] [IsGalois K M]
    (M₀ : Type u) [Field M₀] [Algebra K M₀] [Algebra M₀ M] [IsScalarTower K M₀ M] [Normal K M₀]
    (ξ : Cocycle G (GaloisCocycle.cover K M₀))
    {N : ℕ} (hN : 0 < N) (hN23 : ∀ q : ℕ, q.Prime → q ∣ N → q = 2 ∨ q = 3)
    {ζ : SeparableClosure K} (hζ : IsPrimitiveRoot ζ N) (hζM : ζ ∈ M)
    (htop : FixedCoboundary M (ξ.refine (GaloisCocycle.coverMap K M₀ M)) K⟮ζ⟯) :
    ∀ t : ℕ, t ∣ N → FixedCoboundary M (ξ.refine (GaloisCocycle.coverMap K M₀ M)) K⟮ζ ^ t⟯ := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro ht
    by_cases h1 : t = 1
    · subst h1
      simpa only [pow_one] using htop
    obtain ⟨q, hq, t', rfl⟩ := Nat.exists_prime_and_dvd h1
    have ht0 : 0 < t' := by
      rcases Nat.eq_zero_or_pos t' with h | h
      · subst h
        rw [mul_zero, zero_dvd_iff] at ht
        omega
      · exact h
    have ht' : t' ∣ N := dvd_trans (dvd_mul_left t' q) ht
    have hlt : t' < q * t' := lt_mul_left ht0 hq.one_lt
    have hq23 : q = 2 ∨ q = 3 := hN23 q hq (dvd_trans (dvd_mul_right q t') ht)
    have hprim : IsPrimitiveRoot (ζ ^ t') (N / t') := hζ.pow hN (Nat.mul_div_cancel' ht').symm
    have : NeZero (N / t') := ⟨(Nat.div_pos (Nat.le_of_dvd hN ht') ht0).ne'⟩
    have : IsCyclotomicExtension {N / t'} K K⟮ζ ^ t'⟯ :=
      hprim.intermediateField_adjoin_isCyclotomicExtension K
    have : IsGalois K K⟮ζ ^ t'⟯ := IsCyclotomicExtension.isGalois {N / t'} K _
    have hpow : (ζ ^ t') ^ q = ζ ^ (q * t') := by rw [← pow_mul, mul_comm]
    exact fixedCoboundary_adjoin_pow hcyc M M₀ ξ hq23 hpow (pow_mem hζM t') (ih t' hlt ht')

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in
/-- **Cyclotomic descent in type `E_7`.** Let `G` be a quasi-split simply connected
absolutely almost-simple group of type `E_7` over a totally complex number field `K`, and let
`ζ` be a primitive `N`-th root of unity in the separable closure, where every prime factor of
`N` is `2` or `3`. A cocycle of `G` on a finite Galois field cover that becomes trivial over
`K⟮ζ⟯` is trivial, provided cocycles on Galois covers of degree `2` and `3` vanish over every
totally complex number field. -/
theorem typeE7_cyclotomicDescent (h3 : NumberFieldTotallyComplexTypeE7CyclicStatement.{u})
    [NumberField K] [NumberField.IsTotallyComplex K]
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (d : TitsIndexData G) (e : d.Vertex ≃ Fin 7) (hsc : IsSimplyConnected G)
    (habs : IsAbsolutelyAlmostSimple G) (hE7 : ∀ a b, d.cartan a b = CartanMatrix.E 7 (e a) (e b))
    (hqs : IsQuasiSplit G) {N : ℕ} (hN : 0 < N)
    (hN23 : ∀ q : ℕ, q.Prime → q ∣ N → q = 2 ∨ q = 3)
    {ζ : SeparableClosure K} (hζ : IsPrimitiveRoot ζ N)
    (M₀ : Type u) [Field M₀] [Algebra K M₀] [FiniteDimensional K M₀] [IsGalois K M₀]
    (ξ : Cocycle G (GaloisCocycle.cover K M₀))
    (h : (ξ.baseChangePullback (algebraBaseMap K K⟮ζ⟯)).IsTrivial) : ξ.IsTrivial := by
  -- A finite Galois extension `M` of `K` inside the separable closure containing `K⟮ζ⟯` and a
  -- copy of `M₀`.
  let emb : M₀ →ₐ[K] SeparableClosure K := IsSepClosed.lift
  let φ : M₀ ≃ₐ[K] emb.fieldRange := AlgEquiv.ofInjectiveField emb
  have : IsGalois K emb.fieldRange := (AlgEquiv.transfer_galois φ).mp inferInstance
  have : FiniteDimensional K emb.fieldRange := LinearEquiv.finiteDimensional φ.toLinearEquiv
  have : NeZero N := ⟨hN.ne'⟩
  have : IsCyclotomicExtension {N} K K⟮ζ⟯ := hζ.intermediateField_adjoin_isCyclotomicExtension K
  have : IsGalois K K⟮ζ⟯ := IsCyclotomicExtension.isGalois {N} K _
  have : FiniteDimensional K K⟮ζ⟯ := adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral ζ)
  let M : IntermediateField K (SeparableClosure K) := emb.fieldRange ⊔ K⟮ζ⟯
  have : IsGalois K M := inferInstance
  have : FiniteDimensional K M := inferInstance
  let j : M₀ →ₐ[K] M := (IntermediateField.inclusion le_sup_left).comp φ.toAlgHom
  let : Algebra M₀ M := j.toAlgebra
  have : IsScalarTower K M₀ M := .of_algebraMap_eq fun x => (j.commutes x).symm
  -- The top of the tower.
  have hEM : K⟮ζ⟯ ≤ M := le_sup_right
  let : Algebra K⟮ζ⟯ M := (IntermediateField.inclusion hEM).toAlgebra
  have : IsScalarTower K K⟮ζ⟯ M := .of_algebraMap_eq fun _ => rfl
  have : FiniteDimensional K⟮ζ⟯ M := Module.Finite.of_restrictScalars_finite K _ _
  have : IsGalois K⟮ζ⟯ M := IsGalois.tower_top_of_isGalois K K⟮ζ⟯ M
  obtain ⟨f, hf⟩ :=
    GaloisCocycle.exists_value_refine_of_baseChangePullback_isTrivial (F := K⟮ζ⟯) (M := M) ξ h
  have htop := fixedCoboundary_of_relative M _ K⟮ζ⟯ (fun _ => rfl) f hf
  -- Descend to the bottom `K⟮ζ ^ N⟯ = ⊥`.
  have hbot := fixedCoboundary_pow_of_dvd
    (fun F _ F₁ _ _ _ _ hdeg ζ' => typeE7Cyclic_intermediateField h3 d e hsc habs hE7 hqs F F₁
      hdeg ζ') M M₀ ξ hN hN23 hζ (hEM (mem_adjoin_simple_self K ζ)) htop N dvd_rfl
  have hN1 : K⟮ζ ^ N⟯ = ⊥ := by
    rw [adjoin_simple_eq_bot_iff, hζ.pow_eq_one]
    exact one_mem _
  rw [hN1] at hbot
  obtain ⟨f, hf⟩ := hbot
  refine GaloisCocycle.isTrivial_of_forall_value_refine ξ f fun σ => hf σ fun x hx => ?_
  obtain ⟨c, hc⟩ := mem_bot.mp hx
  rw [show x = algebraMap K M c from Subtype.ext hc.symm, σ.commutes]

end Descent

/-- **The reduction.** Every cocycle `ξ` of a quasi-split simply connected group `G` of type
`E_7` over a totally complex number field `K` on a finite Galois cover `Spec L → Spec K` is
trivial, given the three inputs. Steinberg's torus reduction (`quasiSplitCocycleTorusReduction`)
replaces `ξ`, after a finite Galois refinement `Spec M₀ → Spec L` and a twist, by the image of a
cocycle of a closed torus, and that torus lies in a maximal torus `T'`. The torus cocycle `τ`
in `T'` has a trivial `2^a 3^b`-th power, so it becomes trivial over `K⟮ζ⟯` for a primitive
`N`-th root of unity `ζ` with `N` divisible only by `2` and `3`. The cyclotomic descent
`typeE7_cyclotomicDescent` then shows that the image of `τ` in `G` is trivial, hence so is
`ξ`. -/
theorem numberFieldTotallyComplexTypeE7_of_inputs :
    NumberFieldTotallyComplexTypeE7ReductionStatement.{u} := by
  intro h1 h2 h3 K _ _ _ G _ _ d e hsc habs hE7 hqs L _ _ _ _ ξ
  obtain ⟨R⟩ := quasiSplitCocycleTorusReduction K G hsc.isSemisimple hqs L ξ
  let : Field R.carrier := R.field
  let : Algebra K R.carrier := R.algebra
  have : FiniteDimensional K R.carrier := R.finiteDimensional
  have : IsGalois K R.carrier := R.isGalois
  let T : CommGroupScheme (Spec (CommRingCat.of K)) :=
    { R.torus with comm := R.isTorus.isCommMonObj }
  let i : T.toGrp ⟶ G := R.inclusion
  obtain ⟨T', j, hj, f, hf⟩ :=
    exists_maximalTorus_extension_of_finiteType G i R.isTorus R.isClosedSubgroup
  let τ₀ : Cocycle T.toGrp (GaloisCocycle.cover K R.carrier) := R.torusCocycle
  let τ : Cocycle T'.toGrp (GaloisCocycle.cover K R.carrier) := τ₀.map f
  obtain ⟨a, b, hab⟩ := h1 K G d e hsc habs hE7 T' j hj R.carrier τ
  obtain ⟨N, hN, hNp, hsplit⟩ := h2 K T' hj.1 R.carrier τ (2 ^ a * 3 ^ b) (by positivity) hab
  have hN23 : ∀ q : ℕ, q.Prime → q ∣ N → q = 2 ∨ q = 3 := by
    intro q hq hqN
    rcases (Nat.Prime.dvd_mul hq).mp (hNp q hq hqN) with h | h
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h))
    · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp (hq.dvd_of_dvd_pow h))
  have : NeZero (N : K) := ⟨Nat.cast_ne_zero.mpr hN.ne'⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_isPrimitiveRoot (SeparableClosure K) N
  have hτ : (τ.baseChangePullback (algebraBaseMap K K⟮ζ⟯)).IsTrivial :=
    hsplit K⟮ζ⟯ (AdjoinSimple.gen K ζ) (IsPrimitiveRoot.coe_submonoidClass_iff.mp hζ)
  have hτG : (τ.map j).IsTrivial := typeE7_cyclotomicDescent h3 d e hsc habs hE7 hqs hN hN23 hζ
    R.carrier (τ.map j) (Cocycle.isTrivial_baseChangePullback_map τ j _ hτ)
  let : IsClosedImmersion R.inclusion.hom.hom.left := R.isClosedSubgroup
  let : Mono R.inclusion.hom.hom := Over.mono_of_mono_left _
  have hfj : f.hom.hom ≫ j.hom.hom = R.inclusion.hom.hom := congrArg (fun z => z.hom.hom) hf
  have hl : ((ξ.refine R.refinement).twist R.cochain).IsTrivial := by
    refine Cocycle.IsTrivial.congr (fun a b => ?_) hτG
    change (R.torusCocycle.toFun a b ≫ f.hom.hom) ≫ j.hom.hom = _
    rw [Category.assoc, hfj]
    exact Cocycle.lift_toFun _ R.inclusion R.factorization a b
  exact (@Cocycle.isTrivial_refine_iff _ _ _ _ ξ R.refinement R.quasiCompact_refinement
    R.flat_refinement R.surjective_refinement).mp hl.of_twist

end Langlands.GroupScheme
