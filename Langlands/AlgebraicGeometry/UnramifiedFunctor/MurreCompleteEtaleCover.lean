import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.Etale.StandardEtale

/-! # A finite étale local cover of a finite unramified local algebra

For Step 2a of Murre's induction (Bourbaki exp. 294): a finite, formally unramified local
algebra `B` over a local ring `R`, with `B` henselian, is a quotient of a finite étale local
`R`-algebra `R[X]/(f)`, where `f` lifts the minimal polynomial of a primitive element of the
residue field extension. -/

universe u

open Polynomial IsLocalRing

noncomputable section

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor

namespace CompleteLocal

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- If `f` is monic and its reduction modulo `m` is irreducible, `R[X]/(f)` is local with
maximal ideal `m · R[X]/(f)`. -/
lemma adjoinRoot_isMaximal {f : R[X]}
    (hirr : Irreducible (f.map (residue R))) :
    (Ideal.map (AdjoinRoot.of f) (maximalIdeal R)).IsMaximal := by
  apply Ideal.Quotient.maximal_of_isField
  let e := AdjoinRoot.quotEquivQuotMap f (maximalIdeal R)
  let : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
  have : (Ideal.span {f.map (Ideal.Quotient.mk (maximalIdeal R))}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible (p := f.map (Ideal.Quotient.mk (maximalIdeal R)))
      hirr
  exact MulEquiv.isField (Ideal.Quotient.field _).toIsField e.toMulEquiv

lemma adjoinRoot_isLocalRing {f : R[X]} (hf : f.Monic)
    (hirr : Irreducible (f.map (residue R))) : IsLocalRing (AdjoinRoot f) := by
  have hM := adjoinRoot_isMaximal hirr
  have : Module.Finite R (AdjoinRoot f) := hf.finite_adjoinRoot
  refine IsLocalRing.of_unique_max_ideal ⟨_, hM, fun M hMmax ↦ ?_⟩
  have hc : (M.comap (algebraMap R (AdjoinRoot f))).IsMaximal := Ideal.IsMaximal.under R M
  have hle : Ideal.map (AdjoinRoot.of f) (maximalIdeal R) ≤ M := by
    rw [Ideal.map_le_iff_le_comap]
    exact le_of_eq (IsLocalRing.eq_maximalIdeal hc).symm
  exact (hM.eq_of_le hMmax.ne_top hle).symm

variable {B : Type u} [CommRing B] [IsLocalRing B] [Algebra R B]
  [IsLocalHom (algebraMap R B)]

omit [IsLocalRing R] in
lemma residue_eval_map [IsLocalRing R] (p : R[X]) (b : B) :
    residue B ((p.map (algebraMap R B)).eval b) =
      (p.map (residue R)).eval₂ (algebraMap (ResidueField R) (ResidueField B)) (residue B b) := by
  rw [Polynomial.eval_map, Polynomial.hom_eval₂, Polynomial.eval₂_map]
  congr 1

variable [Module.Finite R B] [Algebra.FormallyUnramified R B] [HenselianRing B (maximalIdeal B)]

/-- A finite formally unramified local algebra `B` over a local ring `R`, henselian, is a
quotient of a finite étale local `R`-algebra. -/
theorem exists_etaleCover :
    ∃ (L : Type u) (_ : CommRing L) (_ : Algebra R L), IsLocalRing L ∧ Module.Finite R L ∧
      Algebra.Etale R L ∧ ∃ π : L →ₐ[R] B, Function.Surjective π := by
  obtain ⟨θ₀, hθ₀⟩ := Field.exists_primitive_element (ResidueField R) (ResidueField B)
  have hint : IsIntegral (ResidueField R) θ₀ := Algebra.IsIntegral.isIntegral θ₀
  have hsep : (minpoly (ResidueField R) θ₀).Separable :=
    Algebra.IsSeparable.isSeparable (ResidueField R) θ₀
  obtain ⟨f, hfmap, -, hf⟩ := lifts_and_degree_eq_and_monic
    ((Polynomial.mem_lifts _).2 (Polynomial.map_surjective _ residue_surjective _))
    (minpoly.monic hint)
  have hirr : Irreducible (f.map (residue R)) := by rw [hfmap]; exact minpoly.irreducible hint
  have hloc := adjoinRoot_isLocalRing hf hirr
  obtain ⟨a₀, ha₀⟩ := residue_surjective θ₀
  have h1 : (f.map (algebraMap R B)).eval a₀ ∈ maximalIdeal B := by
    rw [← residue_eq_zero_iff, residue_eval_map, hfmap, ha₀, ← Polynomial.aeval_def,
      minpoly.aeval]
  have h2 : IsUnit ((f.map (algebraMap R B)).derivative.eval a₀) := by
    by_contra h
    have hm : (f.map (algebraMap R B)).derivative.eval a₀ ∈ maximalIdeal B :=
      (mem_maximalIdeal _).2 h
    rw [← residue_eq_zero_iff, Polynomial.derivative_map, residue_eval_map,
      ← Polynomial.derivative_map, hfmap, ha₀, ← Polynomial.aeval_def] at hm
    exact hsep.aeval_derivative_ne_zero (minpoly.aeval _ _) hm
  obtain ⟨θ, hθroot, hθa⟩ := HenselianRing.is_henselian (f.map (algebraMap R B)) (hf.map _) a₀ h1
    (h2.map _)
  have hθ : aeval θ f = 0 := by
    rw [Polynomial.aeval_def, ← Polynomial.eval_map]; exact hθroot
  have hθres : residue B θ = θ₀ := by
    rw [← ha₀, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]; exact hθa
  -- `f'` is a unit modulo `f`
  have hM : maximalIdeal (AdjoinRoot f) = Ideal.map (AdjoinRoot.of f) (maximalIdeal R) :=
    (IsLocalRing.eq_maximalIdeal (adjoinRoot_isMaximal hirr)).symm
  have hunit : IsUnit (AdjoinRoot.mk f (derivative f)) := by
    by_contra h
    have hm : AdjoinRoot.mk f (derivative f) ∈ Ideal.map (AdjoinRoot.of f) (maximalIdeal R) := by
      rw [← hM]; exact (mem_maximalIdeal _).2 h
    rw [← Ideal.Quotient.eq_zero_iff_mem] at hm
    have h0 := congrArg (AdjoinRoot.quotEquivQuotMap f (maximalIdeal R)) hm
    rw [AdjoinRoot.quotEquivQuotMap_apply_mk, map_zero, Ideal.Quotient.eq_zero_iff_mem,
      Ideal.mem_span_singleton, ← Polynomial.derivative_map] at h0
    have hirr' : Irreducible (f.map (Ideal.Quotient.mk (maximalIdeal R))) := hirr
    have hsep' : (f.map (Ideal.Quotient.mk (maximalIdeal R))).Separable := by
      change (f.map (residue R)).Separable; rw [hfmap]; exact hsep
    exact hirr'.not_isUnit (hsep'.isUnit_of_dvd' dvd_rfl h0)
  obtain ⟨p₁', hp₁⟩ := hunit.exists_right_inv
  obtain ⟨p₁, rfl⟩ := AdjoinRoot.mk_surjective p₁'
  rw [← map_mul, ← (AdjoinRoot.mk f).map_one, ← sub_eq_zero, ← map_sub,
    AdjoinRoot.mk_eq_zero] at hp₁
  obtain ⟨p₂, hp₂⟩ := hp₁
  let P : StandardEtalePair R :=
    { f := f, monic_f := hf, g := 1,
      cond := ⟨p₁, -p₂, 0, by rw [pow_zero, mul_neg, ← sub_eq_add_neg, ← hp₂]; ring⟩ }
  have hmk1 : (AdjoinRoot.mk P.f P.g) = 1 := map_one _
  let e₂ : Localization.Away (AdjoinRoot.mk P.f P.g) ≃ₐ[R] AdjoinRoot f :=
    ((IsLocalization.atUnits (AdjoinRoot f) (Submonoid.powers (AdjoinRoot.mk P.f P.g))
      (S := Localization.Away (AdjoinRoot.mk P.f P.g)) (by
        rintro _ ⟨n, rfl⟩
        change IsUnit ((AdjoinRoot.mk P.f P.g) ^ n)
        rw [hmk1, one_pow]
        exact isUnit_one)).restrictScalars R).symm
  have : Algebra.IsStandardEtale R (AdjoinRoot f) :=
    Algebra.IsStandardEtale.of_equiv (P.equivAwayAdjoinRoot.trans e₂)
  have hθ' : f.eval₂ (Algebra.ofId R B : R →+* B) θ = 0 := hθ
  let π := AdjoinRoot.liftAlgHom f (Algebra.ofId R B) θ hθ'
  refine ⟨AdjoinRoot f, inferInstance, inferInstance, hloc, hf.finite_adjoinRoot, inferInstance,
    π, ?_⟩
  -- surjectivity, by Nakayama
  have : Algebra.EssFiniteType R B := inferInstance
  have hmax := Algebra.FormallyUnramified.map_maximalIdeal (R := R) (S := B)
  have hle : (⊤ : Submodule R B) ≤ LinearMap.range π.toLinearMap ⊔ (maximalIdeal R) • ⊤ := by
    intro b _
    have hb : residue B b ∈ Algebra.adjoin (ResidueField R) {θ₀} := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic, hθ₀]
      trivial
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hb
    obtain ⟨pb, hpb⟩ := hb
    obtain ⟨p, rfl⟩ := Polynomial.map_surjective _ residue_surjective pb
    have hdiff : b - π (AdjoinRoot.mk f p) ∈ maximalIdeal B := by
      rw [← residue_eq_zero_iff, map_sub, sub_eq_zero, AdjoinRoot.liftAlgHom_mk]
      rw [show Polynomial.eval₂ (Algebra.ofId R B : R →+* B) θ p =
        (p.map (algebraMap R B)).eval θ from (Polynomial.eval_map _ _).symm, residue_eval_map,
        hθres, ← hpb]
      rfl
    rw [← hmax] at hdiff
    have hdiff' : b - π (AdjoinRoot.mk f p) ∈ (maximalIdeal R) • (⊤ : Submodule R B) := by
      rw [Ideal.smul_top_eq_map]; exact hdiff
    exact Submodule.mem_sup.2 ⟨π (AdjoinRoot.mk f p), ⟨AdjoinRoot.mk f p, rfl⟩, _, hdiff',
      by ring⟩
  have htop := Submodule.le_of_le_smul_of_le_jacobson_bot (Module.Finite.fg_top)
    (jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge hle
  intro b
  obtain ⟨x, hx⟩ := htop (Submodule.mem_top (x := b))
  exact ⟨x, hx⟩

end CompleteLocal

end Langlands.AlgebraicGeometry.UnramifiedFunctor
