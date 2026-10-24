import Langlands.Representation.Unramified.PrincipalSeriesHecke
import Langlands.Representation.Unramified.SphericalClassificationStatement
import Langlands.Representation.Smooth.Transfer.SubquotientProof
import Langlands.Representation.Smooth.FixedVectors.LawsProof

/-!
# Uniqueness of the spherical principal-series spectrum

Every spherical constituent of the normalized principal series `I(z)` has the standard
Hecke scalars of the spectrum of `z` on its `K`-fixed vectors. The scalars determine the
coefficients of the Euler polynomial, and the Euler polynomial determines the spectrum with
multiplicities. Hence an irreducible admissible representation has at most one spherical
principal-series spectrum.
-/

noncomputable section

namespace Langlands.Unramified

open Correspondence MinusculeCosets Polynomial

universe uF uV

/-! ### The Euler polynomial determines the spectrum -/

namespace Eigenvalues

variable {n : ℕ}

/-- The roots of the Euler polynomial are the inverses of the eigenvalues. -/
theorem eulerPolynomial_roots (s : Eigenvalues n) :
    (eulerPolynomial s).roots = (s : Multiset ℂˣ).map fun z => ((z⁻¹ : ℂˣ) : ℂ) := by
  have h : ∀ z : ℂˣ, (1 - C (z : ℂ) * X) = C (-(z : ℂ)) * (X - C ((z⁻¹ : ℂˣ) : ℂ)) := by
    intro z
    have hz : (z : ℂ) * (z : ℂ)⁻¹ = 1 := mul_inv_cancel₀ z.ne_zero
    rw [Units.val_inv_eq_inv_val]
    calc 1 - C (z : ℂ) * X = C ((z : ℂ) * (z : ℂ)⁻¹) - C (z : ℂ) * X := by rw [hz, map_one]
      _ = C (-(z : ℂ)) * (X - C ((z : ℂ)⁻¹)) := by rw [map_mul, map_neg]; ring
  rw [eulerPolynomial]
  simp_rw [h]
  rw [Multiset.prod_map_mul]
  have hC : ((s : Multiset ℂˣ).map fun z : ℂˣ => C (-(z : ℂ))).prod =
      C (((s : Multiset ℂˣ).map fun z : ℂˣ => -(z : ℂ)).prod) := by
    rw [map_multiset_prod, Multiset.map_map]
    rfl
  have hne : (((s : Multiset ℂˣ).map fun z : ℂˣ => -(z : ℂ)).prod) ≠ 0 := by
    refine Multiset.prod_ne_zero fun h0 => ?_
    obtain ⟨z, -, hz⟩ := Multiset.mem_map.1 h0
    exact z.ne_zero (neg_eq_zero.1 hz)
  have hX : ((s : Multiset ℂˣ).map fun z : ℂˣ => X - C ((z⁻¹ : ℂˣ) : ℂ)).prod =
      (((s : Multiset ℂˣ).map fun z : ℂˣ => ((z⁻¹ : ℂˣ) : ℂ)).map fun a => X - C a).prod := by
    rw [Multiset.map_map]
    rfl
  rw [hC, roots_C_mul _ hne, hX, roots_multiset_prod_X_sub_C]

/-- The Euler polynomial determines the spectrum, with multiplicities. -/
theorem eulerPolynomial_injective :
    Function.Injective (eulerPolynomial : Eigenvalues n → ℂ[X]) := by
  intro s t h
  have hr := congrArg Polynomial.roots h
  rw [eulerPolynomial_roots, eulerPolynomial_roots] at hr
  have hinj : Function.Injective fun z : ℂˣ => ((z⁻¹ : ℂˣ) : ℂ) :=
    fun a b hab => inv_injective (Units.ext hab)
  exact Sym.ext (Multiset.map_injective hinj hr)

end Eigenvalues

/-! ### Generic transfer along intertwiners -/

section Transfer

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {W : Type*} [AddCommGroup W] [Module ℂ W]

/-- A surjective intertwiner between smooth representations maps the `K`-fixed vectors onto
the `K`-fixed vectors. -/
theorem exists_fixed_lift (μ : MeasureTheory.Measure G) [μ.IsHaarMeasure]
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ) (σ : Representation ℂ G W) (hσ : IsSmooth σ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (f : ρ.IntertwiningMap σ)
    (hf : Function.Surjective f.toLinearMap) (w : fixedVectors σ K.toSubgroup) :
    ∃ v : fixedVectors ρ K.toSubgroup, f v.1 = w.1 := by
  obtain ⟨s, hs⟩ := hf w.1
  refine ⟨Hecke.fixedProjection μ ρ hρ K hK s, ?_⟩
  have h1 := congrArg Subtype.val (Hecke.fixedProjection_intertwiner μ ρ hρ K hK hσ f s)
  have hs2 : f s = w.1 := hs
  rw [hs2, Hecke.fixedProjection_fixed] at h1
  exact h1

omit [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] in
/-- The inclusion of a subrepresentation, as an intertwiner. -/
def subrepresentationSubtype (ρ : Representation ℂ G V) (S : Subrepresentation ρ) :
    S.toRepresentation.IntertwiningMap ρ where
  toLinearMap := S.toSubmodule.subtype
  isIntertwining' _ := by
    ext
    rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] in
theorem subrepresentationSubtype_injective (ρ : Representation ℂ G V) (S : Subrepresentation ρ) :
    Function.Injective (subrepresentationSubtype ρ S) :=
  Subtype.val_injective

omit [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] in
/-- An intertwiner carries a finite sum of translates to the same sum of translates. -/
theorem intertwiningMap_sum_translates {I : Type*} (ρ : Representation ℂ G V)
    (σ : Representation ℂ G W) (f : ρ.IntertwiningMap σ) (t : Finset I) (x : I → G) (v : V) :
    f (∑ α ∈ t, ρ (x α) v) = ∑ α ∈ t, σ (x α) (f v) := by
  rw [map_sum]
  exact Finset.sum_congr rfl fun α _ => Representation.IntertwiningMap.isIntertwining _ _ f _ v

omit [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] in
/-- A scalar identity for a finite sum of translates descends along an injective intertwiner. -/
theorem sum_translates_of_injective {I : Type*} (ρ : Representation ℂ G V)
    (σ : Representation ℂ G W) (f : ρ.IntertwiningMap σ) (hf : Function.Injective f)
    (t : Finset I) (x : I → G) (v : V) (c : ℂ)
    (h : ∑ α ∈ t, σ (x α) (f v) = c • f v) : ∑ α ∈ t, ρ (x α) v = c • v := by
  apply hf
  rw [intertwiningMap_sum_translates, map_smul]
  exact h

end Transfer

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance uniquenessFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance uniquenessFieldValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance uniquenessFieldLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance uniquenessGeneralLinearTopology (n : ℕ) :
    TopologicalSpace (GeneralLinear n F.Carrier) := F.canonicalGeneralLinearTopology n
local instance uniquenessGeneralLinearTopologicalGroup (n : ℕ) :
    IsTopologicalGroup (GeneralLinear n F.Carrier) := F.canonicalGeneralLinearTopologicalGroup n
local instance uniquenessGeneralLinearT2 (n : ℕ) : T2Space (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearT2Space n
local instance uniquenessGeneralLinearMeasurable (n : ℕ) :
    MeasurableSpace (GeneralLinear n F.Carrier) := borel _
local instance uniquenessGeneralLinearBorel (n : ℕ) :
    BorelSpace (GeneralLinear n F.Carrier) := ⟨rfl⟩

/-! ### Spherical constituents have the standard Hecke scalars -/

/-- On the `K`-fixed vectors of a smooth subquotient of the principal series of `z`, each
standard double-coset operator acts by the standard Hecke scalar of the spectrum of `z`. -/
theorem cornerAction_of_isSubquotientOf {r : ℕ} {z : Fin (r + 1) → ℂˣ} {W : Type*}
    [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) W)
    (hπ : IsSmooth π) (h : IsSubquotientOf (principalSeriesOfTuple F z) π) (i : Fin (r + 2))
    (v : fixedVectors π (sphericalSubgroup F r)) :
    (Hecke.cornerAction (sphericalHaar F r) π hπ (sphericalOpenSubgroup F r)
        (sphericalOpenSubgroup_isCompact F r) (standardHeckeElement F r i) v : W) =
      standardHeckeScalar F (Eigenvalues.ofTuple z) i • (v : W) := by
  obtain ⟨S, f, hf⟩ := h
  have hι := subrepresentationSubtype_injective (principalSeriesOfTuple F z) S
  have hS : IsSmooth S.toRepresentation :=
    isSmooth_of_injective _ hι (isSmooth_principalSeriesOfTuple F z)
  obtain ⟨s', hs'⟩ := exists_fixed_lift (sphericalHaar F r) S.toRepresentation hS π hπ
    (sphericalOpenSubgroup F r) (sphericalOpenSubgroup_isCompact F r) f hf v
  have hSsum := sum_translates_of_injective S.toRepresentation (principalSeriesOfTuple F z)
    (subrepresentationSubtype (principalSeriesOfTuple F z) S) hι
    Finset.univ (labelledRep F.canonicalTopologicalData.uniformizerUnit (residueLift F))
    s'.1 (standardHeckeScalar F (Eigenvalues.ofTuple z) i)
    (principalSeries_sum_labelledRep F z i
      ⟨subrepresentationSubtype (principalSeriesOfTuple F z) S s'.1,
        map_mem_fixedVectors (subrepresentationSubtype (principalSeriesOfTuple F z) S) s'.2⟩)
  rw [standardHecke_cornerAction_eq_sum F π hπ i v, ← hs',
    ← intertwiningMap_sum_translates, hSsum]
  exact LinearMap.map_smul f.toLinearMap _ _

/-- Every spherical constituent of the ordered normalized principal series of `z` has the
standard Hecke scalars of the unordered spectrum of `z`. -/
theorem hasSphericalHeckeSpectrum_of_isSphericalConstituent {r : ℕ} {z : Fin (r + 1) → ℂˣ}
    {A : AutomorphicObject.{uF, uV} F r.succPNat} (h : IsSphericalConstituent F z A) :
    HasSphericalHeckeSpectrum F A (Eigenvalues.ofTuple z) :=
  ⟨h.1, fun i v => Subtype.ext (cornerAction_of_isSubquotientOf F A.obj.representation
    A.obj.isSmooth h.2 i v)⟩

/-! ### Separation by the Hecke scalars -/

/-- The standard Hecke scalars on a nonzero spherical space determine the spectrum. -/
theorem eq_of_hasSphericalHeckeSpectrum {r : ℕ} {A : AutomorphicObject.{uF, uV} F r.succPNat}
    {s t : Eigenvalues (r + 1)} (hs : HasSphericalHeckeSpectrum F A s)
    (ht : HasSphericalHeckeSpectrum F A t) : s = t := by
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hs.1
  have hsq : (Real.sqrt (F.canonicalTopologicalData.residueCardinality : ℝ) : ℂ) ≠ 0 := by
    have := F.canonicalTopologicalData.residueCardinality_gt_one
    have hq : (0 : ℝ) < F.canonicalTopologicalData.residueCardinality := by
      exact_mod_cast Nat.zero_lt_of_lt this
    exact_mod_cast (Real.sqrt_pos.2 hq).ne'
  have hcoeff : ∀ i : Fin (r + 2),
      elementaryCoefficient s i.val = elementaryCoefficient t i.val := by
    intro i
    have h := (hs.2 i ⟨v, hv⟩).symm.trans (ht.2 i ⟨v, hv⟩)
    have hv' : (⟨v, hv⟩ : fixedVectors A.obj.representation (sphericalSubgroup F r)) ≠ 0 :=
      fun h0 => hv0 (congrArg Subtype.val h0)
    have h' := smul_left_injective ℂ hv' h
    exact mul_left_cancel₀ (pow_ne_zero _ hsq) h'
  apply Eigenvalues.eulerPolynomial_injective
  ext n
  by_cases hn : n ≤ r + 1
  · have h := hcoeff ⟨n, by omega⟩
    exact mul_left_cancel₀ (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) h
  · rw [coeff_eq_zero_of_natDegree_lt (by rw [Eigenvalues.eulerPolynomial_natDegree]; omega),
      coeff_eq_zero_of_natDegree_lt (by rw [Eigenvalues.eulerPolynomial_natDegree]; omega)]

/-! ### The main theorem -/

/-- The unordered spherical principal-series spectrum of an irreducible admissible
representation is unique, with multiplicities. -/
theorem sphericalSpectrumUniqueness : SphericalSpectrumUniquenessStatement.{uF, uV} := by
  intro p _ F r A s t hs ht
  obtain ⟨z, rfl, hz⟩ := hs
  obtain ⟨w, rfl, hw⟩ := ht
  exact eq_of_hasSphericalHeckeSpectrum F
    (hasSphericalHeckeSpectrum_of_isSphericalConstituent F hz)
    (hasSphericalHeckeSpectrum_of_isSphericalConstituent F hw)

end Langlands.Unramified
