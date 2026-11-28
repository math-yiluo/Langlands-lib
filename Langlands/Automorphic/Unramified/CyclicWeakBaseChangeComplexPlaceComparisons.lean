import Langlands.Automorphic.CuspidalArchimedeanComponentIrreducibleProof
import Langlands.Automorphic.CuspidalComplexPlaceParameterUniqueness
import Langlands.Automorphic.ComplexPlaceParameterArithmeticTransport
import Langlands.Automorphic.IsobaricComplexPlaceParameter
import Langlands.Automorphic.Unramified.ComplexPlaceParameterNorm
import Langlands.Automorphic.Unramified.ComplexPlaceParameterTransport
import Langlands.Automorphic.Unramified.IsobaricWeakTransfer
import Langlands.Automorphic.Unramified.WeakInductionUnitaryCentralCharacter
import Langlands.Representation.Archimedean.ComplexStandardPermutationProof
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification

/-!
# Comparisons for the complex-place reductions of cyclic weak base change

Four comparisons between the literal and the aggregate complex-place vocabulary, used to derive
complex-place compatibility of cyclic weak transfers from aggregate statements on isobaric
data. See the paired Markdown.
-/

noncomputable section

universe u uF uE uV uW

open scoped TensorProduct

set_option autoImplicit false

/-! ## Parameter order -/

namespace Langlands.Automorphic

open Langlands.Archimedean Langlands.Global Langlands.LocalFactor.Archimedean

attribute [local instance] localComponentRationalGroup localComponentContinuousGroup
  localComponentSmoothGroup localComponentFormGroup localComponentStableGroup
  localComponentRealizationGroup
attribute [local instance 100] LieRing.ofAssociativeRing

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

local notation "CP" => {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}

set_option backward.isDefEq.respectTransparency false in
/-- A complex standard-module parameter of an actual cuspidal realization may be reordered:
if `T` has the parameter `es` at `v` and `ds` is a permutation of `es`, then `T` has the
parameter `ds` at `v`. -/
theorem CuspidalOperatorRealization.hasComplexPlaceParameter_of_perm {r : ℕ}
    (T : CuspidalOperatorRealization F r) (v : CP) {ds es : List ComplexCharacterData}
    (he : T.realization.HasComplexPlaceParameter v es) (hp : ds.Perm es) :
    T.realization.HasComplexPlaceParameter v ds := by
  have hirr := T.isIrreducibleComplexStandard v es he
  obtain ⟨hlen, g, hg, hgK, hgL⟩ := he
  have hg' : IsComplexStandardIntertwining (r + 1)
      (T.realization.complexPlaceCompactRepresentation v)
      (T.realization.complexPlaceLieAction v) es g := ⟨hgK, hgL⟩
  obtain ⟨B, hBbij, hB⟩ := complexStandardPermutation (r + 1) es ds hlen hp hirr
  have hgB := hB.comp g hg'.map_rep (fun X y => hg'.map_lie (1 ⊗ₜ X) y)
  exact ⟨hp.length_eq.trans hlen, g ∘ₗ B, hg.comp hBbij.1, hgB.1, hgB.2⟩

/-- The class form of `CuspidalOperatorRealization.hasComplexPlaceParameter_of_perm`. -/
theorem PositiveRankCuspidalClass.hasComplexPlaceParameter_of_perm
    (c : PositiveRankCuspidalClass F) (v : CP) {ds es : List ComplexCharacterData}
    (he : c.HasComplexPlaceParameter v es) (hp : ds.Perm es) :
    c.HasComplexPlaceParameter v ds := by
  rcases c with ⟨r, c⟩
  obtain ⟨T, rfl⟩ := c.exists_representative
  exact T.hasComplexPlaceParameter_of_perm v he hp

/-- For the data of one cuspidal class, the aggregate complex-place parameter is the literal
parameter of the class. -/
theorem IsobaricData.hasComplexPlaceParameter_ofCuspidal_iff (c : PositiveRankCuspidalClass F)
    (v : CP) (ds : List ComplexCharacterData) :
    (IsobaricData.ofCuspidal c).HasComplexPlaceParameter v ds ↔
      c.HasComplexPlaceParameter v ds := by
  rw [IsobaricData.hasComplexPlaceParameter_ofCuspidal]
  exact ⟨fun ⟨_, h, hp⟩ => c.hasComplexPlaceParameter_of_perm v h hp,
    fun h => ⟨ds, h, List.Perm.refl ds⟩⟩

end Langlands.Automorphic

/-! ## Unitary central characters -/

namespace Langlands.Automorphic.Unramified

open Filter Polynomial
open Langlands.Global Langlands.Global.AdelicFunctoriality Langlands.Unramified
open ClassFieldTheory.Global.RelativeWeilGroup (HasUnitaryCentralCharacter)
open scoped NumberField

private theorem isUnitary_of_cofinite_uniformizer'
    {F : Type uF} [Field F] [NumberField F] (ω : HeckeCharacter F)
    (h : ∀ᶠ v in cofinite, ω.IsUnramifiedAt v ∧ ‖(ω.finiteUniformizerValue v : ℂ)‖ = 1) :
    ω.IsUnitary := by
  let μ : HeckeCharacter F := (unitsNormRpow 1).comp ω
  have hModulus (x : IdeleClasses F) : μ x = 1 ↔ ‖(ω x : ℂ)‖ = 1 := by
    rw [← Units.val_inj]
    change ((‖(ω x : ℂ)‖ ^ (1 : ℝ) : ℝ) : ℂ) = 1 ↔ ‖(ω x : ℂ)‖ = 1
    simp
  have hfinite := eventually_cofinite.mp h
  have hμ : μ = 1 := by
    apply heckeLocalComponentRigidity F μ 1 hfinite.toFinset
    intro v hv
    have hgood : ω.IsUnramifiedAt v ∧ ‖(ω.finiteUniformizerValue v : ℂ)‖ = 1 := by
      by_contra hbad
      exact hv (hfinite.mem_toFinset.mpr hbad)
    have hIntegral : μ.IsUnramifiedAt v := by
      intro a ha
      change unitsNormRpow 1 (ω.finiteComponent v a) = 1
      rw [hgood.1 a ha, map_one]
    let G := (μ.finiteComponent v).toMonoidHom.ker
    have hG : G = ⊤ :=
      CompletionPadic.subgroup_eq_top_of_uniformizer_mem F v G
        (fun a ha => MonoidHom.mem_ker.mpr (hIntegral a ha))
        (MonoidHom.mem_ker.mpr ((hModulus _).mpr hgood.2))
    refine ⟨hIntegral, fun _ _ => rfl, ?_⟩
    apply DFunLike.ext
    intro a
    exact MonoidHom.mem_ker.mp (hG ▸ Subgroup.mem_top a : a ∈ G)
  intro x
  exact (hModulus x).mp (by rw [hμ]; rfl)

private theorem norm_leadingCoeff_eulerPolynomial'
    {F : Type uF} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    {r : ℕ} {S : CuspidalOperatorRealization F r} {ω : HeckeCharacter F}
    (hω : S.HasCentralCharacter ω) (P : CuspidalSpectralPresentation.{uF, uV} S)
    (v : FinitePlace F) (hv : v ∉ P.exceptional) :
    ‖(P.spectralSystem.eulerPolynomial v hv).leadingCoeff‖ =
      ‖(ω.finiteUniformizerValue v : ℂ)‖ := by
  rw [S.finiteUniformizerValue_eq_elementaryCoefficient v hω P hv]
  simp [SpectralSystem.eulerPolynomial, elementaryCoefficient, ← Polynomial.coeff_natDegree]

/-- Raising every eigenvalue to the `k`th power raises the absolute value of the leading
coefficient of the Euler polynomial to the `k`th power. -/
theorem Eigenvalues.norm_leadingCoeff_eulerPolynomial_power {n : ℕ} (s : Eigenvalues n)
    (k : ℕ) :
    ‖(s.power k).eulerPolynomial.leadingCoeff‖ = ‖s.eulerPolynomial.leadingCoeff‖ ^ k := by
  obtain ⟨z, rfl⟩ := Eigenvalues.ofTuple_surjective n s
  have hlc (a : ℂ) (ha : a ≠ 0) : (1 - C a * X : ℂ[X]).leadingCoeff = -a := by
    have h : (1 - C a * X : ℂ[X]) = C (-a) * X + C 1 := by
      rw [C_neg, C_1]
      ring
    rw [h, leadingCoeff_linear (neg_ne_zero.mpr ha)]
  rw [Eigenvalues.power_ofTuple, Eigenvalues.eulerPolynomial_ofTuple,
    Eigenvalues.eulerPolynomial_ofTuple, leadingCoeff_prod, leadingCoeff_prod,
    Finset.prod_congr rfl fun i _ => hlc _ (z i ^ k).ne_zero,
    Finset.prod_congr rfl fun i _ => hlc _ (z i).ne_zero, _root_.norm_prod, _root_.norm_prod,
    ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [norm_neg, norm_neg, Units.val_pow_eq_pow_val, norm_pow]

/-- A property of the places of `E` that holds at every place above all but finitely many
places of `F` holds at all but finitely many places of `E`. -/
theorem eventually_cofinite_of_forall_above {F : Type uF} {E : Type uE} [Field F] [Field E]
    [NumberField F] [NumberField E] [Algebra F E] {P : FinitePlace E → Prop}
    (h : ∀ᶠ v : FinitePlace F in cofinite, ∀ w : FinitePlacesAbove E v, P w.1) :
    ∀ᶠ w : FinitePlace E in cofinite, P w := by
  have hfin := eventually_cofinite.mp h
  rw [eventually_cofinite]
  refine (hfin.biUnion fun v _ => Set.finite_range
    (fun w : FinitePlacesAbove E v => w.1)).subset ?_
  intro w hw
  have hlies : w.asIdeal.LiesOver (w.under (𝓞 F)).asIdeal := ⟨rfl⟩
  refine Set.mem_biUnion (x := w.under (𝓞 F)) ?_ ⟨⟨w, hlies⟩, rfl⟩
  intro hall
  exact hw (hall ⟨w, hlies⟩)

/-- A cuspidal weak base change of a cuspidal realization with unitary central character has
unitary central character. -/
theorem hasUnitaryCentralCharacter_of_isWeakBaseChangeOf
    {F : Type uF} {E : Type uE} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] [CompactSpace (AdeleQuotient F)] [CompactSpace (AdeleQuotient E)] {r : ℕ}
    (S : CuspidalOperatorRealization F r) (T : CuspidalOperatorRealization E r)
    (hS : HasUnitaryCentralCharacter S)
    (hW : T.isoClass.IsWeakBaseChangeOf.{uF, uE, uV, uW} S.isoClass) :
    HasUnitaryCentralCharacter T := by
  obtain ⟨ω, hωunit, hω⟩ := hS
  obtain ⟨ξ, hξ, _⟩ := T.realization.existsUnique_hasCentralCharacter T.irreducible
  obtain ⟨P, Q, hPQ⟩ :=
    (CuspidalOperatorRealization.IsoClass.isWeakBaseChangeOf_isoClass_iff.{uF, uE, uV, uW}
      T S).mp hW
  refine ⟨ξ, isUnitary_of_cofinite_uniformizer' ξ ?_, hξ⟩
  obtain ⟨A, hA⟩ := HeckeFunctionalEquation.exists_finset_isUnramifiedAt E ξ
  have habove : ∀ᶠ v : FinitePlace F in cofinite, ∀ w : FinitePlacesAbove E v,
      ‖(HeckeCharacter.finiteUniformizerValue ξ w.1 : ℂ)‖ = 1 := by
    filter_upwards [hPQ] with v hv
    obtain ⟨hs, ht, _, heig⟩ := hv
    intro w
    rw [← norm_leadingCoeff_eulerPolynomial' hξ Q w.1 (ht w)]
    change ‖(Q.spectralSystem.eigenvalues w.1 (ht w)).eulerPolynomial.leadingCoeff‖ = 1
    rw [heig w, Eigenvalues.norm_leadingCoeff_eulerPolynomial_power]
    change ‖(P.spectralSystem.eulerPolynomial v hs).leadingCoeff‖ ^ _ = 1
    rw [norm_leadingCoeff_eulerPolynomial' hω P v hs,
      show ‖(HeckeCharacter.finiteUniformizerValue ω v : ℂ)‖ = 1 from hωunit _, one_pow]
  filter_upwards [eventually_cofinite_of_forall_above (F := F)
      (P := fun w => ‖(HeckeCharacter.finiteUniformizerValue ξ w : ℂ)‖ = 1) habove,
    A.eventually_cofinite_notMem]
    with w hw hwA
  exact ⟨hA w hwA, hw⟩

/-- The Galois orbit of a cuspidal class with unitary central character is unitary. -/
theorem isUnitary_galoisOrbit_of_hasUnitaryCentralCharacter {F : Type uF} {E : Type uE}
    [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    [CompactSpace (AdeleQuotient E)] {m : ℕ}
    (T : CuspidalOperatorRealization E m) (hT : HasUnitaryCentralCharacter T) :
    (IsobaricData.galoisOrbit F
      (PositiveRankCuspidalClass.ofFixedRank T.isoClass)).IsUnitary := by
  intro c hc
  obtain ⟨τ, _, rfl⟩ := Multiset.mem_map.mp hc
  let e := τ.toRingEquiv.symm
  change (T.arithmeticComap e).realization.IsUnitarizable
  obtain ⟨χ, hχ, hcentral⟩ := hT
  exact (T.arithmeticComap e).isUnitarizable_of_hasUnitaryCentralCharacter
    ⟨HeckeCharacter.comap e χ, (HeckeCharacter.isUnitary_comap_iff e χ).mpr hχ,
      (T.arithmeticComap_hasCentralCharacter_iff e χ).mpr hcentral⟩

end Langlands.Automorphic.Unramified

/-! ## Galois orbits above a complex place -/

namespace Langlands.Automorphic.Unramified

open NumberField NumberField.InfinitePlace NumberField.ComplexEmbedding
open Langlands.Global Langlands.Global.AdelicFunctoriality Langlands.LocalFactor.Archimedean
open Langlands.Global.ArchimedeanCompactTransport

variable {F : Type uF} {E : Type uE} [Field F] [Field E] [NumberField F] [NumberField E]
  [Algebra F E]

local notation "CPF" =>
  {v : NumberField.InfinitePlace F // NumberField.InfinitePlace.IsComplex v}

omit [NumberField F] [NumberField E] in
private theorem liesOver_of_comap_eq' {q : NumberField.InfinitePlace E}
    {p : NumberField.InfinitePlace F} (h : q.comap (algebraMap F E) = p) : q.LiesOver p := by
  constructor
  rw [← h]
  ext x
  rfl

/-- Every infinite place of `F` has a place of `E` above it. -/
theorem nonempty_infinitePlacesAbove (v : NumberField.InfinitePlace F) :
    Nonempty (InfinitePlacesAbove E v) := by
  obtain ⟨w, hw⟩ := InfinitePlace.comap_surjective (k := F) (K := E) v
  exact ⟨⟨w, liesOver_of_comap_eq' hw⟩⟩

/-- Transport between the coordinates at `v` and at `w` commutes with concatenation. -/
theorem complexPlaceParameterTransport_flatten_ofFn
    (v : CPF) (w : InfinitePlacesAbove E v.1) {d : ℕ}
    (f : Fin d → List ComplexCharacterData) :
    complexPlaceParameterTransport v w (List.ofFn f).flatten =
      (List.ofFn fun i => complexPlaceParameterTransport v w (f i)).flatten := by
  classical
  unfold complexPlaceParameterTransport
  split_ifs
  · rfl
  · rw [List.map_flatten, List.map_ofFn]
    rfl

private theorem conj_comp_conj' :
    ComplexCharacterData.conj ∘ ComplexCharacterData.conj = id :=
  funext ComplexCharacterDataLemmas.conj_conj

omit [NumberField F] in
/-- A Galois automorphism carries a place above `v` to a place above `v`. -/
theorem smul_infinitePlace_liesOver (v : NumberField.InfinitePlace F)
    (w : InfinitePlacesAbove E v) (τ : E ≃ₐ[F] E) :
    (τ • w.1).LiesOver v := by
  have := w.2
  apply liesOver_of_comap_eq'
  refine Eq.trans ?_ (InfinitePlace.LiesOver.comap_eq w.1 v)
  ext x
  simp [InfinitePlace.comap_apply]

omit [NumberField F] in
/-- A place above a complex place is unramified. -/
theorem isUnramified_of_isComplex_under (v : CPF)
    (w : InfinitePlacesAbove E v.1) : InfinitePlace.IsUnramified F w.1 := by
  have := w.2
  refine isUnramified_iff.mpr (Or.inr ?_)
  rw [InfinitePlace.LiesOver.comap_eq w.1 v.1]
  exact v.2

/-- If `w' = τ⁻¹ • w`, the pullback along `τ⁻¹` of the complex place `w'` is `w`. -/
theorem complexPlace_galois (v : CPF)
    (w w' : InfinitePlacesAbove E v.1) (τ : E ≃ₐ[F] E) (hτ : w'.1 = τ⁻¹ • w.1) :
    complexPlace τ.toRingEquiv.symm (complexPlaceAbove v w') = complexPlaceAbove v w := by
  apply Subtype.ext
  change infinitePlaceEquiv τ.toRingEquiv.symm w'.1 = w.1
  rw [hτ]
  ext x
  simp [infinitePlaceEquiv_apply, AlgEquiv.aut_inv]

omit [NumberField F] in
/-- The orientation bookkeeping of the Galois conjugation from `w'` to `w = τ • w'`: the
selected embedding of `w'` read along `τ⁻¹` is that of `w` exactly when `w` and `w'` are
oriented alike over `v`. -/
theorem isAligned_galois_iff (v : CPF)
    (w w' : InfinitePlacesAbove E v.1) (τ : E ≃ₐ[F] E) (hτ : w'.1 = τ⁻¹ • w.1) :
    (w'.1.embedding.comp τ.toRingEquiv.symm.toRingHom = w.1.embedding) ↔
      (w.1.embedding.comp (algebraMap F E) = v.1.embedding ↔
        w'.1.embedding.comp (algebraMap F E) = v.1.embedding) := by
  have := w.2
  have hwC : w.1.IsComplex := InfinitePlace.LiesOver.isComplex_of_isComplex_under w.1 v.2
  have hvne : conjugate v.1.embedding ≠ v.1.embedding := fun h =>
    (isComplex_iff.mp v.2) (ComplexEmbedding.isReal_iff.mpr h)
  have hwne : conjugate w.1.embedding ≠ w.1.embedding := fun h =>
    (isComplex_iff.mp hwC) (ComplexEmbedding.isReal_iff.mpr h)
  have hA_or := InfinitePlace.LiesOver.embedding_comp_eq_or_conjugate_embedding_comp_eq w.1 v.1
  have hmk : mk w'.1.embedding = mk (w.1.embedding.comp τ.toRingEquiv.toRingHom) := by
    rw [mk_embedding, hτ]
    ext x
    simp [InfinitePlace.apply, norm_embedding_eq, AlgEquiv.aut_inv]
  rcases mk_eq_iff.mp hmk with h1 | h1
  · have hL : w'.1.embedding.comp τ.toRingEquiv.symm.toRingHom = w.1.embedding := by
      rw [h1]
      ext x
      simp
    have hB : w'.1.embedding.comp (algebraMap F E) = w.1.embedding.comp (algebraMap F E) := by
      rw [h1]
      ext x
      simp
    rw [hB]
    simp only [hL, iff_self]
  · have h1' : w'.1.embedding = conjugate (w.1.embedding.comp τ.toRingEquiv.toRingHom) := by
      rw [← h1]
      exact (star_star _).symm
    have hL : w'.1.embedding.comp τ.toRingEquiv.symm.toRingHom = conjugate w.1.embedding := by
      rw [h1']
      ext x
      simp [ComplexEmbedding.conjugate_coe_eq]
    have hB : w'.1.embedding.comp (algebraMap F E) =
        conjugate (w.1.embedding.comp (algebraMap F E)) := by
      rw [h1']
      ext x
      simp [ComplexEmbedding.conjugate_coe_eq]
    rw [hL, hB]
    refine iff_of_false hwne ?_
    intro hiff
    rcases hA_or with hA | hA
    · apply hvne
      rw [← hA]
      exact (hiff.mp hA).trans hA.symm
    · have hB' : conjugate (w.1.embedding.comp (algebraMap F E)) = v.1.embedding := by
        rw [← hA]
        ext x
        simp [ComplexEmbedding.conjugate_coe_eq]
      have hA' := hiff.mpr hB'
      apply hvne
      rw [← hA']
      exact hB'.trans hA'.symm

/-- Reading a list at `w' = τ⁻¹ • w` along `τ⁻¹` is transporting it from `w'` to `v` and then
from `v` to `w`. -/
theorem parameterList_galois (v : CPF)
    (w w' : InfinitePlacesAbove E v.1) (τ : E ≃ₐ[F] E) (hτ : w'.1 = τ⁻¹ • w.1)
    (x : List ComplexCharacterData) :
    Automorphic.ComplexPlaceArithmeticTransport.parameterList τ.toRingEquiv.symm
        (complexPlaceAbove v w') x =
      complexPlaceParameterTransport v w (complexPlaceParameterTransport v w' x) := by
  classical
  have key : Automorphic.ComplexPlaceArithmeticTransport.IsAligned τ.toRingEquiv.symm
      (complexPlaceAbove v w') ↔
      (w.1.embedding.comp (algebraMap F E) = v.1.embedding ↔
        w'.1.embedding.comp (algebraMap F E) = v.1.embedding) := by
    unfold Automorphic.ComplexPlaceArithmeticTransport.IsAligned
    rw [complexPlace_galois v w w' τ hτ]
    exact isAligned_galois_iff v w w' τ hτ
  unfold Automorphic.ComplexPlaceArithmeticTransport.parameterList complexPlaceParameterTransport
  split_ifs <;> simp_all [conj_comp_conj']

/-- The Galois conjugate `T^τ` has at `w` the parameter of `T` at `w' = τ⁻¹ • w`, transported
from `w'` to `v` and from `v` to `w`. -/
theorem hasComplexPlaceParameter_galoisConj [CompactSpace (AdeleQuotient E)] {m : ℕ}
    (T : CuspidalOperatorRealization E m) (v : CPF)
    (w w' : InfinitePlacesAbove E v.1) (τ : E ≃ₐ[F] E) (hτ : w'.1 = τ⁻¹ • w.1)
    {x : List ComplexCharacterData}
    (hx : T.isoClass.HasComplexPlaceParameter (complexPlaceAbove v w') x) :
    ((PositiveRankCuspidalClass.ofFixedRank T.isoClass).galoisConj τ).HasComplexPlaceParameter
      (complexPlaceAbove v w)
      (complexPlaceParameterTransport v w (complexPlaceParameterTransport v w' x)) := by
  have h :=
    Automorphic.ComplexPlaceArithmeticTransport.cuspidal_hasComplexPlaceParameter_arithmeticComap
      τ.toRingEquiv.symm T hx
  rw [complexPlace_galois v w w' τ hτ, parameterList_galois v w w' τ hτ] at h
  rw [PositiveRankCuspidalClass.galoisConj_ofFixedRank,
    PositiveRankCuspidalClass.hasComplexPlaceParameter_ofFixedRank]
  change (CuspidalOperatorRealization.IsoClass.arithmeticComap τ.toRingEquiv.symm
    T.isoClass).HasComplexPlaceParameter _ _
  rw [CuspidalOperatorRealization.IsoClass.arithmeticComap_isoClass]
  exact h

variable [IsGalois F E]

/-- Above a complex place `v` of `F` the Galois group acts simply transitively on the places of
`E`: for a place `w` above `v`, `τ ↦ τ⁻¹ • w` is a bijection onto the places above `v`. -/
def galoisPlacesAboveEquiv (v : CPF)
    (w : InfinitePlacesAbove E v.1) : (E ≃ₐ[F] E) ≃ InfinitePlacesAbove E v.1 :=
  Equiv.ofBijective (fun τ => ⟨τ⁻¹ • w.1, smul_infinitePlace_liesOver v.1 w τ⁻¹⟩) (by
    constructor
    · intro τ₁ τ₂ h
      have h' : τ₁⁻¹ • w.1 = τ₂⁻¹ • w.1 := congrArg Subtype.val h
      have hstab : τ₂ * τ₁⁻¹ ∈ MulAction.stabilizer (E ≃ₐ[F] E) w.1 := by
        rw [MulAction.mem_stabilizer_iff, mul_smul, h', smul_inv_smul]
      rw [(isUnramified_of_isComplex_under v w).stabilizer_eq_bot, Subgroup.mem_bot] at hstab
      exact (mul_inv_eq_one.mp hstab).symm
    · intro w'
      have := w.2
      have := w'.2
      obtain ⟨σ, hσ⟩ := exists_smul_eq_of_comap_eq (k := F)
        ((InfinitePlace.LiesOver.comap_eq w.1 v.1).trans
          (InfinitePlace.LiesOver.comap_eq w'.1 v.1).symm)
      exact ⟨σ⁻¹, Subtype.ext (by simpa using hσ)⟩)

omit [NumberField F] in
/-- The place `galoisPlacesAboveEquiv v w τ` is `τ⁻¹ • w`. -/
theorem galoisPlacesAboveEquiv_apply_val (v : CPF)
    (w : InfinitePlacesAbove E v.1) (τ : E ≃ₐ[F] E) :
    (galoisPlacesAboveEquiv v w τ).1 = τ⁻¹ • w.1 :=
  rfl

/-- **Orbit parameter.** If `T` has the parameter `ds w'` at every place `w'` of `E` above the
complex place `v` of `F`, then the Galois orbit of the class of `T` has, at each place `w` above
`v`, the aggregate parameter obtained by transporting the Langlands sum
`complexPlaceLanglandsSum v e ds` from `v` to `w`. -/
theorem galoisOrbit_hasComplexPlaceParameter [CompactSpace (AdeleQuotient E)] {m : ℕ}
    (T : CuspidalOperatorRealization E m) (v : CPF)
    (w : InfinitePlacesAbove E v.1) {d : ℕ} (e : Fin d ≃ InfinitePlacesAbove E v.1)
    (ds : InfinitePlacesAbove E v.1 → List ComplexCharacterData)
    (hds : ∀ w', T.isoClass.HasComplexPlaceParameter (complexPlaceAbove v w') (ds w')) :
    (IsobaricData.galoisOrbit F
        (PositiveRankCuspidalClass.ofFixedRank T.isoClass)).HasComplexPlaceParameter
      (complexPlaceAbove v w)
      (complexPlaceParameterTransport v w (complexPlaceLanglandsSum v e ds)) := by
  let ψ := galoisPlacesAboveEquiv v w
  let c := PositiveRankCuspidalClass.ofFixedRank T.isoClass
  refine ⟨d, fun j => c.galoisConj (ψ.symm (e j)), ?_,
    fun j => complexPlaceParameterTransport v w
      (complexPlaceParameterTransport v (e j) (ds (e j))), fun j => ?_, ?_⟩
  · have h : (Finset.univ : Finset (Fin d)).val.map (fun j => c.galoisConj (ψ.symm (e j))) =
        ((Finset.univ : Finset (Fin d)).val.map (e.trans ψ.symm)).map
          (fun τ => c.galoisConj τ) := by
      rw [Multiset.map_map]
      rfl
    rw [h, Multiset.map_univ_val_equiv]
    rfl
  · have hτ : (e j).1 = (ψ.symm (e j))⁻¹ • w.1 :=
      (congrArg Subtype.val (ψ.apply_symm_apply (e j))).symm
    exact hasComplexPlaceParameter_galoisConj T v w (e j) (ψ.symm (e j)) hτ (hds (e j))
  · rw [complexPlaceLanglandsSum, complexPlaceParameterTransport_flatten_ofFn]

end Langlands.Automorphic.Unramified
