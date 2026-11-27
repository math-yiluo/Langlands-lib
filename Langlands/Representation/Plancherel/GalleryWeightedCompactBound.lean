import Langlands.Representation.Plancherel.ActualCommonLeviCompactAgreement
import Langlands.Representation.Plancherel.ActualCommonLeviCompactTensorNorm
import Langlands.Representation.Plancherel.DynamicContinuedGalleryRoundTrip
import Langlands.Representation.Plancherel.RationalUnitaryBoundTransport
import Langlands.Representation.Plancherel.WeightedCompactTensorEstimate

/-! # The weighted compact tensor bound for a distance-additive triple -/

noncomputable section

set_option maxHeartbeats 3200000
set_option maxRecDepth 4096
set_option quotPrecheck false
set_option hygiene false

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj NNReal TensorProduct
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel.DynamicCommonLeviPresentations

open Aubert.General Induction CompactInduction HarishChandraSchwartz
open DynamicOppositeStandardIntertwining DynamicCommonLeviComposition DynamicCommonLeviCompact
open ActualCommonLeviTensor ActualCommonLeviCompactTensor ActualCommonLeviV3 ActualCommonLeviIwasawa
open DynamicCommonLeviContinuation UnramifiedOperatorFamily DynamicOppositeCanonicalScalar

attribute [local instance]
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningIsAffine
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningT2Space
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningIsTopologicalGroup
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningT2Space2
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningLocallyCompactSpace
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningNonarchimedeanGroup
  DynamicOppositeStandardIntertwining.centralizerClosedImmersion
  DynamicOppositeStandardIntertwining.centralizerAffine
  DynamicOppositeCanonicalScalar.centralizerFiniteType
  DynamicOppositeStandardIntertwining.dynamicOppositeStandardIntertwiningTopologicalSpace2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarSecondCountableTopology2
  DynamicCommonLeviContinuation.radicalMeasurable DynamicCommonLeviContinuation.radicalBorel
  DynamicCommonLeviContinuation.intersectionMeasurable DynamicCommonLeviContinuation.intersectionBorel
  DynamicCommonLeviContinuation.quotientMeasurable DynamicCommonLeviContinuation.quotientBorel
  ActualCommonLeviV3.ambientMeasurable ActualCommonLeviV3.ambientBorel
  ActualCommonLeviV3.leviMeasurable ActualCommonLeviV3.leviBorel
  ActualCommonLeviV3.leviLocallyCompact ActualCommonLeviV3.parabolicLocallyCompact

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) (hG : IsConnectedReductive G)
  (A : SmoothRep.{0, u, uV} ℂ (levi χ))
  (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))

local notation "X" => unramifiedCharacters (normCharacters χ)
local notation "Xu" => unitaryUnramifiedCharacters (normCharacters χ)
local notation "Reg" => unramifiedRegularFunctions (normCharacters χ)
local notation "Vertex" => GalleryVertex χ
local notation "d[" x "]" => commonDecomposition χ (x : Vertex).val (x : Vertex).property
local notation "hδ[" x "]" => radical_unimodular (x : Vertex).val hG
local notation "hU[" x "]" => radical_isClosed (x : Vertex).val
local notation "V[" x "]" => CompactInductionPicture d[x] K A
local notation "D[" x "]" => CompactInductionPicture d[x] K A.contragredient
local notation "I[" x "," z "]" => UnramifiedLeviInduction d[x] hU[x]
  (leviNormCharacters χ) (parameterTransport χ z) A

variable (hPK : ∀ (x : Vertex) (g : rationalPoints G), ∃ p : parabolic x.val, ∃ k : K,
  g = (p : rationalPoints G) * (k : rationalPoints G))
  (p : CompactContinuationSystem χ hG A K hK hPK)
  (y θ x : Vertex)

local notation "Datum[" v "," w "]" => GenericComparisonData χ hG K hK
  (v : Vertex).val (v : Vertex).property (hPK v) (w : Vertex).val (w : Vertex).property (hPK w) A

variable (g₀ : Datum[y,θ]) (g₁ : Datum[x,y])

local notation "Locus[" d "," v "," w "]" => genericLocus χ hG K hK (v : Vertex).val
  (v : Vertex).property (hPK v) (w : Vertex).val (w : Vertex).property (hPK w) A (d).forward (d).reverse
local notation "J[" v "," w "," z "]" => compactContinuationValue χ hG A K hK hPK p v w z
local notation "P" => (p θ x).presentation
local notation "Q" => (g₀).reverse.presentation
local notation "Qv[" z "]" => ((Q).denominator.val ((z : X)⁻¹))⁻¹ • (Q).numerator ((z : X)⁻¹)

variable (C : Subgroup (levi χ)) [C.Normal] (hC : C ≤ Subgroup.center (levi χ))
  [MeasurableSpace (levi χ ⧸ C)] [BorelSpace (levi χ ⧸ C)]
  (mq : Measure (levi χ ⧸ C)) [mq.IsHaarMeasure] [mq.IsInvInvariant]
  (hsq : IsSquareIntegrableModCentralSubgroup C hC A.representation mq)
  (hi : A.representation.IsIrreducible) (b : InvariantPositiveForm A.representation)

local notation "m[" x "]" => compactNormModel χ hG A K hK (x : Vertex).val (x : Vertex).property (hPK x) b
local notation "dm[" x "]" => compactNormModel χ hG A.contragredient K hK (x : Vertex).val
  (x : Vertex).property (hPK x) (dualInvariantForm b (compactOpenCofinal_of_nonarchimedean (levi χ)) hsq.1)
local notation "e" => TensorProduct.congr (m[x]) (dm[y])

/-- The polynomial numerator of a regular scalar ratio times the tensor of
actual compact operators, with the reverse dual at the inverse parameter. -/
def galleryWeightedNumerator (a : Reg) (z : X) :
    (V[θ] ⊗[ℂ] D[θ]) →ₗ[ℂ] (V[x] ⊗[ℂ] D[y]) :=
  a.val z • TensorProduct.map ((P).numerator z) ((Q).numerator z⁻¹)

/-- The product of the three prescribed denominators. -/
def galleryWeightedDenominator (d : Reg) : Reg :=
  d * ((P).denominator * unramifiedRegularInversion (normCharacters χ) (Q).denominator)

local notation "N[" a "]" => galleryWeightedNumerator χ hG A K hK hPK p y θ x g₀ a
local notation "B[" d "]" => galleryWeightedDenominator χ hG A K hK hPK p y θ x g₀ d
local notation "W[" a "," d "," z "]" => ((a).val z / (d).val z) • TensorProduct.map (J[θ,x,z]) (Qv[z])

/-- The displayed numerator has a finite Laurent expansion on each input. -/
theorem galleryWeightedNumerator_polynomial (a : Reg) :
    IsPolynomialOperatorOn Set.univ (fun z => N[a] z.val) := by
  have hQ : IsPolynomialOperatorOn Set.univ (fun z => (Q).numerator (z.val : X)⁻¹) :=
    fun v => ((Q).polynomial v).inversion
  exact fun v => (((P).polynomial.tensor hQ) v).regular_smul a

/-- The numerator clears the mixed tensor on the common denominator locus. -/
theorem galleryWeightedNumerator_clears (a d : Reg) (z : X) (hd : d.val z ≠ 0)
    (hP : z ∈ (p θ x).regularRegion) (hQ : z⁻¹ ∈ (g₀).reverse.regularRegion) :
    N[a] z = (B[d]).val z • W[a,d,z] := by
  let pz := (P).denominator.val z
  let qz := (Q).denominator.val z⁻¹
  have hpz : pz ≠ 0 := hP
  have hqz : qz ≠ 0 := hQ
  have h : a.val z = (d.val z * (pz * qz)) * ((a.val z / d.val z) * (qz⁻¹ * pz⁻¹)) := by
    field_simp [hd, hpz, hqz]
  change a.val z • TensorProduct.map ((P).numerator z) ((Q).numerator z⁻¹) =
    (d.val z * (pz * qz)) • ((a.val z / d.val z) •
      TensorProduct.map (pz⁻¹ • (P).numerator z) (qz⁻¹ • (Q).numerator z⁻¹))
  simp only [TensorProduct.map_smul_left, TensorProduct.map_smul_right, smul_smul]
  exact congrArg (fun u : ℂ => u • TensorProduct.map ((P).numerator z) ((Q).numerator z⁻¹)) h

set_option backward.isDefEq.respectTransparency.types false in
private theorem forward_generic_eq (v w : Vertex) (d : Datum[v,w])
    (z : Locus[d,v,w]) (hr : z.val ∈ (p v w).regularRegion) [Nontrivial A] :
    (d).forward.presentation.continuedOperator ⟨z.val, z.property.choose.1⟩ = J[v,w,z.val] := by
  have hi₀ := ((Langlands.isIrreducible_iff_of_equiv
    (normalizedInductionLeviEquiv d[v] hU[v] hδ[v] (twistObject χ z.val A))).mp ((d).irreducible z).1)
  have hi₁ := ((Langlands.isIrreducible_iff_of_equiv
    (normalizedInductionLeviEquiv d[w] hU[w] hδ[w] (twistObject χ z.val A))).mp ((d).irreducible z).2)
  exact continuedPair_eq_on_irreducible χ hG A K hK v.val w.val v.property w.property
    (hPK v) (hPK w) z.val (d).forward z.property.choose.1 hi₀ hi₁ (p v w) hr

-- The hypotheses are the regular comparisons used by the estimate.
variable (U : Set X) (a d : Reg) (κ : ℂ)
  (hU : ∀ z ∈ U, z ∈ Locus[g₀,y,θ] ∧ z ∈ Locus[g₁,x,y] ∧
    z ∈ (p y θ).regularRegion ∧ z ∈ (p θ x).regularRegion ∧
    z ∈ (p y x).regularRegion ∧ z ∈ (p x y).regularRegion ∧ d.val z ≠ 0 ∧
    ∃ j : ℂ, (J[x,y,z]).comp (J[y,x,z]) = j • LinearMap.id ∧ (a.val z / d.val z) * j = κ)

local notation "Eu" => ((unitaryParameter χ) ⁻¹' U : Set Xu)

include hi hU in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 5500000 in
private theorem galleryWeightedValue_bound {Tc : CommGroupScheme (Spec (CommRingCat.of F))}
    {sc : Tc.toGrp ⟶ parameterScheme χ} (hs : IsSplitComponent sc)
    (hd : IsDistanceAdditive y.val θ.val x.val) [Nontrivial A] :
    ∀ t : (V[θ] ⊗[ℂ] D[θ]), ∃ c : ℝ, 0 ≤ c ∧ ∀ z : Eu,
      ‖(e) (W[a,d,unitaryParameter χ z.val] t)‖ ≤ c := by
  obtain ⟨c, _, hcomp⟩ := exists_compactContinuationValue_comp_smul χ hG A K hK hPK p
    hs y θ x hd hi hsq.1
  obtain ⟨B, hB, hBv⟩ := exists_uniform_compactForward_inverse_bound χ hG A K hK
    x.val x.property (hPK x) b y.val y.property (hPK y) (g₁).forward (g₁).reverse hsq.1
  refine exists_uniform_tensor_bound_of_tmul (fun z : Eu => (e).toLinearMap.comp
    (W[a,d,unitaryParameter χ z.val])) ?_
  intro v ℓ
  refine ⟨(B * ‖(c : ℂ) * κ‖) * (‖m[θ] v‖ * ‖dm[θ] ℓ‖),
    mul_nonneg (mul_nonneg hB (norm_nonneg _)) (mul_nonneg (norm_nonneg _) (norm_nonneg _)), ?_⟩
  intro z
  let w := unitaryParameter χ z.val
  obtain ⟨h₀, h₁, hf, ht, hs', hr, _, j, hj, hw⟩ := hU w z.property
  let w₀ : Locus[g₀,y,θ] := ⟨w, h₀⟩
  let w₁ : Locus[g₁,x,y] := ⟨w, h₁⟩
  have hFr := h₀.choose.1
  let T₀ := (g₀).forward.presentation.continuedOperator ⟨w, hFr⟩
  have hTb := (forward_bijective_iff_compact χ hG A K hK y.val y.property (hPK y)
    θ.val θ.property (hPK θ) (g₀).forward ⟨w, hFr⟩).mp h₀.choose_spec.1
  let F₀ := LinearEquiv.ofBijective T₀ hTb
  have he₀ : F₀.toLinearMap = J[y,θ,w] :=
    forward_generic_eq χ hG A K hK hPK p y θ g₀ w₀ hf
  have he₁ := forward_generic_eq χ hG A K hK hPK p x y g₁ w₁ hr
  have hc : (J[θ,x,w]).comp F₀.toLinearMap = (c : ℂ) • J[y,x,w] := by
    rw [he₀]
    exact hcomp w hf ht hs'
  have hRi (v' : V[x]) : ‖m[x] v'‖ ≤ B * ‖m[y] (J[x,y,w] v')‖ := by
    rw [← he₁]
    exact hBv z.val h₁ ((g₁).irreducible w₁).1 v'
  have hIso (v' : V[θ]) (ℓ' : D[θ]) :
      ‖m[y] (F₀.symm v')‖ * ‖dm[y] (Qv[w] ℓ')‖ = ‖m[θ] v'‖ * ‖dm[θ] ℓ'‖ :=
    compactComparison_inverse_product_norm χ hG A K hK y.val y.property (hPK y)
      C hC mq hsq hi θ.val θ.property (hPK θ) g₀ b z.val h₀ (F₀.symm v') v' ℓ'
      (F₀.apply_symm_apply v')
  exact weightedTensor_norm_tmul_le (m[θ]) (m[y]) (m[x]) (dm[θ]) (dm[y]) F₀ (Qv[w])
    (J[θ,x,w]) (J[y,x,w]) (J[x,y,w]) (c : ℂ) j (a.val w / d.val w) κ B hc hj hw hRi hIso v ℓ

include hi hU in
set_option backward.isDefEq.respectTransparency.types false in
/-- A scalar times the round trip is constant on a dense unitary locus.
The normalized comparison and the outer inverse estimate then give the
cleared unitary bound for the actual mixed tensor of compact operators. -/
theorem galleryWeightedCompact_hasClearedUnitaryBound {Tc : CommGroupScheme (Spec (CommRingCat.of F))}
    {sc : Tc.toGrp ⟶ parameterScheme χ} (hs : IsSplitComponent sc)
    (hd : IsDistanceAdditive y.val θ.val x.val) [Nontrivial A] (hDense : Dense Eu) :
    HasClearedUnitaryBound (parameterScheme χ) (fun z => (e).toLinearMap.comp (N[a] z)) (B[d]) := by
  apply hasClearedUnitaryBound_of_dense (parameterScheme χ) _
    ((galleryWeightedNumerator_polynomial χ hG A K hK hPK p y θ x g₀ a).postcomp (e).toLinearMap) _
    Eu hDense
  intro t
  obtain ⟨c, hc, hbound⟩ := galleryWeightedValue_bound χ hG A K hK hPK p y θ x g₀ g₁
    C hC mq hsq hi b U a d κ hU hs hd t
  refine ⟨c, hc, fun z hz => ?_⟩
  let w := unitaryParameter χ z
  have h := hU w hz
  have hclr := galleryWeightedNumerator_clears χ hG A K hK hPK p y θ x g₀ a d w
    h.2.2.2.2.2.2.1 h.2.2.2.1 h.1.choose.2
  change ‖(e) (N[a] w t)‖ ≤ _
  rw [hclr, LinearMap.smul_apply, map_smul, norm_smul, mul_comm c]
  exact mul_le_mul_of_nonneg_left (hbound ⟨z, hz⟩) (norm_nonneg _)

end Langlands.Plancherel.DynamicCommonLeviPresentations
