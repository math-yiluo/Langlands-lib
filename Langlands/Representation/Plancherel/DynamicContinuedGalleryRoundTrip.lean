import Langlands.Representation.Plancherel.DynamicContinuedPairComposition
import Langlands.Representation.Plancherel.ContinuedPairScalarComposition
import Langlands.Representation.Plancherel.ActualCommonLeviV3GenericData
import Langlands.Representation.Plancherel.ActualCommonLeviUnitaryContinuation

/-! # Round trips for a system of continued compact standard operators -/

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
open ActualCommonLeviTensor ActualCommonLeviCompactTensor ActualCommonLeviV3
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
local notation "R" => unramifiedRegularFunctions (normCharacters χ)
local notation "Vertex" => GalleryVertex χ
local notation "Iwasawa[" x "]" => ∀ g : rationalPoints G, ∃ p : parabolic (x : Vertex).val,
  ∃ k : K, g = (p : rationalPoints G) * (k : rationalPoints G)
local notation "V[" x "]" => CompactInductionPicture
  (commonDecomposition χ (x : Vertex).val (x : Vertex).property) K A
local notation "d[" x "]" => commonDecomposition χ (x : Vertex).val (x : Vertex).property
local notation "hu[" x "]" => radical_isClosed (x : Vertex).val
local notation "hp[" x "]" => parabolic_isClosed (x : Vertex).val
local notation "hr[" x "]" => commonProjection_continuous χ (x : Vertex).val (x : Vertex).property
local notation "hδ[" x "]" => radical_unimodular (x : Vertex).val hG

variable (hPK : ∀ x : Vertex, Iwasawa[x])

/-- A continuation of each ordered pair on the specified inducing carrier,
with all quotient measures still those fixed by the common compact. -/
abbrev CompactContinuationSystem :=
  ∀ x y : Vertex, ContinuedPair χ hG K hK x.val x.property (hPK x) y.val y.property (hPK y) A

variable (p : CompactContinuationSystem χ hG A K hK hPK)

local notation "J[" x "," y "]" => (p x y).presentation
local notation "reg[" x "," y "]" => (p x y).regularRegion
local notation "U[" x "," z "]" => UnramifiedLeviInduction
  d[x] hu[x] (leviNormCharacters χ) (parameterTransport χ z) A

/-- A fixed inducing form and admissibility give a system on all ordered pairs. -/
def compactContinuationSystemOfUnitary (hA : A.IsAdmissible)
    (hI : A.representation.IsIrreducible) (b : InvariantPositiveForm A.representation) :
    CompactContinuationSystem χ hG A K hK hPK :=
  fun x y => continuedPairOfUnitarizable χ hG K hK x.val x.property (hPK x)
    y.val y.property (hPK y) A hA (SmoothRep.hasFiniteLength_of_isIrreducible hI) ⟨b⟩

/-- An everywhere-defined rational expression for the compact operator.
On the denominator's regular region this is its actual continued value. -/
def compactContinuationValue (x y : Vertex) (z : X) : V[x] →ₗ[ℂ] V[y] :=
  ((J[x,y]).denominator.val z)⁻¹ • (J[x,y]).numerator z

local notation "Jc[" x "," y "," z "]" => compactContinuationValue χ hG A K hK hPK p x y z

/-- The positive measure comparison for a distance-additive triple. -/
theorem exists_compactContinuationValue_comp_smul {Tc : CommGroupScheme (Spec (CommRingCat.of F))}
    {a : Tc.toGrp ⟶ parameterScheme χ} (ha : IsSplitComponent a) (x y w : Vertex)
    (hd : IsDistanceAdditive x.val y.val w.val) (hirr : A.IsIrreducible) (hadm : A.IsAdmissible) :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ z : X, z ∈ reg[x,y] → z ∈ reg[y,w] → z ∈ reg[x,w] →
      (Jc[y,w,z]).comp (Jc[x,y,z]) = (c : ℂ) • Jc[x,w,z] := by
  obtain ⟨c, hc, he⟩ := exists_continuedPair_comp_smul hG ha K hK A x y w (hPK x) (hPK y)
    (hPK w) (p x y) (p y w) (p x w) hd hirr hadm
  exact ⟨c, hc, fun z h₁ h₂ h₃ => he ⟨z, ⟨⟨h₁, h₂⟩, h₃⟩⟩⟩

local notation "B[" x "," y "]" => fun z : (p x y).region => pairFamily χ K hK
  (x : Vertex).val (x : Vertex).property (y : Vertex).val (y : Vertex).property (p x y).modulus
  A ⟨z.val, (p x y).converges z.property⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- On every regular irreducible fiber the actual round trip is scalar. -/
theorem compactContinuationValue_roundTrip_isScalar (x y : Vertex) (z : X)
    (hxy : z ∈ reg[x,y]) (hyx : z ∈ reg[y,x]) (hi : (U[x,z]).IsIrreducible) :
    ∃ j : ℂ, (Jc[y,x,z]).comp (Jc[x,y,z]) = j • LinearMap.id :=
  continuedInductionComposite_generic_scalar (parameterScheme χ)
    (parameterProjection_continuous χ) (parameterScheme_isConnectedReductive χ hG)
    d[x] hu[x] hδ[x] d[y] hu[y] hδ[y] K hK hp[x] hp[y] (hPK x) (hPK y) hr[x] hr[y]
    (parameterHomeomorph χ) (normCharacters_continuous χ) A (B[x,y]) (B[y,x])
    (J[x,y]) (J[y,x]) (p x y).isOpen_region (p x y).nonempty_region (fun _ h => h)
    (p y x).isOpen_region (p y x).nonempty_region (fun _ h => h) (D := {z})
    (fun _ hz => (Set.mem_singleton_iff.mp hz).symm ▸ hi) ⟨z, rfl, hxy, hyx⟩

/-- The actual compact value of a regular ordered pair is nonzero. -/
theorem compactContinuationValue_ne_zero [Nontrivial A] (x y : Vertex) (z : X)
    (hz : z ∈ reg[x,y]) : Jc[x,y,z] ≠ 0 :=
  continuedPair_continuedOperator_ne_zero χ hG K hK x.val x.property (hPK x)
    y.val y.property (hPK y) A (p x y) ⟨z, hz⟩

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
private theorem isDistanceAdditive_opposite_endpoint (x y : Vertex) :
    IsDistanceAdditive x.val y.val x.opposite.val := by
  have he : radical x.val ⊓ radical x.opposite.val = ⊥ := radical_inf_oppositeRadical x.val
  have hrev : radical x.opposite.val ⊓ oppositeRadical x.opposite.val = ⊥ :=
    radical_inf_oppositeRadical x.opposite.val
  constructor
  · rw [he]
    exact bot_le
  · change radical x.opposite.val ⊓ oppositeRadical x.opposite.val ≤ _
    rw [hrev]
    exact bot_le

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom] in
private theorem isDistanceAdditive_opposite_endpoint_reverse (x y : Vertex) :
    IsDistanceAdditive x.opposite.val y.val x.val := by
  have hs := isDistanceAdditive_opposite_endpoint χ x y
  exact ⟨(inf_comm _ _).trans_le hs.1, (inf_comm _ _).trans_le hs.2⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- The two opposite scalars share a fixed proportionality factor. Four
actual continued composition squares account for their prescribed measures. -/
theorem exists_opposite_roundTrip_scale [Nontrivial A] [DecidableEq Vertex]
    {Tc : CommGroupScheme (Spec (CommRingCat.of F))}
    {a : Tc.toGrp ⟶ parameterScheme χ} (ha : IsSplitComponent a) (x y : Vertex)
    (hirr : A.IsIrreducible) (hadm : A.IsAdmissible) :
    ∃ t : ℝ≥0, 0 < t ∧ ∀ z : X,
      (∀ v ∈ ({x, y, x.opposite, y.opposite} : Finset Vertex),
        ∀ w ∈ ({x, y, x.opposite, y.opposite} : Finset Vertex), z ∈ reg[v,w]) →
      ∀ s₀ s₁ : ℂ,
        (Jc[x.opposite,x,z]).comp (Jc[x,x.opposite,z]) = s₀ • LinearMap.id →
        (Jc[y.opposite,y,z]).comp (Jc[y,y.opposite,z]) = s₁ • LinearMap.id →
        s₁ = (t : ℂ) * s₀ := by
  classical
  let X' := x.opposite
  let Y' := y.opposite
  have hAdd₁ := isDistanceAdditive_opposite_endpoint_reverse χ y x
  have hAdd₂ := isDistanceAdditive_opposite_endpoint χ y X'
  have hAdd₃ := isDistanceAdditive_opposite_endpoint_reverse χ x Y'
  have hAdd₄ := isDistanceAdditive_opposite_endpoint χ x y
  obtain ⟨a₁, ha₁, h₁⟩ := exists_compactContinuationValue_comp_smul χ hG A K hK hPK p
    ha Y' x y hAdd₁ hirr hadm
  obtain ⟨a₂, ha₂, h₂⟩ := exists_compactContinuationValue_comp_smul χ hG A K hK hPK p
    ha y X' Y' hAdd₂ hirr hadm
  obtain ⟨a₃, ha₃, h₃⟩ := exists_compactContinuationValue_comp_smul χ hG A K hK hPK p
    ha X' Y' x hAdd₃ hirr hadm
  obtain ⟨a₄, ha₄, h₄⟩ := exists_compactContinuationValue_comp_smul χ hG A K hK hPK p
    ha x y X' hAdd₄ hirr hadm
  refine ⟨(a₃ * a₄) / (a₁ * a₂), div_pos (mul_pos ha₃ ha₄) (mul_pos ha₁ ha₂), ?_⟩
  intro z hz s₀ s₁ h₀ h₅
  have hreg v w (hv : v ∈ ({x, y, X', Y'} : Finset Vertex))
      (hw : w ∈ ({x, y, X', Y'} : Finset Vertex)) : z ∈ reg[v,w] := hz v hv w hw
  have hx : x ∈ ({x, y, X', Y'} : Finset Vertex) := by simp
  have hy : y ∈ ({x, y, X', Y'} : Finset Vertex) := by simp
  have hx' : X' ∈ ({x, y, X', Y'} : Finset Vertex) := by simp
  have hy' : Y' ∈ ({x, y, X', Y'} : Finset Vertex) := by simp
  have hc := oppositeScalar_mul_of_scaled_composition
    (Jc[x,y,z]) (Jc[Y',x,z]) (Jc[X',Y',z]) (Jc[y,X',z]) (Jc[Y',y,z]) (Jc[y,Y',z])
    (Jc[X',x,z]) (Jc[x,X',z])
    (compactContinuationValue_ne_zero χ hG A K hK hPK p x y z (hreg x y hx hy))
    (h₁ z (hreg Y' x hy' hx) (hreg x y hx hy) (hreg Y' y hy' hy))
    (h₂ z (hreg y X' hy hx') (hreg X' Y' hx' hy') (hreg y Y' hy hy'))
    (h₃ z (hreg X' Y' hx' hy') (hreg Y' x hy' hx) (hreg X' x hx' hx))
    (h₄ z (hreg x y hx hy) (hreg y X' hy hx') (hreg x X' hx hx')) h₀ h₅
  have hne : (a₁ : ℂ) * (a₂ : ℂ) ≠ 0 := mul_ne_zero (by exact_mod_cast ha₁.ne') (by exact_mod_cast ha₂.ne')
  push_cast
  rw [div_mul_eq_mul_div, eq_div_iff hne, mul_comm s₁, mul_assoc]
  simpa only [mul_assoc] using hc

set_option backward.isDefEq.respectTransparency.types false in
/-- The opposite scalar factors through the round trips to the intermediate
parabolic and from there to the opposite one. -/
theorem exists_opposite_roundTrip_product [Nontrivial A] [DecidableEq Vertex]
    {Tc : CommGroupScheme (Spec (CommRingCat.of F))}
    {a : Tc.toGrp ⟶ parameterScheme χ} (ha : IsSplitComponent a) (x y : Vertex)
    (hirr : A.IsIrreducible) (hadm : A.IsAdmissible) :
    ∃ t : ℝ≥0, 0 < t ∧ ∀ z : X,
      (∀ v ∈ ({x, y, x.opposite} : Finset Vertex),
        ∀ w ∈ ({x, y, x.opposite} : Finset Vertex), z ∈ reg[v,w]) →
      ∀ s₀ s₁ s₂ : ℂ,
        (Jc[x.opposite,x,z]).comp (Jc[x,x.opposite,z]) = s₀ • LinearMap.id →
        (Jc[y,x,z]).comp (Jc[x,y,z]) = s₁ • LinearMap.id →
        (Jc[x.opposite,y,z]).comp (Jc[y,x.opposite,z]) = s₂ • LinearMap.id →
        s₁ * s₂ = (t : ℂ) * s₀ := by
  obtain ⟨a₁, ha₁, h₁⟩ := exists_compactContinuationValue_comp_smul χ hG A K hK hPK p
    ha x y x.opposite (isDistanceAdditive_opposite_endpoint χ x y) hirr hadm
  obtain ⟨a₂, ha₂, h₂⟩ := exists_compactContinuationValue_comp_smul χ hG A K hK hPK p
    ha x.opposite y x (isDistanceAdditive_opposite_endpoint_reverse χ x y) hirr hadm
  refine ⟨a₁ * a₂, mul_pos ha₁ ha₂, ?_⟩
  intro z hz s₀ s₁ s₂ h₀ h₃ h₄
  have hx : x ∈ ({x, y, x.opposite} : Finset Vertex) := by simp
  have hy : y ∈ ({x, y, x.opposite} : Finset Vertex) := by simp
  have hx' : x.opposite ∈ ({x, y, x.opposite} : Finset Vertex) := by simp
  obtain ⟨v, hv⟩ := DFunLike.ne_iff.mp
    (compactContinuationValue_ne_zero χ hG A K hK hPK p x y z (hz x hx y hy))
  have hv' : v ≠ 0 := fun e => hv (e.symm ▸ map_zero _)
  let : Nontrivial (V[x]) := ⟨v, 0, hv'⟩
  have h := roundTripScalar_mul_of_scaled_composition
    (Jc[x,y,z]) (Jc[y,x,z]) (Jc[y,x.opposite,z]) (Jc[x.opposite,y,z])
    (Jc[x,x.opposite,z]) (Jc[x.opposite,x,z])
    (h₁ z (hz x hx y hy) (hz y hy x.opposite hx') (hz x hx x.opposite hx'))
    (h₂ z (hz x.opposite hx' y hy) (hz y hy x hx) (hz x.opposite hx' x hx)) h₀ h₃ h₄
  exact h.symm.trans (by push_cast; rfl)

set_option backward.isDefEq.respectTransparency.types false in
/-- The outer round trip and the remaining inner round trip multiply to
the opposite scalar of the specified initial parabolic up to one Haar
factor. -/
theorem exists_gallery_roundTrip_product [Nontrivial A] [DecidableEq Vertex]
    {Tc : CommGroupScheme (Spec (CommRingCat.of F))}
    {a : Tc.toGrp ⟶ parameterScheme χ} (ha : IsSplitComponent a) (θ x y : Vertex)
    (hirr : A.IsIrreducible) (hadm : A.IsAdmissible) :
    ∃ t : ℝ≥0, 0 < t ∧ ∀ z : X,
      (∀ v ∈ ({θ, θ.opposite, x, x.opposite, y} : Finset Vertex),
        ∀ w ∈ ({θ, θ.opposite, x, x.opposite, y} : Finset Vertex), z ∈ reg[v,w]) →
      Function.Surjective (Jc[y,x,z]) →
      ∀ sθ sx si so : ℂ,
        (Jc[θ.opposite,θ,z]).comp (Jc[θ,θ.opposite,z]) = sθ • LinearMap.id →
        (Jc[x.opposite,x,z]).comp (Jc[x,x.opposite,z]) = sx • LinearMap.id →
        (Jc[x.opposite,y,z]).comp (Jc[y,x.opposite,z]) = si • LinearMap.id →
        (Jc[x,y,z]).comp (Jc[y,x,z]) = so • LinearMap.id →
        so * si = (t : ℂ) * sθ := by
  obtain ⟨r, hr, hrp⟩ := exists_opposite_roundTrip_scale χ hG A K hK hPK p ha θ x hirr hadm
  obtain ⟨s, hs, hsp⟩ := exists_opposite_roundTrip_product χ hG A K hK hPK p ha x y hirr hadm
  refine ⟨s * r, mul_pos hs hr, ?_⟩
  intro z hz hsurj sθ sx si so hθ hx hI hO
  have hsub₀ : ({θ, x, θ.opposite, x.opposite} : Finset Vertex) ⊆
      {θ, θ.opposite, x, x.opposite, y} := by simp [Finset.insert_subset_iff]
  have hsub₁ : ({x, y, x.opposite} : Finset Vertex) ⊆ {θ, θ.opposite, x, x.opposite, y} := by
    simp [Finset.insert_subset_iff]
  have h1 := hrp z (fun v hv w hw => hz v (hsub₀ hv) w (hsub₀ hw)) sθ sx hθ hx
  have hO' : (Jc[y,x,z]).comp (Jc[x,y,z]) = so • LinearMap.id := by
    apply LinearMap.ext
    intro w
    obtain ⟨v, rfl⟩ := hsurj w
    have he : Jc[x,y,z] (Jc[y,x,z] v) = so • v := LinearMap.congr_fun hO v
    change Jc[y,x,z] (Jc[x,y,z] (Jc[y,x,z] v)) = so • Jc[y,x,z] v
    rw [he, map_smul]
  have h2 := hsp z (fun v hv w hw => hz v (hsub₁ hv) w (hsub₁ hw)) sx so si hx hO' hI
  rw [h1, ← mul_assoc] at h2
  simpa only [NNReal.coe_mul, Complex.ofReal_mul] using h2

end Langlands.Plancherel.DynamicCommonLeviPresentations
