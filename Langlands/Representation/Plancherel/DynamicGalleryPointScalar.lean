import Langlands.Representation.Plancherel.DynamicContinuedGalleryRoundTrip
import Langlands.Representation.Plancherel.ActualCommonLeviNonvanishing
import Langlands.Representation.Plancherel.ActualCommonLeviV3GenericLocus

/-! # The gallery round-trip product at one irreducible regular parameter -/

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

variable (p : CompactContinuationSystem χ hG A K hK hPK)

local notation "J[" x "," y "]" => (p x y).presentation
local notation "reg[" x "," y "]" => (p x y).regularRegion
local notation "U[" x "," z "]" => UnramifiedLeviInduction
  d[x] hu[x] (leviNormCharacters χ) (parameterTransport χ z) A

local notation "Jc[" x "," y "," z "]" => compactContinuationValue χ hG A K hK hPK p x y z

set_option backward.isDefEq.respectTransparency.types false in
/-- At a parameter regular for all ordered pairs of the five vertices, with
irreducible induced representations at `x` and `y`, the outer and inner
round trips are scalar and their product is the fixed multiple of the
round trip at `θ` given by `exists_gallery_roundTrip_product`. -/
theorem gallery_roundTrip_point_product [Nontrivial A] [DecidableEq Vertex] (θ x y : Vertex)
    (t : ℂ)
    (hprod : ∀ z : X,
      (∀ v ∈ ({θ, θ.opposite, x, x.opposite, y} : Finset Vertex),
        ∀ w ∈ ({θ, θ.opposite, x, x.opposite, y} : Finset Vertex), z ∈ reg[v,w]) →
      Function.Surjective (Jc[y,x,z]) →
      ∀ sθ sx si so : ℂ,
        (Jc[θ.opposite,θ,z]).comp (Jc[θ,θ.opposite,z]) = sθ • LinearMap.id →
        (Jc[x.opposite,x,z]).comp (Jc[x,x.opposite,z]) = sx • LinearMap.id →
        (Jc[x.opposite,y,z]).comp (Jc[y,x.opposite,z]) = si • LinearMap.id →
        (Jc[x,y,z]).comp (Jc[y,x,z]) = so • LinearMap.id →
        so * si = t * sθ)
    (z : X)
    (hAll : ∀ v ∈ ({θ, θ.opposite, x, x.opposite, y} : Finset Vertex),
      ∀ w ∈ ({θ, θ.opposite, x, x.opposite, y} : Finset Vertex), z ∈ reg[v,w])
    (hx : (U[x,z]).IsIrreducible) (hy : (U[y,z]).IsIrreducible) (sθ : ℂ)
    (hθ : (Jc[θ.opposite,θ,z]).comp (Jc[θ,θ.opposite,z]) = sθ • LinearMap.id) :
    ∃ si so : ℂ, (Jc[x.opposite,y,z]).comp (Jc[y,x.opposite,z]) = si • LinearMap.id ∧
      (Jc[x,y,z]).comp (Jc[y,x,z]) = so • LinearMap.id ∧ so * si = t * sθ := by
  have hvx : x ∈ ({θ, θ.opposite, x, x.opposite, y} : Finset Vertex) := by simp
  have hvy : y ∈ ({θ, θ.opposite, x, x.opposite, y} : Finset Vertex) := by simp
  have hvox : x.opposite ∈ ({θ, θ.opposite, x, x.opposite, y} : Finset Vertex) := by simp
  obtain ⟨sx, hsx⟩ := compactContinuationValue_roundTrip_isScalar χ hG A K hK hPK p x x.opposite z
    (hAll x hvx x.opposite hvox) (hAll x.opposite hvox x hvx) hx
  obtain ⟨si, hsi⟩ := compactContinuationValue_roundTrip_isScalar χ hG A K hK hPK p y x.opposite z
    (hAll y hvy x.opposite hvox) (hAll x.opposite hvox y hvy) hy
  obtain ⟨so, hso⟩ := compactContinuationValue_roundTrip_isScalar χ hG A K hK hPK p y x z
    (hAll y hvy x hvx) (hAll x hvx y hvy) hy
  have hsurj : Function.Surjective (Jc[y,x,z]) :=
    ((forward_bijective_iff_compact χ hG A K hK y.val y.property (hPK y) x.val x.property
      (hPK x) (p y x) ⟨z, hAll y hvy x hvx⟩).mp
      (continuedPair_operator_bijective_of_irreducible χ hG K hK y.val y.property (hPK y)
        x.val x.property (hPK x) A (p y x) ⟨z, hAll y hvy x hvx⟩ hy hx)).2
  exact ⟨si, so, hsi, hso, hprod z hAll hsurj sθ sx si so hθ hsx hsi hso⟩

end Langlands.Plancherel.DynamicCommonLeviPresentations
