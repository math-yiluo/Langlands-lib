import Langlands.Representation.Plancherel.DynamicRepresentedIntegralOperators
import Langlands.Representation.Plancherel.DynamicCommonLeviGallery

/-! # Integral-normalized operators at the vertices of a dynamic gallery -/

noncomputable section

universe u uV

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel.DynamicCommonLeviPresentations

open Aubert.General Induction Aubert.General.RepresentedParabolic Haar
open DynamicOppositeStandardIntertwining DynamicOppositeCanonicalScalar
open DynamicCommonLeviStructuralComparison DynamicCommonLeviComposition

attribute [local instance]
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsAffine
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarIsTopologicalGroup
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarT2Space2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarLocallyCompactSpace
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup
  DynamicOppositeCanonicalScalar.centralizerClosedImmersion
  DynamicOppositeCanonicalScalar.centralizerAffine
  DynamicOppositeCanonicalScalar.centralizerFiniteType
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarTopologicalSpace2
  DynamicOppositeCanonicalScalar.dynamicOppositeCanonicalScalarNonarchimedeanGroup2
  equalitySubgroupMeasurable equalitySubgroupBorel

variable {F : Type u} [Field F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] {χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G}

/-- The dynamic cocharacters retaining the original literal common centralizer. -/
abbrev GalleryVertex (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G) :=
  {ψ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G // Dynamic.centralizer ψ = Dynamic.centralizer χ}

/-- The opposite vertex retains the same embedded common centralizer. -/
def GalleryVertex.opposite (x : GalleryVertex χ) : GalleryVertex χ :=
  ⟨Dynamic.inverseCocharacter x.val, centralizer_inverseCocharacter_eq χ x.val x.property⟩

variable {T : CommGroupScheme (Spec (CommRingCat.of F))} {a : T.toGrp ⟶ parameterScheme χ}
  (hG : IsConnectedReductive G) (ha : IsSplitComponent a)

/-- Use the fixed split component for all the represented vertices. -/
abbrev galleryVertexData (x : GalleryVertex χ) : ParabolicData χ x.val T a :=
  parabolicData χ x.val hG x.property T a ha

variable [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [LocallyOfFiniteType G.X.hom]
  (K : OpenSubgroup (rationalPoints G)) (hK : IsCompact (K : Set (rationalPoints G)))

local notation "d" => galleryVertexData hG ha
local notation "I" => fun x σ => representedInduction hG (d x) σ
/-- The fixed complement Haar measure for a pair of gallery vertices. -/
def galleryPairHaar (x y : GalleryVertex χ) :
    Measure (representedComplement (d x.opposite) (d y)) :=
  representedPairHaar (d y) (d x.opposite) K hK

instance galleryPairHaar_isHaarMeasure (x y : GalleryVertex χ) :
    (galleryPairHaar hG ha K hK x y).IsHaarMeasure :=
  representedPairHaar_isHaarMeasure (ψ₀ := x.val) (d y) (d x.opposite) K hK

local notation "μpair" => galleryPairHaar hG ha K hK

/-- The fixed represented operator at a `PQ`-regular input. Away from that
locus the total function takes the value zero. -/
def galleryIntegralOperator
    (σ : SmoothRep.{0, u, uV} ℂ (rationalPoints (parameterScheme χ))) (x y : GalleryVertex χ) :
    (I x σ).representation.IntertwiningMap (I y σ).representation := by
  classical
  exact if h : representedIsPQRegular hG (d x) (d y) σ then
    representedIntegralOperator hG (d x) (d y) (d x.opposite) x.property ha (μpair x y) σ h
  else 0

/-- At `PQ`-regular inputs the operator satisfies the specified integral identity. -/
theorem galleryIntegralOperator_spec
    (σ : SmoothRep.{0, u, uV} ℂ (rationalPoints (parameterScheme χ))) (x y : GalleryVertex χ)
    (hPQ : representedIsPQRegular hG (d x) (d y) σ) :
    representedIsIntegralIntertwiner hG (d x) (d y) (d x.opposite) (μpair x y) σ
      (galleryIntegralOperator hG ha K hK σ x y) := by
  unfold galleryIntegralOperator
  rw [dite_eq_left hPQ]
  exact representedIntegralOperator_spec hG (d x) (d y) (d x.opposite) x.property ha (μpair x y) σ hPQ

/-- A single nonzero principal open is `PQ`-regular for all ordered pairs of
vertices in a specified finite set. -/
theorem exists_generic_galleryRegular
    (vertices : Finset (GalleryVertex χ))
    (σ : SmoothRep.{0, u, uV} ℂ (rationalPoints (parameterScheme χ)))
    (hσ : σ.IsIrreducible) (hA : σ.IsAdmissible) :
    ∃ poly : MvPolynomial (Fin (rationalImageRank (parameterScheme χ))) ℂ, poly ≠ 0 ∧
      ∀ z ∈ rationalUnramifiedPrincipalOpen (parameterScheme χ)
        (parameterScheme_isConnectedReductive χ hG) poly,
        ∀ x ∈ vertices, ∀ y ∈ vertices, representedIsPQRegular hG (d x) (d y)
          (σ.twist z.val.toMonoidHom (unramifiedCharacter_isOpen_ker (normCharacters χ) z)) := by
  classical
  choose polys hne hpoly using fun p : GalleryVertex χ × GalleryVertex χ =>
    exists_generic_representedIsPQRegular hG (d p.1) (d p.2) ha σ hσ hA
  let products := vertices ×ˢ vertices
  refine ⟨∏ p ∈ products, polys p, Finset.prod_ne_zero_iff.mpr fun i _ => hne i, ?_⟩
  intro z hZ x hx y hy
  have hz := (mem_rationalUnramifiedPrincipalOpen (parameterScheme χ)
    (parameterScheme_isConnectedReductive χ hG) _ z).mp hZ
  rw [map_prod] at hz
  exact hpoly (x, y) z ((mem_rationalUnramifiedPrincipalOpen (parameterScheme χ)
    (parameterScheme_isConnectedReductive χ hG) _ z).mpr
    (Finset.prod_ne_zero_iff.mp hz (x, y) (Finset.mem_product.mpr ⟨hx, hy⟩)))

/-- The two-step composition at the fixed gallery measures gives a scalar
independent of the inducing representation. -/
theorem exists_galleryIntegralOperator_comp_smul (x y w : GalleryVertex χ)
    (hd : IsDistanceAdditive x.val y.val w.val) :
    ∃ c : ℝ≥0, 0 < c ∧ ∀ (σ : SmoothRep.{0, u, uV} ℂ (rationalPoints (parameterScheme χ))),
      representedIsPQRegular hG (d x) (d y) σ →
      representedIsPQRegular hG (d y) (d w) σ →
      representedIsPQRegular hG (d x) (d w) σ →
      (galleryIntegralOperator hG ha K hK σ y w).comp (galleryIntegralOperator hG ha K hK σ x y) =
        (c : ℂ) • galleryIntegralOperator hG ha K hK σ x w := by
  obtain ⟨c, hc, hcomp⟩ := exists_representedIntegralIntertwiner_comp_smul hG
    (d x) (d y) (d w) (d x.opposite) (d y.opposite) x.property y.property w.property hd ha
    (μpair x y) (μpair y w) (μpair x w)
  refine ⟨c, hc, fun σ hxy hyw hxw => ?_⟩
  exact hcomp σ _ _ _ hxw
    (galleryIntegralOperator_spec hG ha K hK σ x y hxy)
    (galleryIntegralOperator_spec hG ha K hK σ y w hyw)
    (galleryIntegralOperator_spec hG ha K hK σ x w hxw)

set_option maxHeartbeats 600000 in
/-- On a repeated vertex, the fixed Haar measure gives the identity map. -/
theorem galleryIntegralOperator_self
    (σ : SmoothRep.{0, u, uV} ℂ (rationalPoints (parameterScheme χ)))
    (x : GalleryVertex χ) (hPQ : representedIsPQRegular hG (d x) (d x) σ) :
    galleryIntegralOperator hG ha K hK σ x x = Representation.IntertwiningMap.id (I x σ).representation := by
  have hV : representedComplement (d x.opposite) (d x) = ⊥ :=
    (representedComplement_eq (d x.opposite) (d x)).trans
      ((inf_comm _ _).trans (radical_inf_oppositeRadical x.val))
  have h1 (y : representedComplement (d x.opposite) (d x)) : y.val = 1 := by
    exact Subgroup.mem_bot.mp
      ((congrArg (fun V : Subgroup (rationalPoints G) => y.val ∈ V) hV).mp y.property)
  have hset : {y : representedComplement (d x.opposite) (d x) | y.val ∈ K} = Set.univ :=
    Set.eq_univ_of_forall fun y => by
      change y.val ∈ K
      rw [h1]
      exact K.one_mem
  have hmass : (μpair x x) Set.univ = 1 :=
    hset ▸ subgroupCompactOpenHaar_mass K hK _ (representedComplement_isClosed (d x.opposite) (d x))
  have : IsFiniteMeasure (μpair x x) := ⟨hmass.symm ▸ ENNReal.one_lt_top⟩
  refine (existsUnique_representedIntegralOperator hG (d x) (d x) (d x.opposite)
    x.property ha (μpair x x) σ hPQ).unique (galleryIntegralOperator_spec hG ha K hK σ x x hPQ) ?_
  intro f hf ℓ
  let values : representedComplement (d x.opposite) (d x) → ℂ := fun y => ℓ (eval _ _ f y.val)
  let value : ℂ := ℓ (eval _ _ f 1)
  have hconst : values = fun _ => value := funext fun y => congrArg (fun g => ℓ (eval _ _ f g)) (h1 y)
  have hi : Integrable values (μpair x x) := hconst.symm ▸ integrable_const value
  refine ⟨hi, ?_⟩
  change value = ∫ y, values y ∂(μpair x x)
  rw [hconst, integral_const, Measure.real, hmass, ENNReal.toReal_one, one_smul]

end Langlands.Plancherel.DynamicCommonLeviPresentations
