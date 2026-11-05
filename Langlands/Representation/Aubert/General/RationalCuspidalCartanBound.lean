import Langlands.Representation.Aubert.General.CuspidalCartanPairingBound
import Langlands.Representation.Aubert.General.RationalCartanLatticeModel
import Langlands.Representation.Aubert.General.RationalCuspidalCompactRestrictionStatement
import Langlands.Representation.Smooth.SmoothPart.BasicProof

/-! # Coefficient pairing bounds on the actual rational Cartan cover -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.Aubert.General

open RationalPointFamily

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)

/-- Dominant uniformizer translates of a finite centralizer set, for each face. -/
def dominantUniformizerCartanSet (F₀ : Set (rationalPoints G))
    (I : Finset (SimpleRoot i ν)) : Set (rationalPoints G) :=
  {t | ∃ x : cocharacterLattice S, ∃ f ∈ F₀,
    t = uniformizerPowers i (.ofAdd x) * f ∧
      ∀ β ∈ I, 0 ≤ simpleRootPairing i ν β x}

/-- The literal dominant uniformizer cone has a lattice model without an
auxiliary centralizer valuation or a character-evaluation bijectivity premise. -/
theorem isCartanLatticeModel_dominantUniformizer
    (hi : IsMaximalSplitTorus i) (hfinite : (simpleRelativeRoots i ν).Finite)
    (hexists : ∀ I : Finset (SimpleRoot i ν),
      ∃ ζ, IsStandardCocharacter i ν (rootSet i ν I) ζ)
    {K0 : Subgroup (rationalPoints G)} (hbasis : SimultaneousStandardBasisAt i ν K0)
    {F₀ : Set (rationalPoints G)} (hF₀ : F₀.Finite) (hcentral : F₀ ⊆ centralizerPoints i) :
    letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
    IsCartanLatticeModel (levi i ν) (unipotent i ν)
      (dominantUniformizerCartanSet i ν F₀) (uniformizerPowers i) (simpleRootPairing i ν) F₀ := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : TopologicalSpace (rationalPoints G) := rationalPointTopology F G.X
  exact
    { finite_F₀ := hF₀
      exists_rep := fun I => ⟨0, fun t ht => by
        simpa only [dominantUniformizerCartanSet, Set.mem_ofPred_eq, neg_zero] using ht⟩
      e_mem_levi := uniformizerPowers_mem_levi i ν
      F₀_subset_levi := fun I f hf => centralizerPoints_le_levi i ν I (hcentral hf)
      levi_le_normalizer := RationalPointFamily.levi_le_normalizer i ν
      commute_of_pair_eq_zero := fun I x hx m hm =>
        commute_uniformizerPowers i ν hfinite I (hexists I) x hx m hm
      exists_standard := fun I => by
        obtain ⟨ζ, hζ⟩ := hexists I
        exact ⟨ζ, fun β hβ => hζ.2.1 β.1 ((val_mem_rootSet i ν I β).mpr hβ),
          fun β hβ => hζ.2.2 β.1 β.2 fun h' => hβ ((val_mem_rootSet i ν I β).mp h')⟩
      contracts := fun J u hu => uniformizerPowers_conj_mem i ν hi hfinite hexists hbasis J u hu }

section Coefficients

variable [IsAffine G.X.left] [Mono i.hom.hom.left]

local instance canonicalPointTopology : TopologicalSpace (rationalPoints G) :=
  rationalPointTopology F G.X

variable [LocallyCompactSpace (rationalPoints G)] [NonarchimedeanGroup (rationalPoints G)]

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [Mono i.hom.hom.left] in
/-- Proper-standard cuspidality puts every vector in every proper actual
untwisted relation space; the normalizing character does not change the carrier. -/
theorem IsCuspidal.mem_jacquet_relations
    (h : ∀ I, IsSemidirectDecomposition (parabolic i ν I) (levi i ν I) (unipotent i ν I))
    (hU : ∀ I, IsClosed (unipotent i ν I : Set (rationalPoints G)))
    [Fintype (SimpleRoot i ν)] {A : SmoothRep.{0, u, v} ℂ (rationalPoints G)}
    (hA : IsCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) h hU A)
    {J : Finset (SimpleRoot i ν)} (hJ : J ≠ Finset.univ) (w : A) :
    w ∈ Jacquet.relations A.representation (unipotent i ν J) := by
  have hsub : Subsingleton
      (Jacquet.Localization.Coinvariants A.representation (unipotent i ν J) 1) := hA ⟨J, hJ⟩
  have hw : Jacquet.Localization.mk A.representation (unipotent i ν J) 1 w = 0 :=
    hsub.elim _ _
  simpa only [Jacquet.Localization.relations_one] using
    (Jacquet.Localization.mk_eq_zero A.representation (unipotent i ν J) 1 w).mp hw

/-- Each smooth-dual coefficient is bounded on dominant uniformizer translates
of a finite centralizer subset. -/
theorem exists_rational_coefficient_pairing_bound
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hStandard : StandardCocharacterStatement.{u})
    (hRoots : HasRelativeRootSystem i)
    (hU : ∀ I, IsClosed (unipotent i ν I : Set (rationalPoints G)))
    {K0 : Subgroup (rationalPoints G)} (hbasis : SimultaneousStandardBasisAt i ν K0)
    {F₀ : Set (rationalPoints G)} (hF₀ : F₀.Finite) (hcentral : F₀ ⊆ centralizerPoints i) :
    letI := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
    let h := isSemidirectDecomposition_of_standardCocharacterStatement
      i ν hStandard hG hi hν
    ∀ (A : SmoothRep.{0, u, v} ℂ (rationalPoints G)),
      IsCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) h hU A →
      ∀ (ℓ : Module.Dual ℂ A), IsSmoothVector A.representation.dual ℓ → ∀ w : A,
        ∃ B : ℤ, ∀ x : cocharacterLattice S, (∀ β, 0 ≤ simpleRootPairing i ν β x) →
          ∀ f ∈ F₀, matrixCoefficient A.representation ℓ w (uniformizerPowers i (.ofAdd x) * f) ≠ 0 →
            ∀ β, simpleRootPairing i ν β x ≤ B := by
  let := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  let h := isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν
  dsimp only
  intro A hA ℓ hℓ w
  have hexists : ∀ I : Finset (SimpleRoot i ν),
      ∃ ζ, IsStandardCocharacter i ν (rootSet i ν I) ζ := fun I =>
    (hStandard F G hG S i hi ν hν _ (rootSet_subset i ν I)).1
  let hM := isCartanLatticeModel_dominantUniformizer i ν hi
    (hRoots.finite_simpleRelativeRoots i hi.isSplitSubtorus.1 ν) hexists hbasis hF₀ hcentral
  obtain ⟨K, hK⟩ := hℓ
  have hL : ∀ k ∈ K, ∀ z : A, ℓ (A.representation k z) = ℓ z := by
    intro k hk z
    have hh := congrArg (fun f : Module.Dual ℂ A => f z) (hK ⟨k⁻¹, K.inv_mem hk⟩)
    change ℓ (A.representation ((k⁻¹)⁻¹) z) = ℓ z at hh
    simpa only [inv_inv] using hh
  exact hM.exists_coefficient_pairing_bound
    (levi_univ_eq_top i ν hStandard hG hi hν) A.representation K ℓ hL w
    (fun J hJ => IsCuspidal.mem_jacquet_relations i ν h hU hA hJ w)

/-- One pairing bound works after all left and right translates in a compact
set, because its orbits on each smooth vector and smooth dual vector are finite. -/
theorem exists_rational_compact_translate_pairing_bound
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hStandard : StandardCocharacterStatement.{u})
    (hRoots : HasRelativeRootSystem i)
    (hU : ∀ I, IsClosed (unipotent i ν I : Set (rationalPoints G)))
    {K0 : Subgroup (rationalPoints G)} (hbasis : SimultaneousStandardBasisAt i ν K0)
    {F₀ : Set (rationalPoints G)} (hF₀ : F₀.Finite) (hcentral : F₀ ⊆ centralizerPoints i)
    (C : Set (rationalPoints G)) (hC : IsCompact C) :
    letI := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
    let h := isSemidirectDecomposition_of_standardCocharacterStatement
      i ν hStandard hG hi hν
    ∀ (A : SmoothRep.{0, u, v} ℂ (rationalPoints G)),
      IsCuspidal (parabolic i ν) (levi i ν) (unipotent i ν) h hU A →
      ∀ (ℓ : Module.Dual ℂ A), IsSmoothVector A.representation.dual ℓ → ∀ w : A,
        ∃ B : ℤ, ∀ k₁ ∈ C, ∀ k₂ ∈ C, ∀ x : cocharacterLattice S,
          (∀ β, 0 ≤ simpleRootPairing i ν β x) → ∀ f ∈ F₀,
            matrixCoefficient A.representation ℓ w
              (k₁ * uniformizerPowers i (.ofAdd x) * f * k₂) ≠ 0 →
                ∀ β, simpleRootPairing i ν β x ≤ B := by
  let := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  dsimp only
  intro A hA ℓ hℓ w
  let Y : Set A := (fun k => A.representation k w) '' C
  have hY : Y.Finite := JacquetCartanDatum.finite_image_of_isCompact
    A.representation A.isSmooth hC w
  let Z : Set (Module.Dual ℂ A) :=
    (fun k => A.representation.dual k ℓ) '' (Inv.inv '' C)
  have hZ : Z.Finite := by
    let l : smoothVectors A.representation.dual := ⟨ℓ, hℓ⟩
    have hh := JacquetCartanDatum.finite_image_of_isCompact
      (smoothPart A.representation.dual) (isSmooth_smoothPart A.representation.dual)
      (hC.image continuous_inv) l
    refine (hh.image
      (fun z : smoothVectors A.representation.dual => (z : Module.Dual ℂ A))).subset ?_
    rintro _ ⟨k, hk, rfl⟩
    refine ⟨smoothPart A.representation.dual k l, ⟨k, hk, rfl⟩, ?_⟩
    exact Representation.IntertwiningMap.isIntertwining _ _
      (smoothInclusion A.representation.dual) k l
  have hZsmooth : ∀ l ∈ Z, IsSmoothVector A.representation.dual l := by
    rintro _ ⟨k, _, rfl⟩
    exact isSmoothVector_apply k hℓ
  have hbounds : ∀ p : Z × Y, ∃ B : ℤ, ∀ x : cocharacterLattice S,
      (∀ β, 0 ≤ simpleRootPairing i ν β x) → ∀ f ∈ F₀,
        matrixCoefficient A.representation p.1.1 p.2.1 (uniformizerPowers i (.ofAdd x) * f) ≠ 0 →
          ∀ β, simpleRootPairing i ν β x ≤ B := fun p =>
    exists_rational_coefficient_pairing_bound i ν hG hi hν hStandard hRoots hU hbasis hF₀ hcentral
      A hA p.1.1 (hZsmooth p.1.1 p.1.2) p.2.1
  choose b hb using hbounds
  let : Fintype Z := hZ.fintype
  let : Fintype Y := hY.fintype
  obtain ⟨B, hB⟩ := (Set.finite_range b).bddAbove
  refine ⟨B, fun k₁ hk₁ k₂ hk₂ x hx f hf hnonzero β => ?_⟩
  let p : Z × Y :=
    (⟨A.representation.dual k₁⁻¹ ℓ, ⟨k₁⁻¹, ⟨k₁, hk₁, rfl⟩, rfl⟩⟩,
      ⟨A.representation k₂ w, ⟨k₂, hk₂, rfl⟩⟩)
  have hc : matrixCoefficient A.representation p.1.1 p.2.1
      (uniformizerPowers i (.ofAdd x) * f) =
      matrixCoefficient A.representation ℓ w
        (k₁ * uniformizerPowers i (.ofAdd x) * f * k₂) := by
    change ℓ (A.representation ((k₁⁻¹)⁻¹)
      (A.representation (uniformizerPowers i (.ofAdd x) * f) (A.representation k₂ w))) = _
    simp only [inv_inv, matrixCoefficient_apply, map_mul, Module.End.mul_apply]
  exact (hb p x hx f hf (hc.symm ▸ hnonzero) β).trans (hB ⟨p, rfl⟩)

end Coefficients

end Langlands.Aubert.General
