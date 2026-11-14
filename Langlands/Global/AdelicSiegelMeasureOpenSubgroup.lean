import Langlands.Global.AdelicSiegelMeasureReduction
import Langlands.Analysis.Local.OpenCompactFactorizationHaar

/-! # Finite Haar measure of adelic Siegel sets with an open-subgroup Iwasawa input

`siegelProductFiniteMeasureStatement_of_inputs` uses the Iwasawa decomposition
`P(𝔸_F) K = G(𝔸_F)` only to write the Haar measure of right `K`-saturated sets through the
Haar measure of the parabolic part. It is enough that some open subgroup `H₁ ⊇ K` satisfies
`H₁ ⊆ P(𝔸_F) K`: the Siegel set lies in `P(𝔸_F) K ⊆ P(𝔸_F) H₁`, and on the open set
`P(𝔸_F) H₁` the saturated-set formula holds by
`CompactFactorization.exists_measure_inter_mul_eq_of_isOpen`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Set Topology Opposite
open scoped CategoryTheory.MonObj ENNReal NNReal Pointwise

namespace Langlands.Global.AdelicSiegelFactors

open Langlands.GroupScheme AdelicGroupPoints

/-- **Finite Haar measure of Siegel sets, open-subgroup form.** Compactness of unipotent
rational quotients, the modulus formula for the positive torus on `N(𝔸_F)` and compactness of
simple-root boxes imply: for compact factors whose compact subgroup `K` commutes on its
parabolic part with `A_{T₀}`, and an open subgroup `H₁ ⊇ K` with `H₁ ⊆ P(𝔸_F) K`, the weak
Siegel product meets `G(𝔸_F)¹` in a set of finite Haar measure. No Iwasawa decomposition of
all of `G(𝔸_F)` is assumed. -/
theorem measure_weakSiegelProduct_lt_top_of_openSubgroup
    (hU : UnipotentRationalQuotientCompactStatement.{u})
    (hmod : PositiveTorusUnipotentModulusStatement.{u})
    (hbox : SimpleRootBoxCompactStatement.{u})
    (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] (hG : IsConnectedReductive G)
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (ν : cocharacterLattice T)
    (T₀ : CommGroupScheme (Spec (CommRingCat.of F))) (j : T₀ ⟶ T)
    (hsetup : IsSiegelAlgebraicSetup F G T i ν T₀ j)
    (C : CompactFactors F G (Standard.unipotentScheme i ν ∅) (Standard.leviScheme i ν ∅))
    (t : ℝ≥0ˣ)
    (H₁ : Subgroup (AdelicGroupPoints F G)) (hH₁ : IsOpen (H₁ : Set (AdelicGroupPoints F G)))
    (hKH₁ : C.compactSubgroup ≤ H₁)
    (hH₁P : (H₁ : Set (AdelicGroupPoints F G)) ⊆
      Set.range (map F (Standard.parabolicScheme i ν ∅) G (Standard.parabolicHom i ν ∅)) *
        (C.compactSubgroup : Set (AdelicGroupPoints F G)))
    (hcompat : IsPositiveTorusCompatible F G T i ν T₀ j C.compactSubgroup) :
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    (Measure.haar : Measure (normOneSubgroup F G))
      (Subtype.val ⁻¹' weakSiegelProduct F G T i ν
        (canonicalStandardFactors F G T i ν) C T₀ j t) < ∞ := by
  classical
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨hTmax, -, -, -, -, hlevi, -, ⟨D, d, t₀, hd, -, ht₀⟩, -⟩ := id hsetup
  -- the adelic subgroups, read inside `G(𝔸_F)¹`
  have hNH := standardUnipotentImage_le_normOne F G T i ν T₀ j hsetup hU
  have hKH : C.compactSubgroup ≤ normOneSubgroup F G :=
    compactSubgroup_le_normOneSubgroup F G C.compactSubgroup C.compact_compactSubgroup
  have hHc := isClosed_normOneSubgroup F G
  let Q : Subgroup (normOneSubgroup F G) := (standardParabolicImage F G T i ν).subgroupOf _
  let M : Subgroup (normOneSubgroup F G) := (standardLeviImage F G T i ν).subgroupOf _
  let U : Subgroup (normOneSubgroup F G) := (standardUnipotentImage F G T i ν).subgroupOf _
  let K : Subgroup (normOneSubgroup F G) := C.compactSubgroup.subgroupOf _
  have hQ : IsClosed (Q : Set (normOneSubgroup F G)) :=
    (isClosed_standardParabolicImage F G T i ν).preimage continuous_subtype_val
  have hM : IsClosed (M : Set (normOneSubgroup F G)) :=
    (isClosed_standardLeviImage F G T i ν).preimage continuous_subtype_val
  have hUc : IsClosed (U : Set (normOneSubgroup F G)) :=
    (isClosed_standardUnipotentImage F G T i ν).preimage continuous_subtype_val
  have hK : IsCompact (K : Set (normOneSubgroup F G)) :=
    hHc.isClosedEmbedding_subtypeVal.isCompact_preimage C.compact_compactSubgroup
  -- the Levi decomposition `Q = M ⋉ U` with continuous projection
  obtain ⟨f, hfc, hfM, hfid, hfker⟩ := exists_standardLeviPart F G T i ν T₀ j hsetup
  have hfH : ∀ q : Q, f ⟨(q : normOneSubgroup F G), q.2⟩ ∈ normOneSubgroup F G := by
    intro q
    let p : standardParabolicImage F G T i ν := ⟨(q : normOneSubgroup F G), q.2⟩
    have hmem : (f p)⁻¹ * (p : AdelicGroupPoints F G) ∈ standardUnipotentImage F G T i ν := by
      have h := (hfker ((⟨f p, standardLeviImage_le_parabolic F G T i ν (hfM p)⟩ :
        standardParabolicImage F G T i ν)⁻¹ * p)).mp (by
          rw [map_mul, map_inv, hfid (f p) (hfM p), inv_mul_cancel])
      simpa using h
    have h1 : (p : AdelicGroupPoints F G) ∈ normOneSubgroup F G := (q : normOneSubgroup F G).2
    have h2 := (normOneSubgroup F G).mul_mem h1 ((normOneSubgroup F G).inv_mem (hNH hmem))
    simpa using h2
  let ιQ : Q →* standardParabolicImage F G T i ν :=
    ((normOneSubgroup F G).subtype.comp Q.subtype).codRestrict _ (fun q => q.2)
  let fH : Q →* normOneSubgroup F G := (f.comp ιQ).codRestrict _ hfH
  have hMQ : M ≤ Q := fun x hx => standardLeviImage_le_parabolic F G T i ν hx
  have hUQ : U ≤ Q := fun x hx => standardUnipotentImage_le_parabolic F G T i ν hx
  have hfHM : ∀ q, fH q ∈ M := fun q => hfM _
  have hfHid : ∀ m (hm : m ∈ M), fH ⟨m, hMQ hm⟩ = m := fun m hm => Subtype.ext (hfid _ hm)
  have hfHker : ∀ q, fH q = 1 ↔ (q : normOneSubgroup F G) ∈ U := fun q =>
    (show fH q = 1 ↔ f ⟨(q : normOneSubgroup F G), q.2⟩ = 1 from
      ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩).trans (hfker _)
  have hsd := Aubert.General.IsSemidirectDecomposition.of_retraction hMQ hUQ fH hfHM hfHid
    hfHker
  have hfHc : Continuous fH := by
    have : Continuous (fun q : Q => f ⟨(q : normOneSubgroup F G), q.2⟩) :=
      hfc.comp ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
    exact this.subtype_mk _
  have hp := Aubert.General.IsSemidirectDecomposition.continuous_of_retraction_projection
    hMQ hUQ fH hfHM hfHid hfHker hfHc
  -- The saturated-set bound uses factorization inside the open subgroup H₁'.
  have : LocallyCompactSpace Q := hQ.locallyCompactSpace
  let μQ : Measure Q := Measure.haar
  let H₁' : Subgroup (normOneSubgroup F G) := H₁.subgroupOf _
  have hH₁' : IsOpen (H₁' : Set (normOneSubgroup F G)) := hH₁.preimage continuous_subtype_val
  have hKH₁' : K ≤ H₁' := fun x hx => hKH₁ hx
  have hQK : ∀ g ∈ H₁', ∃ q ∈ Q, ∃ k ∈ K, g = q * k := by
    intro g hg₁
    have hg : (g : AdelicGroupPoints F G) ∈
        Set.range (map F (Standard.parabolicScheme i ν ∅) G (Standard.parabolicHom i ν ∅)) *
          (C.compactSubgroup : Set (AdelicGroupPoints F G)) := hH₁P hg₁
    obtain ⟨_, ⟨y, rfl⟩, k, hk, hyk⟩ := hg
    have hyH : map F (Standard.parabolicScheme i ν ∅) G (Standard.parabolicHom i ν ∅) y ∈
        normOneSubgroup F G := by
      have hy : map F (Standard.parabolicScheme i ν ∅) G (Standard.parabolicHom i ν ∅) y =
          (g : AdelicGroupPoints F G) * k⁻¹ := by
        rw [← hyk]
        exact (mul_inv_cancel_right _ _).symm
      rw [hy]
      exact (normOneSubgroup F G).mul_mem g.2 ((normOneSubgroup F G).inv_mem (hKH hk))
    exact ⟨⟨_, hyH⟩, ⟨y, rfl⟩, ⟨k, hKH hk⟩, hk, Subtype.ext hyk.symm⟩
  obtain ⟨c, hc⟩ := CompactFactorization.exists_measure_inter_mul_eq_of_isOpen
    (Measure.haar : Measure (normOneSubgroup F G)) Q hQ K hK H₁' hH₁' hKH₁' hQK μQ
  -- the Haar measure restricted to the open set `Q H₁`
  let s : Set (normOneSubgroup F G) := (Q : Set (normOneSubgroup F G)) * (H₁' : Set _)
  have hs : MeasurableSet s := (hH₁'.mul_left).measurableSet
  let μ' : Measure (normOneSubgroup F G) := (Measure.haar : Measure (normOneSubgroup F G)).restrict s
  have hc' : ∀ S : Set (normOneSubgroup F G), MeasurableSet S → (∀ a ∈ S, ∀ k ∈ K, a * k ∈ S) →
      μ' S ≤ c * μQ ((Subtype.val : Q → normOneSubgroup F G) ⁻¹' S) := by
    intro S hS hsat
    rw [Measure.restrict_apply hS]
    exact (hc S hS hsat).le
  -- the positive torus inside `G(𝔸_F)¹`
  have hT : SubgroupFunctor.range (CommGroupScheme.groupHom j ≫ i) ≤ derivedSubgroup G := by
    rw [← ht₀, ← hd.2]
    intro V x hx
    obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    exact SubgroupFunctor.mem_range.mpr ⟨y ≫ t₀.hom.hom, by
      simp only [Grp.comp_hom_hom, Category.assoc]⟩
  let a := positiveMapNormOneOfDerived F G T i T₀ j hT
  have haM : ∀ x, a.toMonoidHom x ∈ M := fun x =>
    positiveMap_mem_standardLeviImage F G T i ν T₀ j x
  have hacent : ∀ x, ∀ m ∈ M, Commute (a.toMonoidHom x) m := by
    intro x m hm
    have hm' : (m : AdelicGroupPoints F G) ∈ (torusCentralizer i).carrier
        ((algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F (Adeles F)))) := by
      rw [← hlevi, ← standardLeviImage_eq]
      exact hm
    have hm'' : ∀ (V : Over (Spec (CommRingCat.of F)))
        (b : V ⟶ (algSpec (CommRingCat.of F)).obj (op (CommAlgCat.of F (Adeles F))))
        (s : V ⟶ T.X), Commute (b ≫ (m : AdelicGroupPoints F G)) (s ≫ i.hom.hom) := hm'
    have h' : Commute (m : AdelicGroupPoints F G) (positiveMap F G T i T₀ j x) := by
      have h := hm'' _ (𝟙 _) (x.val ≫ (CommGroupScheme.groupHom j).hom.hom)
      rw [Category.id_comp] at h
      convert h using 1
      change x.val ≫ (CommGroupScheme.groupHom j ≫ i).hom.hom = _
      simp only [Grp.comp_hom_hom, Category.assoc]
    exact Subtype.ext h'.symm.eq
  have haK : ∀ k ∈ K, k ∈ Q → ∀ x, Commute k (a.toMonoidHom x) := by
    intro k hk hkQ x
    exact Subtype.ext (hcompat (k : AdelicGroupPoints F G) hk hkQ x).eq
  -- simple roots, the compact box and the modulus
  have hTs : IsSplitTorus T.toGrp := hTmax.1.1
  let : Fintype (simpleRelativeRoots i ν) := (hTs.finite_simpleRelativeRoots i ν).fintype
  let lam : simpleRelativeRoots i ν → PositiveRealTorus.intrinsicSubgroup F T₀ →* ℝ≥0ˣ :=
    fun α => (PositiveRealTorus.normCharacter F T₀ (j ≫ (α : characterLattice T))).toMonoidHom.comp
      (PositiveRealTorus.intrinsicSubgroup F T₀).subtype
  have hboxc : IsCompact (SiegelSetMeasure.dyadicBox lam) := by
    have h := hbox F G hG T i ν T₀ j hsetup 2
    convert h using 1
    ext x
    simp only [SiegelSetMeasure.dyadicBox, Set.mem_ofPred_eq, Subtype.forall]
    exact Iff.rfl
  obtain ⟨e, he, hexp⟩ := exists_simpleRoot_exponents (G := G) i ν j hTs
  have hδ : ∀ x, ∏ α, (lam α x : ℝ≥0) ^ e α ≤
      (HaarModulus.closedNormalizerCharacter U hUc
        ⟨a.toMonoidHom x, hsd.levi_le_normalizer (haM x)⟩ : ℝ≥0) := by
    intro x
    have h1 := Aubert.General.closedNormalizerCharacter_subgroupOf_of_mem
      (normOneSubgroup F G) (standardUnipotentImage F G T i ν) hHc
      (isClosed_standardUnipotentImage F G T i ν) hNH (a.toMonoidHom x)
      (positiveMap_mem_normalizer F G T i ν T₀ j x) (hsd.levi_le_normalizer (haM x))
    have h2 := (hexp x.1).symm.trans (hmod F G hG T i ν T₀ j hsetup x).symm
    exact le_of_eq (h2.trans (congrArg (fun u : ℝ≥0ˣ => (u : ℝ≥0)) h1.symm))
  -- the abstract Siegel-set bound
  have key := SiegelSetMeasure.measure_mul_chamber_mul_lt_top
    μ' hQ hM hUc hK hsd hp μQ c hc'
    (ΩU := Subtype.val ⁻¹'
      (map F (Standard.unipotentScheme i ν ∅) G (Standard.unipotentHom i ν ∅) '' C.omegaN))
    (ΩM := Subtype.val ⁻¹'
      ((fun m : normOneSubgroup F (Standard.leviScheme i ν ∅) =>
        map F (Standard.leviScheme i ν ∅) G (Standard.leviHom i ν ∅) m) '' C.omegaM))
    (hHc.isClosedEmbedding_subtypeVal.isCompact_preimage
      (C.compact_omegaN.image (map F _ G (Standard.unipotentHom i ν ∅)).continuous))
    (by rintro g ⟨n, -, hn⟩; exact ⟨n, hn⟩)
    (hHc.isClosedEmbedding_subtypeVal.isCompact_preimage
      (C.compact_omegaM.image
        ((map F _ G (Standard.leviHom i ν ∅)).continuous.comp continuous_subtype_val)))
    (by rintro g ⟨m, -, hm⟩; exact ⟨(m : AdelicGroupPoints F (Standard.leviScheme i ν ∅)), hm⟩)
    a.toMonoidHom a.continuous haM hacent haK lam hboxc e he hδ (t := (t : ℝ≥0)) t.ne_zero
  refine lt_of_le_of_lt ?_ key
  rw [Measure.restrict_eq_self]
  swap
  · -- the Siegel factors lie in `Q K ⊆ Q H₁`
    rintro _ ⟨_, ⟨_, ⟨u, ⟨n, -, hn⟩, m, ⟨m', -, hm'⟩, rfl⟩, _, ⟨x, -, rfl⟩, rfl⟩, k, hk, rfl⟩
    refine ⟨u * m * a.toMonoidHom x, Q.mul_mem (Q.mul_mem (hUQ ⟨n, hn⟩)
      (hMQ ⟨(m' : AdelicGroupPoints F (Standard.leviScheme i ν ∅)), hm'⟩)) (hMQ (haM x)),
      k, hKH₁' hk, rfl⟩
  refine measure_mono ?_
  intro g hg
  obtain ⟨n, hn, m, hm, x, hx, k, hk, hgeq⟩ :=
    (mem_productSet_iff F G T i ν (canonicalStandardFactors F G T i ν) C T₀ j
      (PositiveRealTorus.weakSimpleRootChamber F T₀ T j G i ν t)
      (g : AdelicGroupPoints F G)).mp hg
  have hnH : map F (Standard.unipotentScheme i ν ∅) G (Standard.unipotentHom i ν ∅) n ∈
      normOneSubgroup F G := hNH ⟨n, rfl⟩
  have hmH : map F (Standard.leviScheme i ν ∅) G (Standard.leviHom i ν ∅) m.1 ∈
      normOneSubgroup F G :=
    map_normOneSubgroup_le F _ G (Standard.leviHom i ν ∅) ⟨m.1, m.2, rfl⟩
  have hgdecomp : g = ⟨_, hnH⟩ * ⟨_, hmH⟩ * a.toMonoidHom x * ⟨k, hKH hk⟩ :=
    Subtype.ext hgeq.symm
  rw [hgdecomp]
  refine Set.mul_mem_mul (Set.mul_mem_mul (Set.mul_mem_mul ⟨n, hn, rfl⟩ ⟨m, hm, rfl⟩)
    ⟨x, ?_, rfl⟩) hk
  intro α
  exact Units.val_le_val.mpr (hx α α.2)

end Langlands.Global.AdelicSiegelFactors
