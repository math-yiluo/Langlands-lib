import Langlands.Global.AdelicNormOneParabolicQuotientMeasure
import Langlands.Global.AdelicRelativeParabolicDensity

/-! # Relative split Iwasawa measure on the rational parabolic quotient -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory MeasureTheory.Measure Set Topology
open scoped CategoryTheory.MonObj Pointwise

set_option autoImplicit false

namespace Langlands.Global.AdelicGroupPoints.ParabolicIwasawaMeasure

open GroupScheme PositiveRealTorus
open LeftCosetSpace (mk fundamentalDomain fundamentalDomain_unique measurableSet_fundamentalDomain
  haarQuotientMeasure)

variable {F : Type} [Field F] [NumberField F]
  {G P M U : GroupScheme (Spec (CommRingCat.of F))}
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
  [IsAffineHom M.X.hom] [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom] [IsAffine U.X.left]
  (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P)
  [IsClosedImmersion (iU ≫ p).hom.hom.left] (l : M ⟶ P)
  [IsIso (subgroupMultiplication l iU)] (hU : LeviSubgroup.IsGeometricUnipotentRadical iU)
  (a : A.toGrp ⟶ M) (hM : IsConnectedReductive M) (ha : IsSplitComponent a)

local notation "G₁" => normOneSubgroup F G
local notation "H" => ambientNormOneLevi p
local notation "L" => ambientNormOneLevi (l ≫ p)
local notation "N" => AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iU ≫ p))
local notation "B" => relativePositiveSubgroup (l ≫ p) a
local notation "M₁" => normOneSubgroup F M
local notation "Q" => ambientNormOneParabolicImage p
local notation "ΓG" => parabolicRationalNormOneSubgroup p
local notation "ΓP" => relativeLeviRationalSubgroup p
local notation "ΓL" => relativeLeviRationalSubgroup (l ≫ p)
local notation "ΓM" => rationalNormOneSubgroup F M
local notation "ΓN" => AdelicSubgroupPoints.rationalSubgroup F G (SubgroupFunctor.range (iU ≫ p))
local notation "E" => normOneParabolicCoordinates p iU l hU
local notation "EL" => relativeLeviDecomposition (l ≫ p) a hM ha
local notation "rd" => normOneRadicalInclusion p iU hU
local notation "lv" => normOneLeviSection p l
local notation "pr" => normOneLeviProjection p iU l hU
local notation "DN" => fundamentalDomain ΓN
  (AdelicSubgroupPoints.isDiscrete_rationalSubgroup F G (SubgroupFunctor.range (iU ≫ p)))
local notation "DM" => fundamentalDomain ΓM (isDiscrete_rationalNormOneSubgroup F M)

omit [IsAffineHom M.X.hom] in
private theorem project_coordinates (x : N × L) : pr (E x) = x.2 :=
  Subtype.ext (proj_coordinates p iU l hU (x.1, x.2.val))

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsAffineHom M.X.hom] in
private theorem normOnePrincipal_mem_iff {S : GroupScheme (Spec (CommRingCat.of F))}
    (f : S ⟶ G) (x : ambientNormOneLevi f) :
    x ∈ relativeLeviRationalSubgroup f ↔ x.val ∈ rationalSubgroup F S := by
  constructor
  · rintro ⟨y, ⟨r, hr⟩, hy⟩
    exact ⟨r, (congrArg Subtype.val hr).trans (congrArg Subtype.val hy)⟩
  · rintro ⟨r, hr⟩
    exact ⟨rationalNormOne F S r, ⟨r, rfl⟩, Subtype.ext hr⟩

omit [IsAffineHom M.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom] [IsClosedImmersion p.hom.hom.left] in
private theorem section_principal {m : L} (hm : m ∈ ΓL) : lv m ∈ ΓP := by
  rw [normOnePrincipal_mem_iff] at hm ⊢
  obtain ⟨r, hr⟩ := hm
  change map F M P l m.val ∈ rationalSubgroup F P
  rw [← hr, map_rational]
  exact ⟨_, rfl⟩

omit [IsAffineHom M.X.hom] in
private theorem project_principal {x : H} (hx : x ∈ ΓP) : pr x ∈ ΓL := by
  rw [normOnePrincipal_mem_iff] at hx ⊢
  exact proj_mem_rationalSubgroup iU l hU hx

omit [IsAffineHom M.X.hom] in
private theorem parabolicProduct_unique (D : Set L)
    (hD : ∀ m : L, ∃! r : ΓL, r.val * m ∈ D) (x : H) :
    ∃! r : ΓP, r.val * x ∈ E '' (DN ×ˢ D) := by
  have hE (n : N) (m : L) : E (n, m) = rd n * lv m := Subtype.ext rfl
  have hpr (n : N) (m : L) : pr (E (n, m)) = m := project_coordinates p iU l hU (n, m)
  have hsec (m : L) : pr (lv m) = m := by simpa only [hE, map_one, one_mul] using hpr 1 m
  have hleft (u n : N) (m : L) : rd u * E (n, m) = E (u * n, m) := by
    rw [hE, hE, map_mul, mul_assoc]
  obtain ⟨⟨n, m⟩, rfl⟩ := (E).surjective x
  obtain ⟨rL, hrL, uniqueL⟩ := hD m
  let y := lv rL.val * E (n, m)
  let z := (E).symm y
  have hz : E z = y := (E).apply_symm_apply y
  have hz₂ : z.2 = rL.val * m := by
    rw [← project_coordinates p iU l hU z, hz]
    change pr (lv rL.val * E (n, m)) = _
    rw [map_mul, hsec, hpr]
  obtain ⟨rN, hrN, uniqueN⟩ := fundamentalDomain_unique ΓN
    (AdelicSubgroupPoints.isDiscrete_rationalSubgroup F G (SubgroupFunctor.range (iU ≫ p))) z.1
  have hN (u : ΓN) : rd u.val ∈ ΓP := by
    change u.val ∈ (ΓP).comap rd
    rw [normOneRadical_comap_principal p iU hU]
    exact u.property
  let r : ΓP := ⟨rd rN.val * lv rL.val, (ΓP).mul_mem (hN rN) (section_principal p l rL.property)⟩
  have hmove (u : N) : rd u * y = E (u * z.1, z.2) := by
    rw [← hz]
    exact hleft u z.1 z.2
  refine ⟨r, ⟨(rN.val * z.1, z.2), ⟨hrN, hz₂.symm ▸ hrL⟩, ?_⟩, ?_⟩
  · change E (rN.val * z.1, z.2) = (rd rN.val * lv rL.val) * E (n, m)
    rw [mul_assoc]
    exact (hmove rN.val).symm
  · intro δ hδ
    obtain ⟨⟨u, v⟩, ⟨hu, hv⟩, hev⟩ := hδ
    have hv' : v = pr δ.val * m := by
      rw [← hpr u v, hev, map_mul, hpr]
    let rL' : ΓL := ⟨pr δ.val, project_principal p iU l hU δ.property⟩
    have hrL' : rL' = rL := uniqueL rL' (by
      change pr δ.val * m ∈ D
      rw [← hv']
      exact hv)
    have hδP : pr δ.val = rL.val := congrArg Subtype.val hrL'
    let q := δ.val * (lv rL.val)⁻¹
    let w := (E).symm q
    have hw : E w = q := (E).apply_symm_apply q
    have hw₂ : w.2 = 1 := by
      rw [← project_coordinates p iU l hU w, hw]
      change pr (δ.val * (lv rL.val)⁻¹) = 1
      rw [map_mul, map_inv, hδP, hsec, mul_inv_cancel]
    have hw₁ : rd w.1 = q := by rw [← hw, ← show E (w.1, w.2) = E w from rfl, hE, hw₂, map_one, mul_one]
    have hW : w.1 ∈ ΓN := by
      rw [← normOneRadical_comap_principal p iU hU, Subgroup.mem_comap, hw₁]
      exact (ΓP).mul_mem δ.property ((ΓP).inv_mem (section_principal p l rL.property))
    have hrep : δ.val = rd w.1 * lv rL.val := by rw [hw₁]; exact (inv_mul_cancel_right _ _).symm
    have hcoord : E (u, v) = E (w.1 * z.1, z.2) := by
      rw [hev, hrep, mul_assoc]
      exact hmove w.1
    have hfirst : u = w.1 * z.1 := congrArg Prod.fst ((E).injective hcoord)
    have hh : (⟨w.1, hW⟩ : ΓN) = rN := uniqueN _ (by
      change w.1 * z.1 ∈ DN
      rw [← hfirst]
      exact hu)
    have hnorm : w.1 = rN.val := congrArg Subtype.val hh
    apply Subtype.ext
    rw [hrep, hnorm]

private theorem directProductTransversal_unique {S₀ S₁ X : Type*} [Group S₀] [Group S₁] [Group X]
    (e : S₀ × S₁ ≃* X) (Λ : Subgroup S₁) (Γ : Subgroup X)
    (hΓ : ∀ z, e z ∈ Γ ↔ z.1 = 1 ∧ z.2 ∈ Λ)
    (D : Set S₁) (hD : ∀ z : S₁, ∃! s : Λ, s.val * z ∈ D) (m : X) :
    ∃! r : Γ, r.val * m ∈ e '' (Set.univ ×ˢ D) := by
  let S := e '' (Set.univ ×ˢ D)
  change ∃! r : Γ, r.val * m ∈ S
  obtain ⟨⟨b, m₁⟩, rfl⟩ := e.surjective m
  obtain ⟨r, hr, hu⟩ := hD m₁
  let δ : Γ := ⟨e (1, r.val), (hΓ (1, r.val)).mpr ⟨rfl, r.property⟩⟩
  have hmem (q : S₁) : e (1, q) * e (b, m₁) ∈ S ↔ q * m₁ ∈ D := by
    change e (1, q) * e (b, m₁) ∈ e '' (Set.univ ×ˢ D) ↔ _
    rw [← map_mul, e.injective.mem_set_image]
    exact and_iff_right (mem_univ _)
  refine ⟨δ, (hmem r.val).mpr hr, fun s hs => ?_⟩
  let w := e.symm s.val
  have hw : e w = s.val := e.apply_symm_apply _
  have hprincipal := (hΓ w).mp (hw.symm ▸ s.property)
  have hw' : (1, w.2) = w := Prod.ext hprincipal.1.symm rfl
  have he : e (1, w.2) = s.val := (congrArg e hw').trans hw
  let sM : Λ := ⟨w.2, hprincipal.2⟩
  have hEq : sM = r := hu sM ((hmem w.2).mp (by rw [he]; exact hs))
  exact Subtype.ext (he.symm.trans (congrArg (fun q : Λ => e (1, q.val)) hEq))

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsAffine P.X.left]
  [LocallyOfFiniteType P.X.hom] [IsClosedImmersion p.hom.hom.left] in
private theorem relativeLeviProduct_unique (m : L) :
    ∃! r : ΓL, r.val * m ∈ EL '' (Set.univ ×ˢ DM) :=
  directProductTransversal_unique (EL).toMulEquiv ΓM ΓL
    (relativeLeviDecomposition_mem_rational (l ≫ p) a hM ha) DM
    (fundamentalDomain_unique ΓM (isDiscrete_rationalNormOneSubgroup F M)) m

variable {K : Subgroup (AdelicGroupPoints F G)}

/-- Multiply the radical, relative split component, intrinsic norm-one Levi, and compact
coordinates before passing to the rational parabolic quotient. -/
def normOneRelativeParabolicQuotientCoordinates (hKc : IsCompact (K : Set (AdelicGroupPoints F G))) :
    (N × (B × M₁)) × K → LeftCosetSpace ΓG := fun x =>
  normOneParabolicQuotientCoordinates p iU l hU hKc ((x.1.1, EL x.1.2), x.2)

/-- The relative multiplication followed by the rational quotient map is measurable. -/
theorem measurable_normOneRelativeParabolicQuotientCoordinates
    (hKc : IsCompact (K : Set (AdelicGroupPoints F G))) :
    Measurable (normOneRelativeParabolicQuotientCoordinates p iU l hU a hM ha hKc) := by
  let coord (x : (N × (B × M₁)) × K) : N × L := (x.1.1, EL x.1.2)
  have hc : Measurable coord := (measurable_fst.comp measurable_fst).prodMk
    ((EL).continuous.measurable.comp (measurable_snd.comp measurable_fst))
  have hj : Measurable (fun z : N × L => (normOneParabolicImageEquiv p (E z)).val) :=
    measurable_subtype_coe.comp ((normOneParabolicImageEquiv p).continuous.measurable.comp
      (E).continuous.measurable)
  have hk : Measurable (compactToNormOne K hKc) :=
    (continuous_subtype_val.subtype_mk _ : Continuous (fun k : K =>
      (⟨k.val, (compactToNormOne K hKc k).property⟩ : G₁))).measurable
  exact (LeftCosetSpace.measurable_mk _).comp (((hj.comp hc).mul
    (hk.comp measurable_snd)))

/-- The relative split Iwasawa measure before restriction to a particular shell. The radical
and intrinsic Levi measures are restricted to strict principal fundamental domains. -/
def RelativeParabolicQuotientMeasureStatement (hK : IsIwasawaCompact p K) (dn : Measure N) : Prop :=
  ∃ μA : Measure B, μA.IsHaarMeasure ∧ SigmaFinite μA ∧
    haarQuotientMeasure ΓG (isDiscrete_parabolicRationalNormOneSubgroup p) =
      Measure.map (normOneRelativeParabolicQuotientCoordinates p iU l hU a hM ha hK.isCompact)
        (((dn.restrict DN).prod ((μA.withDensity (relativePositiveDensity p l a)).prod
          ((Measure.haar : Measure M₁).restrict DM))).prod
            (compactHaarProbability F G K hK.isCompact))

set_option maxHeartbeats 1200000 in
/-- Choose the compatible parabolic Haar, use the strict product transversals and transport
the weighted Levi factor to split and intrinsic coordinates. -/
theorem relativeParabolicQuotientMeasure
    (hG : IsConnectedReductive G) {χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G}
    (hP : (Dynamic.parabolic χ).IsRepresentedBy p)
    (hN : (Dynamic.unipotent χ).IsRepresentedBy (iU ≫ p))
    (hK : IsIwasawaCompact p K) (dn : Measure N) [dn.IsHaarMeasure] :
    RelativeParabolicQuotientMeasureStatement p iU l hU a hM ha hK dn := by
  let e := normOneParabolicImageEquiv p
  let j := (Q).subtype.comp e.toMonoidHom
  let kIncl := compactToNormOne K hK.isCompact
  let dk := compactHaarProbability F G K hK.isCompact
  let : LocallyCompactSpace N :=
    (AdelicSubgroupPoints.isClosed_adelicPoints_range F G (iU ≫ p)).locallyCompactSpace
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK.isCompact
  obtain ⟨dq, hqHaar, hq⟩ := exists_ambientNormOneIwasawaMeasure p hK
  let dp := dq.map e.symm
  let : dp.IsHaarMeasure := e.symm.isHaarMeasure_map dq
  have he : MeasurePreserving e dp dq :=
    MeasurePreserving.symm e.symm.toHomeomorph.toMeasurableEquiv
      ⟨e.symm.toHomeomorph.continuous.measurable, rfl⟩
  have hj : Measurable j := continuous_subtype_val.measurable.comp he.measurable
  have hk : Measurable kIncl :=
    (continuous_subtype_val.subtype_mk _ : Continuous (fun k : K =>
      (⟨k.val, (kIncl k).property⟩ : G₁))).measurable
  have hpush : Measure.map (fun x : H × K => j x.1 * kIncl x.2) (dp.prod dk) =
      (Measure.haar : Measure G₁) := by
    let mult : Q × K → G₁ := fun x => x.1.val * kIncl x.2
    have hm : Measurable mult := (continuous_subtype_val.measurable.comp measurable_fst).mul
      (hk.comp measurable_snd)
    have hp := he.prod (MeasurePreserving.id dk)
    change Measure.map (mult ∘ Prod.map e id) (dp.prod dk) = _
    rw [← Measure.map_map hm hp.measurable, hp.map_eq]
    exact hq
  have hΓ : (ΓP).map j = ΓG := by
    rw [relativeLeviRationalSubgroup, Subgroup.map_map, parabolicRationalNormOneSubgroup]
    rfl
  obtain ⟨dm, hdm, hm⟩ := exists_normOneParabolicHaarProduct p iU l hU dn dp
  let : dm.IsHaarMeasure := hdm
  obtain ⟨μA, hμA, hsf, hL⟩ := relativeParabolicDensity p iU l hU a hM ha hG hP hN dm
  refine ⟨μA, hμA, hsf, ?_⟩
  let S := EL '' (Set.univ ×ˢ DM)
  let D := E '' (DN ×ˢ S)
  have hS : MeasurableSet S := (EL).toHomeomorph.toMeasurableEquiv.measurableEmbedding.measurableSet_image'
    (MeasurableSet.univ.prod (measurableSet_fundamentalDomain _ _))
  have hD : MeasurableSet D := (E).toMeasurableEquiv.measurableEmbedding.measurableSet_image'
    ((measurableSet_fundamentalDomain _ _).prod hS)
  have hu := LeftCosetSpace.discreteQuotientMeasure_map_mul_prod j
    (Subtype.val_injective.comp e.injective) hj kIncl hk ΓP ΓG
    (isDiscrete_parabolicRationalNormOneSubgroup p) Measure.haar dp dk hΓ hpush hD
    (parabolicProduct_unique p iU l hU S (relativeLeviProduct_unique p l a hM ha))
  let dM := dm.withDensity (normOneParabolicDensity p iU l hU)
  let dl := (μA.withDensity (relativePositiveDensity p l a)).prod ((Measure.haar : Measure M₁).restrict DM)
  let dN := dn.restrict DN
  let eL : B × M₁ → L := EL
  have heL : Measurable eL := (EL).continuous.measurable
  have hres : dp.restrict D = Measure.map E (dN.prod (dM.restrict S)) :=
    (by
      have h := hm.restrict_image_emb (E).toMeasurableEquiv.measurableEmbedding (DN ×ˢ S)
      rw [← Measure.prod_restrict] at h
      exact h.map_eq.symm)
  have hlevi : dM.restrict S = Measure.map eL dl := (hL DM).map_eq.symm
  let f : H × K → LeftCosetSpace ΓG := fun x => mk ΓG (j x.1 * kIncl x.2)
  have hf : Measurable f := (LeftCosetSpace.measurable_mk _).comp
    ((hj.comp measurable_fst).mul (hk.comp measurable_snd))
  change haarQuotientMeasure ΓG _ = Measure.map f ((dp.restrict D).prod dk) at hu
  have hmap := Measure.map_prod_map (dN.prod (dM.restrict S)) dk
    (E).continuous.measurable (measurable_id (α := K))
  rw [Measure.map_id] at hmap
  rw [hres, hmap, Measure.map_map hf ((E).continuous.measurable.prodMap measurable_id), hlevi] at hu
  have hmapL := Measure.map_prod_map dN dl (measurable_id (α := N)) heL
  rw [Measure.map_id] at hmapL
  rw [hmapL] at hu
  have hh := Measure.map_prod_map (dN.prod dl) dk (measurable_id.prodMap heL)
    (measurable_id (α := K))
  rw [Measure.map_id] at hh
  rw [hh, Measure.map_map (hf.comp ((E).continuous.measurable.prodMap measurable_id))
    ((measurable_id.prodMap heL).prodMap measurable_id)] at hu
  exact hu

end Langlands.Global.AdelicGroupPoints.ParabolicIwasawaMeasure
