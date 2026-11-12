import Langlands.BruhatTits.SpecialCompact.MoyPrasadIwahoriProduct
import Langlands.GroupScheme.Rational.CocharacterCentralizerPointDetection
import Langlands.GroupScheme.Rational.RootSupportFiniteness
import Langlands.GroupScheme.Rational.RootProductStatement

/-! # Grouping original Moy–Prasad root coordinates by a standard parabolic -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Set
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building

namespace Langlands.BruhatTits.SpecialCompact

section Finite

variable {α : Type*}

/-- A finite set can be enumerated with a selected part first. -/
theorem exists_fin_enumeration_partition (s t : Set α) (hs : s.Finite) :
    ∃ (m n : ℕ) (a : Fin m → α) (b : Fin n → α),
      Function.Injective (Fin.append a b) ∧
      Set.range (Fin.append a b) = s ∧
      (∀ j, a j ∈ s ∩ t) ∧ (∀ j, b j ∈ s \ t) := by
  classical
  obtain ⟨m, a, hai, har⟩ := (hs.inter_of_left t).fin_param
  obtain ⟨n, b, hbi, hbr⟩ := (show (s \ t).Finite from hs.sdiff).fin_param
  have ha j : a j ∈ s ∩ t := har ▸ Set.mem_range_self j
  have hb j : b j ∈ s \ t := hbr ▸ Set.mem_range_self j
  refine ⟨m, n, a, b, Fin.append_injective_iff.mpr ⟨hai, hbi, ?_⟩, ?_, ha, hb⟩
  · intro j k h
    exact (hb k).2 (h ▸ (ha j).2)
  · ext c
    constructor
    · rintro ⟨j, rfl⟩
      induction j using Fin.addCases with
      | left j => simpa using (ha j).1
      | right j => simpa using (hb j).1
    · intro hc
      by_cases hct : c ∈ t
      · obtain ⟨j, rfl⟩ := (show c ∈ Set.range a from har.symm ▸ ⟨hc, hct⟩)
        exact ⟨Fin.castAdd n j, by simp⟩
      · obtain ⟨j, rfl⟩ := (show c ∈ Set.range b from hbr.symm ▸ ⟨hc, hct⟩)
        exact ⟨Fin.natAdd m j, by simp⟩

end Finite

section Products

variable {H : Type*} [Group H]

/-- Membership of each coordinate puts its ordered product in a subgroup. -/
theorem ofFn_prod_mem_subgroup (K : Subgroup H) {n : ℕ} (v : Fin n → H)
    (hv : ∀ j, v j ∈ K) : (List.ofFn v).prod ∈ K := by
  apply K.list_prod_mem
  simpa only [List.forall_mem_ofFn_iff] using hv

/-- Split an ordered finite product without permuting any factors. -/
theorem ofFn_prod_split {m n : ℕ} (v : Fin (m + n) → H) :
    (List.ofFn v).prod =
      (List.ofFn fun j => v (Fin.castAdd n j)).prod *
        (List.ofFn fun j => v (Fin.natAdd m j)).prod := by
  rw [List.ofFn_add, List.prod_append]
  apply congrArg₂ (· * ·) _ rfl
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext j
  exact congrArg v (Fin.ext rfl)

end Products

section Blocks

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G) (Zf : P.CentralizerFiltration)
    (x : P.Apartment) (nu : cocharacterLattice P.S)
    (J : Set (characterLattice P.S)) (r : NNReal)

/-- Both original factors of a root block lie in the original depth group. -/
theorem filtrationBlock_subset_moyPrasad
    {a : characterLattice P.S} (ha : a ∈ relativeRoots P.i) :
    P.apartment.filtrationBlock x (fun _ => (r : ℝ)) a ⊆ Zf.moyPrasad x r := by
  intro g hg
  apply (le_sup_right : P.apartment.sharpFiltration x (fun _ => (r : ℝ)) ≤
    Zf.moyPrasad x r)
  exact le_iSup (fun b : relativeRoots P.i =>
    Subgroup.closure (P.apartment.filtrationBlock x (fun _ => (r : ℝ)) b)) ⟨a, ha⟩
      (Subgroup.subset_closure hg)

/-- A block whose root vanishes on every standard cocharacter belongs to
the literal standard Levi, including its doubled-root factor. -/
theorem filtrationBlock_subset_standardLevi_of_pairing_eq_zero
    {a : characterLattice P.S}
    (ha : ∀ zeta, IsStandardCocharacter P.i nu J zeta →
      latticePairing P.S a zeta = 0) :
    P.apartment.filtrationBlock x (fun _ => (r : ℝ)) a ⊆
      standardLeviPoints P.i nu J := by
  have hroot (b : characterLattice P.S)
      (hb : ∀ zeta, IsStandardCocharacter P.i nu J zeta →
        latticePairing P.S b zeta = 0) :
      P.apartment.filtration x b r ≤ standardLeviPoints P.i nu J := by
    intro g hg
    rw [mem_standardLevi]
    intro zeta hzeta
    exact RelativeRoot.subgroup_le_dynamicCentralizer_of_pairing_eq_zero
      P.i b zeta (hb zeta hzeta) _
      (P.apartment.filtration_le_rootGroupPoints x b r hg)
  intro g hg
  obtain ⟨v, hv, w, hw, rfl⟩ := P.apartment.mem_filtrationBlock.mp hg
  apply Subgroup.mul_mem _ (hroot a ha hv)
  by_cases h2a : 2 • a ∈ relativeRoots P.i
  · rw [P.apartment.doubleFiltration_of_mem x a r h2a] at hw
    apply hroot (2 • a) _ hw
    intro zeta hzeta
    simp [ha zeta hzeta]
  · rw [P.apartment.doubleFiltration_of_not_mem x a r h2a] at hw
    rw [Subgroup.mem_bot.mp hw]
    exact Subgroup.one_mem _

/-- Each ordinary generator of the selected radical depth group is retained. -/
theorem filtration_le_standardRadicalDepth
    {a : characterLattice P.S}
    (ha : a ∈ positiveRelativeRoots P.i nu \ AddSubmonoid.closure J) :
    P.apartment.filtration x a r ≤
      standardRadicalDepth P.toValuationBuildingData x nu J r := by
  intro g hg
  apply Subgroup.subset_closure
  exact Set.mem_iUnion.mpr ⟨⟨a, ha⟩, hg⟩

/-- A radical root block stays in the same original generated radical
depth group; standard-cocharacter signs also retain a doubled root. -/
theorem filtrationBlock_subset_standardRadicalDepth
    {zeta : cocharacterLattice P.S} (hzeta : IsStandardCocharacter P.i nu J zeta)
    {a : characterLattice P.S}
    (ha : a ∈ positiveRelativeRoots P.i nu \ AddSubmonoid.closure J) :
    P.apartment.filtrationBlock x (fun _ => (r : ℝ)) a ⊆
      standardRadicalDepth P.toValuationBuildingData x nu J r := by
  intro g hg
  obtain ⟨v, hv, w, hw, rfl⟩ := P.apartment.mem_filtrationBlock.mp hg
  apply Subgroup.mul_mem _ (filtration_le_standardRadicalDepth P x nu J r ha hv)
  by_cases h2a : 2 • a ∈ relativeRoots P.i
  · rw [P.apartment.doubleFiltration_of_mem x a r h2a] at hw
    have hpos : 0 < latticePairing P.S a zeta :=
      (hzeta.pairing_pos_iff_not_mem_closure P.i nu ha.1).mpr ha.2
    have h2pos : 2 • a ∈ positiveRelativeRoots P.i nu := by
      refine ⟨h2a, ?_⟩
      simpa only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul, Nat.cast_ofNat] using
        mul_pos (by decide : (0 : ℤ) < 2) ha.1.2
    have h2not : 2 • a ∉ AddSubmonoid.closure J := by
      apply (hzeta.pairing_pos_iff_not_mem_closure P.i nu h2pos).mp
      simpa only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul, Nat.cast_ofNat] using
        mul_pos (by decide : (0 : ℤ) < 2) hpos
    exact filtration_le_standardRadicalDepth P x nu J r ⟨h2pos, h2not⟩ hw
  · rw [P.apartment.doubleFiltration_of_not_mem x a r h2a] at hw
    rw [Subgroup.mem_bot.mp hw]
    exact Subgroup.one_mem _

/-- Negative Levi roots also vanish on every original standard cocharacter. -/
theorem filtrationBlock_subset_standardLevi_of_mem_negative_closure
    {a : characterLattice P.S}
    (ha : a ∈ AddSubmonoid.closure (Neg.neg '' J)) :
    P.apartment.filtrationBlock x (fun _ => (r : ℝ)) a ⊆
      standardLeviPoints P.i nu J := by
  apply filtrationBlock_subset_standardLevi_of_pairing_eq_zero
  intro zeta hzeta
  have hneg := relativeRootNegation F G P.isConnectedReductive P.S P.i
    P.isMaximalSplitTorus
  have heq := (hzeta.neg P.i nu hneg).pairing_eq_zero_of_mem_closure P.i (-nu) ha
  simpa using heq

/-- Every original centralizer-filtration factor belongs to the original
Moy–Prasad group and the literal standard Levi. -/
theorem centralizerFiltration_map_mem_moyPrasad_inf_standardLevi
    (z : Zf.filtration r) :
    rationalPoints.map P.centralizer.j (z : rationalPoints P.centralizer.Z) ∈
      Zf.moyPrasad x r ⊓ standardLeviPoints P.i nu J := by
  constructor
  · exact (le_sup_left : Zf.image r ≤ Zf.moyPrasad x r) ⟨z, z.property, rfl⟩
  · apply torusCentralizer_le_standardLevi P.i nu J (Over.mk (𝟙 _))
    exact P.centralizer.isRepresentedBy.2.le _
      ⟨(z : rationalPoints P.centralizer.Z), rfl⟩

end Blocks

section Coordinates

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G) (Zf : P.CentralizerFiltration)
    (x : P.Apartment) (nu : cocharacterLattice P.S)
    (J : Set (characterLattice P.S)) (r : NNReal)
    {zeta : cocharacterLattice P.S} (hzeta : IsStandardCocharacter P.i nu J zeta)
    {nb nmneg nmpos np : ℕ}
    (abar : Fin nb → characterLattice P.S) (amneg : Fin nmneg → characterLattice P.S)
    (ampos : Fin nmpos → characterLattice P.S) (apos : Fin np → characterLattice P.S)
    (hbar : ∀ j, abar j ∈ positiveRelativeRoots P.i (-nu) \ AddSubmonoid.closure (Neg.neg '' J))
    (hmneg : ∀ j, amneg j ∈ positiveRelativeRoots P.i (-nu) ∩
      (AddSubmonoid.closure (Neg.neg '' J) : Set (characterLattice P.S)))
    (hmpos : ∀ j, ampos j ∈ positiveRelativeRoots P.i nu ∩
      (AddSubmonoid.closure J : Set (characterLattice P.S)))
    (hpos : ∀ j, apos j ∈ positiveRelativeRoots P.i nu \ AddSubmonoid.closure J)

/-- Group the original coordinates, in their original order, into the
opposite radical, literal Moy–Prasad/Levi intersection, and radical. -/
def parabolicMoyPrasadCoordinates
    (p : (∀ j, P.apartment.filtrationBlock x (fun _ => (r : ℝ))
        (Fin.append abar amneg j)) × Zf.filtration r ×
      (∀ j, P.apartment.filtrationBlock x (fun _ => (r : ℝ))
        (Fin.append ampos apos j))) :
    standardRadicalDepth P.toValuationBuildingData x (-nu) (Neg.neg '' J) r ×
      ↥(Zf.moyPrasad x r ⊓ standardLeviPoints P.i nu J) ×
      standardRadicalDepth P.toValuationBuildingData x nu J r := by
  let vb := fun j : Fin nb => (p.1 (Fin.castAdd nmneg j) : rationalPoints G)
  let vmn := fun j : Fin nmneg => (p.1 (Fin.natAdd nb j) : rationalPoints G)
  let vmp := fun j : Fin nmpos => (p.2.2 (Fin.castAdd np j) : rationalPoints G)
  let vp := fun j : Fin np => (p.2.2 (Fin.natAdd nmpos j) : rationalPoints G)
  have hvb j : vb j ∈ P.apartment.filtrationBlock x (fun _ => (r : ℝ)) (abar j) := by
    simpa only [vb, Fin.append_left] using (p.1 (Fin.castAdd nmneg j)).property
  have hvmn j : vmn j ∈ P.apartment.filtrationBlock x (fun _ => (r : ℝ)) (amneg j) := by
    simpa only [vmn, Fin.append_right] using (p.1 (Fin.natAdd nb j)).property
  have hvmp j : vmp j ∈ P.apartment.filtrationBlock x (fun _ => (r : ℝ)) (ampos j) := by
    simpa only [vmp, Fin.append_left] using (p.2.2 (Fin.castAdd np j)).property
  have hvp j : vp j ∈ P.apartment.filtrationBlock x (fun _ => (r : ℝ)) (apos j) := by
    simpa only [vp, Fin.append_right] using (p.2.2 (Fin.natAdd nmpos j)).property
  have hneg := relativeRootNegation F G P.isConnectedReductive P.S P.i
    P.isMaximalSplitTorus
  refine (⟨(List.ofFn vb).prod, ?_⟩,
    ⟨(List.ofFn vmn).prod *
      rationalPoints.map P.centralizer.j (p.2.1 : rationalPoints P.centralizer.Z) *
        (List.ofFn vmp).prod, ?_⟩,
    ⟨(List.ofFn vp).prod, ?_⟩)
  · exact ofFn_prod_mem_subgroup _ vb fun j =>
      filtrationBlock_subset_standardRadicalDepth P x (-nu) (Neg.neg '' J) r
        (hzeta.neg P.i nu hneg) (hbar j) (hvb j)
  · have hmn : (List.ofFn vmn).prod ∈
        Zf.moyPrasad x r ⊓ standardLeviPoints P.i nu J := by
      apply ofFn_prod_mem_subgroup _ vmn
      intro j
      exact ⟨filtrationBlock_subset_moyPrasad P Zf x r (hmneg j).1.1 (hvmn j),
        filtrationBlock_subset_standardLevi_of_mem_negative_closure
          P x nu J r (hmneg j).2 (hvmn j)⟩
    have hmp : (List.ofFn vmp).prod ∈
        Zf.moyPrasad x r ⊓ standardLeviPoints P.i nu J := by
      apply ofFn_prod_mem_subgroup _ vmp
      intro j
      refine ⟨filtrationBlock_subset_moyPrasad P Zf x r (hmpos j).1.1 (hvmp j), ?_⟩
      apply filtrationBlock_subset_standardLevi_of_pairing_eq_zero P x nu J r _ (hvmp j)
      intro z hz
      exact hz.pairing_eq_zero_of_mem_closure P.i nu (hmpos j).2
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hmn
      (centralizerFiltration_map_mem_moyPrasad_inf_standardLevi P Zf x nu J r p.2.1)) hmp
  · exact ofFn_prod_mem_subgroup _ vp fun j =>
      filtrationBlock_subset_standardRadicalDepth P x nu J r hzeta (hpos j) (hvp j)

/-- Regrouping the coordinates leaves their actual product unchanged. -/
theorem parabolicMoyPrasadCoordinates_product
    (p : (∀ j, P.apartment.filtrationBlock x (fun _ => (r : ℝ))
        (Fin.append abar amneg j)) × Zf.filtration r ×
      (∀ j, P.apartment.filtrationBlock x (fun _ => (r : ℝ))
        (Fin.append ampos apos j))) :
    (moyPrasadRadicalDepthProduct P Zf x nu J r
      (parabolicMoyPrasadCoordinates P Zf x nu J r hzeta
        abar amneg ampos apos hbar hmneg hmpos hpos p) : rationalPoints G) =
      P.apartment.orderedFiltrationBlockProduct x (fun _ => (r : ℝ))
        (Fin.append abar amneg) p.1 *
      rationalPoints.map P.centralizer.j (p.2.1 : rationalPoints P.centralizer.Z) *
      P.apartment.orderedFiltrationBlockProduct x (fun _ => (r : ℝ))
        (Fin.append ampos apos) p.2.2 := by
  dsimp [moyPrasadRadicalDepthProduct, orderedSubgroupIntersectionProduct,
    parabolicMoyPrasadCoordinates, KPApartmentData.orderedFiltrationBlockProduct]
  rw [ofFn_prod_split (fun j => (p.1 j : rationalPoints G)),
    ofFn_prod_split (fun j => (p.2.2 j : rationalPoints G))]
  simp only [mul_assoc]

end Coordinates

section Covering

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (P : ParahoricBuildingData G) (Zf : P.CentralizerFiltration)
    (x : P.Apartment) (nu : cocharacterLattice P.S)
    (J : Set (characterLattice P.S)) (r : NNReal)

/-- Covering by all orders of the original root blocks implies covering
by the original generated radicals and the literal Levi intersection. -/
theorem moyPrasadRadicalDepthProduct_surjective_of_ordered_cover
    {zeta : cocharacterLattice P.S} (hzeta : IsStandardCocharacter P.i nu J zeta)
    (hcover : ∀ (nneg npos : ℕ) (aneg : Fin nneg → characterLattice P.S)
      (apos : Fin npos → characterLattice P.S),
      Function.Injective aneg →
      Set.range aneg = RelativeRoot.indivisiblePositiveRoots P.i (-nu) →
      Function.Injective apos →
      Set.range apos = RelativeRoot.indivisiblePositiveRoots P.i nu →
      Set.range (fun p : (∀ j, P.apartment.filtrationBlock x (fun _ => (r : ℝ))
          (aneg j)) × Zf.filtration r ×
        (∀ j, P.apartment.filtrationBlock x (fun _ => (r : ℝ)) (apos j)) =>
          P.apartment.orderedFiltrationBlockProduct x (fun _ => (r : ℝ)) aneg p.1 *
          rationalPoints.map P.centralizer.j (p.2.1 : rationalPoints P.centralizer.Z) *
          P.apartment.orderedFiltrationBlockProduct x (fun _ => (r : ℝ)) apos p.2.2) =
        (Zf.moyPrasad x r : Set (rationalPoints G))) :
    Function.Surjective (moyPrasadRadicalDepthProduct P Zf x nu J r) := by
  classical
  let : Smooth G.X.hom := P.isConnectedReductive.smooth
  have hfin (v : cocharacterLattice P.S) :
      (RelativeRoot.indivisiblePositiveRoots P.i v).Finite :=
    (P.isMaximalSplitTorus.1.1.finite_relativeRoots P.i).subset (fun _ ha => ha.1.1)
  obtain ⟨nb, nmneg, abar, amneg, hbmi, hbmr, hb, hmn⟩ :=
    exists_fin_enumeration_partition (RelativeRoot.indivisiblePositiveRoots P.i (-nu))
      (AddSubmonoid.closure (Neg.neg '' J) : Set (characterLattice P.S))ᶜ (hfin (-nu))
  obtain ⟨nmpos, np, ampos, apos, hmpi, hmpr, hmp, hp⟩ :=
    exists_fin_enumeration_partition (RelativeRoot.indivisiblePositiveRoots P.i nu)
      (AddSubmonoid.closure J : Set (characterLattice P.S)) (hfin nu)
  have hbar j : abar j ∈ positiveRelativeRoots P.i (-nu) \
      AddSubmonoid.closure (Neg.neg '' J) :=
    ⟨⟨(hb j).1.1.1, (hb j).1.2⟩, (hb j).2⟩
  have hmneg j : amneg j ∈ positiveRelativeRoots P.i (-nu) ∩
      (AddSubmonoid.closure (Neg.neg '' J) : Set (characterLattice P.S)) := by
    refine ⟨⟨(hmn j).1.1.1, (hmn j).1.2⟩, ?_⟩
    simpa only [Set.mem_compl_iff, not_not] using (hmn j).2
  have hmpos j : ampos j ∈ positiveRelativeRoots P.i nu ∩
      (AddSubmonoid.closure J : Set (characterLattice P.S)) :=
    ⟨⟨(hmp j).1.1.1, (hmp j).1.2⟩, (hmp j).2⟩
  have hpos j : apos j ∈ positiveRelativeRoots P.i nu \ AddSubmonoid.closure J :=
    ⟨⟨(hp j).1.1.1, (hp j).1.2⟩, (hp j).2⟩
  have hprod := hcover (nb + nmneg) (nmpos + np)
    (Fin.append abar amneg) (Fin.append ampos apos) hbmi hbmr hmpi hmpr
  intro g
  have hg : (g : rationalPoints G) ∈ (Zf.moyPrasad x r : Set (rationalPoints G)) := g.property
  rw [← hprod] at hg
  obtain ⟨p, hpg⟩ := hg
  refine ⟨parabolicMoyPrasadCoordinates P Zf x nu J r hzeta
    abar amneg ampos apos hbar hmneg hmpos hpos p, Subtype.ext ?_⟩
  exact (parabolicMoyPrasadCoordinates_product P Zf x nu J r hzeta
    abar amneg ampos apos hbar hmneg hmpos hpos p).trans hpg

end Covering

end Langlands.BruhatTits.SpecialCompact
