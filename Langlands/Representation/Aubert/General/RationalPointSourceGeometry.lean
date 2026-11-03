import Langlands.Representation.Aubert.General.RationalJacquetGeometricCommon
import Langlands.Representation.Aubert.General.RationalTwistedRootSupport
import Langlands.GroupScheme.Rational.ParabolicPointConjugation
import Langlands.GroupScheme.Rational.StandardLeviRootTransport
import Langlands.GroupScheme.Rational.CocharacterStandardFace
import Langlands.GroupScheme.Dynamic.LeviCocharacterCombination

/-! # Point-Coxeter source intersections from standard-face pairings -/

noncomputable section

open Classical

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Langlands.Aubert.General.RationalPointFamily Langlands.Group.RelativeWeylIndexing

namespace Dynamic

variable {S : Scheme.{u}} {T : CommGroupScheme S} {G : GroupScheme S}

/-- Adding a torus cocharacter that centralizes a point does not change the
conjugation orbit of that point. -/
private theorem orbit_groupHom_add_of_mem_centralizer (i : T.toGrp ⟶ G)
    (xi lam : cocharacterLattice T) {U : Over S} {g : U ⟶ G.X}
    (hg : g ∈ (centralizer (CommGroupScheme.groupHom lam ≫ i)).carrier U) :
    orbit (CommGroupScheme.groupHom (xi + lam) ≫ i) g =
      orbit (CommGroupScheme.groupHom xi ≫ i) g := by
  let a := snd U (Gm S).X ≫ (CommGroupScheme.groupHom lam ≫ i).hom.hom
  let b := snd U (Gm S).X ≫ (CommGroupScheme.groupHom xi ≫ i).hom.hom
  let x := fst U (Gm S).X ≫ g
  have hx : Commute x a := commute_cocharacter_of_mem_centralizer _
    ((centralizer _).comp_mem (fst U (Gm S).X) hg) _
  have hsum : snd U (Gm S).X ≫ (CommGroupScheme.groupHom (xi + lam) ≫ i).hom.hom =
      b * a := by
    rw [Grp.comp_hom_hom, ← Category.assoc, comp_groupHom_add, MonObj.mul_comp]
    rfl
  change (snd U (Gm S).X ≫ (CommGroupScheme.groupHom (xi + lam) ≫ i).hom.hom) * x *
      (snd U (Gm S).X ≫ (CommGroupScheme.groupHom (xi + lam) ≫ i).hom.hom)⁻¹ =
    b * x * b⁻¹
  rw [hsum]
  calc
    b * a * x * (b * a)⁻¹ = b * (a * x * a⁻¹) * b⁻¹ := by group
    _ = b * x * b⁻¹ := by rw [← hx.eq, mul_inv_cancel_right]

/-- On a point centralized by `lam`, the dynamic parabolic conditions of
`xi + lam` and `xi` agree. -/
private theorem mem_parabolic_groupHom_add_iff_of_mem_centralizer (i : T.toGrp ⟶ G)
    (xi lam : cocharacterLattice T) {U : Over S} {g : U ⟶ G.X}
    (hg : g ∈ (centralizer (CommGroupScheme.groupHom lam ≫ i)).carrier U) :
    g ∈ (parabolic (CommGroupScheme.groupHom (xi + lam) ≫ i)).carrier U ↔
      g ∈ (parabolic (CommGroupScheme.groupHom xi ≫ i)).carrier U := by
  simp only [mem_parabolic, IsOrbitExtension, orbit_groupHom_add_of_mem_centralizer i xi lam hg]

/-- On a point centralized by `lam`, the dynamic unipotent conditions of
`xi + lam` and `xi` agree. -/
private theorem mem_unipotent_groupHom_add_iff_of_mem_centralizer (i : T.toGrp ⟶ G)
    (xi lam : cocharacterLattice T) {U : Over S} {g : U ⟶ G.X}
    (hg : g ∈ (centralizer (CommGroupScheme.groupHom lam ≫ i)).carrier U) :
    g ∈ (unipotent (CommGroupScheme.groupHom (xi + lam) ≫ i)).carrier U ↔
      g ∈ (unipotent (CommGroupScheme.groupHom xi ≫ i)).carrier U := by
  simp only [mem_unipotent, HasLimit, IsOrbitExtension,
    orbit_groupHom_add_of_mem_centralizer i xi lam hg]


/-- The same orbit equality also preserves dynamic centralizer membership. -/
private theorem mem_centralizer_groupHom_add_iff_of_mem_centralizer (i : T.toGrp ⟶ G)
    (xi lam : cocharacterLattice T) {U : Over S} {g : U ⟶ G.X}
    (hg : g ∈ (centralizer (CommGroupScheme.groupHom lam ≫ i)).carrier U) :
    g ∈ (centralizer (CommGroupScheme.groupHom (xi + lam) ≫ i)).carrier U ↔
      g ∈ (centralizer (CommGroupScheme.groupHom xi ≫ i)).carrier U := by
  rw [mem_centralizer, mem_centralizer,
    orbit_groupHom_add_of_mem_centralizer i xi lam hg]

end Dynamic

end Langlands.GroupScheme

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme Group.RelativeWeylIndexing

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
  (ν : cocharacterLattice T) [Fintype (SimpleRoot i ν)]
  (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
  {CM : CoxeterMatrix (SimpleRoot i ν)}
  (cs : ActualCoxeterSystem (torusPoints i) CM)

/-- The root-level face condition sufficient for source geometry. It contains
only actual character pairings and finite simple-reflection labels. -/
def PointSourcePairingFaces : Prop :=
  ∀ (I J : Finset (SimpleRoot i ν)) (w : Weyl i), IsMinimal cs I J w →
    ∀ (zeta : cocharacterLattice T), IsStandardCocharacter i ν (rootSet i ν I) zeta →
      ∀ (a : SimpleRoot i ν), a ∈ J →
        0 ≤ latticePairing T (weylCharacterAction i hN hZ w a.1) zeta ∧
          (latticePairing T (weylCharacterAction i hN hZ w a.1) zeta = 0 ↔
            a ∈ simpleImage cs w⁻¹ I ∩ J)

omit [Mono i.hom.hom.left] [Fintype (SimpleRoot i ν)] in
/-- Shifting a cocharacter that is zero on `K` and positive on `J \ K` by a
large multiple of a standard cocharacter for `J` gives a standard cocharacter
for `K`. -/
private theorem IsStandardCocharacter.exists_add_zsmul_of_face
    (hfinite : (simpleRelativeRoots i ν).Finite)
    {J K : Set (characterLattice T)} (hKJ : K ⊆ J) {mu : cocharacterLattice T}
    (hmu : IsStandardCocharacter i ν J mu) (xi : cocharacterLattice T)
    (hK : ∀ α ∈ K, latticePairing T α xi = 0)
    (hJ : ∀ α ∈ J, α ∉ K → 0 < latticePairing T α xi) :
    ∃ m : ℤ, IsStandardCocharacter i ν K (xi + m • mu) := by
  obtain ⟨b, hb⟩ := (hfinite.image (fun α => -latticePairing T α xi)).bddAbove
  let m : ℤ := max b 0 + 1
  have hm : 0 ≤ m := by dsimp [m]; omega
  refine ⟨m, hKJ.trans hmu.1, ?_, ?_⟩
  · intro α hα
    simp only [map_add, map_smul, hK α hα, hmu.2.1 α (hKJ hα), smul_zero, add_zero]
  · intro α hα hαK
    simp only [map_add, map_smul, smul_eq_mul]
    by_cases hαJ : α ∈ J
    · rw [hmu.2.1 α hαJ, mul_zero, add_zero]
      exact hJ α hαJ hαK
    · have hbound : -latticePairing T α xi ≤ b := hb ⟨α, hα, rfl⟩
      have hpos : 0 < latticePairing T α mu := hmu.2.2 α hα hαJ
      have hmul : m ≤ m * latticePairing T α mu := by
        have hle : (1 : ℤ) ≤ latticePairing T α mu := by omega
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hle hm
      dsimp [m] at hmul ⊢
      omega


omit [IsAffineHom G.X.hom] [Mono i.hom.hom.left] in
private theorem pointDynamicParabolic_comap (n : normalizerPoints i)
    (zeta : cocharacterLattice T) :
    (Dynamic.parabolic (CommGroupScheme.groupHom zeta ≫ i)).comap
        (G.innerIso (n : Langlands.GroupScheme.rationalPoints G)).hom =
      Dynamic.parabolic (CommGroupScheme.groupHom
        ((cocharacterAut (normalizingAut i n)).symm zeta) ≫ i) := by
  rw [Dynamic.parabolic_eq_comap_of_iso (CommGroupScheme.groupHom
      ((cocharacterAut (normalizingAut i n)).symm zeta) ≫ i)
      (G.innerIso (n : Langlands.GroupScheme.rationalPoints G)),
    ← groupHom_cocharacterAut_comp, LinearEquiv.apply_symm_apply]

omit [IsAffineHom G.X.hom] [Mono i.hom.hom.left] in
private theorem pointDynamicCentralizer_comap (n : normalizerPoints i)
    (zeta : cocharacterLattice T) :
    (Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i)).comap
        (G.innerIso (n : Langlands.GroupScheme.rationalPoints G)).hom =
      Dynamic.centralizer (CommGroupScheme.groupHom
        ((cocharacterAut (normalizingAut i n)).symm zeta) ≫ i) := by
  rw [Dynamic.centralizer_eq_comap_of_iso (CommGroupScheme.groupHom
      ((cocharacterAut (normalizingAut i n)).symm zeta) ≫ i)
      (G.innerIso (n : Langlands.GroupScheme.rationalPoints G)),
    ← groupHom_cocharacterAut_comp, LinearEquiv.apply_symm_apply]

omit [IsAffineHom G.X.hom] [Mono i.hom.hom.left] in
private theorem pointDynamicUnipotent_comap (n : normalizerPoints i)
    (zeta : cocharacterLattice T) :
    (Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ i)).comap
        (G.innerIso (n : Langlands.GroupScheme.rationalPoints G)).hom =
      Dynamic.unipotent (CommGroupScheme.groupHom
        ((cocharacterAut (normalizingAut i n)).symm zeta) ≫ i) := by
  rw [Dynamic.unipotent_eq_comap_of_iso (CommGroupScheme.groupHom
      ((cocharacterAut (normalizingAut i n)).symm zeta) ≫ i)
      (G.innerIso (n : Langlands.GroupScheme.rationalPoints G)),
    ← groupHom_cocharacterAut_comp, LinearEquiv.apply_symm_apply]

omit [IsAffineHom G.X.hom] in
private theorem pointPairing_inverseTransport
    (n : Group.RelativeWeyl.normalizer (torusPoints i))
    (a : characterLattice T) (zeta : cocharacterLattice T) :
    latticePairing T a ((cocharacterAut
        (normalizingAut i ((normalizerEquiv i hN).symm n))).symm zeta) =
      latticePairing T (weylCharacterAction i hN hZ (QuotientGroup.mk n) a) zeta := by
  rw [weylCharacterAction_point_mk]
  change _ = latticePairing T
    (characterAut (normalizingAut i ((normalizerEquiv i hN).symm n)) a) zeta
  conv_rhs => rw [← (cocharacterAut
    (normalizingAut i ((normalizerEquiv i hN).symm n))).apply_symm_apply zeta]
  exact (latticePairing_characterAut_cocharacterAut _ a _).symm


variable (hFaces : PointSourcePairingFaces i ν hN hZ cs)
  (hStandard : StandardCocharacterStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)

include hFaces hStandard hG hi hν in
/-- A standard cocharacter for the intersection face gives the same three
restricted dynamic conditions as the inverse normalizer transport. -/
theorem pointSourceComparison_of_pairingFaces
    (I J : Finset (SimpleRoot i ν)) (w : Weyl i) (hw : IsMinimal cs I J w)
    (n : Group.RelativeWeyl.normalizer (torusPoints i)) (hn : QuotientGroup.mk n = w)
    (zeta : cocharacterLattice T)
    (hzeta : IsStandardCocharacter i ν (rootSet i ν I) zeta) :
    ∃ eta : cocharacterLattice T,
      IsStandardCocharacter i ν (rootSet i ν (simpleImage cs w⁻¹ I ∩ J)) eta ∧
      ∀ {U : Over (Spec (CommRingCat.of k))} {g : U ⟶ G.X},
        g ∈ (standardLevi i ν (rootSet i ν J)).carrier U →
          (g ∈ ((Dynamic.parabolic (CommGroupScheme.groupHom zeta ≫ i)).comap
              (G.innerIso (n : Langlands.GroupScheme.rationalPoints G)).hom).carrier U ↔
            g ∈ (Dynamic.parabolic (CommGroupScheme.groupHom eta ≫ i)).carrier U) ∧
          (g ∈ ((Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i)).comap
              (G.innerIso (n : Langlands.GroupScheme.rationalPoints G)).hom).carrier U ↔
            g ∈ (Dynamic.centralizer (CommGroupScheme.groupHom eta ≫ i)).carrier U) ∧
          (g ∈ ((Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ i)).comap
              (G.innerIso (n : Langlands.GroupScheme.rationalPoints G)).hom).carrier U ↔
            g ∈ (Dynamic.unipotent (CommGroupScheme.groupHom eta ≫ i)).carrier U) := by
  have hfinite : (simpleRelativeRoots i ν).Finite := Set.finite_coe_iff.mp inferInstance
  obtain ⟨mu, hmu⟩ :=
    (hStandard k G hG T i hi ν hν (rootSet i ν J) (rootSet_subset i ν J)).1
  let ns := (normalizerEquiv i hN).symm n
  let xi := (cocharacterAut (normalizingAut i ns)).symm zeta
  have hxi : ∀ a, latticePairing T a xi =
      latticePairing T (weylCharacterAction i hN hZ w a) zeta := by
    intro a
    rw [← hn]
    exact pointPairing_inverseTransport i hN hZ n a zeta
  have hKJ : rootSet i ν (simpleImage cs w⁻¹ I ∩ J) ⊆ rootSet i ν J :=
    (rootSet_subset_iff i ν _ _).2 Finset.inter_subset_right
  obtain ⟨m, hm⟩ := IsStandardCocharacter.exists_add_zsmul_of_face i ν hfinite hKJ hmu xi
    (by
      rintro _ ⟨a, ha, rfl⟩
      rw [hxi]
      exact ((hFaces I J w hw zeta hzeta a (Finset.mem_inter.mp ha).2).2).mpr ha)
    (by
      rintro _ ⟨a, ha, rfl⟩ hnot
      rw [hxi]
      have haK : a ∉ simpleImage cs w⁻¹ I ∩ J := by
        intro haK
        exact hnot ⟨a, haK, rfl⟩
      obtain ⟨hnonneg, hzero⟩ := hFaces I J w hw zeta hzeta a ha
      exact lt_of_le_of_ne hnonneg (Ne.symm fun hz => haK (hzero.mp hz)))
  refine ⟨xi + m • mu, hm, ?_⟩
  intro U g hg
  have hc : g ∈ (Dynamic.centralizer (CommGroupScheme.groupHom (m • mu) ≫ i)).carrier U :=
    (Dynamic.centralizingCocharacters i g).smul_mem m ((mem_standardLevi i ν).1 hg mu hmu)
  change _ ∧ _ ∧ _
  have hnP := pointDynamicParabolic_comap i ns zeta
  have hnL := pointDynamicCentralizer_comap i ns zeta
  have hnU := pointDynamicUnipotent_comap i ns zeta
  change (Dynamic.parabolic (CommGroupScheme.groupHom zeta ≫ i)).comap
    (G.innerIso (n : Langlands.GroupScheme.rationalPoints G)).hom = _ at hnP
  change (Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i)).comap
    (G.innerIso (n : Langlands.GroupScheme.rationalPoints G)).hom = _ at hnL
  change (Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ i)).comap
    (G.innerIso (n : Langlands.GroupScheme.rationalPoints G)).hom = _ at hnU
  rw [hnP, hnL, hnU]
  exact ⟨(Dynamic.mem_parabolic_groupHom_add_iff_of_mem_centralizer i xi _ hc).symm,
    (Dynamic.mem_centralizer_groupHom_add_iff_of_mem_centralizer i xi _ hc).symm,
    (Dynamic.mem_unipotent_groupHom_add_iff_of_mem_centralizer i xi _ hc).symm⟩

omit [IsAffineHom G.X.hom] in
private theorem inf_eq_of_mem_iff (L A B : SubgroupFunctor G)
    (h : ∀ (U : Over (Spec (CommRingCat.of k))) (g : U ⟶ G.X),
      g ∈ L.carrier U → (g ∈ A.carrier U ↔ g ∈ B.carrier U)) :
    L ⊓ A = L ⊓ B := by
  apply SubgroupFunctor.ext
  intro U
  apply Subgroup.ext
  intro g
  change (g ∈ L.carrier U ∧ g ∈ A.carrier U) ↔ (g ∈ L.carrier U ∧ g ∈ B.carrier U)
  exact and_congr_right (h U g)

include hFaces hStandard hG hi hν in
/-- The face pairing condition and the retained standard-cocharacter statement
give all three source subgroup-functor identities at each actual point lift. -/
theorem pointSourceFunctorIdentities_of_pairingFaces
    (I J : Finset (SimpleRoot i ν)) (w : Weyl i) (hw : IsMinimal cs I J w)
    (n : Group.RelativeWeyl.normalizer (torusPoints i)) (hn : QuotientGroup.mk n = w) :
    let K := simpleImage cs w⁻¹ I ∩ J
    (standardLevi i ν (rootSet i ν J) ⊓
        (standardLevi i ν (rootSet i ν I)).comap
          (G.innerIso (n : Langlands.GroupScheme.rationalPoints G)).hom =
      standardLevi i ν (rootSet i ν J) ⊓ standardLevi i ν (rootSet i ν K)) ∧
    (standardLevi i ν (rootSet i ν J) ⊓
        (standardParabolic i ν (rootSet i ν I)).comap
          (G.innerIso (n : Langlands.GroupScheme.rationalPoints G)).hom =
      standardLevi i ν (rootSet i ν J) ⊓ standardParabolic i ν (rootSet i ν K)) ∧
    (standardLevi i ν (rootSet i ν J) ⊓
        (standardUnipotent i ν (rootSet i ν I)).comap
          (G.innerIso (n : Langlands.GroupScheme.rationalPoints G)).hom =
      standardLevi i ν (rootSet i ν J) ⊓ standardUnipotent i ν (rootSet i ν K)) := by
  dsimp only
  obtain ⟨zeta, hzeta⟩ :=
    (hStandard k G hG T i hi ν hν (rootSet i ν I) (rootSet_subset i ν I)).1
  obtain ⟨eta, heta, hcmp⟩ := pointSourceComparison_of_pairingFaces
    i ν hN hZ cs hFaces hStandard hG hi hν I J w hw n hn zeta hzeta
  obtain ⟨hPI, hLI, hUI⟩ :=
    (hStandard k G hG T i hi ν hν (rootSet i ν I) (rootSet_subset i ν I)).2 zeta hzeta
  obtain ⟨hPK, hLK, hUK⟩ :=
    (hStandard k G hG T i hi ν hν _ (rootSet_subset i ν _)).2 eta heta
  rw [hPI, hLI, hUI, hPK, hLK, hUK]
  exact ⟨inf_eq_of_mem_iff _ _ _ fun _ _ hg => (hcmp hg).2.1,
    inf_eq_of_mem_iff _ _ _ fun _ _ hg => (hcmp hg).1,
    inf_eq_of_mem_iff _ _ _ fun _ _ hg => (hcmp hg).2.2⟩

variable (hInter : StandardLeviIntersectionStatement.{u})

include hFaces hStandard hG hi hν hInter in
/-- Evaluate the three functor identities at the base field and simplify the
intersection with the coarse Levi. This gives the exact structural input to
the actual geometric Jacquet-term comparison. -/
theorem pointSourceIntersectionIdentities_of_pairingFaces :
    PointSourceIntersectionIdentities i ν cs := by
  intro I J w hw n hn
  dsimp only
  let K := simpleImage cs w⁻¹ I ∩ J
  obtain ⟨hL, hP, hU⟩ := pointSourceFunctorIdentities_of_pairingFaces
    i ν hN hZ cs hFaces hStandard hG hi hν I J w hw n hn
  have hLp := congrArg SubgroupFunctor.rationalPoints hL
  have hPp := congrArg SubgroupFunctor.rationalPoints hP
  have hUp := congrArg SubgroupFunctor.rationalPoints hU
  change levi i ν J ⊓
      ((standardLevi i ν (rootSet i ν I)).comap
        (G.innerIso (n : Langlands.GroupScheme.rationalPoints G)).hom).rationalPoints =
    levi i ν J ⊓ levi i ν K at hLp
  change levi i ν J ⊓
      ((standardParabolic i ν (rootSet i ν I)).comap
        (G.innerIso (n : Langlands.GroupScheme.rationalPoints G)).hom).rationalPoints =
    levi i ν J ⊓ parabolic i ν K at hPp
  change levi i ν J ⊓
      ((standardUnipotent i ν (rootSet i ν I)).comap
        (G.innerIso (n : Langlands.GroupScheme.rationalPoints G)).hom).rationalPoints =
    levi i ν J ⊓ unipotent i ν K at hUp
  rw [SubgroupFunctor.rationalPoints_comap_innerIso_hom_eq_map] at hLp hPp hUp
  have hKJ : levi i ν K ≤ levi i ν J :=
    levi_le_of_subset i ν hInter hG hi hν K J Finset.inter_subset_right
  refine ⟨hLp.trans (inf_eq_right.mpr hKJ), ?_, ?_⟩
  · exact (congrArg (fun H => H.subgroupOf (levi i ν J)) hPp).trans
      (Subgroup.inf_subgroupOf_left _ _)
  · exact (congrArg (fun H => H.subgroupOf (levi i ν J)) hUp).trans
      (Subgroup.inf_subgroupOf_left _ _)

variable
  (hLength : RootLengthComparison i ν hN hZ cs)
  (hSimple : PositiveSimpleReflectionComparison i ν hN hZ cs)

include hLength hSimple in
/-- The actual point-Coxeter root comparisons prove the face condition without
a scheme realization or any subgroup identity as an additional premise. -/
theorem pointSourcePairingFaces_of_rootComparisons :
    PointSourcePairingFaces i ν hN hZ cs := by
  intro I J w hw zeta hzeta a ha
  refine ⟨point_pairing_weyl_nonneg_of_mem_closure
    i ν hN hZ cs hLength hzeta hw (AddSubmonoid.subset_closure ⟨a, ha, rfl⟩), ?_⟩
  have he := point_mem_intersectionSubset_iff_pairing_eq_zero
    i ν hN hZ cs hLength hSimple hzeta hw a
  rw [intersectionSubset_eq_simpleImage_inter cs hw] at he
  simp only [Finset.mem_inter] at he ⊢
  exact ⟨fun hz => he.mpr ⟨ha, hz⟩, fun hmem => (he.mp hmem).2⟩

include hLength hSimple hStandard hG hi hν hInter in
/-- The retained point-Coxeter and standard-cocharacter hypotheses give all
three source identities at the exact weak scope used by rational compatibility. -/
theorem pointSourceIntersectionIdentities :
    PointSourceIntersectionIdentities i ν cs :=
  pointSourceIntersectionIdentities_of_pairingFaces i ν hN hZ cs
    (pointSourcePairingFaces_of_rootComparisons i ν hN hZ cs hLength hSimple)
    hStandard hG hi hν hInter

end Langlands.Aubert.General.RationalPointFamily
