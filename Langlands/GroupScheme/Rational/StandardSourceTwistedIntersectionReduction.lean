import Langlands.GroupScheme.Rational.StandardSourceTwistedIntersectionStatement
import Langlands.GroupScheme.Rational.StandardLeviTwistedRootSupport
import Langlands.GroupScheme.Rational.CoxeterStandardCocharacter
import Langlands.GroupScheme.Rational.StandardLeviAnnihilator
import Langlands.GroupScheme.Rational.StandardLeviRootTransport
import Langlands.GroupScheme.Rational.StandardCocharacterReduction
import Langlands.GroupScheme.Rational.RelativeRootNegationStatement
import Langlands.GroupScheme.Rational.CocharacterStandardFace
import Langlands.GroupScheme.Dynamic.LeviCocharacterCombination

/-! # Standard source parabolics and radicals from standard-face comparison -/

noncomputable section

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

end Dynamic

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

section Transport

variable (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] (n : normalizerPoints i)

omit [Mono i.hom.hom.left] in
/-- Inverse conjugation by a normalizer point carries the dynamic parabolic of a
torus cocharacter to that of the inversely transported cocharacter. -/
theorem dynamicParabolic_comap_innerIso (zeta : cocharacterLattice T) :
    (Dynamic.parabolic (CommGroupScheme.groupHom zeta ≫ i)).comap
        (G.innerIso (n : rationalPoints G)).hom =
      Dynamic.parabolic (CommGroupScheme.groupHom
        ((cocharacterAut (normalizingAut i n)).symm zeta) ≫ i) := by
  rw [Dynamic.parabolic_eq_comap_of_iso (CommGroupScheme.groupHom
      ((cocharacterAut (normalizingAut i n)).symm zeta) ≫ i)
      (G.innerIso (n : rationalPoints G)),
    ← groupHom_cocharacterAut_comp, LinearEquiv.apply_symm_apply]

omit [Mono i.hom.hom.left] in
/-- Inverse conjugation by a normalizer point carries the dynamic unipotent
subgroup of a torus cocharacter to that of the inversely transported cocharacter. -/
theorem dynamicUnipotent_comap_innerIso (zeta : cocharacterLattice T) :
    (Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ i)).comap
        (G.innerIso (n : rationalPoints G)).hom =
      Dynamic.unipotent (CommGroupScheme.groupHom
        ((cocharacterAut (normalizingAut i n)).symm zeta) ≫ i) := by
  rw [Dynamic.unipotent_eq_comap_of_iso (CommGroupScheme.groupHom
      ((cocharacterAut (normalizingAut i n)).symm zeta) ≫ i)
      (G.innerIso (n : rationalPoints G)),
    ← groupHom_cocharacterAut_comp, LinearEquiv.apply_symm_apply]

/-- The inversely transported cocharacter pairs with a character as the
original cocharacter pairs with the Weyl-transported character. -/
theorem latticePairing_cocharacterAut_symm (α : characterLattice T)
    (zeta : cocharacterLattice T) :
    latticePairing T α ((cocharacterAut (normalizingAut i n)).symm zeta) =
      latticePairing T (schemeWeylCharacterAction i (QuotientGroup.mk n) α) zeta := by
  rw [schemeWeylCharacterAction_mk]
  change _ = latticePairing T (characterAut (normalizingAut i n) α) zeta
  conv_rhs => rw [← (cocharacterAut (normalizingAut i n)).apply_symm_apply zeta]
  exact (latticePairing_characterAut_cocharacterAut _ α _).symm

end Transport

section Combinatorics

variable [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

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

end Combinatorics

section Twisted

variable {i : T.toGrp ⟶ G} [IsAffineHom G.X.hom] [Mono i.hom.hom.left]
  {ν : cocharacterLattice T} {CM : CoxeterMatrix (SimpleRoot i ν)}
  {cs : CoxeterSystem CM (relativeWeylGroup i)}

/-- For a minimum double-coset representative `w`, a cocharacter pairing with
characters as a standard cocharacter for `I` pairs with their `w`-transports
becomes standard for the intersection subset after a large shift by a standard
cocharacter for `J`. -/
theorem IsRelativeWeylCoxeterRealization.exists_standardCocharacter_intersectionSubset
    (h : IsRelativeWeylCoxeterRealization i ν cs) (hν : IsGenericCocharacter i ν)
    (hfinite : (simpleRelativeRoots i ν).Finite)
    {I J : Finset (SimpleRoot i ν)} {w : relativeWeylGroup i} (hw : IsMinimal cs I J w)
    {zeta mu : cocharacterLattice T}
    (hzeta : IsStandardCocharacter i ν (rootSet i ν I) zeta)
    (hmu : IsStandardCocharacter i ν (rootSet i ν J) mu)
    (xi : cocharacterLattice T)
    (hxi : ∀ α, latticePairing T α xi =
      latticePairing T (schemeWeylCharacterAction i w α) zeta) :
    ∃ m : ℤ, IsStandardCocharacter i ν
      (rootSet i ν (intersectionSubset cs I J w)) (xi + m • mu) := by
  refine hmu.exists_add_zsmul_of_face i ν hfinite
    ((rootSet_subset_iff i ν _ _).2 (intersectionSubset_subset cs I J w)) xi ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩
    rw [hxi]
    exact ((h.mem_intersectionSubset_iff_pairing_eq_zero hν hzeta w a).mp ha).2
  · rintro _ ⟨a, ha, rfl⟩ haK
    rw [hxi]
    have hnonneg := h.pairing_weyl_nonneg_of_mem_closure hzeta hw
      (AddSubmonoid.subset_closure ⟨a, ha, rfl⟩)
    have hne : latticePairing T (schemeWeylCharacterAction i w a.1) zeta ≠ 0 := by
      intro hzero
      exact haK ⟨a, (h.mem_intersectionSubset_iff_pairing_eq_zero hν hzeta w a).mpr
        ⟨ha, hzero⟩, rfl⟩
    exact lt_of_le_of_ne hnonneg (Ne.symm hne)

end Twisted

section Faces

variable [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)

/-- Every finite set of simple relative roots has a face on which any two
standard cocharacters give the same three dynamic subgroup functors. This
property includes no existence assertion. -/
def StandardFaceDynamicComparison : Prop :=
  ∀ K : Finset (SimpleRoot i ν), StandardCocharacterDynamicComparison i ν (rootSet i ν K)

/-- Under negation stability and the two root-sign inclusion criteria, the
standard parabolic and unipotent subgroups of a face are the dynamic subgroups
of each of its standard cocharacters. -/
theorem standard_eq_dynamic_of_signInclusions (hν : IsGenericCocharacter i ν)
    (hneg : ∀ α ∈ relativeRoots i, -α ∈ relativeRoots i)
    (hincl : ∀ zeta eta : cocharacterLattice T,
      (Dynamic.parabolic (CommGroupScheme.groupHom zeta ≫ i) ≤
          Dynamic.parabolic (CommGroupScheme.groupHom eta ≫ i) ↔
        ∀ α ∈ relativeRoots i,
          0 ≤ latticePairing T α zeta → 0 ≤ latticePairing T α eta) ∧
      ((∀ α ∈ relativeRoots i,
          0 < latticePairing T α zeta → 0 < latticePairing T α eta) →
        Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ i) ≤
          Dynamic.unipotent (CommGroupScheme.groupHom eta ≫ i)))
    {J : Set (characterLattice T)} {eta : cocharacterLattice T}
    (heta : IsStandardCocharacter i ν J eta) :
    standardParabolic i ν J = Dynamic.parabolic (CommGroupScheme.groupHom eta ≫ i) ∧
      standardUnipotent i ν J = Dynamic.unipotent (CommGroupScheme.groupHom eta ≫ i) := by
  refine ⟨(dynamicParabolic_eq_standardParabolic_of_isStandardCocharacter i ν hν hneg
      (fun zeta eta' hsign => (hincl zeta eta').1.2 hsign) heta).symm,
    le_antisymm (standardUnipotent_le_dynamicUnipotent i ν heta) ?_⟩
  intro U g hg
  rw [mem_standardUnipotent]
  intro eta' heta'
  exact (hincl eta eta').2 (fun α hα hpos =>
    ((heta.haveSameRelativeRootSigns i ν hν hneg heta') α hα).2.2.1 hpos) U hg

end Faces

section Source

variable {i : T.toGrp ⟶ G} [IsAffineHom G.X.hom] [Mono i.hom.hom.left]
  {ν : cocharacterLattice T} {CM : CoxeterMatrix (SimpleRoot i ν)}
  {cs : CoxeterSystem CM (relativeWeylGroup i)}

/-- For every standard cocharacter `zeta` for `I` there is a standard
cocharacter `eta` for the intersection subset such that, on points of the
standard Levi for `J`, the inverse-conjugated dynamic parabolic and unipotent
conditions of `zeta` are those of `eta`. -/
theorem IsRelativeWeylCoxeterRealization.exists_source_comparison
    [Finite (SimpleRoot i ν)] (h : IsRelativeWeylCoxeterRealization i ν cs)
    (hν : IsGenericCocharacter i ν)
    {I J : Finset (SimpleRoot i ν)} {w : relativeWeylGroup i} (hw : IsMinimal cs I J w)
    (n : normalizerPoints i) (hn : QuotientGroup.mk n = w)
    {zeta : cocharacterLattice T} (hzeta : IsStandardCocharacter i ν (rootSet i ν I) zeta) :
    ∃ eta : cocharacterLattice T,
      IsStandardCocharacter i ν (rootSet i ν (intersectionSubset cs I J w)) eta ∧
      ∀ {U : Over (Spec (CommRingCat.of k))} {g : U ⟶ G.X},
        g ∈ (standardLevi i ν (rootSet i ν J)).carrier U →
          (g ∈ ((Dynamic.parabolic (CommGroupScheme.groupHom zeta ≫ i)).comap
              (G.innerIso (n : rationalPoints G)).hom).carrier U ↔
            g ∈ (Dynamic.parabolic (CommGroupScheme.groupHom eta ≫ i)).carrier U) ∧
          (g ∈ ((Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ i)).comap
              (G.innerIso (n : rationalPoints G)).hom).carrier U ↔
            g ∈ (Dynamic.unipotent (CommGroupScheme.groupHom eta ≫ i)).carrier U) := by
  have hfinite : (simpleRelativeRoots i ν).Finite := Set.finite_coe_iff.mp inferInstance
  obtain ⟨mu, hmu⟩ := h.exists_standardCocharacter_finset J
  let xi := (cocharacterAut (normalizingAut i n)).symm zeta
  have hxi : ∀ α, latticePairing T α xi =
      latticePairing T (schemeWeylCharacterAction i w α) zeta := by
    intro α
    rw [← hn]
    exact latticePairing_cocharacterAut_symm i n α zeta
  obtain ⟨m, hm⟩ :=
    h.exists_standardCocharacter_intersectionSubset hν hfinite hw hzeta hmu xi hxi
  refine ⟨xi + m • mu, hm, ?_⟩
  intro U g hg
  have hc : g ∈ (Dynamic.centralizer (CommGroupScheme.groupHom (m • mu) ≫ i)).carrier U :=
    (Dynamic.centralizingCocharacters i g).smul_mem m ((mem_standardLevi i ν).1 hg mu hmu)
  rw [dynamicParabolic_comap_innerIso i n zeta, dynamicUnipotent_comap_innerIso i n zeta]
  exact ⟨(Dynamic.mem_parabolic_groupHom_add_iff_of_mem_centralizer i xi _ hc).symm,
    (Dynamic.mem_unipotent_groupHom_add_iff_of_mem_centralizer i xi _ hc).symm⟩

/-- Inside `L_J`, the standard parabolic of the intersection subset lies in the
inverse conjugate of the standard parabolic of `I`. -/
theorem IsRelativeWeylCoxeterRealization.standardLevi_inf_standardParabolic_le
    [Finite (SimpleRoot i ν)] (h : IsRelativeWeylCoxeterRealization i ν cs)
    (hν : IsGenericCocharacter i ν)
    {I J : Finset (SimpleRoot i ν)} {w : relativeWeylGroup i} (hw : IsMinimal cs I J w)
    (n : normalizerPoints i) (hn : QuotientGroup.mk n = w) :
    standardLevi i ν (rootSet i ν J) ⊓
        standardParabolic i ν (rootSet i ν (intersectionSubset cs I J w)) ≤
      standardLevi i ν (rootSet i ν J) ⊓
        (standardParabolic i ν (rootSet i ν I)).comap
          (G.innerIso (n : rationalPoints G)).hom := by
  rw [SubgroupFunctor.le_def]
  intro U g hg
  rw [SubgroupFunctor.inf_carrier, Subgroup.mem_inf] at hg ⊢
  obtain ⟨hgL, hgP⟩ := hg
  refine ⟨hgL, ?_⟩
  rw [SubgroupFunctor.mem_comap, mem_standardParabolic]
  intro zeta hzeta
  obtain ⟨eta, heta, hcmp⟩ := h.exists_source_comparison hν hw n hn hzeta
  exact (hcmp hgL).1.2 ((mem_standardParabolic i ν).1 hgP eta heta)

/-- Inside `L_J`, the standard unipotent subgroup of the intersection subset
lies in the inverse conjugate of the standard unipotent subgroup of `I`. -/
theorem IsRelativeWeylCoxeterRealization.standardLevi_inf_standardUnipotent_le
    [Finite (SimpleRoot i ν)] (h : IsRelativeWeylCoxeterRealization i ν cs)
    (hν : IsGenericCocharacter i ν)
    {I J : Finset (SimpleRoot i ν)} {w : relativeWeylGroup i} (hw : IsMinimal cs I J w)
    (n : normalizerPoints i) (hn : QuotientGroup.mk n = w) :
    standardLevi i ν (rootSet i ν J) ⊓
        standardUnipotent i ν (rootSet i ν (intersectionSubset cs I J w)) ≤
      standardLevi i ν (rootSet i ν J) ⊓
        (standardUnipotent i ν (rootSet i ν I)).comap
          (G.innerIso (n : rationalPoints G)).hom := by
  rw [SubgroupFunctor.le_def]
  intro U g hg
  rw [SubgroupFunctor.inf_carrier, Subgroup.mem_inf] at hg ⊢
  obtain ⟨hgL, hgU⟩ := hg
  refine ⟨hgL, ?_⟩
  rw [SubgroupFunctor.mem_comap, mem_standardUnipotent]
  intro zeta hzeta
  obtain ⟨eta, heta, hcmp⟩ := h.exists_source_comparison hν hw n hn hzeta
  exact (hcmp hgL).2.2 ((mem_standardUnipotent i ν).1 hgU eta heta)

/-- If the standard parabolic and unipotent subgroups of the intersection subset
are the dynamic subgroups of each of its standard cocharacters, both source
identities hold for one minimum representative and lift. -/
theorem IsRelativeWeylCoxeterRealization.standardSource_eq_of_standard_eq
    [Finite (SimpleRoot i ν)] (h : IsRelativeWeylCoxeterRealization i ν cs)
    (hν : IsGenericCocharacter i ν)
    {I J : Finset (SimpleRoot i ν)} {w : relativeWeylGroup i} (hw : IsMinimal cs I J w)
    (n : normalizerPoints i) (hn : QuotientGroup.mk n = w)
    (hK : ∀ eta : cocharacterLattice T,
      IsStandardCocharacter i ν (rootSet i ν (intersectionSubset cs I J w)) eta →
        standardParabolic i ν (rootSet i ν (intersectionSubset cs I J w)) =
            Dynamic.parabolic (CommGroupScheme.groupHom eta ≫ i) ∧
          standardUnipotent i ν (rootSet i ν (intersectionSubset cs I J w)) =
            Dynamic.unipotent (CommGroupScheme.groupHom eta ≫ i)) :
    (standardLevi i ν (rootSet i ν J) ⊓
        (standardParabolic i ν (rootSet i ν I)).comap
          (G.innerIso (n : rationalPoints G)).hom =
      standardLevi i ν (rootSet i ν J) ⊓
        standardParabolic i ν (rootSet i ν (intersectionSubset cs I J w))) ∧
    (standardLevi i ν (rootSet i ν J) ⊓
        (standardUnipotent i ν (rootSet i ν I)).comap
          (G.innerIso (n : rationalPoints G)).hom =
      standardLevi i ν (rootSet i ν J) ⊓
        standardUnipotent i ν (rootSet i ν (intersectionSubset cs I J w))) := by
  obtain ⟨zeta, hzeta⟩ := h.exists_standardCocharacter_finset I
  obtain ⟨eta, heta, hcmp⟩ := h.exists_source_comparison hν hw n hn hzeta
  obtain ⟨hP, hU⟩ := hK eta heta
  refine ⟨le_antisymm ?_ (h.standardLevi_inf_standardParabolic_le hν hw n hn),
    le_antisymm ?_ (h.standardLevi_inf_standardUnipotent_le hν hw n hn)⟩
  · rw [SubgroupFunctor.le_def]
    intro U g hg
    rw [SubgroupFunctor.inf_carrier, Subgroup.mem_inf] at hg ⊢
    obtain ⟨hgL, hgP⟩ := hg
    rw [SubgroupFunctor.mem_comap, mem_standardParabolic] at hgP
    refine ⟨hgL, ?_⟩
    rw [hP]
    exact (hcmp hgL).1.1 (hgP zeta hzeta)
  · rw [SubgroupFunctor.le_def]
    intro U g hg
    rw [SubgroupFunctor.inf_carrier, Subgroup.mem_inf] at hg ⊢
    obtain ⟨hgL, hgU⟩ := hg
    rw [SubgroupFunctor.mem_comap, mem_standardUnipotent] at hgU
    refine ⟨hgL, ?_⟩
    rw [hU]
    exact (hcmp hgL).2.1 (hgU zeta hzeta)

/-- Dynamic comparison among the standard cocharacters of the intersection
subset gives both source identities for one minimum representative and lift. -/
theorem IsRelativeWeylCoxeterRealization.standardSource_eq_of_comparison
    [Finite (SimpleRoot i ν)] (h : IsRelativeWeylCoxeterRealization i ν cs)
    (hν : IsGenericCocharacter i ν)
    {I J : Finset (SimpleRoot i ν)} {w : relativeWeylGroup i} (hw : IsMinimal cs I J w)
    (n : normalizerPoints i) (hn : QuotientGroup.mk n = w)
    (hK : StandardCocharacterDynamicComparison i ν
      (rootSet i ν (intersectionSubset cs I J w))) :
    (standardLevi i ν (rootSet i ν J) ⊓
        (standardParabolic i ν (rootSet i ν I)).comap
          (G.innerIso (n : rationalPoints G)).hom =
      standardLevi i ν (rootSet i ν J) ⊓
        standardParabolic i ν (rootSet i ν (intersectionSubset cs I J w))) ∧
    (standardLevi i ν (rootSet i ν J) ⊓
        (standardUnipotent i ν (rootSet i ν I)).comap
          (G.innerIso (n : rationalPoints G)).hom =
      standardLevi i ν (rootSet i ν J) ⊓
        standardUnipotent i ν (rootSet i ν (intersectionSubset cs I J w))) :=
  h.standardSource_eq_of_standard_eq hν hw n hn fun _ heta =>
    ⟨(hK.standard_eq_dynamic i ν _ heta).1, (hK.standard_eq_dynamic i ν _ heta).2.2⟩

/-- Agreement of the standard parabolic and unipotent subgroups of every finite
face with the dynamic subgroups of its standard cocharacters gives the source
standardness property for every minimum representative and every lift. -/
theorem IsRelativeWeylCoxeterRealization.isStandardSourceTwistedIntersection_of_standard_eq
    [Finite (SimpleRoot i ν)] (h : IsRelativeWeylCoxeterRealization i ν cs)
    (hν : IsGenericCocharacter i ν)
    (hK : ∀ (K : Finset (SimpleRoot i ν)) (eta : cocharacterLattice T),
      IsStandardCocharacter i ν (rootSet i ν K) eta →
        standardParabolic i ν (rootSet i ν K) =
            Dynamic.parabolic (CommGroupScheme.groupHom eta ≫ i) ∧
          standardUnipotent i ν (rootSet i ν K) =
            Dynamic.unipotent (CommGroupScheme.groupHom eta ≫ i)) :
    IsStandardSourceTwistedIntersection i ν cs :=
  fun _ _ _ hw n hn => h.standardSource_eq_of_standard_eq hν hw n hn (hK _)

/-- Dynamic comparison on every finite standard face gives the source
standardness property for every minimum representative and every lift. -/
theorem IsRelativeWeylCoxeterRealization.isStandardSourceTwistedIntersection
    [Finite (SimpleRoot i ν)] (h : IsRelativeWeylCoxeterRealization i ν cs)
    (hν : IsGenericCocharacter i ν)
    (hK : StandardFaceDynamicComparison i ν) :
    IsStandardSourceTwistedIntersection i ν cs :=
  fun _ _ _ hw n hn => h.standardSource_eq_of_comparison hν hw n hn (hK _)

end Source

/-- Conditional assembly of the unchanged target from the published standard
cocharacter statement. This theorem does not prove that statement. -/
theorem standardSourceTwistedIntersectionStatement_of_standardCocharacterStatement
    (hstd : StandardCocharacterStatement.{u}) :
    StandardSourceTwistedIntersectionStatement.{u} := by
  intro k _ G hG T i hi ν
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  intro hν CM cs h
  have := hG.smooth
  have : Finite (SimpleRoot i ν) :=
    (hi.isSplitSubtorus.1.finite_simpleRelativeRoots i ν).to_subtype
  refine h.isStandardSourceTwistedIntersection hν fun K => ?_
  have hK : rootSet i ν K ⊆ simpleRelativeRoots i ν := by
    rintro _ ⟨a, -, rfl⟩
    exact a.2
  exact (standardCocharacterDynamicComparison_iff i ν _).2
    (hstd k G hG T i hi ν hν _ hK).2

/-- Conditional assembly of the unchanged target from negation stability of the
actual relative roots and the sign-to-dynamic comparison. This theorem proves
neither input statement. -/
theorem standardSourceTwistedIntersectionStatement_of_negation_of_signs
    (hneg : RelativeRootNegationStatement.{u})
    (hsign : RelativeRootSignsDetermineDynamicStatement.{u}) :
    StandardSourceTwistedIntersectionStatement.{u} := by
  intro k _ G hG T i hi ν
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  intro hν CM cs h
  have := hG.smooth
  have : Finite (SimpleRoot i ν) :=
    (hi.isSplitSubtorus.1.finite_simpleRelativeRoots i ν).to_subtype
  refine h.isStandardSourceTwistedIntersection hν fun K zeta hzeta eta heta => ?_
  exact hsign k G hG T i hi zeta eta
    (hzeta.haveSameRelativeRootSigns i ν hν (hneg k G hG T i hi) heta)

/-- Conditional assembly of the unchanged target from negation stability of the
actual relative roots and the root-sign inclusion criteria. This theorem proves
neither input statement. -/
theorem standardSourceTwistedIntersectionStatement_of_negation_of_signInclusions
    (hneg : RelativeRootNegationStatement.{u})
    (hincl : RelativeRootSignInclusionsStatement.{u}) :
    StandardSourceTwistedIntersectionStatement.{u} := by
  intro k _ G hG T i hi ν
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  intro hν CM cs h
  have := hG.smooth
  have : Finite (SimpleRoot i ν) :=
    (hi.isSplitSubtorus.1.finite_simpleRelativeRoots i ν).to_subtype
  exact h.isStandardSourceTwistedIntersection_of_standard_eq hν fun _ _ heta =>
    standard_eq_dynamic_of_signInclusions i ν hν (hneg k G hG T i hi)
      (hincl k G hG T i hi) heta

end Langlands.GroupScheme
