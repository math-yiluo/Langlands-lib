import Langlands.Geometry.Building.GenericPointSharpExchange
import Langlands.GroupTheory.HeightContraction
import Langlands.GroupScheme.Rational.DynamicRadicalRootGeneration
import Langlands.GroupScheme.Rational.DynamicRootOrderedProductProof
import Langlands.GroupScheme.Rational.GenericCentralizerProof
import Langlands.GroupScheme.Rational.DynamicSemistandardIntersectionModels
import Mathlib.Data.Fin.Tuple.Sort

/-!
# The unique fixed point of an Iwasawa subgroup containing a regular torus element

For apartment data `D : KPApartmentData i ω` of a connected reductive group with reduced
relative roots, over any field, let `K` be a subgroup fixing the image of an apartment point
`x`, such that `G(k) = K · P(k)` for the dynamic parabolic `P` of a generic cocharacter `ν`,
`K` contains the depth-zero root groups at `x`, and `K` contains a centralizer point `s`
fixing `x` that acts on every positive root group with "unit eigenvalue gap" (conjugation
by `s` followed by division keeps every value). Then the image of `x` is the only point of
the reduced building fixed by `K`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.GroupScheme.RelativeRoot

open CategoryTheory.Limits

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- Under disjoint indivisible positive rays, every subgroup containing the positive actual
root groups contains the dynamic radical `U(ν)(k)`. This is the published
`dynamicUnipotent_le_of_disjoint_positive_rays`, whose proof only uses the positive root
groups. -/
theorem dynamicUnipotent_le_of_positive_rootGroups
    (hG : IsConnectedReductive G) {i : S.toGrp ⟶ G}
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice S)
    (hdisj : ∀ a ∈ indivisiblePositiveRoots i ν,
      ∀ b ∈ indivisiblePositiveRoots i ν, a ≠ b →
        Disjoint (cyclicTail a 1 : Set (characterLattice S))
          (cyclicTail b 1 : Set (characterLattice S)))
    (K : Subgroup (rationalPoints G))
    (hroot : ∀ a ∈ indivisiblePositiveRoots i ν,
      (subgroup i a).carrier (Over.mk (𝟙 _)) ≤ K) :
    (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)) ≤ K := by
  have := hG.smooth
  have hfin : (indivisiblePositiveRoots i ν).Finite :=
    (hi.isSplitSubtorus.1.finite_relativeRoots i).subset (fun _ ha => ha.1.1)
  obtain ⟨n, a, hinj, ha⟩ := hfin.fin_param
  let b := AutomorphicAction.conjugation i
  let A := positiveSemigroup ν
  obtain ⟨⟨U, jU, hjU, hjUc, hUs, hUc⟩, hStable, _, hUnip, _, _⟩ :=
    semigroupRealization k G hG.smooth inferInstance S hi.1.1 b A
  have hzero : (0 : characterLattice S) ∉ A := by
    change ¬ 0 < latticePairing S 0 ν
    simp
  obtain ⟨hUu, _⟩ := hUnip U jU hjU hzero
  let : IsAffineHom U.X.hom := hjUc.isAffineHom
  let : Smooth U.X.hom := hUs
  let : ConnectedSpace U.X.left := hUc
  let c := b.onRepresentedSubgroup jU hjU hStable
  have hequiv : ∀ (T : Over (Spec (CommRingCat.of k))) (s : T ⟶ S.X)
      (x : T ⟶ U.X), c.act s x ≫ jU.hom.hom = b.act s (x ≫ jU.hom.hom) :=
    fun _ s x => b.onRepresentedSubgroup_act_comp jU hjU hStable s x
  have htop : (⊤ : SubgroupFunctor U).map jU = semigroupSubgroup b A := by
    rw [SubgroupFunctor.map_top, hjU.2]
  have hsupport : actionWeightSupport c ⊤ = positiveRelativeRoots i ν := by
    rw [← actionWeightSupport_map jU hjU.1 c b hequiv, htop]
    exact actionWeightSupport_positiveSemigroup semigroupRealization hG.smooth hi.1.1 i ν
  have hblocks := rootRayBlock_pairwise i ν a hinj ha hdisj
  have hcover : (⋃ r, rootRayBlock i (a r)) = actionWeightSupport c ⊤ :=
    (iUnion_rootRayBlock i ν a ha
      (fun χ hχ => positive_iff_mem_indivisiblePositiveRoot_ray i ν hχ)).trans hsupport.symm
  obtain ⟨H, jH, hH, hIso⟩ :=
    hasOrderedSemigroupProducts_of_unipotent c hi.1.1 hUu n
      (fun r => rootRayBlock i (a r)) hcover hblocks.1 hblocks.2
  have hrootmem (r : Fin n) : a r ∈ indivisiblePositiveRoots i ν :=
    ha ▸ Set.mem_range_self r
  have hsemigroup (r : Fin n) :
      ((semigroupSubgroup c (AddSubsemigroup.closure (rootRayBlock i (a r)))).map jU) =
        semigroupSubgroup b (cyclicTail (a r) 1) := by
    rw [closure_rootRayBlock i (hrootmem r).1.1]
    apply semigroupSubgroup_map_eq jU hjUc c b hequiv
    rw [hjU.2]
    exact semigroupSubgroup_mono b (cyclicTail_one_le_positiveSemigroup (hrootmem r).2)
  have hfactor (r : Fin n) : (subgroup i (a r)).IsRepresentedBy (jH r ≫ jU) := by
    have hrep : (semigroupSubgroup b (cyclicTail (a r) 1)).IsRepresentedBy (jH r ≫ jU) := by
      rw [← hsemigroup r]
      exact (hH r).1.comp hjU
    have hcyclic := cyclicRootFunctorComparison k G hG.smooth inferInstance
      S hi.1.1 i (a r) (hrootmem r).1.1.1
    exact hcyclic ▸ hrep
  have hDynamic :
      Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i) = semigroupSubgroup b A :=
    (dynamicSemigroupComparison k G hG.smooth inferInstance hG.connectedSpace S hi.1.1 i ν).2.2
  let := hIso
  intro g hg
  have hgA : g ∈ (semigroupSubgroup b A).carrier (Over.mk (𝟙 _)) := hDynamic ▸ hg
  let gU : rationalPoints U := (hjU.pointsEquiv _).symm ⟨g, hgA⟩
  let x : rationalPoints (∏ᶜ H) := gU ≫ inv (orderedMultiplication jH)
  have hx : x ≫ orderedMultiplication (fun r => jH r ≫ jU) = g := by
    rw [← orderedMultiplication_comp jH jU]
    simp only [x, Category.assoc, IsIso.inv_hom_id_assoc]
    exact hjU.pointsEquiv_symm_comp _
  rw [← hx, comp_orderedMultiplication]
  unfold orderedPoints
  apply K.list_prod_mem
  intro y hy
  obtain ⟨r, rfl⟩ := List.mem_ofFn.mp hy
  exact hroot (a r) (hrootmem r)
    (((hfactor r).pointsEquiv _ (finiteProductPointsEquiv H _ x r)).property)

end Langlands.GroupScheme.RelativeRoot

namespace Langlands.Geometry.Building

namespace KPApartmentData

variable {k : Type u} [Field k] {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} {i : S.toGrp ⟶ G}
  [Mono i.hom.hom.left] [IsAffineHom G.X.hom] {ω : kˣ → ℝ}

section Roots

/-- With a reduced relative root system, every positive root is indivisible. -/
theorem mem_indivisiblePositiveRoots_of_reduced [Smooth G.X.hom] (hS : IsSplitTorus S.toGrp)
    (hrank : RelativeRoot.HasRankOneFactorization i)
    (hred : ∀ a ∈ relativeRoots i, 2 • a ∉ relativeRoots i) {ν : cocharacterLattice S}
    {b : characterLattice S} (hb : b ∈ positiveRelativeRoots i ν) :
    b ∈ RelativeRoot.indivisiblePositiveRoots i ν := by
  have hE : RelativeRoot.HasOppositeFactorPairs i :=
    fun a ha g hg hg1 => (hrank a ha g hg hg1).1.exists
  refine ⟨⟨hb.1, fun c hc m hm hmc => ?_⟩, hb.2⟩
  have hcb := hE.rootCoroot_pairing i hS ⟨b, hb.1⟩
  rcases hE.root_eq_or_twice_of_common_positive_multiple i hS hc hb.1 (m := m) (n := 1)
      (by omega) one_pos (by rw [one_smul]; exact hmc) with h | h | h
  · subst h
    have hp := congrArg (fun χ => latticePairing S χ (hE.rootCoroot i hS ⟨c, hb.1⟩)) hmc
    simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul, hcb] at hp
    omega
  · subst h
    have hp := congrArg (fun χ => latticePairing S χ (hE.rootCoroot i hS ⟨b, hb.1⟩)) hmc
    simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul, hcb] at hp
    omega
  · exact hred c hc (h ▸ hb.1)

/-- With a reduced relative root system, positive and indivisible positive roots agree. -/
theorem positiveRelativeRoots_eq_indivisible [Smooth G.X.hom] (hS : IsSplitTorus S.toGrp)
    (hrank : RelativeRoot.HasRankOneFactorization i)
    (hred : ∀ a ∈ relativeRoots i, 2 • a ∉ relativeRoots i) (ν : cocharacterLattice S) :
    positiveRelativeRoots i ν = RelativeRoot.indivisiblePositiveRoots i ν :=
  Set.ext fun _ => ⟨fun hb => mem_indivisiblePositiveRoots_of_reduced hS hrank hred hb,
    fun hb => ⟨hb.1.1, hb.2⟩⟩

omit [Mono i.hom.hom.left] in
/-- A finite enumeration of the positive roots with monotone heights `⟨a, ν⟩`. -/
theorem exists_sorted_enumeration [Smooth G.X.hom] (hS : IsSplitTorus S.toGrp)
    (ν : cocharacterLattice S) :
    ∃ (n : ℕ) (a : Fin n → characterLattice S), Function.Injective a ∧
      Set.range a = positiveRelativeRoots i ν ∧
        Monotone (fun j => (latticePairing S (a j) ν).toNat) := by
  have hfin : (positiveRelativeRoots i ν).Finite :=
    (hS.finite_relativeRoots i).subset (fun _ ha => ha.1)
  obtain ⟨n, a₀, hinj, hrange⟩ := hfin.fin_param
  let σ := Tuple.sort (fun j => (latticePairing S (a₀ j) ν).toNat)
  refine ⟨n, a₀ ∘ σ, hinj.comp σ.injective, ?_, ?_⟩
  · rw [Set.range_comp, Equiv.range_eq_univ, Set.image_univ, hrange]
  · exact Tuple.monotone_sort (fun j => (latticePairing S (a₀ j) ν).toNat)

end Roots

variable (D : KPApartmentData i ω)

section Enumeration

variable {n : ℕ} {ν : cocharacterLattice S} {a : Fin n → characterLattice S}

theorem commutator_chamberRootGroup_enum (hrange : Set.range a = positiveRelativeRoots i ν)
    (x : D.Apartment) (strict : Bool) (j l : Fin n) :
    ⁅D.chamberRootGroup x strict (a j), D.chamberRootGroup x strict (a l)⁆ ≤
      ⨆ m, ⨆ (_ : max (latticePairing S (a j) ν).toNat (latticePairing S (a l) ν).toNat <
        (latticePairing S (a m) ν).toNat), D.chamberRootGroup x strict (a m) := by
  have haj : a j ∈ positiveRelativeRoots i ν := hrange ▸ Set.mem_range_self j
  have hal : a l ∈ positiveRelativeRoots i ν := hrange ▸ Set.mem_range_self l
  refine (D.chamberRootGroup_commutator_height x strict ν haj hal).trans ?_
  refine iSup_le fun c => iSup_le fun hc => ?_
  obtain ⟨m, hm⟩ := (show (c : characterLattice S) ∈ Set.range a by rw [hrange]; exact c.2)
  exact le_iSup_of_le m (le_iSup_of_le (hm.symm ▸ hc) (by rw [hm]))

theorem iSup_chamberRootGroup_enum (hrange : Set.range a = positiveRelativeRoots i ν)
    (x : D.Apartment) (strict : Bool) :
    (⨆ b : positiveRelativeRoots i ν, D.chamberRootGroup x strict b) =
      ⨆ j, D.chamberRootGroup x strict (a j) := by
  apply le_antisymm
  · refine iSup_le fun b => ?_
    obtain ⟨j, hj⟩ := (show (b : characterLattice S) ∈ Set.range a by rw [hrange]; exact b.2)
    exact le_iSup_of_le j (by rw [hj])
  · exact iSup_le fun j => le_iSup_of_le
      (⟨a j, hrange ▸ Set.mem_range_self j⟩ : positiveRelativeRoots i ν) le_rfl

end Enumeration

/-- Coordinates of an actual root group isolate depth-zero membership: for a reduced root
system, an element of a positive root group lying in the subgroup generated by the positive
depth-zero root groups at `x` has depth zero at `x`. -/
theorem mem_filtration_of_mem_rootGroup_of_mem_positiveRootGroups_of_reduced
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hred : ∀ a ∈ relativeRoots i, 2 • a ∉ relativeRoots i)
    (x : D.Apartment) (ν : cocharacterLattice S)
    {b : characterLattice S} (hb : b ∈ positiveRelativeRoots i ν)
    {g : rationalPoints G} (hg : g ∈ rootGroupPoints i b)
    (hgpos : g ∈ ⨆ c : positiveRelativeRoots i ν, D.chamberRootGroup x false c) :
    g ∈ D.filtration x b 0 := by
  classical
  have : Smooth G.X.hom := hG.smooth
  have hS : IsSplitTorus S.toGrp := hi.1.1
  have hrank : RelativeRoot.HasRankOneFactorization i :=
    rootRankOneFactorization k G hG S i hi
  have hfinite : (positiveRelativeRoots i ν).Finite :=
    (hS.finite_relativeRoots i).subset (fun _ ha => ha.1)
  obtain ⟨n, a, ha, hrange⟩ := hfinite.fin_param
  have hrange' : Set.range a = RelativeRoot.indivisiblePositiveRoots i ν := by
    rw [hrange, positiveRelativeRoots_eq_indivisible hS hrank hred ν]
  obtain ⟨r, hr⟩ := (show b ∈ Set.range a by rw [hrange]; exact hb)
  obtain ⟨t, ht⟩ := (show g ∈ Set.range
      (RelativeRoot.CentralExtension.orderedProduct
        (fun j => (D.chamberRootGroup x false (a j)).subtype)) by
    rw [Langlands.GroupTheory.HeightCollection.range_orderedProduct_eq_iSup _
      (fun j => (latticePairing S (a j) ν).toNat)
      (D.commutator_chamberRootGroup_enum hrange x false),
      ← D.iSup_chamberRootGroup_enum hrange x false]
    exact hgpos)
  let t' : ∀ j, rootGroupPoints i (a j) := fun j =>
    ⟨t j, D.filtration_le_rootGroupPoints x (a j) 0 (t j).property⟩
  let s : ∀ j, rootGroupPoints i (a j) := fun j =>
    if h : j = r then ⟨g, by simpa only [h, hr] using hg⟩ else 1
  have hsprod : (List.ofFn fun j => (s j : rationalPoints G)).prod = g := by
    have hsingle : ∀ j, j ≠ r → (s j : rationalPoints G) = 1 := fun j hj => by
      simp [s, hj]
    rw [List.ofFn_eq_map, List.prod_map_eq_pow_single r _ (fun j hj _ => hsingle j hj)]
    simp [s]
  have hcoords : t' = s :=
    RelativeRoot.orderedRootSubgroupPoints_injective_of_statement
      RelativeRoot.dynamicRootOrderedProduct hG hi ν a ha hrange' (Over.mk (𝟙 _))
      (ht.trans hsprod.symm)
  have hcoord : (t r : rationalPoints G) = g := by
    have hc := congrArg (fun z => (z r : rationalPoints G)) hcoords
    simpa only [t', s, dite_eq_left rfl] using hc
  have hmem : (t r : rationalPoints G) ∈ D.filtration x b 0 := by
    rw [← hr]
    exact (t r).property
  rwa [hcoord] at hmem

section Shift

/-- The apartment point `z + T ν`. -/
def shift (z : D.Apartment) (ν : cocharacterLattice S) (T : ℝ) : D.Apartment :=
  (Submodule.Quotient.mk (T ⊗ₜ[ℤ] ν) : TranslationSpace i) +ᵥ z

theorem shift_val (z : D.Apartment) (ν : cocharacterLattice S) (T : ℝ)
    (a : characterLattice S) (g : rationalPoints G) :
    (D.shift z ν T).val a g = z.val a g + ((T * latticePairing S a ν : ℝ) : WithTop ℝ) := by
  simp only [shift, val_mk_vadd, RootFunctionFamily.vadd_apply, eval_tmul]

/-- Moving in the direction of `ν` enlarges the depth-zero groups of positive roots. -/
theorem filtration_le_filtration_shift (z : D.Apartment) {ν : cocharacterLattice S}
    {a : characterLattice S} (ha : 0 < latticePairing S a ν) {T T' : ℝ} (hT : T ≤ T') :
    D.filtration (D.shift z ν T) a 0 ≤ D.filtration (D.shift z ν T') a 0 := by
  intro g hg
  rw [mem_filtration] at hg ⊢
  refine ⟨hg.1, ?_⟩
  have h1 := hg.2
  rw [shift_val] at h1 ⊢
  have hle : T * (latticePairing S a ν : ℝ) ≤ T' * latticePairing S a ν :=
    mul_le_mul_of_nonneg_right hT (by exact_mod_cast ha.le)
  induction hz : z.val a g using WithTop.recTopCoe with
  | top => simp
  | coe r =>
    rw [hz] at h1
    rw [← WithTop.coe_add] at h1 ⊢
    rw [WithTop.coe_le_coe] at h1 ⊢
    linarith

theorem shift_zero (z : D.Apartment) (ν : cocharacterLattice S) : D.shift z ν 0 = z := by
  simp only [shift, zero_tmul, Submodule.Quotient.mk_zero, zero_vadd]

/-- Every element of `U(ν)(k)` lies in the subgroup generated by the positive depth-zero
root groups at some point `z + T ν`. -/
theorem exists_shift_mem (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (z : D.Apartment) (ν : cocharacterLattice S) {g : rationalPoints G}
    (hg : g ∈ (Dynamic.unipotent
      (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _))) :
    ∃ T : ℕ, g ∈ ⨆ b : positiveRelativeRoots i ν, D.filtration (D.shift z ν T) b 0 := by
  have : Smooth G.X.hom := hG.smooth
  have hS : IsSplitTorus S.toGrp := hi.1.1
  have hrank : RelativeRoot.HasRankOneFactorization i :=
    rootRankOneFactorization k G hG S i hi
  have hE : RelativeRoot.HasOppositeFactorPairs i :=
    fun a ha g hg hg1 => (hrank a ha g hg hg1).1.exists
  let X : ℕ → Subgroup (rationalPoints G) := fun T =>
    ⨆ b : positiveRelativeRoots i ν, D.filtration (D.shift z ν T) b 0
  have hmono : Monotone X := fun T T' hTT' =>
    iSup_mono fun b => D.filtration_le_filtration_shift z b.2.2 (by exact_mod_cast hTT')
  have hK := RelativeRoot.dynamicUnipotent_le_of_positive_rootGroups hG hi ν
    (fun a ha b hb hne => hE.disjoint_cyclicTail_indivisibleRoots i hS ha.1 hb.1 hne)
    (⨆ T, X T) (fun a ha u hu => ?_) hg
  · exact (Subgroup.mem_iSup_of_directed hmono.directed_le).mp hK
  by_cases hu1 : u = 1
  · rw [hu1]
    exact one_mem _
  obtain ⟨r, hr⟩ := exists_val_eq_coe z ha.1.1 hu hu1
  have hpos : (1 : ℝ) ≤ latticePairing S a ν := by exact_mod_cast ha.2
  have ha' : a ∈ positiveRelativeRoots i ν := ⟨ha.1.1, ha.2⟩
  refine Subgroup.mem_iSup_of_mem ⌈-r⌉₊ (Subgroup.mem_iSup_of_mem
    (⟨a, ha'⟩ : positiveRelativeRoots i ν) ?_)
  refine ⟨hu, ?_⟩
  change (0 : WithTop ℝ) ≤ (D.shift z ν (⌈-r⌉₊ : ℝ)).val a u
  rw [shift_val, hr, ← WithTop.coe_add, ← WithTop.coe_zero, WithTop.coe_le_coe]
  have hceil : -r ≤ (⌈-r⌉₊ : ℝ) := Nat.le_ceil _
  have hnn : (0 : ℝ) ≤ ⌈-r⌉₊ := Nat.cast_nonneg _
  nlinarith

end Shift

omit [Mono i.hom.hom.left] in
/-- Centralizer points lie in the dynamic parabolic of a generic cocharacter. -/
theorem mem_parabolic_of_mem_centralizerPoints (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice S) (hν : IsGenericCocharacter i ν)
    {s : rationalPoints G} (hsC : s ∈ centralizerPoints i) :
    s ∈ (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)) := by
  have hcent := genericCentralizer k G hG S i hi ν hν
  have hsZ : s ∈ (torusCentralizer i).carrier (Over.mk (𝟙 _)) := by
    rw [torusCentralizer_carrier_base]
    exact hsC
  rw [← hcent] at hsZ
  exact Dynamic.centralizer_le_parabolic _ _ hsZ

/-- Conjugation by a centralizer point fixing one apartment point preserves every depth-zero
root group at every point. -/
theorem conj_mem_chamberRootGroup_of_mem_centralizerPoints (hS : IsSplitTorus S.toGrp)
    {s : rationalPoints G} (hsC : s ∈ centralizerPoints i) {z : D.Apartment}
    (hsz : (⟨s, centralizerPoints_le_normalizerPoints i hsC⟩ : normalizerPoints i) • z = z)
    (y : D.Apartment) (a : characterLattice S) {h : rationalPoints G}
    (hh : h ∈ D.chamberRootGroup y false a) : s * h * s⁻¹ ∈ D.chamberRootGroup y false a := by
  have hsy : (⟨s, centralizerPoints_le_normalizerPoints i hsC⟩ : normalizerPoints i) • y = y :=
    smul_eq_self_of_mem_centralizerPoints (D := D)
      (n := ⟨s, centralizerPoints_le_normalizerPoints i hsC⟩) hsC hsz
  have hsW : weylAction i (⟨s, centralizerPoints_le_normalizerPoints i hsC⟩ :
      normalizerPoints i) = 1 := (hS.weylAction_eq_one_iff i _).2 hsC
  have h' := D.conj_mem_filtration
    (⟨s, centralizerPoints_le_normalizerPoints i hsC⟩ : normalizerPoints i) hh
  rw [hsy, hsW] at h'
  exact h'

/-- The commutator of `s` with `u` fixes the image of `z` if `s` fixes the images of `z`
and `u • z`. -/
theorem inv_mul_conj_smul_apartmentMap {s u : rationalPoints G} {z : D.Apartment}
    (hsz : s • D.apartmentMap z = D.apartmentMap z)
    (hfix : s • u • D.apartmentMap z = u • D.apartmentMap z) :
    (u⁻¹ * (s * u * s⁻¹)) • D.apartmentMap z = D.apartmentMap z := by
  have hsinv : s⁻¹ • D.apartmentMap z = D.apartmentMap z := by
    rw [inv_smul_eq_iff, hsz]
  rw [mul_smul, mul_smul, mul_smul, hsinv, hfix, inv_smul_smul]

/-- **Fixed cosets of a regular centralizer point.** Let `s` be a centralizer point fixing
`z` such that, on every positive root group, conjugation by `s` followed by division keeps
all values at `z`. If `u ∈ U(ν)(k)` and `s` fixes the image of `u • z` in the reduced
building, then `u` lies in the subgroup generated by the positive depth-zero root groups at
`z`. -/
theorem mem_positiveRootGroups_of_smul_smul_eq
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hred : ∀ a ∈ relativeRoots i, 2 • a ∉ relativeRoots i)
    (ν : cocharacterLattice S) (hν : IsGenericCocharacter i ν) (z : D.Apartment)
    {s : rationalPoints G} (hsC : s ∈ centralizerPoints i)
    (hsz : (⟨s, centralizerPoints_le_normalizerPoints i hsC⟩ : normalizerPoints i) • z = z)
    (hsval : ∀ b ∈ positiveRelativeRoots i ν, ∀ h ∈ rootGroupPoints i b,
      z.val b (h⁻¹ * (s * h * s⁻¹)) = z.val b h)
    {u : rationalPoints G}
    (hu : u ∈ (Dynamic.unipotent
      (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)))
    (hfix : s • u • D.apartmentMap z = u • D.apartmentMap z) :
    u ∈ ⨆ b : positiveRelativeRoots i ν, D.chamberRootGroup z false b := by
  have : Smooth G.X.hom := hG.smooth
  have hS : IsSplitTorus S.toGrp := hi.1.1
  have hrank : RelativeRoot.HasRankOneFactorization i :=
    rootRankOneFactorization k G hG S i hi
  have hsz' : s • D.apartmentMap z = D.apartmentMap z := by
    have h := D.apartmentMap_smul
      (⟨s, centralizerPoints_le_normalizerPoints i hsC⟩ : normalizerPoints i) z
    rw [hsz] at h
    exact h.symm
  have hvU : u⁻¹ * (s * u * s⁻¹) ∈ (Dynamic.unipotent
      (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)) :=
    mul_mem (inv_mem hu) (Dynamic.conj_mem_unipotent _
      (mem_parabolic_of_mem_centralizerPoints hG hi ν hν hsC) hu)
  have hvX := D.mem_positiveRootGroups_of_mem_unipotent_of_smul_apartmentMap_eq hG hi z ν hν
    hvU (D.inv_mul_conj_smul_apartmentMap hsz' hfix)
  obtain ⟨T, hT⟩ := D.exists_shift_mem hG hi z ν hu
  obtain ⟨n, a, ha, hrange, hmono⟩ := exists_sorted_enumeration (i := i) hS ν
  have hrange' : Set.range a = RelativeRoot.indivisiblePositiveRoots i ν := by
    rw [hrange, positiveRelativeRoots_eq_indivisible hS hrank hred ν]
  have hapos : ∀ j, a j ∈ positiveRelativeRoots i ν := fun j => hrange ▸ Set.mem_range_self j
  have hXH : ∀ j, D.chamberRootGroup z false (a j) ≤
      D.chamberRootGroup (D.shift z ν T) false (a j) := by
    intro j
    have h := D.filtration_le_filtration_shift z (hapos j).2 (T := 0) (T' := T)
      (by exact_mod_cast Nat.zero_le T)
    rw [shift_zero] at h
    exact h
  have hinj : ∀ f g : Fin n → rationalPoints G,
      (∀ j, f j ∈ D.chamberRootGroup (D.shift z ν T) false (a j)) →
      (∀ j, g j ∈ D.chamberRootGroup (D.shift z ν T) false (a j)) →
      (List.ofFn f).prod = (List.ofFn g).prod → f = g := by
    intro f g hf hg hfg
    let x₁ : ∀ j, rootGroupPoints i (a j) := fun j =>
      ⟨f j, D.filtration_le_rootGroupPoints (D.shift z ν T) (a j) 0 (hf j)⟩
    let x₂ : ∀ j, rootGroupPoints i (a j) := fun j =>
      ⟨g j, D.filtration_le_rootGroupPoints (D.shift z ν T) (a j) 0 (hg j)⟩
    have hcoord : x₁ = x₂ := RelativeRoot.orderedRootSubgroupPoints_injective_of_statement
      RelativeRoot.dynamicRootOrderedProduct hG hi ν a ha hrange' (Over.mk (𝟙 _)) hfg
    funext j
    exact congrArg (fun y => (y j : rationalPoints G)) hcoord
  have hrankX : ∀ j, ∀ h ∈ D.chamberRootGroup (D.shift z ν T) false (a j),
      h⁻¹ * (MulAut.conj s).toMonoidHom h ∈ D.chamberRootGroup z false (a j) →
        h ∈ D.chamberRootGroup z false (a j) := by
    intro j h hh hX
    have hhU : h ∈ rootGroupPoints i (a j) :=
      D.filtration_le_rootGroupPoints (D.shift z ν T) (a j) 0 hh
    have hX' : h⁻¹ * (s * h * s⁻¹) ∈ D.filtration z (a j) 0 := hX
    change h ∈ D.filtration z (a j) 0
    rw [mem_filtration] at hX' ⊢
    refine ⟨hhU, ?_⟩
    rw [← hsval (a j) (hapos j) h hhU]
    exact hX'.2
  have huH : u ∈ ⨆ j, D.chamberRootGroup (D.shift z ν T) false (a j) := by
    rw [← D.iSup_chamberRootGroup_enum hrange (D.shift z ν T) false]
    exact hT
  have hvX' : u⁻¹ * (MulAut.conj s).toMonoidHom u ∈
      ⨆ j, D.chamberRootGroup z false (a j) := by
    rw [← D.iSup_chamberRootGroup_enum hrange z false]
    exact hvX
  rw [D.iSup_chamberRootGroup_enum hrange z false]
  exact Langlands.GroupTheory.HeightContraction.mem_iSup_of_inv_mul_map_mem
    (fun j => D.chamberRootGroup (D.shift z ν T) false (a j))
    (fun j => D.chamberRootGroup z false (a j))
    (fun j => (latticePairing S (a j) ν).toNat) hmono
    (D.commutator_chamberRootGroup_enum hrange (D.shift z ν T) false)
    (D.commutator_chamberRootGroup_enum hrange z false) hXH hinj (MulAut.conj s).toMonoidHom
    (fun j h hh => D.conj_mem_chamberRootGroup_of_mem_centralizerPoints hS hsC hsz _ _ hh)
    (fun j h hh => D.conj_mem_chamberRootGroup_of_mem_centralizerPoints hS hsC hsz _ _ hh)
    hrankX huH hvX'

/-- An element of the subgroup generated by the positive depth-zero root groups at `z` fixes
the image of `z`. -/
theorem positiveRootGroups_le_reducedFixer (ν : cocharacterLattice S) (z : D.Apartment) :
    (⨆ b : positiveRelativeRoots i ν, D.chamberRootGroup z false b) ≤
      D.reducedFixer (D.apartmentMap z) :=
  (iSup_le fun b => D.filtration_le_sharpFixer z b.2.1).trans (D.sharpFixer_le_reducedFixer z)

/-- If every depth-zero root group at `x` fixes the image of `z`, and every root takes the
value zero at `x`, then `z = x`. -/
theorem eq_of_filtration_le_reducedFixer (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hred : ∀ a ∈ relativeRoots i, 2 • a ∉ relativeRoots i)
    (x z : D.Apartment)
    (hzero : ∀ a ∈ relativeRoots i, ∃ u ∈ rootGroupPoints i a, x.val a u = 0)
    (hfix : ∀ a ∈ relativeRoots i, ∀ u ∈ D.filtration x a 0,
      u • D.apartmentMap z = D.apartmentMap z) : z = x := by
  have : Smooth G.X.hom := hG.smooth
  have hS : IsSplitTorus S.toGrp := hi.1.1
  have hrank : RelativeRoot.HasRankOneFactorization i :=
    rootRankOneFactorization k G hG S i hi
  obtain ⟨ν₀, hν₀⟩ := hS.exists_genericCocharacter i
  obtain ⟨v, hv⟩ := D.equipollent_of_mem x.mem z.mem
  have hnonneg : ∀ a ∈ relativeRoots i, 0 ≤ eval S a v := by
    intro a ha
    obtain ⟨u, hu, hu0⟩ := hzero a ha
    have hchoice : ∃ ν : cocharacterLattice S,
        IsGenericCocharacter i ν ∧ 0 < latticePairing S a ν := by
      rcases lt_or_gt_of_ne (hν₀ a ha) with hneg | hpos
      · refine ⟨-ν₀, ?_, ?_⟩
        · intro b hb
          simpa only [map_neg] using neg_ne_zero.mpr (hν₀ b hb)
        · simpa only [map_neg] using neg_pos.mpr hneg
      · exact ⟨ν₀, hν₀, hpos⟩
    obtain ⟨ν, hν, hpos⟩ := hchoice
    have huF : u ∈ D.filtration x a 0 := ⟨hu, by rw [hu0]; rfl⟩
    have huU := RelativeRoot.subgroup_le_dynamicUnipotent i ν hpos (Over.mk (𝟙 _)) hu
    have huX := D.mem_positiveRootGroups_of_mem_unipotent_of_smul_apartmentMap_eq hG hi z ν hν
      huU (hfix a ha u huF)
    have huz := D.mem_filtration_of_mem_rootGroup_of_mem_positiveRootGroups_of_reduced hG hi hred z ν
      ⟨ha, hpos⟩ hu huX
    have h2 := huz.2
    rw [hv, RootFunctionFamily.vadd_apply, hu0, zero_add] at h2
    exact WithTop.coe_le_coe.mp h2
  have hall : ∀ d ∈ relativeRoots i, eval S d v = 0 := by
    intro d hd
    have h1 := hnonneg d hd
    have h2 := hnonneg (-d) (neg_mem_relativeRoots_of_rankOne hS hrank x hd)
    rw [eval_neg_char] at h2
    linarith
  refine KPApartmentData.Apartment.ext ?_
  rw [hv]
  exact x.isValuation.vadd_eq_self_iff.2 (mem_rootAnnihilator.2 hall)

/-- **The unique fixed point.** Let `K` be a subgroup of `G(k)` fixing the image of `x`,
with `G(k) = K · P(k)` for the dynamic parabolic `P` of a generic cocharacter `ν`, containing
every depth-zero root group at `x` and a centralizer point `s` fixing `x` that keeps all
values of positive root elements after conjugation and division. If every root takes the
value zero at `x` and the relative roots are reduced, then the image of `x` is the only
point of the reduced building fixed by `K`. -/
theorem eq_apartmentMap_of_forall_smul_eq (hG : IsConnectedReductive G)
    (hi : IsMaximalSplitTorus i) (hred : ∀ a ∈ relativeRoots i, 2 • a ∉ relativeRoots i)
    (x : D.Apartment) (K : Subgroup (rationalPoints G))
    (hKx : ∀ g ∈ K, g • D.apartmentMap x = D.apartmentMap x)
    (ν : cocharacterLattice S) (hν : IsGenericCocharacter i ν)
    (hIw : ∀ g : rationalPoints G, ∃ κ ∈ K,
      ∃ p ∈ (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)),
        g = κ * p)
    {s : rationalPoints G} (hsK : s ∈ K) (hsC : s ∈ centralizerPoints i)
    (hsx : (⟨s, centralizerPoints_le_normalizerPoints i hsC⟩ : normalizerPoints i) • x = x)
    (hsval : ∀ b ∈ positiveRelativeRoots i ν, ∀ h ∈ rootGroupPoints i b, ∀ z : D.Apartment,
      z.val b (h⁻¹ * (s * h * s⁻¹)) = z.val b h)
    (hroot0 : ∀ a ∈ relativeRoots i, D.filtration x a 0 ≤ K)
    (hzero : ∀ a ∈ relativeRoots i, ∃ u ∈ rootGroupPoints i a, x.val a u = 0)
    (y : D.ReducedBuilding) (hy : ∀ g ∈ K, g • y = y) : y = D.apartmentMap x := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  obtain ⟨g, z, rfl⟩ := D.exists_smul_apartmentMap y
  obtain ⟨κ, hκ, p, hp, rfl⟩ := hIw g
  have hp' : p ∈ ((Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i)).carrier
      (Over.mk (𝟙 _)) : Set (rationalPoints G)) *
      ((Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)).carrier
        (Over.mk (𝟙 _)) : Set (rationalPoints G)) := by
    rw [← Dynamic.parabolic_eq_centralizer_mul_unipotent]
    exact hp
  obtain ⟨l, hl, u, hu, rfl⟩ := hp'
  have hlC : l ∈ centralizerPoints i := by
    have hcent := genericCentralizer k G hG S i hi ν hν
    rw [hcent, torusCentralizer_carrier_base] at hl
    exact hl
  have hlN : l ∈ normalizerPoints i := centralizerPoints_le_normalizerPoints i hlC
  obtain ⟨z', hz'⟩ : ∃ z', z' = (⟨l, hlN⟩ : normalizerPoints i) • z := ⟨_, rfl⟩
  obtain ⟨u', hu'⟩ : ∃ u', u' = l * u * l⁻¹ := ⟨_, rfl⟩
  have hu'U : u' ∈ (Dynamic.unipotent
      (CommGroupScheme.groupHom ν ≫ i)).carrier (Over.mk (𝟙 _)) := by
    rw [hu']
    exact Dynamic.conj_mem_unipotent _ (Dynamic.centralizer_le_parabolic _ _ hl) hu
  have hgz : (κ * (l * u)) • D.apartmentMap z = κ • u' • D.apartmentMap z' := by
    rw [hz', hu', D.apartmentMap_smul, smul_smul, smul_smul]
    congr 1
    show κ * (l * u) = κ * (l * u * l⁻¹) * l
    group
  rw [hgz] at hy ⊢
  -- the translate `y' = u' • [z']` is fixed by `K`
  have hy' : ∀ g ∈ K, g • u' • D.apartmentMap z' = u' • D.apartmentMap z' := by
    intro g hg
    have h := hy (κ * g * κ⁻¹) (mul_mem (mul_mem hκ hg) (inv_mem hκ))
    generalize u' • D.apartmentMap z' = y₀ at h ⊢
    calc g • y₀ = κ⁻¹ • (κ * g * κ⁻¹) • κ • y₀ := by
          rw [smul_smul, smul_smul]
          congr 1
          group
      _ = κ⁻¹ • κ • y₀ := by rw [h]
      _ = y₀ := inv_smul_smul κ y₀
  have hsz' : (⟨s, centralizerPoints_le_normalizerPoints i hsC⟩ : normalizerPoints i) • z' =
      z' := smul_eq_self_of_mem_centralizerPoints (D := D)
        (n := ⟨s, centralizerPoints_le_normalizerPoints i hsC⟩) hsC hsx
  have hu'X := D.mem_positiveRootGroups_of_smul_smul_eq hG hi hred ν hν z' hsC hsz'
    (fun b hb h hh => hsval b hb h hh z') hu'U (hy' s hsK)
  have hu'z : u' • D.apartmentMap z' = D.apartmentMap z' :=
    (D.mem_reducedFixer).mp (D.positiveRootGroups_le_reducedFixer ν z' hu'X)
  rw [hu'z] at hy' ⊢
  have hz'x : z' = x := D.eq_of_filtration_le_reducedFixer hG hi hred x z' hzero
    (fun a ha u hu => hy' u (hroot0 a ha hu))
  rw [hz'x]
  exact hKx κ hκ

end KPApartmentData

end Langlands.Geometry.Building
