import Langlands.Representation.Plancherel.RationalPlancherelConstant
import Langlands.GroupScheme.Rational.SplitTorusCentralizerReduction
import Langlands.GroupScheme.Rational.DynamicSemistandardIntersectionModels
import Langlands.GroupScheme.Dynamic.RelativeCentralizerComparison
import Langlands.AlgebraicGeometry.PointTopology.RepresentedSubgroup
import Langlands.GroupScheme.Torus.WeightRestriction

/-! # Finiteness of the rank-one constants `γ(M_α|M)` and of `c(G|M)`

Waldspurger 2003, I.1 (p.241) uses that the constants `γ(M_α|M)` entering
`c(G|M) = γ(G|M)⁻¹ ∏_{α ∈ Σ_red(P)} γ(M_α|M)` are finite and positive. For a split torus
`i : T → G` of a smooth connected affine group `G` over a nonarchimedean local field, this file
proves:

* every submodule centralizer `cocharacterSubmoduleCentralizer i N` is the dynamic centralizer
  of a single cocharacter `ν ∈ N`, generic in `N` for the roots of `T`
  (`exists_dynamicCentralizer_eq_cocharacterSubmoduleCentralizer`);
* the source constant `γ^L` of a closed subgroup `L ⊆ G(F)` that is the group of points of a
  smooth closed subgroup scheme `H` through which the cocharacter factors equals the Library's
  `γ` of `H` (`leviGamma_eq_gamma_of_isClosedSubgroup`), hence is finite;
* consequently every `rankOneGamma i ζ K hK N` is finite, and `c(G|M)` lies in `(0, ∞)`
  (`plancherelConstant_ne_top_of_isSplitTorus`, `plancherelConstantReal_pos_of_isSplitTorus`).
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory Topology
open scoped CategoryTheory.MonObj ENNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Plancherel.RationalDynamicSource

open Aubert.General Haar HarishChandraSchwartz
open BruhatTits.DynamicUnipotentContainment

/-! ### Common-compact source constants along closed embeddings -/

section Embedding

variable {A : Type*} {B : Type*} [Group A] [Group B] [TopologicalSpace A] [TopologicalSpace B]

/-- An embedding homomorphism `emb : B → A` restricts to an isomorphism of topological groups from
a subgroup `P` of `B` onto a subgroup `P'` of `A` when `emb⁻¹ P' = P` and `P' ⊆ emb(B)`. -/
def subgroupEmbeddingEquiv (emb : B →* A) (hemb : IsEmbedding emb) (P : Subgroup B)
    (P' : Subgroup A) (hpar : ∀ b, emb b ∈ P' ↔ b ∈ P) (hrange : ∀ a ∈ P', ∃ b, emb b = a) :
    P ≃ₜ* P' := by
  let f : P →* P' :=
    { toFun := fun p => ⟨emb (p : B), (hpar p).2 p.2⟩
      map_one' := Subtype.ext (map_one emb)
      map_mul' := fun x y => Subtype.ext (map_mul emb (x : B) (y : B)) }
  have hbij : Function.Bijective f := by
    refine ⟨fun x y h => Subtype.ext (hemb.injective (congrArg Subtype.val h)), fun a => ?_⟩
    obtain ⟨b, hb⟩ := hrange a a.2
    exact ⟨⟨b, (hpar b).1 (hb ▸ a.2)⟩, Subtype.ext hb⟩
  let e := MulEquiv.ofBijective f hbij
  refine { e with continuous_toFun := ?_, continuous_invFun := ?_ }
  · exact (hemb.continuous.comp continuous_subtype_val).subtype_mk _
  · change Continuous (fun a : P' => e.symm a)
    have hemb : IsEmbedding (fun p : P => emb (p : B)) := hemb.comp IsEmbedding.subtypeVal
    rw [hemb.continuous_iff]
    have h : ((fun p : P => emb (p : B)) ∘ fun a : P' => e.symm a) = fun a : P' => (a : A) := by
      funext a
      exact congrArg Subtype.val (e.apply_symm_apply a)
    rw [h]
    exact continuous_subtype_val

@[simp] theorem subgroupEmbeddingEquiv_apply_coe (emb : B →* A) (hemb : IsEmbedding emb)
    (P : Subgroup B) (P' : Subgroup A) (hpar : ∀ b, emb b ∈ P' ↔ b ∈ P)
    (hrange : ∀ a ∈ P', ∃ b, emb b = a) (p : P) :
    (subgroupEmbeddingEquiv emb hemb P P' hpar hrange p : A) = emb p :=
  rfl

variable [IsTopologicalGroup A] [IsTopologicalGroup B]
  [MeasurableSpace A] [BorelSpace A] [MeasurableSpace B] [BorelSpace B] [LocallyCompactSpace A]

/-- Along a closed embedding `emb : B → A`, the source-normalized Haar measure of a closed subgroup
`P` of `B` for `emb⁻¹ K` is carried to that of its image `P'` for `K`, with no scalar. -/
theorem measurePreserving_subgroupEmbeddingEquiv (emb : B →* A) (hemb : IsClosedEmbedding emb)
    (K : OpenSubgroup A) (hK : IsCompact (K : Set A))
    {P : Subgroup B} {P' : Subgroup A} (hP : IsClosed (P : Set B))
    (hP' : IsClosed (P' : Set A))
    (hpar : ∀ b, emb b ∈ P' ↔ b ∈ P) (hrange : ∀ a ∈ P', ∃ b, emb b = a) :
    MeasurePreserving (subgroupEmbeddingEquiv emb hemb.isEmbedding P P' hpar hrange)
      (subgroupCompactOpenHaar (K.comap emb hemb.continuous) (hemb.isCompact_preimage hK) P hP)
      (subgroupCompactOpenHaar K hK P' hP') := by
  let eP := subgroupEmbeddingEquiv emb hemb.isEmbedding P P' hpar hrange
  let sourceMu :=
    subgroupCompactOpenHaar (K.comap emb hemb.continuous) (hemb.isCompact_preimage hK) P hP
  have : sourceMu.Regular :=
    subgroupCompactOpenHaar_regular (K.comap emb hemb.continuous) (hemb.isCompact_preimage hK) P hP
  have : sourceMu.IsHaarMeasure :=
    subgroupCompactOpenHaar_isHaarMeasure (K.comap emb hemb.continuous)
      (hemb.isCompact_preimage hK) P hP
  have : (Measure.map eP sourceMu).Regular := Measure.Regular.map eP.toHomeomorph
  have : Measure.IsHaarMeasure (Measure.map eP sourceMu) := eP.isHaarMeasure_map sourceMu
  have heHm : Measurable (eP : P → P') := eP.continuous.measurable
  refine ⟨heHm, ?_⟩
  apply compactOpenHaarAlong_eq_of_mass_one K hK P'.subtype hP'.isClosedEmbedding_subtypeVal
  change (Measure.map (eP : P → P') sourceMu) {h : P' | (h : A) ∈ K} = 1
  trans sourceMu (eP ⁻¹' {h : P' | (h : A) ∈ K})
  · exact Measure.map_apply heHm ((K.isOpen.preimage continuous_subtype_val).measurableSet)
  have hpre : eP ⁻¹' {h : P' | (h : A) ∈ K} =
      {p : P | (p : B) ∈ K.comap emb hemb.continuous} := by
    ext p
    exact Iff.rfl
  rw [hpre]
  exact subgroupCompactOpenHaar_mass _ _ P hP

/-- **Gamma along a closed embedding.** If `emb : B → A` is a closed embedding and `P', V'` are the
images of closed subgroups `P, V` of `B`, the common-compact open-cell constant of `P', V'` in
`A` for `K` equals that of `P, V` in `B` for `emb⁻¹ K`. -/
theorem compactNormalizedSourceGamma_eq_of_isClosedEmbedding (emb : B →* A)
    (hemb : IsClosedEmbedding emb) (K : OpenSubgroup A) (hK : IsCompact (K : Set A))
    {P V : Subgroup B} (hP : IsClosed (P : Set B)) (hV : IsClosed (V : Set B))
    {P' V' : Subgroup A} (hP' : IsClosed (P' : Set A)) (hV' : IsClosed (V' : Set A))
    (hpar : ∀ b, emb b ∈ P' ↔ b ∈ P) (hparRange : ∀ a ∈ P', ∃ b, emb b = a)
    (hopp : ∀ b, emb b ∈ V' ↔ b ∈ V) (hoppRange : ∀ a ∈ V', ∃ b, emb b = a) :
    compactNormalizedSourceGamma hP' K hK V' hV' =
      compactNormalizedSourceGamma hP (K.comap emb hemb.continuous) (hemb.isCompact_preimage hK)
        V hV := by
  let eP := subgroupEmbeddingEquiv emb hemb.isEmbedding P P' hpar hparRange
  let eV := subgroupEmbeddingEquiv emb hemb.isEmbedding V V' hopp hoppRange
  have hPm := measurePreserving_subgroupEmbeddingEquiv emb hemb K hK hP hP' hpar hparRange
  have hVm := measurePreserving_subgroupEmbeddingEquiv emb hemb K hK hV hV' hopp hoppRange
  unfold compactNormalizedSourceGamma openCellConstant
  rw [← hVm.lintegral_comp_emb eV.toHomeomorph.measurableEmbedding]
  refine lintegral_congr fun v => ?_
  rw [← hPm.lintegral_comp_emb eP.toHomeomorph.measurableEmbedding]
  refine lintegral_congr fun p => ?_
  change ((K : Subgroup A) : Set A).indicator 1 (emb (p : B) * (emb (v : B))⁻¹) =
    (((K.comap emb hemb.continuous : OpenSubgroup B) : Subgroup B) : Set B).indicator 1
      ((p : B) * (v : B)⁻¹)
  rw [← map_inv, ← map_mul]
  by_cases hx : emb ((p : B) * (v : B)⁻¹) ∈ K
  · rw [Set.indicator_of_mem (show emb ((p : B) * (v : B)⁻¹) ∈ ((K : Subgroup A) : Set A) from hx),
      Set.indicator_of_mem (show (p : B) * (v : B)⁻¹ ∈
        (((K.comap emb hemb.continuous : OpenSubgroup B) : Subgroup B) : Set B) from hx)]
    rfl
  · rw [Set.indicator_of_notMem
        (show emb ((p : B) * (v : B)⁻¹) ∉ ((K : Subgroup A) : Set A) from hx),
      Set.indicator_of_notMem (show (p : B) * (v : B)⁻¹ ∉
        (((K.comap emb hemb.continuous : OpenSubgroup B) : Subgroup B) : Set B) from hx)]

end Embedding

/-! ### A generic cocharacter of a cocharacter submodule -/

section Algebraic

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

/-- Finitely many characters, each nonzero somewhere on a submodule `N` of cocharacters, are
simultaneously nonzero at one cocharacter of `N`. -/
theorem exists_mem_forall_latticePairing_ne_zero (N : Submodule ℤ (cocharacterLattice T))
    (s : Finset (characterLattice T)) (hs : ∀ a ∈ s, ∃ ξ ∈ N, latticePairing T a ξ ≠ 0) :
    ∃ ν ∈ N, ∀ a ∈ s, latticePairing T a ν ≠ 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, N.zero_mem, fun a ha => by simp at ha⟩
  | @insert a s ha ih =>
    obtain ⟨ν, hνN, hν⟩ := ih fun b hb => hs b (Finset.mem_insert_of_mem hb)
    obtain ⟨ξ, hξN, hξ⟩ := hs a (Finset.mem_insert_self a s)
    let m : ℤ := 1 + ∑ c ∈ insert a s, |latticePairing T c ν|
    refine ⟨ν + m • ξ, N.add_mem hνN (N.smul_mem m hξN), fun b hb hzero => ?_⟩
    have hle : |latticePairing T b ν| ≤ ∑ c ∈ insert a s, |latticePairing T c ν| :=
      Finset.single_le_sum (f := fun c => |latticePairing T c ν|) (fun c _ => abs_nonneg _) hb
    have hpos : |latticePairing T b ν| < m := by
      change |latticePairing T b ν| < 1 + ∑ c ∈ insert a s, |latticePairing T c ν|
      linarith
    rw [map_add, map_zsmul, smul_eq_mul] at hzero
    by_cases hbξ : latticePairing T b ξ = 0
    · rw [hbξ, mul_zero, add_zero] at hzero
      have hba : b ≠ a := by
        rintro rfl
        exact hξ hbξ
      exact hν b (Finset.mem_of_mem_insert_of_ne hb hba) hzero
    · have h1 : 1 ≤ |latticePairing T b ξ| := Int.one_le_abs hbξ
      have hm0 : 0 < m := lt_of_le_of_lt (abs_nonneg _) hpos
      have h2 : |latticePairing T b ν| = m * |latticePairing T b ξ| := by
        rw [eq_neg_of_add_eq_zero_left hzero, abs_neg, abs_mul, abs_of_pos hm0]
      nlinarith

variable [IsAffineHom G.X.hom]

/-- `ν` is generic in the cocharacter submodule `N`: it lies in `N`, and every relative root
vanishing at `ν` vanishes on all of `N`. -/
def IsGenericInSubmodule (i : T.toGrp ⟶ G) (N : Submodule ℤ (cocharacterLattice T))
    (ν : cocharacterLattice T) : Prop :=
  ν ∈ N ∧ ∀ a ∈ relativeRoots i, latticePairing T a ν = 0 → ∀ ξ ∈ N, latticePairing T a ξ = 0

/-- With finitely many relative roots, every cocharacter submodule has a generic element. -/
theorem exists_isGenericInSubmodule (i : T.toGrp ⟶ G) (N : Submodule ℤ (cocharacterLattice T))
    (hfin : (relativeRoots i).Finite) : ∃ ν, IsGenericInSubmodule i N ν := by
  classical
  let S : Set (characterLattice T) :=
    {a | a ∈ relativeRoots i ∧ ∃ ξ ∈ N, latticePairing T a ξ ≠ 0}
  have hS : S.Finite := hfin.subset fun a ha => ha.1
  obtain ⟨ν, hνN, hν⟩ := exists_mem_forall_latticePairing_ne_zero N hS.toFinset
    (fun a ha => ((Set.Finite.mem_toFinset hS).mp ha).2)
  refine ⟨ν, hνN, fun a ha hzero ξ hξ => ?_⟩
  by_contra hne
  exact hν a ((Set.Finite.mem_toFinset hS).mpr ⟨ha, ξ, hξ, hne⟩) hzero

variable [LocallyOfFiniteType G.X.hom]

/-- If every relative root vanishing at `ν` vanishes at `ξ`, the zero weight space of `ν` in the
Lie algebra lies in that of `ξ`. -/
theorem weightSpace_zero_le_of_pairing (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
    (ν ξ : cocharacterLattice T)
    (h : ∀ a ∈ relativeRoots i, latticePairing T a ν = 0 → latticePairing T a ξ = 0) :
    weightSpace (CommGroupScheme.groupHom ν ≫ i) 0 ≤
      weightSpace (CommGroupScheme.groupHom ξ ≫ i) 0 := by
  classical
  rw [weightSpace_comp_eq_iSup hT isSplitTorus_gm ν i 0]
  refine iSup_le fun a' => ?_
  obtain ⟨a, ha'⟩ := a'
  change weightSpace i a ≤ _
  by_cases hbot : weightSpace i a = ⊥
  · rw [hbot]
    exact bot_le
  have hξa : ξ ≫ a = 0 := by
    by_cases ha0 : a = 0
    · subst a
      exact Limits.comp_zero
    have hroot : a ∈ relativeRoots i := mem_relativeRoots.mpr ⟨ha0, hbot⟩
    have hν0 : latticePairing T a ν = 0 := by
      rw [latticePairing_apply, ha', map_zero]
    have hξ0 := h a hroot hν0
    rw [latticePairing_apply] at hξ0
    exact (gmEndEquiv k).injective (hξ0.trans (map_zero _).symm)
  have hle := weightSpace_le_comp ξ i a
  rwa [hξa] at hle

variable [Smooth G.X.hom] [ConnectedSpace G.X.left]

/-- In a smooth connected affine group, if every relative root vanishing at `ν` vanishes at `ξ`,
then `Z_G(ν) ⊆ Z_G(ξ)`. -/
theorem dynamicCentralizer_le_of_pairing (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G)
    (ν ξ : cocharacterLattice T)
    (h : ∀ a ∈ relativeRoots i, latticePairing T a ν = 0 → latticePairing T a ξ = 0) :
    Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i) ≤
      Dynamic.centralizer (CommGroupScheme.groupHom ξ ≫ i) := by
  refine dynamicCentralizer_le_of_weightSpace_zero_le dynamicSmooth dynamicConnected dynamicLie
    lieSubgroupEquality _ _ ?_ ?_
  · exact (SubgroupFunctor.range_comp_le _ i).trans
      ((range_le_torusCentralizer i).trans (torusCentralizer_le_dynamicCentralizer i _))
  · rw [map_zero]
    exact weightSpace_zero_le_of_pairing hT i ν ξ h

/-- A generic element `ν` of `N` has the same centralizer as the whole submodule `N`. -/
theorem dynamicCentralizer_eq_cocharacterSubmoduleCentralizer (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) {N : Submodule ℤ (cocharacterLattice T)} {ν : cocharacterLattice T}
    (hν : IsGenericInSubmodule i N ν) :
    Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i) = cocharacterSubmoduleCentralizer i N := by
  apply le_antisymm
  · intro U g hg
    rw [mem_cocharacterSubmoduleCentralizer]
    intro ξ hξ
    exact dynamicCentralizer_le_of_pairing hT i ν ξ (fun a ha h0 => hν.2 a ha h0 ξ hξ) U hg
  · intro U g hg
    exact (mem_cocharacterSubmoduleCentralizer i N).1 hg ν hν.1

/-- **`M_α` is the centralizer of one cocharacter.** For a split torus of a smooth connected
affine group, every submodule centralizer is the dynamic centralizer of one cocharacter of the
submodule. -/
theorem exists_dynamicCentralizer_eq_cocharacterSubmoduleCentralizer (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) (N : Submodule ℤ (cocharacterLattice T)) :
    ∃ ν ∈ N, Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ i) =
      cocharacterSubmoduleCentralizer i N := by
  obtain ⟨ν, hν⟩ := exists_isGenericInSubmodule i N (hT.finite_relativeRoots i)
  exact ⟨ν, hν.1, dynamicCentralizer_eq_cocharacterSubmoduleCentralizer hT i hν⟩

end Algebraic

/-! ### Actual rational points -/

section Local

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

attribute [local instance] plancherelConstantPointTopology plancherelConstantPointMeasurable
  plancherelConstantPointBorel plancherelConstantFieldT2 plancherelConstantPointTopologicalGroup
  plancherelConstantPointLocallyCompact plancherelConstantFieldSecondCountable
  plancherelConstantPointSecondCountable plancherelConstantSubgroupSecondCountable

local notation "X₀" => Over.mk (𝟙 (Spec (CommRingCat.of F)))

variable {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
  [LocallyOfFiniteType G.X.hom]

section ClosedSubgroup

variable {H : GroupScheme (Spec (CommRingCat.of F))} [IsAffine H.X.left]
  [LocallyOfFiniteType H.X.hom]
  {S : SubgroupFunctor G} {j : H ⟶ G} (hj : S.IsRepresentedBy j) (hjc : IsClosedSubgroup j)

include hj hjc

/-- The point map `H(F) → G(F)`, `x ↦ x ≫ j`, of a closed subgroup scheme, as a group
homomorphism. -/
def closedSubgroupPointHom : RationalPoint F H.X →* RationalPoint F G.X :=
  (S.carrier X₀).subtype.comp
    (rationalPointSubgroupHomeomorph F S j hj hjc).toMulEquiv.toMonoidHom

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom]
  [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom] in
@[simp] theorem closedSubgroupPointHom_apply (x : RationalPoint F H.X) :
    closedSubgroupPointHom hj hjc x = x ≫ j.hom.hom :=
  rfl

omit [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType H.X.hom] in
theorem isClosedEmbedding_closedSubgroupPointHom :
    IsClosedEmbedding (closedSubgroupPointHom hj hjc) := by
  have : IsClosedImmersion j.hom.hom.left := hjc
  exact isClosedEmbedding_rationalPointMap F j.hom.hom

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom]
  [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom] in
theorem closedSubgroupPointHom_mem (x : RationalPoint F H.X) :
    closedSubgroupPointHom hj hjc x ∈ S.carrier X₀ :=
  (rationalPointSubgroupHomeomorph F S j hj hjc x).2

omit [ValuativeRel F] [IsNonarchimedeanLocalField F] [LocallyOfFiniteType G.X.hom]
  [IsAffine H.X.left] [LocallyOfFiniteType H.X.hom] in
theorem exists_closedSubgroupPointHom_eq {a : RationalPoint F G.X} (ha : a ∈ S.carrier X₀) :
    ∃ x, closedSubgroupPointHom hj hjc x = a := by
  obtain ⟨x, hx⟩ := (hj.pointsEquiv X₀).surjective ⟨a, ha⟩
  exact ⟨x, congrArg Subtype.val hx⟩

/-- The compact open subgroup of `H(F)` that is the preimage of `K` under the point map. -/
abbrev closedSubgroupCompact (K : OpenSubgroup (RationalPoint F G.X)) :
    OpenSubgroup (RationalPoint F H.X) :=
  K.comap (closedSubgroupPointHom hj hjc) (isClosedEmbedding_closedSubgroupPointHom hj hjc).continuous

omit [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType H.X.hom] in
theorem isCompact_closedSubgroupCompact (K : OpenSubgroup (RationalPoint F G.X))
    (hK : IsCompact (K : Set (RationalPoint F G.X))) :
    IsCompact (closedSubgroupCompact hj hjc K : Set (RationalPoint F H.X)) :=
  (isClosedEmbedding_closedSubgroupPointHom hj hjc).isCompact_preimage hK

/-- **`γ^L` of a closed subgroup scheme.** If the closed subgroup `L = S(F)` of `G(F)` is the
group of points of a closed subgroup scheme `j : H → G`, and `χ = χ' ≫ j` for a cocharacter `χ'`
of `H`, then `γ^L(P_G(χ) ∩ L)` is the Library's `γ` of `P_H(χ')` in `H`, for the compact open
preimage of `K` in `H(F)`. -/
theorem leviGamma_eq_gamma_of_isClosedSubgroup
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (χ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ H) (hχ : χ' ≫ j = χ)
    (K : OpenSubgroup (RationalPoint F G.X)) (hK : IsCompact (K : Set (RationalPoint F G.X)))
    (hS : IsClosed ((S.carrier X₀ : Subgroup (RationalPoint F G.X)) :
      Set (RationalPoint F G.X))) :
    leviGamma χ K hK (S.carrier X₀) hS =
      gamma χ' (closedSubgroupCompact hj hjc K) (isCompact_closedSubgroupCompact hj hjc K hK) := by
  have hpar := Dynamic.parabolic_eq_comap_of_isClosedSubgroup χ' j hjc
  have hopp := Dynamic.unipotent_eq_comap_of_isClosedSubgroup (oppositeCocharacter χ') j hjc
  have hoppχ : oppositeCocharacter χ' ≫ j = oppositeCocharacter χ := by
    rw [oppositeCocharacter, oppositeCocharacter, Category.assoc, hχ]
  exact compactNormalizedSourceGamma_eq_of_isClosedEmbedding (closedSubgroupPointHom hj hjc)
    (isClosedEmbedding_closedSubgroupPointHom hj hjc) K hK
    (isClosed_dynamic_parabolic F H χ') (isClosed_unipotentPoints (oppositeCocharacter χ'))
    (isClosed_parabolic_inf χ _ hS) (isClosed_oppositeRadical_inf χ _ hS)
    (fun x => by
      change x ≫ j.hom.hom ∈ SubgroupFunctor.carrier (Dynamic.parabolic χ) X₀ ⊓ S.carrier X₀ ↔
        x ∈ SubgroupFunctor.carrier (Dynamic.parabolic χ') X₀
      rw [Subgroup.mem_inf, hpar, SubgroupFunctor.mem_comap, hχ]
      exact ⟨fun h => h.1, fun h => ⟨h, closedSubgroupPointHom_mem hj hjc x⟩⟩)
    (fun a ha => exists_closedSubgroupPointHom_eq hj hjc (Subgroup.mem_inf.mp ha).2)
    (fun x => by
      change x ≫ j.hom.hom ∈ unipotentPoints (oppositeCocharacter χ) ⊓ S.carrier X₀ ↔
        x ∈ unipotentPoints (oppositeCocharacter χ')
      rw [Subgroup.mem_inf, unipotentPoints, unipotentPoints, hopp, SubgroupFunctor.mem_comap,
        hoppχ]
      exact ⟨fun h => h.1, fun h => ⟨h, closedSubgroupPointHom_mem hj hjc x⟩⟩)
    (fun a ha => exists_closedSubgroupPointHom_eq hj hjc (Subgroup.mem_inf.mp ha).2)

/-- For a smooth closed subgroup scheme through which the cocharacter factors, `γ^L` is finite. -/
theorem leviGamma_ne_top_of_isClosedSubgroup [Smooth H.X.hom]
    (χ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (χ' : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ H) (hχ : χ' ≫ j = χ)
    (K : OpenSubgroup (RationalPoint F G.X)) (hK : IsCompact (K : Set (RationalPoint F G.X)))
    (hS : IsClosed ((S.carrier X₀ : Subgroup (RationalPoint F G.X)) :
      Set (RationalPoint F G.X))) :
    leviGamma χ K hK (S.carrier X₀) hS ≠ ⊤ := by
  rw [leviGamma_eq_gamma_of_isClosedSubgroup hj hjc χ χ' hχ K hK hS]
  exact (gamma_ne_zero_ne_top_of_smooth _ _ χ').2

end ClosedSubgroup

section RankOne

variable {T : CommGroupScheme (Spec (CommRingCat.of F))} (i : T.toGrp ⟶ G)
  (ζ : cocharacterLattice T)
  (K : OpenSubgroup (RationalPoint F G.X)) (hK : IsCompact (K : Set (RationalPoint F G.X)))
  [Smooth G.X.hom] [ConnectedSpace G.X.left]

/-- **Finiteness of `γ(M_α|M)`.** For a split torus `T` of a smooth connected affine group, every
rank-one constant `rankOneGamma i ζ K hK N` is finite: `M_N = Z_G(ν)` for a generic `ν ∈ N`, the
centralizer scheme of `ν` is smooth, and `ζ` factors through it. -/
theorem rankOneGamma_ne_top (hT : IsSplitTorus T.toGrp)
    (N : Submodule ℤ (cocharacterLattice T)) : rankOneGamma i ζ K hK N ≠ ⊤ := by
  obtain ⟨ν, -, hνN⟩ := exists_dynamicCentralizer_eq_cocharacterSubmoduleCentralizer hT i N
  let ψ := CommGroupScheme.groupHom ν ≫ i
  have hjψ := Dynamic.Affine.isRepresentedBy_centralizerHom ψ
  have hjc := Dynamic.Affine.isClosedSubgroup_centralizerHom ψ
  have hj : (cocharacterSubmoduleCentralizer i N).IsRepresentedBy
      (Dynamic.Affine.centralizerHom ψ) := by
    rw [← hνN]
    exact hjψ
  have : IsClosedImmersion (Dynamic.Affine.centralizerHom ψ).hom.hom.left := hjc
  have : IsAffine (Dynamic.Affine.centralizerScheme ψ).X.left :=
    isAffine_of_isAffineHom (Dynamic.Affine.centralizerHom ψ).hom.hom.left
  have : Smooth (Dynamic.Affine.centralizerScheme ψ).X.hom :=
    Dynamic.smooth_affineCentralizer_overRing ψ inferInstance
  have : LocallyOfFiniteType (Dynamic.Affine.centralizerScheme ψ).X.hom := inferInstance
  exact leviGamma_ne_top_of_isClosedSubgroup hj hjc _
    (Dynamic.intersectionCocharacter i (CommGroupScheme.groupHom ν)
      (CommGroupScheme.groupHom ζ) hjψ)
    (Dynamic.intersectionCocharacter_comp i _ _ hjψ) K hK _

theorem rankOneGammaProduct_ne_top_of_isSplitTorus (hT : IsSplitTorus T.toGrp) :
    rankOneGammaProduct i ζ K hK ≠ ⊤ :=
  rankOneGammaProduct_ne_top i ζ K hK fun N _ => rankOneGamma_ne_top i ζ K hK hT N

/-- **`c(G|M)` is finite.** -/
theorem plancherelConstant_ne_top_of_isSplitTorus (hT : IsSplitTorus T.toGrp) :
    plancherelConstant i ζ K hK ≠ ⊤ :=
  plancherelConstant_ne_top i ζ K hK fun N _ => rankOneGamma_ne_top i ζ K hK hT N

/-- **`0 < c(G|M) < ∞`.** -/
theorem plancherelConstant_pos_ne_top (hT : IsSplitTorus T.toGrp) :
    0 < plancherelConstant i ζ K hK ∧ plancherelConstant i ζ K hK ≠ ⊤ :=
  ⟨pos_iff_ne_zero.mpr (plancherelConstant_ne_zero_of_smooth i ζ K hK),
    plancherelConstant_ne_top_of_isSplitTorus i ζ K hK hT⟩

/-- The real value of `c(G|M)` is positive. -/
theorem plancherelConstantReal_pos_of_isSplitTorus (hT : IsSplitTorus T.toGrp) :
    0 < plancherelConstantReal i ζ K hK :=
  plancherelConstantReal_pos_of_smooth i ζ K hK fun N _ => rankOneGamma_ne_top i ζ K hK hT N

end RankOne

end Local

end Langlands.Plancherel.RationalDynamicSource
