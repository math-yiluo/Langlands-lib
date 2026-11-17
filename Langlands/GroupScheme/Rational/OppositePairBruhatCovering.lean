import Langlands.GroupScheme.Rational.RootGeneratedCentralizerReduction
import Langlands.GroupScheme.Rational.RootSystemFromFactorPairs
import Langlands.GroupScheme.Rational.DynamicRadicalRootGeneration
import Langlands.GroupScheme.Rational.CentralizerElementaryProduct
import Langlands.GroupScheme.Rational.SimplyConnectedCentralizerProductReduction
import Langlands.GroupScheme.Rational.RootGeneratedSubgroup
import Langlands.GroupScheme.Rational.RelativeTitsNondegeneracy
import Langlands.GroupScheme.Absolute.BruhatCoveringStatement
import Langlands.AlgebraicGeometry.PointTopology.SmoothSeparablyClosedDensity

/-! # The Bruhat covering for a generic dynamic parabolic from opposite root pairs -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.Aubert.General.RationalPointFamily

namespace Langlands.GroupScheme

namespace RelativeRoot

variable {k : Type u} [Field k]
  {S : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- At one actual maximal split torus and cocharacter, disjoint indivisible positive rays give
the ordered factorization of the rational points of `U(ν)` along every enumeration of the
indivisible positive roots. -/
theorem hasOrderedRootPointFactorization_of_disjoint_positive_rays
    (hG : IsConnectedReductive G) {i : S.toGrp ⟶ G}
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice S)
    (hdisj : ∀ a ∈ indivisiblePositiveRoots i ν,
      ∀ b ∈ indivisiblePositiveRoots i ν, a ≠ b →
        Disjoint (cyclicTail a 1 : Set (characterLattice S))
          (cyclicTail b 1 : Set (characterLattice S))) :
    HasOrderedRootPointFactorization i ν := by
  have := hG.smooth
  intro n a hinj ha x hx
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
  exact exists_orderedRootPoints (e := asIso (orderedMultiplication jH)) (hDynamic ▸ hjU)
    hfactor (orderedMultiplication_comp jH jU) hx

end RelativeRoot

section Covering

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

local instance oppositePairBruhatCoveringIsAffine {K : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom K.X.hom] : IsAffine K.X.left := isAffine_of_isAffineHom K.X.hom

/-- **Generation by root groups and the torus centralizer.** Over a separably closed field,
let `i` be a maximal split torus of a connected reductive group and `ν` a generic cocharacter
whose distinct indivisible positive (and negative) roots have disjoint integral rays. Then every
rational point is a product `h * z` of a point `h` of the subgroup generated by the actual root
groups and a point `z` centralizing the torus. The proof writes a rational point as a product
of two points of the opposite open cell. -/
theorem exists_relativeRootGenerated_mul_centralizer_of_isSepClosed [IsSepClosed k]
    (hG : IsConnectedReductive G) {i : T.toGrp ⟶ G} (hi : IsMaximalSplitTorus i)
    {ν : cocharacterLattice T} (hν : IsGenericCocharacter i ν)
    (hdisj : ∀ ξ ∈ ({ν, -ν} : Set (cocharacterLattice T)),
      ∀ a ∈ RelativeRoot.indivisiblePositiveRoots i ξ,
      ∀ b ∈ RelativeRoot.indivisiblePositiveRoots i ξ, a ≠ b →
        Disjoint (RelativeRoot.cyclicTail a 1 : Set (characterLattice T))
          (RelativeRoot.cyclicTail b 1 : Set (characterLattice T)))
    (g : rationalPoints G) :
    ∃ h ∈ relativeRootGeneratedSubgroup i, ∃ z ∈ centralizerPoints i, g = h * z := by
  have := hG.smooth
  have := hG.connectedSpace
  have := hi.isSplitSubtorus.mono
  let χ := CommGroupScheme.groupHom ν ≫ i
  let N := relativeRootGeneratedSubgroup i
  have hd := Langlands.AlgebraicGeometry.PointTopology.hasDenseRationalPoints_of_smooth_of_isSepClosed
    k G.X
  have hU : (Dynamic.unipotent χ).rationalPoints ≤ N :=
    dynamicUnipotent_le_relativeRootGeneratedSubgroup i hG hi ν (hdisj ν (Or.inl rfl))
  have hU' : (Dynamic.unipotent
      (CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ χ)).rationalPoints
        ≤ N := by
    have h := dynamicUnipotent_le_relativeRootGeneratedSubgroup i hG hi (-ν)
      (hdisj (-ν) (Or.inr rfl))
    rw [groupHom_neg_comp_eq_oppositeCocharacter i ν] at h
    exact h
  have hZ : ∀ z ∈ (Dynamic.centralizer χ).rationalPoints, z ∈ centralizerPoints i := by
    intro z hz
    have hgen := genericCentralizer k G hG T i hi ν hν
    change z ∈ (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)) at hz
    rw [hgen, torusCentralizer_carrier_base] at hz
    exact hz
  let m := Dynamic.oppositeCellMul χ
  have : IsOpenImmersion m.left := Dynamic.isOpenImmersion_oppositeCellMul χ
  have hne : (Set.range m.left).Nonempty :=
    ⟨_, ⟨(CartesianMonoidalCategory.lift (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
        (Dynamic.Affine.unipotentScheme (CommGroupScheme.groupHom
          (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ χ)).X)
      (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ (Dynamic.Affine.parabolicScheme χ).X)).left
        (IsLocalRing.closedPoint k), rfl⟩⟩
  obtain ⟨c, hc, hcg⟩ := Dynamic.exists_mem_open_inv_mul_mem_open hd
    m.left.isOpenEmbedding.isOpen_range hne g
  obtain ⟨z₁, hz₁, hn₁⟩ := Dynamic.exists_centralizer_of_mem_cell χ N hU hU' c hc
  obtain ⟨z₂, hz₂, hn₂⟩ := Dynamic.exists_centralizer_of_mem_cell χ N hU hU' (c⁻¹ * g) hcg
  have hz₁C := hZ z₁ hz₁
  have hz₂C := hZ z₂ hz₂
  have hconj : z₁ * ((c⁻¹ * g) * z₂⁻¹) * z₁⁻¹ ∈ N :=
    (Subgroup.mem_normalizer_iff.mp
      (normalizerPoints_le_normalizer_relativeRootGeneratedSubgroup i
        (centralizerPoints_le_normalizerPoints i hz₁C)) _).mp hn₂
  refine ⟨(c * z₁⁻¹) * (z₁ * ((c⁻¹ * g) * z₂⁻¹) * z₁⁻¹), N.mul_mem hn₁ hconj, z₁ * z₂,
    (centralizerPoints i).mul_mem hz₁C hz₂C, ?_⟩
  group

/-- Opposite factor pairs at a maximal split torus give disjoint integral rays of distinct
indivisible positive roots, for every cocharacter. -/
theorem disjoint_positive_rays_of_oppositeFactorPairs
    (hG : IsConnectedReductive G) {i : T.toGrp ⟶ G} (hi : IsMaximalSplitTorus i)
    (hE : RelativeRoot.HasOppositeFactorPairs i) (ξ : cocharacterLattice T) :
    ∀ a ∈ RelativeRoot.indivisiblePositiveRoots i ξ,
      ∀ b ∈ RelativeRoot.indivisiblePositiveRoots i ξ, a ≠ b →
        Disjoint (RelativeRoot.cyclicTail a 1 : Set (characterLattice T))
          (RelativeRoot.cyclicTail b 1 : Set (characterLattice T)) := by
  have := hG.smooth
  have := hi.isSplitSubtorus.mono
  intro a ha b hb hne
  exact hE.disjoint_cyclicTail_indivisibleRoots i hi.isSplitSubtorus.1 ha.1 hb.1 hne

/-- **Tits word covering from opposite factor pairs.** Let `i` be a maximal split torus of a
connected reductive group over a field and `ν` a generic cocharacter. If every nonidentity
point of every actual root group admits an opposite factor pair, then the subgroup generated by
the actual root groups is covered by the double cosets `U(ν)(k) n U(ν)(k)` with `n` normalizing
the torus. -/
theorem hasRootGeneratedBruhatCovering_normalizerPoints_of_oppositeFactorPairs
    (hG : IsConnectedReductive G) {i : T.toGrp ⟶ G} (hi : IsMaximalSplitTorus i)
    {ν : cocharacterLattice T} (hν : IsGenericCocharacter i ν)
    (hE : RelativeRoot.HasOppositeFactorPairs i) :
    haveI := hi.isSplitSubtorus.mono
    HasRootGeneratedBruhatCovering i ν (normalizerPoints i) := by
  have := hG.smooth
  have := hi.isSplitSubtorus.mono
  have hT : IsSplitTorus T.toGrp := hi.isSplitSubtorus.1
  have hroot : HasRelativeRootSystem i :=
    RelativeRoot.hasRelativeRootSystem_of_hasOppositeFactorPairs i hG hi hE
  let D := RelativeRootReflectionData.ofOppositeFactorPairs i hT hE
  have hcox : HasRelativeWeylCoxeterSystem i ν :=
    D.hasRelativeWeylCoxeterSystem_of_rootPairingWeylCoxeter
      Langlands.Group.rootPairingWeylCoxeterStatement_proof hT hroot hν
      (fun a => (RelativeRoot.rootGeneratedRepresentative_spec i hT hE a).2.2)
  obtain ⟨_, _, C, cs, hcs⟩ := hcox
  have hSimple : ∀ a : SimpleRoot i ν, IsRelativeReflection i a.val (cs.simple a) :=
    hcs.isRelativeReflection_simple
  have hprod : HasOrderedRootPointFactorization i ν :=
    RelativeRoot.hasOrderedRootPointFactorization_of_disjoint_positive_rays hG hi ν
      (disjoint_positive_rays_of_oppositeFactorPairs hG hi hE ν)
  have hfac : HasSimpleRootUnipotentFactorization i ν :=
    hasSimpleRootUnipotentFactorization_of_orderedRootPoints i ν hν
      (fun _ ha => hroot.neg_mem_relativeRoots i hT ha)
      (hroot.linearIndependent_simpleRelativeRoots i ν hT hν)
      (hroot.finite_relativeRoots i hT) hprod
  obtain ⟨m, hm, hmL, -⟩ :=
    hasRootGeneratedSimpleReflectionLifts_of_oppositeFactorPairs i ν hT hroot hν hE cs hSimple
  intro g hg
  obtain ⟨u, hu, n, hn, v, hv, rfl⟩ :=
    hasRootGeneratedBruhatCovering_rankOneLiftPoints i ν hT hroot hν hfac hE cs hSimple m hm
      hmL hg
  exact ⟨u, hu, n, RelativeRoot.rankOneLiftPoints_le_normalizerPoints i m hn, v, hv, rfl⟩

/-- **Rational Bruhat covering from opposite factor pairs.** Over a separably closed field, let
`i` be a maximal split torus of a connected reductive group and `ν` a generic cocharacter. If
every nonidentity point of every actual root group admits an opposite factor pair, then every
rational point is `u * n * v` with `u, v` in `U(ν)(k)` and `n` normalizing the torus. -/
theorem exists_unipotent_normalizer_unipotent_of_oppositeFactorPairs [IsSepClosed k]
    (hG : IsConnectedReductive G) {i : T.toGrp ⟶ G} (hi : IsMaximalSplitTorus i)
    {ν : cocharacterLattice T} (hν : IsGenericCocharacter i ν)
    (hE : RelativeRoot.HasOppositeFactorPairs i) (g : rationalPoints G) :
    ∃ u ∈ RationalPoint.unipotent (CommGroupScheme.groupHom ν ≫ i),
      ∃ n ∈ normalizerPoints i,
        ∃ v ∈ RationalPoint.unipotent (CommGroupScheme.groupHom ν ≫ i), g = u * n * v := by
  have := hi.isSplitSubtorus.mono
  obtain ⟨h, hh, z, hz, rfl⟩ := exists_relativeRootGenerated_mul_centralizer_of_isSepClosed hG hi
    hν (fun ξ _ => disjoint_positive_rays_of_oppositeFactorPairs hG hi hE ξ) g
  obtain ⟨u, hu, n, hn, v, hv, rfl⟩ :=
    hasRootGeneratedBruhatCovering_normalizerPoints_of_oppositeFactorPairs hG hi hν hE hh
  refine ⟨u, hu, n * z, (normalizerPoints i).mul_mem hn
    (centralizerPoints_le_normalizerPoints i hz), z⁻¹ * v * z⁻¹⁻¹,
    centralizerPoints_conj_mem_dynamicUnipotent i ν ((centralizerPoints i).inv_mem hz) hv, ?_⟩
  group

/-- **The Bruhat covering for a generic dynamic parabolic.** Over a separably closed field, let
`i` be a maximal split torus of a connected reductive group and `ν` a generic cocharacter. If
every nonidentity point of every actual root group admits an opposite factor pair, then the
closed subgroup representing `P(ν)` satisfies `G(k) = P(k) N_G(T)(k) P(k)` with the torus `i`. -/
theorem borelTorusBruhatCovering_parabolicHom_of_oppositeFactorPairs [IsSepClosed k]
    (hG : IsConnectedReductive G) {i : T.toGrp ⟶ G} (hi : IsMaximalSplitTorus i)
    {ν : cocharacterLattice T} (hν : IsGenericCocharacter i ν)
    (hE : RelativeRoot.HasOppositeFactorPairs i) :
    BorelTorusBruhatCovering (Dynamic.Affine.parabolicHom (CommGroupScheme.groupHom ν ≫ i)) i := by
  intro g
  obtain ⟨u, hu, n, hn, v, hv, rfl⟩ :=
    exists_unipotent_normalizer_unipotent_of_oppositeFactorPairs hG hi hν hE g
  have hrep := Dynamic.Affine.isRepresentedBy_parabolicHom (CommGroupScheme.groupHom ν ≫ i)
  have hu' := RationalPoint.unipotent_le_parabolic _ hu
  have hv' := RationalPoint.unipotent_le_parabolic _ hv
  change u ∈ (Dynamic.parabolic _).carrier _ at hu'
  change v ∈ (Dynamic.parabolic _).carrier _ at hv'
  rw [← hrep.2] at hu' hv'
  obtain ⟨b₁, rfl⟩ := hu'
  obtain ⟨b₂, rfl⟩ := hv'
  exact ⟨b₁, b₂, ⟨n, hn⟩, rfl⟩

end Covering

end Langlands.GroupScheme
