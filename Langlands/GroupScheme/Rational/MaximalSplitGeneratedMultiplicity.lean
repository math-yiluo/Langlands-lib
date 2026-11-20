import Langlands.GroupScheme.Rational.MaximalSplitGeneratedWeights
import Langlands.GroupScheme.Dynamic.SchemeDecomposition
import Langlands.GroupScheme.Dynamic.LimitMap
import Langlands.GroupScheme.HomImageEmbedding
import Langlands.GroupScheme.Rational.CocharacterCentralizerPointDetection
import Langlands.GroupScheme.Dynamic.ParabolicLieCriterion
import Langlands.GroupScheme.Reductive.SplitLeviGluingGeneratedDensity
import Langlands.GroupScheme.Rational.RootSignUnipotentLie
import Langlands.GroupScheme.Lie.SignedDynamicDimension
import Langlands.GroupScheme.Rational.TangentImage
import Langlands.GroupScheme.Rational.MonicRootParametrization
import Langlands.GroupScheme.Rational.VectorLieCoordinates
import Langlands.GroupScheme.GeneratedFamily

/-! # Multiplicity one at the line weights of the generated split subgroup -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.GroupScheme.MaximalSplitSubgroup

open VectorGroup RootCell RelativeRoot

section SelfGeneration

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
    {I : Type*} {A : I → GroupScheme (Spec (CommRingCat.of k))} {a : ∀ j, A j ⟶ G}

/-- A generated closed subgroup is generated, as its own ambient group, by the lifts of the
family. -/
theorem IsGeneratedByFamily.self {V : GroupScheme (Spec (CommRingCat.of k))} {v : V ⟶ G}
    (hv : IsGeneratedByFamily A a v) (b : ∀ j, A j ⟶ V) (hb : ∀ j, b j ≫ v = a j) :
    IsGeneratedByFamily A b (𝟙 V) := by
  have : IsClosedImmersion v.hom.hom.left := hv.1
  have hmono : Mono v.hom.hom := Over.mono_of_mono_left _
  refine ⟨?_, ?_, ?_⟩
  · change IsClosedImmersion (𝟙 V.X.left)
    infer_instance
  · intro j
    exact ⟨(b j).hom.hom, by simp⟩
  · intro Q q hq hfamily
    have hsub : SubgroupFunctor.range v ≤ SubgroupFunctor.range (q ≫ v) := by
      apply hv.2.2 Q (q ≫ v) (hq.comp hv.1)
      intro j
      obtain ⟨c, hc⟩ := hfamily j
      refine ⟨c, ?_⟩
      rw [Grp.comp_hom_hom, ← Category.assoc, hc, ← Grp.comp_hom_hom, hb]
    intro W x _
    have hx : x ≫ v.hom.hom ∈ (SubgroupFunctor.range v).carrier W :=
      SubgroupFunctor.mem_range.mpr ⟨x, rfl⟩
    obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp (hsub W hx)
    apply SubgroupFunctor.mem_range.mpr
    refine ⟨y, hmono.right_cancellation _ _ ?_⟩
    simpa only [Grp.comp_hom_hom, Category.assoc] using hy

end SelfGeneration

section Projection

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {H : GroupScheme (Spec (CommRingCat.of k))}

theorem smooth_ga : Smooth (Ga k).X.hom :=
  Corepresented.smooth_groupScheme_iff.mpr inferInstance

theorem isAffineHom_ga : IsAffineHom (Ga k).X.hom := by
  change IsAffineHom (Spec.map (CommRingCat.ofHom (algebraMap k (MvPolynomial (Fin 1) k))))
  infer_instance

theorem connectedSpace_ga : ConnectedSpace (Ga k).X.left := by
  change ConnectedSpace (Spec (CommRingCat.of (MvPolynomial (Fin 1) k)))
  infer_instance

/-- A cocharacter `eta` *isolates* the index `i₀` of a family of characters `a` when it kills
`a i₀` and pairs positively with every other `a j`. -/
def IsIsolatingCocharacter {Idx : Type*} (a : Idx → characterLattice T) (i₀ : Idx)
    (eta : cocharacterLattice T) : Prop :=
  latticePairing T (a i₀) eta = 0 ∧ ∀ j, j ≠ i₀ → 0 < latticePairing T (a j) eta

/-- Lines of weight orthogonal or positive on `eta` lie in the dynamic parabolic of `eta`. -/
theorem range_le_parabolic_of_lines {Idx : Type*} (t : T.toGrp ⟶ H)
    (a : Idx → characterLattice T) (x : Idx → (Ga k ⟶ H))
    (hx : ∀ i, IsTorusEquivariant t (x i) (a i)) (i₀ : Idx) (eta : cocharacterLattice T)
    (heta : IsIsolatingCocharacter a i₀ eta)
    (j : Idx) :
    SubgroupFunctor.range (x j) ≤ Dynamic.parabolic (CommGroupScheme.groupHom eta ≫ t) := by
  obtain ⟨heta0, heta⟩ := heta
  by_cases hj : j = i₀
  · subst hj
    exact ((range_le_subgroup_of_isTorusEquivariant t _ (x j) (hx j)).trans
      (RelativeRoot.subgroup_le_dynamicCentralizer_of_pairing_eq_zero t _ eta heta0)).trans
        (Dynamic.centralizer_le_parabolic _)
  · exact ((range_le_subgroup_of_isTorusEquivariant t _ (x j) (hx j)).trans
      (RelativeRoot.subgroup_le_dynamicUnipotent t eta (heta j hj))).trans
        (Dynamic.unipotent_le_parabolic _)

/-- A morphism whose values on a set of rational points with dense locations lie in the range
of a closed immersion has its whole image in that range. -/
theorem range_subset_of_dense_rationalPoints {V E : GroupScheme (Spec (CommRingCat.of k))}
    (φ : V.X ⟶ H.X) (e : E ⟶ H) [IsClosedImmersion e.hom.hom.left] (S : Set (rationalPoints V))
    (hS : Dense (rationalPointImage V S)) (hφ : ∀ g ∈ S, g ≫ φ ∈ rangePts e) :
    Set.range φ.left ⊆ Set.range e.hom.hom.left := by
  have hC : IsClosed (Set.range e.hom.hom.left) := e.hom.hom.left.isClosedEmbedding.isClosed_range
  rintro _ ⟨p, rfl⟩
  have himg : φ.left '' rationalPointImage V S ⊆ Set.range e.hom.hom.left := by
    rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    obtain ⟨c, hc⟩ := SubgroupFunctor.mem_range.mp (hφ g hg)
    have h1 : (g ≫ φ).left (IsLocalRing.closedPoint k) =
        φ.left (g.left (IsLocalRing.closedPoint k)) := rfl
    have h2 : (c ≫ e.hom.hom).left (IsLocalRing.closedPoint k) =
        e.hom.hom.left (c.left (IsLocalRing.closedPoint k)) := rfl
    exact ⟨c.left (IsLocalRing.closedPoint k), by rw [← h2, hc, h1]⟩
  have hp : p ∈ closure (rationalPointImage V S) := by
    rw [hS.closure_eq]
    trivial
  exact closure_minimal himg hC
    (image_closure_subset_closure_image φ.left.continuous ⟨p, hp, rfl⟩)

/-- **Centralizer points of the generated subgroup lie on the orthogonal line.** Let `V` be
the closed subgroup generated by lines `x i` of weights `a i`, over an algebraically closed
field. If a cocharacter `eta` kills `a i₀` and pairs positively with every other `a j`, then
every point of `V` centralizing `eta` lies on the line `x i₀`. The proof sends `V` through the
limit homomorphism of the dynamic parabolic of `eta`, which maps `x i₀` identically and kills the
other lines. -/
theorem centralizer_points_mem_range_line [IsAlgClosed k] [Smooth H.X.hom] [IsAffineHom H.X.hom]
    {Idx : Type*} (t : T.toGrp ⟶ H) (a : Idx → characterLattice T) (x : Idx → (Ga k ⟶ H))
    (hx : ∀ i, IsTorusEquivariant t (x i) (a i)) (i₀ : Idx) (eta : cocharacterLattice T)
    (heta : IsIsolatingCocharacter a i₀ eta)
    (hmono : Mono (x i₀).hom.hom)
    {V : GroupScheme (Spec (CommRingCat.of k))} (v : V ⟶ H) [Smooth V.X.hom]
    [IsAffineHom V.X.hom] (hv : IsGeneratedByFamily (fun _ : Idx => Ga k) x v)
    {W : Over (Spec (CommRingCat.of k))} (w : W ⟶ V.X)
    (hw : w ≫ v.hom.hom ∈ (Dynamic.centralizer (CommGroupScheme.groupHom eta ≫ t)).carrier W) :
    w ≫ v.hom.hom ∈ (SubgroupFunctor.range (x i₀)).carrier W := by
  classical
  have heta' := heta
  obtain ⟨heta0, heta⟩ := heta
  let : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  let χ := CommGroupScheme.groupHom eta ≫ t
  have hP := Dynamic.Affine.isRepresentedBy_parabolicHom χ
  have hZ := Dynamic.Affine.isRepresentedBy_centralizerHom χ
  have : IsClosedImmersion v.hom.hom.left := hv.1
  have hvmono : Mono v.hom.hom := Over.mono_of_mono_left _
  have hrv : (SubgroupFunctor.range v).IsRepresentedBy v := ⟨hvmono, rfl⟩
  have hvP : SubgroupFunctor.range v ≤ Dynamic.parabolic χ := by
    rw [← hP.2]
    exact hv.2.2 _ _ (Dynamic.Affine.isClosedSubgroup_parabolicHom χ) (fun j =>
      (factorsThrough_hom_iff_range_le (x j) _).mpr (by
        rw [hP.2]
        exact range_le_parabolic_of_lines t a x hx i₀ eta heta' j))
  let vP := hP.liftOfLE v hvP
  have hvP' : vP ≫ Dynamic.Affine.parabolicHom χ = v := hP.liftOfLE_comp v hvP
  let φ : V.X ⟶ H.X :=
    (vP ≫ Dynamic.limitGroupHom hP hZ ≫ Dynamic.Affine.centralizerHom χ).hom.hom
  have hφ : ∀ {W' : Over (Spec (CommRingCat.of k))} (w' : W' ⟶ V.X),
      w' ≫ φ = Dynamic.limit χ
        ⟨w' ≫ v.hom.hom, hvP _ (SubgroupFunctor.mem_range.mpr ⟨w', rfl⟩)⟩ := by
    intro W' w'
    have h := Dynamic.limitGroupHom_comp hP hZ (w' ≫ vP.hom.hom)
    have he : hP.pointsEquiv W' (w' ≫ vP.hom.hom) =
        ⟨w' ≫ v.hom.hom, hvP _ (SubgroupFunctor.mem_range.mpr ⟨w', rfl⟩)⟩ := by
      apply Subtype.ext
      rw [SubgroupFunctor.IsRepresentedBy.pointsEquiv_apply_coe, Category.assoc,
        ← Grp.comp_hom_hom, hvP']
    rw [he] at h
    rw [← h]
    simp only [φ, Grp.comp_hom_hom, Category.assoc]
  have hlimc : ∀ {W' : Over (Spec (CommRingCat.of k))} (g : (Dynamic.parabolic χ).carrier W'),
      (g : W' ⟶ H.X) ∈ (Dynamic.centralizer χ).carrier W' → Dynamic.limit χ g = g :=
    fun g hg => Dynamic.limit_eq χ (Dynamic.hasLimit_of_mem_centralizer χ hg)
  -- lifts of the lines into `V`
  let b : ∀ j : Idx, Ga k ⟶ V := fun j =>
    hrv.liftOfLE (x j) ((factorsThrough_hom_iff_range_le (x j) v).mp (hv.2.1 j))
  have hb : ∀ j, b j ≫ v = x j := fun j => hrv.liftOfLE_comp _ _
  -- the limit on rational points, as a monoid homomorphism
  let f : rationalPoints V →* rationalPoints H :=
    { toFun := fun g => g ≫ φ
      map_one' := MonObj.one_comp _
      map_mul' := fun g h => MonObj.mul_comp _ _ _ }
  have hcent0 : SubgroupFunctor.range (x i₀) ≤ Dynamic.centralizer χ :=
    (range_le_subgroup_of_isTorusEquivariant t _ (x i₀) (hx i₀)).trans
      (RelativeRoot.subgroup_le_dynamicCentralizer_of_pairing_eq_zero t _ eta heta0)
  have hgenf : Subgroup.closure (⋃ j, (rangePts (b j) : Set (rationalPoints V))) ≤
      (rangePts (x i₀)).comap f := by
    rw [Subgroup.closure_le]
    intro g hg
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hg
    obtain ⟨c, rfl⟩ := SubgroupFunctor.mem_range.mp hj
    change (c ≫ (b j).hom.hom) ≫ φ ∈ rangePts (x i₀)
    rw [hφ]
    have hc : (c ≫ (b j).hom.hom) ≫ v.hom.hom = c ≫ (x j).hom.hom := by
      rw [Category.assoc, ← Grp.comp_hom_hom, hb]
    by_cases hj0 : j = i₀
    · subst hj0
      have hmem : (c ≫ (b j).hom.hom) ≫ v.hom.hom ∈ (Dynamic.centralizer χ).carrier _ := by
        rw [hc]
        exact hcent0 _ (SubgroupFunctor.mem_range.mpr ⟨c, rfl⟩)
      rw [hlimc ⟨_, _⟩ hmem]
      exact SubgroupFunctor.mem_range.mpr ⟨c, hc.symm⟩
    · have hmem : (c ≫ (b j).hom.hom) ≫ v.hom.hom ∈ (Dynamic.unipotent χ).carrier _ := by
        rw [hc]
        exact ((range_le_subgroup_of_isTorusEquivariant t _ (x j) (hx j)).trans
          (RelativeRoot.subgroup_le_dynamicUnipotent t eta (heta j hj0))) _
            (SubgroupFunctor.mem_range.mpr ⟨c, rfl⟩)
      rw [(Dynamic.limit_eq_one_iff χ ⟨_, _⟩).mpr hmem]
      exact one_mem _
  -- density of the generated rational points of `V`
  have : Smooth (Ga k).X.hom := smooth_ga
  have : IsAffineHom (Ga k).X.hom := isAffineHom_ga
  have : ConnectedSpace (Ga k).X.left := connectedSpace_ga
  have hA : ∀ j : Idx, Smooth (Ga k).X.hom ∧ IsAffineHom (Ga k).X.hom ∧
      ConnectedSpace (Ga k).X.left := fun _ => ⟨inferInstance, inferInstance, inferInstance⟩
  have hdense := LeviGluing.dense_rationalPointImage_closure_of_isGeneratedByFamily
    (H := V) hA (IsGeneratedByFamily.self hv b hb)
  -- the closed line
  have hxc : IsClosedSubgroup (x i₀) := HomImage.isClosedSubgroup_of_mono (x i₀)
  have : IsClosedImmersion (x i₀).hom.hom.left := hxc
  have hrange : Set.range φ.left ⊆ Set.range (x i₀).hom.hom.left :=
    range_subset_of_dense_rationalPoints φ (x i₀) _ hdense (fun g hg => hgenf hg)
  have : IsReduced V.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field k _ V.X.hom
  obtain ⟨ψ, hψ⟩ := LeviGluing.factorsThrough_of_range_subset hxc φ hrange
  have hlim : w ≫ φ = w ≫ v.hom.hom := by
    rw [hφ]
    exact hlimc ⟨_, _⟩ hw
  rw [← hlim, ← hψ, ← Category.assoc]
  exact SubgroupFunctor.mem_range.mpr ⟨_, rfl⟩

end Projection

section Multiplicity

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {H : GroupScheme (Spec (CommRingCat.of k))}

attribute [local instance] isAffineHom_ga

/-- The weight space of a weight in a semigroup lies in the semigroup weight span. -/
theorem weightSpace_le_semigroupWeightSpan [IsAffineHom H.X.hom] (t : T.toGrp ⟶ H)
    (A : AddSubsemigroup (characterLattice T)) {χ : characterLattice T} (hχ : χ ∈ A) :
    weightSpace t χ ≤ semigroupWeightSpan (AutomorphicAction.conjugation t) A := by
  rw [← actionWeightSpace_conjugation t χ]
  exact le_iSup (fun c : A => actionWeightSpace (AutomorphicAction.conjugation t) c.val) ⟨χ, hχ⟩

/-- **Multiplicity one at a line weight** (CGP C.2.29, Step 2). Under the hypotheses of
`torusCentralizer_eq_range_of_generated`, let `eta` be a cocharacter killing `a i₀` and pairing
positively with every other `a j`. Then the weight space of `a i₀` is the differential image
of the line `x i₀`. -/
theorem weightSpace_eq_lie_range [IsAlgClosed k] [Smooth H.X.hom] [IsAffineHom H.X.hom]
    (hT : IsSplitTorus T.toGrp) {Idx : Type*}
    (t : T.toGrp ⟶ H) (a : Idx → characterLattice T) (ν : Idx → cocharacterLattice T)
    (x y : Idx → (Ga k ⟶ H))
    (hx : ∀ i, IsTorusEquivariant t (x i) (a i)) (hy : ∀ i, IsTorusEquivariant t (y i) (-a i))
    (hrel : ∀ i, RelationOver t (ν i) (x i) (y i) (Over.mk (𝟙 (Spec (CommRingCat.of k)))))
    (hcomm : ∀ i j, i ≠ j → ∀ g ∈ rangePts (x i), ∀ h ∈ rangePts (y j), Commute g h)
    (hgen : Dense (rationalPointImage H (Subgroup.closure
      ((⋃ i, (rangePts (x i) : Set (rationalPoints H))) ∪ (⋃ i, (rangePts (y i) : Set (rationalPoints H))) ∪
        (rangePts t : Set (rationalPoints H))) : Set (rationalPoints H))))
    (cch : cocharacterLattice T) (hpos : ∀ i, 0 < latticePairing T (a i) cch)
    (ht : IsClosedSubgroup t) (i₀ : Idx) (eta : cocharacterLattice T)
    (heta : IsIsolatingCocharacter a i₀ eta)
    [Mono (x i₀).hom.hom] :
    weightSpace t (a i₀) = LinearMap.range (Lie.targetMapLinear (x i₀) k) := by
  classical
  have heta' := heta
  obtain ⟨heta0, heta⟩ := heta
  refine le_antisymm ?_ (hx i₀).lie_range_le_weightSpace
  intro X hX
  let : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  have : Smooth (Ga k).X.hom := smooth_ga
  have : IsAffineHom (Ga k).X.hom := isAffineHom_ga
  have : ConnectedSpace (Ga k).X.left := connectedSpace_ga
  obtain ⟨V, v, hVs, hVa, -, hv⟩ := FiniteGeneration.exists_smooth_generated_family
    (G := H) (A := fun _ : Idx => Ga k) (a := x)
    (fun _ => ⟨inferInstance, inferInstance, inferInstance⟩)
  let χ := CommGroupScheme.groupHom cch ≫ t
  let χn := CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ χ
  have hn := Dynamic.Affine.isRepresentedBy_unipotentHom χn
  have hu := Dynamic.Affine.isRepresentedBy_unipotentHom χ
  have hvle : SubgroupFunctor.range v ≤ Dynamic.unipotent χ := by
    rw [← hu.2]
    refine hv.2.2 _ _ (Dynamic.Affine.isClosedSubgroup_unipotentHom χ) (fun j =>
      (factorsThrough_hom_iff_range_le (x j) _).mpr ?_)
    rw [hu.2]
    exact (range_le_subgroup_of_isTorusEquivariant t _ (x j) (hx j)).trans
      (RelativeRoot.subgroup_le_dynamicUnipotent t cch (hpos j))
  have hxv : ∀ i, rangePts (x i) ≤ rangePts v := by
    intro i g hg
    obtain ⟨c, hc⟩ := (factorsThrough_hom_iff_range_le (x i) v).mp (hv.2.1 i) _ hg
    exact ⟨c, hc⟩
  have hrep := (isRepresentedBy_dynamicFactors_of_generated t a ν x y hx hy hrel hcomm hgen cch
    ht (Dynamic.Affine.unipotentHom χn) v (Dynamic.Affine.isClosedSubgroup_unipotentHom χn)
    hv.1 hn.2.le hvle ?_ hxv).2.2
  · have hXu : X ∈ tangentSubmodule (Dynamic.unipotent χ) := by
      rw [tangentSubmodule_unipotent_eq_semigroupWeightSpan hT t cch]
      exact weightSpace_le_semigroupWeightSpan t _ (hpos i₀) hX
    have hXz : X ∈ tangentSubmodule (Dynamic.centralizer (CommGroupScheme.groupHom eta ≫ t)) := by
      rw [tangentSubmodule_centralizer_eq_semigroupWeightSpan hT t eta]
      exact weightSpace_le_semigroupWeightSpan t _ heta0 hX
    rw [← hrep.2] at hXu
    obtain ⟨w, hw⟩ := SubgroupFunctor.mem_range.mp hXu
    have hmem := centralizer_points_mem_range_line t a x hx i₀ eta heta' inferInstance v hv w
      (by rw [hw]; exact hXz)
    rw [← tangentSubmodule_range]
    change X.toMul.val ∈ (SubgroupFunctor.range (x i₀)).carrier _
    rw [← hw]
    exact hmem
  · intro i g hg
    show g ∈ (SubgroupFunctor.range (Dynamic.Affine.unipotentHom χn)).carrier _
    rw [hn.2, show χn = CommGroupScheme.groupHom (-cch) ≫ t from groupHom_neg_comp t cch]
    have hp : 0 < latticePairing T (-a i) (-cch) := by
      simpa only [map_neg, LinearMap.neg_apply, neg_neg] using hpos i
    exact RelativeRoot.subgroup_le_dynamicUnipotent t (-cch) hp _
      (range_le_subgroup_of_isTorusEquivariant t _ (y i) (hy i) _ hg)

/-- The weight space of a line weight with an orthogonal cocharacter as in
`weightSpace_eq_lie_range` is a line. -/
theorem finrank_weightSpace_eq_one [IsAlgClosed k] [Smooth H.X.hom] [IsAffineHom H.X.hom]
    (hT : IsSplitTorus T.toGrp) {Idx : Type*}
    (t : T.toGrp ⟶ H) (a : Idx → characterLattice T) (ν : Idx → cocharacterLattice T)
    (x y : Idx → (Ga k ⟶ H))
    (hx : ∀ i, IsTorusEquivariant t (x i) (a i)) (hy : ∀ i, IsTorusEquivariant t (y i) (-a i))
    (hrel : ∀ i, RelationOver t (ν i) (x i) (y i) (Over.mk (𝟙 (Spec (CommRingCat.of k)))))
    (hcomm : ∀ i j, i ≠ j → ∀ g ∈ rangePts (x i), ∀ h ∈ rangePts (y j), Commute g h)
    (hgen : Dense (rationalPointImage H (Subgroup.closure
      ((⋃ i, (rangePts (x i) : Set (rationalPoints H))) ∪ (⋃ i, (rangePts (y i) : Set (rationalPoints H))) ∪
        (rangePts t : Set (rationalPoints H))) : Set (rationalPoints H))))
    (cch : cocharacterLattice T) (hpos : ∀ i, 0 < latticePairing T (a i) cch)
    (ht : IsClosedSubgroup t) (i₀ : Idx) (eta : cocharacterLattice T)
    (heta : IsIsolatingCocharacter a i₀ eta)
    [Mono (x i₀).hom.hom] :
    Module.finrank k (weightSpace t (a i₀)) = 1 := by
  rw [weightSpace_eq_lie_range hT t a ν x y hx hy hrel hcomm hgen cch hpos ht i₀ eta heta,
    LinearMap.finrank_range_of_inj (Lie.targetMapLinear_injective (x i₀) k),
    (RelativeRoot.vectorLieCoordinates (VectorGroup.coordinates (CommRingCat.of k) 1)
      VectorGroup.isNaturalVectorCoordinates (CommAlgCat.of k k)).finrank_eq]
  simp

end Multiplicity

end Langlands.GroupScheme.MaximalSplitSubgroup
