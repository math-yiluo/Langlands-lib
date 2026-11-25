import Langlands.GroupScheme.Reductive.SplitIsogenyGraphTorus
import Langlands.GroupScheme.Reductive.SplitLeviGluingFactorInjectivity

/-! # The first projection of a local-isogeny graph -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RootDatumIsogenyRealization

open LeviGluing

variable {k : Type u} [Field k]
    {G₁ G₂ : GroupScheme (Spec (CommRingCat.of k))}
    {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G₁.X.hom] [Smooth G₁.X.hom]
    [IsAffineHom G₂.X.hom] [Smooth G₂.X.hom]
    {i₁ : T.toGrp ⟶ G₁} {i₂ : T'.toGrp ⟶ G₂} {t : T ⟶ T'}
    (D : SimpleIsogenyGraph i₁ i₂ t)

local instance affine_of_affineHom {H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom H.X.hom] : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom

namespace SimpleIsogenyGraph

private theorem root_le_range_comp
    {H A L G : GroupScheme (Spec (CommRingCat.of k))}
    {a : A ⟶ H} (ha : IsClosedSubgroup a) (r : L ⟶ H)
    (hr : SubgroupFunctor.range r ≤ SubgroupFunctor.range a) (p : H ⟶ G)
    {F : SubgroupFunctor G} (hF : F.IsRepresentedBy (r ≫ p)) :
    F ≤ SubgroupFunctor.range (a ≫ p) := by
  let : IsClosedImmersion a.hom.hom.left := ha
  have har : (SubgroupFunctor.range a).IsRepresentedBy a := ⟨Over.mono_of_mono_left _, rfl⟩
  let q := har.factorHom r hr
  have hq : q ≫ a = r := har.factorHom_comp r hr
  rw [← hF.2, ← hq, Category.assoc]
  intro W x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  exact SubgroupFunctor.mem_range.mpr ⟨y ≫ q.hom.hom, by
    simp only [Grp.comp_hom_hom, Category.assoc]⟩

namespace GraphDynamicFactors

variable {D} (E : D.GraphDynamicFactors)

/-- The actual restriction of the first projection to the positive graph factor,
with faithfully flat geometry from its source simple-root composites. -/
def positiveFirstProjectionData [IsAlgClosed k]
    {J : Type u} {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
    (hP : IsRootDatumOf i₁ P) (hG : IsConnectedReductive G₁) (hmax : IsMaximalTorus i₁) :
    UnipotentProjectionData D.envelope.first E.positive.inclusion D.directions.chamber i₁ := by
  let : ConnectedSpace G₁.X.left := hG.connectedSpace
  apply unipotentProjectionData D.envelope.first E.positive.inclusion D.envelope.torusLift i₁
    D.envelope.torusLift_first D.directions.chamber E.positiveRep D.split hmax.2.1 hP
    D.directions.generic
    (LocalIsogenyGraphEnvelope.chamber_centralizer_eq_range hG D.split hmax
      D.directions.chamber D.directions.generic)
  intro a ha
  let a' : D.SimpleIndex := ⟨a, ha⟩
  exact root_le_range_comp E.positive.closed (D.positiveHom a')
    (by rw [E.positiveRep.2]; exact D.positive_le_unipotent a') D.envelope.first
    (D.positive_first_rep a')

/-- The actual restriction to the negative graph factor, using the same local maps. -/
def negativeFirstProjectionData [IsAlgClosed k]
    {J : Type u} {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
    (hP : IsRootDatumOf i₁ P) (hG : IsConnectedReductive G₁) (hmax : IsMaximalTorus i₁) :
    UnipotentProjectionData D.envelope.first E.negative.inclusion (-D.directions.chamber) i₁ := by
  let : ConnectedSpace G₁.X.left := hG.connectedSpace
  have haU : (Dynamic.unipotent (CommGroupScheme.groupHom (-D.directions.chamber) ≫
      D.envelope.torusLift)).IsRepresentedBy E.negative.inclusion := by
    rw [groupHom_neg_comp_eq_oppositeCocharacter]
    exact E.negativeRep
  have hν : IsGenericCocharacter i₁ (-D.directions.chamber) := by
    intro a ha
    rw [map_neg]
    exact neg_ne_zero.mpr (D.directions.generic a ha)
  have hZ : Dynamic.centralizer (CommGroupScheme.groupHom (-D.directions.chamber) ≫ i₁) =
      SubgroupFunctor.range i₁ := by
    rw [Dynamic.centralizer_groupHom_neg]
    exact LocalIsogenyGraphEnvelope.chamber_centralizer_eq_range hG D.split hmax
      D.directions.chamber D.directions.generic
  apply unipotentProjectionData D.envelope.first E.negative.inclusion D.envelope.torusLift i₁
    D.envelope.torusLift_first (-D.directions.chamber) haU D.split hmax.2.1 hP hν hZ
  intro a ha
  have hn := neg_mem_simpleRelativeRoots hP ha
  simp only [neg_neg] at hn
  let a' : D.SimpleIndex := ⟨-a, hn⟩
  have hr := D.negative_first_rep a'
  change (RelativeRoot.subgroup i₁ (-(-a))).IsRepresentedBy (D.negativeHom a' ≫ D.envelope.first) at hr
  rw [neg_neg] at hr
  exact root_le_range_comp E.negative.closed (D.negativeHom a')
    (by
      rw [E.negativeRep.2]
      simpa only [groupHom_neg_comp_eq_oppositeCocharacter, Dynamic.oppositeCocharacter,
        Category.assoc] using D.negative_le_unipotent a') D.envelope.first hr

end GraphDynamicFactors

omit [Smooth G₁.X.hom] [IsAffineHom G₂.X.hom] [Smooth G₂.X.hom] in
/-- Along a simple root `a`, a weight orthogonal to the direction of `a` has a
one-dimensional weight space in the reductive graph which contains the nonzero image of
the corresponding weight space of the local Levi. A projection restricting to a
monomorphism on that Levi therefore kills no nonzero vector of this weight space. -/
theorem weightKernelTrivial_of_orthogonal [IsAlgClosed k]
    (hG₁ : IsConnectedReductive G₁) (hmax₁ : IsMaximalTorus i₁)
    (hroots : roots D.envelope.torusLift = roots i₁)
    (hH : IsConnectedReductive D.envelope.group)
    (htmax : IsMaximalTorus D.envelope.torusLift)
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : D.envelope.group ⟶ G) (a : D.SimpleIndex)
    [Mono (D.envelope.localLift a ≫ p).hom.hom]
    {χ : characterLattice T} (hχ0 : χ ≠ 0)
    (hχa : latticePairing T χ (D.directions.direction a) = 0) :
    WeightKernelTrivial p D.envelope.torusLift χ := by
  by_cases hχ : χ ∈ roots D.envelope.torusLift
  swap
  · exact weightKernelTrivial_of_not_mem_roots p _ hχ0 hχ
  have hZ := dynamicCentralizerReductive k G₁ hG₁ _ (D.comparisons a).left
    (D.comparisons a).leftInclusion (D.comparisons a).leftClosed (D.comparisons a).leftRep
  let : IsAffineHom (D.comparisons a).left.X.hom := hZ.isAffineHom
  have hB := dynamicCentralizerRoots k G₁ hG₁ T D.split i₁ hmax₁ (D.directions.direction a)
    (D.comparisons a).left (D.comparisons a).leftInclusion (D.comparisons a).leftClosed
    (D.comparisons a).leftRep hZ (D.comparisons a).leftTorus (D.comparisons a).leftTorusComp
  have hχs : χ ∈ roots (D.comparisons a).leftTorus := by
    rw [hB]
    exact ⟨hroots.subset hχ, hχa⟩
  obtain ⟨Y, hY, hY0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (mem_roots.mp hχs).2
  have hX₀ := lieKernelHomLinear_mem_weightSpace (D.envelope.localLift a)
    (D.comparisons a).leftTorus χ hY
  rw [D.envelope.leftTorus_localLift] at hX₀
  obtain ⟨e⟩ := rootLieLine_of_dynamicCentralizerReductive dynamicCentralizerReductive k
    D.envelope.group hH T D.split D.envelope.torusLift htmax χ hχ
  have hdim : Module.finrank k (weightSpace D.envelope.torusLift χ) = 1 :=
    e.finrank_eq.symm.trans (Module.finrank_self k)
  apply weightKernelTrivial_of_finrank_eq_one p _ hdim hX₀
  rw [← LinearMap.comp_apply, ← Lie.targetMapLinear_comp]
  intro h
  apply hY0
  apply Lie.targetMapLinear_injective (D.envelope.localLift a ≫ p) (CommRingCat.of k)
  rw [h, map_zero]

omit [Smooth G₁.X.hom] [IsAffineHom G₂.X.hom] [Smooth G₂.X.hom] in
/-- The simple reflections of a root datum of the first torus are realized by rational
points of the local Levis, hence of the graph, normalizing the graph torus. The triviality
of the kernel on weight spaces is therefore stable under these reflections. -/
theorem weightKernelTrivial_reflection {J₁ : Type*}
    {P₁ : RootDatum J₁ (characterLattice T) (cocharacterLattice T)}
    (hP₁ : IsRootDatumOf i₁ P₁) {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] (p : D.envelope.group ⟶ G) {j : J₁}
    (hj : P₁.root j ∈ simpleRelativeRoots i₁ D.directions.chamber) {χ : characterLattice T}
    (h : WeightKernelTrivial p D.envelope.torusLift χ) :
    WeightKernelTrivial p D.envelope.torusLift (P₁.reflection j χ) := by
  let a : D.SimpleIndex := ⟨P₁.root j, hj⟩
  obtain ⟨n, σ, hn, hσ⟩ := hP₁.2.2 j
  have hfix := cocharacter_comp_eq_of_reflection hP₁ hσ (D.directions.annihilates a)
  have hmem := constantPoint_mem_centralizer hn hfix (Over.mk (𝟙 (Spec (CommRingCat.of k))))
  rw [constantPoint_self, ← (D.comparisons a).leftRep.2] at hmem
  obtain ⟨m, hm⟩ := SubgroupFunctor.mem_range.1 hmem
  have : Mono (D.comparisons a).leftInclusion.hom.hom := (D.comparisons a).leftRep.1
  have hm' : IsNormalizingPoint (D.comparisons a).leftTorus m σ := by
    apply IsNormalizingPoint.of_comp (D.comparisons a).leftInclusion
    rw [(D.comparisons a).leftTorusComp, hm]
    exact hn
  have hn' := hm'.comp (D.envelope.localLift a)
  rw [D.envelope.leftTorus_localLift] at hn'
  have h' := weightKernelTrivial_of_normalizing p _ hn' h
  rwa [← characterAut_apply, hσ] at h'

omit [IsAffineHom G₂.X.hom] [Smooth G₂.X.hom] in
/-- Every weight space of the graph torus meets the kernel of the differential of a
projection trivially, when the projection restricts to monomorphisms on the local Levis
and on the torus. Induction over the positive roots starts at the simple roots and their
doubles, which are orthogonal to the directions of their local Levis, and uses the simple
reflections. -/
theorem weightKernelTrivial [IsAlgClosed k] (E : D.GraphDynamicFactors)
    (hG₁ : IsConnectedReductive G₁) (hmax₁ : IsMaximalTorus i₁) {J₁ : Type*}
    {P₁ : RootDatum J₁ (characterLattice T) (cocharacterLattice T)}
    (hP₁ : IsRootDatumOf i₁ P₁) (hroots : roots D.envelope.torusLift = roots i₁)
    (hH : IsConnectedReductive D.envelope.group)
    (htmax : IsMaximalTorus D.envelope.torusLift)
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : D.envelope.group ⟶ G) {i : T.toGrp ⟶ G} (ht : D.envelope.torusLift ≫ p = i)
    [Mono i.hom.hom] (hmono : ∀ a : D.SimpleIndex, Mono (D.envelope.localLift a ≫ p).hom.hom)
    (χ : characterLattice T) : WeightKernelTrivial p D.envelope.torusLift χ := by
  let : IsAffineHom T.toGrp.X.hom := D.split.isAffineHom
  have hQ : ∀ a (ha : a ∈ simpleRelativeRoots i₁ D.directions.chamber)
      (ψ : characterLattice T), latticePairing T ψ D.directions.chamber ≠ 0 →
      latticePairing T ψ (D.directions.direction ⟨a, ha⟩) = 0 →
      WeightKernelTrivial p D.envelope.torusLift ψ := by
    intro a ha ψ hψc hψa
    have : Mono (D.envelope.localLift ⟨a, ha⟩ ≫ p).hom.hom := hmono ⟨a, ha⟩
    refine D.weightKernelTrivial_of_orthogonal hG₁ hmax₁ hroots hH htmax p ⟨a, ha⟩ ?_ hψa
    rintro rfl
    exact hψc (by rw [map_zero, LinearMap.zero_apply])
  have hpos := positive_induction hP₁ D.split D.directions.generic
    (fun ψ => WeightKernelTrivial p D.envelope.torusLift ψ ∧
      WeightKernelTrivial p D.envelope.torusLift (-ψ))
    (fun a ha => by
      have hann := D.directions.annihilates ⟨a, ha⟩
      have hc := ha.1.2
      refine ⟨hQ a ha a hc.ne' hann, hQ a ha (-a) ?_ ?_⟩
      · rw [map_neg, LinearMap.neg_apply]
        omega
      · rw [map_neg, LinearMap.neg_apply, hann, neg_zero])
    (fun a ha _ => by
      have hann : latticePairing T a (D.directions.direction ⟨a, ha⟩) = 0 :=
        D.directions.annihilates ⟨a, ha⟩
      have hc := ha.1.2
      refine ⟨hQ a ha (2 • a) ?_ ?_, hQ a ha (-(2 • a)) ?_ ?_⟩
      · rw [two_nsmul, map_add, LinearMap.add_apply]
        omega
      · rw [two_nsmul, map_add, LinearMap.add_apply, hann, add_zero]
      · rw [two_nsmul, map_neg, LinearMap.neg_apply, map_add, LinearMap.add_apply]
        omega
      · rw [two_nsmul, map_neg, LinearMap.neg_apply, map_add, LinearMap.add_apply, hann,
          add_zero, neg_zero])
    (fun j hj ψ hψ => ⟨D.weightKernelTrivial_reflection hP₁ p hj hψ.1, by
      have : AddMonoidHomClass (characterLattice T ≃ₗ[ℤ] characterLattice T) _ _ :=
        SemilinearMapClass.instAddMonoidHomClass _
      rw [← map_neg]
      exact D.weightKernelTrivial_reflection hP₁ p hj hψ.2⟩)
  by_cases h0 : χ = 0
  · subst h0
    exact weightKernelTrivial_zero p _ ht E.torus_selfCentralizing
  by_cases hχ : χ ∈ roots D.envelope.torusLift
  · have hχ₁ := hroots.subset hχ
    rcases lt_trichotomy 0 (latticePairing T χ D.directions.chamber) with h | h | h
    · exact (hpos χ ⟨hχ₁, h⟩).1
    · exact absurd h.symm (D.directions.generic χ hχ₁)
    · have h' := (hpos (-χ) ⟨neg_mem_roots hP₁ hχ₁, by
        rw [map_neg, LinearMap.neg_apply]
        omega⟩).2
      rwa [neg_neg] at h'
  · exact weightKernelTrivial_of_not_mem_roots p _ h0 hχ


namespace GraphDynamicFactors

variable {D} (E : D.GraphDynamicFactors)

set_option maxHeartbeats 800000 in
/-- Assemble the first actual graph projection from its two unipotent
isomorphisms and the identity on the common source torus. -/
def firstProjectionIso
    (hG : IsConnectedReductive G₁) (hmax : IsMaximalTorus i₁)
    (positive : UnipotentProjectionData D.envelope.first E.positive.inclusion D.directions.chamber i₁)
    (negative : UnipotentProjectionData D.envelope.first E.negative.inclusion (-D.directions.chamber) i₁)
    [IsIso positive.hom] [IsIso negative.hom] : D.envelope.group ≅ G₁ := by
  let : ConnectedSpace G₁.X.left := hG.connectedSpace
  let : IsClosedImmersion i₁.hom.hom.left := hmax.2.1
  have hZ : (Dynamic.centralizer (CommGroupScheme.groupHom D.directions.chamber ≫ i₁)).IsRepresentedBy i₁ :=
    ⟨Over.mono_of_mono_left _, (LocalIsogenyGraphEnvelope.chamber_centralizer_eq_range
      hG D.split hmax D.directions.chamber D.directions.generic).symm⟩
  have hMG : (Dynamic.unipotent (CommGroupScheme.groupHom
      (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫
      (CommGroupScheme.groupHom D.directions.chamber ≫ i₁))).IsRepresentedBy
      (Dynamic.Affine.unipotentHom (CommGroupScheme.groupHom (-D.directions.chamber) ≫ i₁)) := by
    change (Dynamic.unipotent (Dynamic.oppositeCocharacter
      (CommGroupScheme.groupHom D.directions.chamber ≫ i₁))).IsRepresentedBy _
    rw [← groupHom_neg_comp_eq_oppositeCocharacter]
    exact Dynamic.Affine.isRepresentedBy_unipotentHom _
  exact Dynamic.isoOfTripleCellIsomorphisms
    (CommGroupScheme.groupHom D.directions.chamber ≫ D.envelope.torusLift)
    (CommGroupScheme.groupHom D.directions.chamber ≫ i₁)
    E.negativeRep E.torusRep E.positiveRep hMG hZ
    (Dynamic.Affine.isRepresentedBy_unipotentHom _)
    D.envelope.first (asIso negative.hom) (Iso.refl T.toGrp) (asIso positive.hom)
    negative.comp (by simpa only [Iso.refl_hom, Category.id_comp] using
      D.envelope.torusLift_first.symm) positive.comp

omit [IsAffineHom G₂.X.hom] [Smooth G₂.X.hom] in
@[simp]
theorem firstProjectionIso_hom
    (hG : IsConnectedReductive G₁) (hmax : IsMaximalTorus i₁)
    (positive : UnipotentProjectionData D.envelope.first E.positive.inclusion D.directions.chamber i₁)
    (negative : UnipotentProjectionData D.envelope.first E.negative.inclusion (-D.directions.chamber) i₁)
    [IsIso positive.hom] [IsIso negative.hom] :
    (E.firstProjectionIso hG hmax positive negative).hom = D.envelope.first := rfl

end GraphDynamicFactors

/-- Graph root geometry makes the first projection an actual isomorphism.
Only the source-side local Levi restrictions need be monomorphisms. -/
def firstProjectionIsoOfGeometry [IsAlgClosed k] (E : D.GraphTorusGeometry)
    {J : Type u} {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
    (hP : IsRootDatumOf i₁ P) (hG : IsConnectedReductive G₁) (hmax : IsMaximalTorus i₁)
    (hH : IsConnectedReductive D.envelope.group) : D.envelope.group ≅ G₁ := by
  let positive := E.factors.positiveFirstProjectionData hP hG hmax
  let negative := E.factors.negativeFirstProjectionData hP hG hmax
  let : IsClosedImmersion i₁.hom.hom.left := hmax.2.1
  let : Mono i₁.hom.hom := Over.mono_of_mono_left _
  have hfirst := D.weightKernelTrivial E.factors hG hmax hP E.roots_eq hH E.maximal
    D.envelope.first D.envelope.torusLift_first (fun a => by
      rw [D.envelope.localLift_first]
      exact (D.comparisons a).leftRep.1)
  have hinj := eq_one_of_targetMap_eq_one D.envelope.first
    (targetMapLinear_injective_of_weightKernelTrivial D.envelope.first D.envelope.torusLift
      D.split hfirst)
  have hneg : (Dynamic.unipotent (CommGroupScheme.groupHom (-D.directions.chamber) ≫
      D.envelope.torusLift)).IsRepresentedBy E.factors.negative.inclusion := by
    rw [groupHom_neg_comp_eq_oppositeCocharacter]
    exact E.factors.negativeRep
  let : IsIso positive.hom := UnipotentProjectionData.isIso_of_lieKernel
    D.envelope.torusLift D.envelope.torusLift_first D.directions.chamber hmax.2.1
    E.factors.positiveRep positive hinj
  let : IsIso negative.hom := UnipotentProjectionData.isIso_of_lieKernel
    D.envelope.torusLift D.envelope.torusLift_first (-D.directions.chamber) hmax.2.1
    hneg negative hinj
  exact E.factors.firstProjectionIso hG hmax positive negative

omit [IsAffineHom G₂.X.hom] [Smooth G₂.X.hom] in
@[simp]
theorem firstProjectionIsoOfGeometry_hom [IsAlgClosed k] (E : D.GraphTorusGeometry)
    {J : Type u} {P : RootDatum J (characterLattice T) (cocharacterLattice T)}
    (hP : IsRootDatumOf i₁ P) (hG : IsConnectedReductive G₁) (hmax : IsMaximalTorus i₁)
    (hH : IsConnectedReductive D.envelope.group) :
    (D.firstProjectionIsoOfGeometry E hP hG hmax hH).hom = D.envelope.first := rfl

section Construction

variable [IsAlgClosed k]
    {J J' : Type u} [Finite J] [Finite J']
    (P : RootDatum J (characterLattice T) (cocharacterLattice T))
    (P' : RootDatum J' (characterLattice T') (cocharacterLattice T'))
    [Module.Finite ℤ (characterLattice T)] [Module.Finite ℤ (cocharacterLattice T)]
    [Module.Finite ℤ (characterLattice T')] [Module.Finite ℤ (cocharacterLattice T')]
    [P.IsReduced] [P'.IsReduced]
    (hP : IsRootDatumOf i₁ P) (hP' : IsRootDatumOf i₂ P')
    (hT' : IsSplitTorus T'.toGrp) {p : ℕ}
    (f : Langlands.LinearAlgebra.RootDatumIsogeny p P' P)
    (hw : ∀ χ : characterLattice T', t ≫ χ = f.weightMap χ)
    (hG : IsConnectedReductive G₁) (hmax : IsMaximalTorus i₁)
    (hH : IsConnectedReductive D.envelope.group)

/-- The first projection of the reductive local-isogeny graph is invertible over
an algebraically closed field, for arbitrary prescribed positive root factors. -/
def firstProjectionIsoOfReductive : D.envelope.group ≅ G₁ :=
  D.firstProjectionIsoOfGeometry
    (D.graphTorusGeometryOfReductive P P' hP hP' hT' f hw hG hmax hH) hP hG hmax hH

@[simp]
theorem firstProjectionIsoOfReductive_hom :
    (D.firstProjectionIsoOfReductive P P' hP hP' hT' f hw hG hmax hH).hom =
      D.envelope.first := rfl

end Construction

end SimpleIsogenyGraph

end Langlands.GroupScheme.RootDatumIsogenyRealization
