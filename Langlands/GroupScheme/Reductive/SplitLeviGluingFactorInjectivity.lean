import Langlands.GroupScheme.Reductive.SplitLeviGluingGraphFactorIsomorphisms
import Langlands.GroupScheme.Rational.SplitUnipotentExtensionSection
import Langlands.GroupScheme.SubgroupIntersection
import Langlands.GroupScheme.Dynamic.UnipotentConnected
import Langlands.GroupScheme.Lie.ZeroTangentTriviality
import Langlands.GroupScheme.Rational.EndpointReductions
import Langlands.GroupScheme.Dynamic.ClosedSubgroup
import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.GroupScheme.Reductive.SplitLeviGluingDescent
import Langlands.GroupScheme.Reductive.SplitLeviGluingGraphTorus
import Langlands.GroupScheme.Reductive.SplitLeviGluingGraphReductive
import Langlands.GroupScheme.Reductive.SplitLeviGluingSimpleGeneration
import Langlands.GroupScheme.Reductive.RootLieLineFromTangent
import Langlands.GroupScheme.Reductive.RootTorusGeneration
import Langlands.GroupScheme.Dynamic.CentralizerRootsProof
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.GroupScheme.Rational.RootFactorPairTransport
import Langlands.GroupScheme.Rational.RootKernelTorus
import Langlands.GroupScheme.Torus.WeightDecomposition
import Langlands.GroupScheme.Lie.WeightImagePullback
import Langlands.GroupScheme.HomConjugacy
import Langlands.GroupScheme.Rational.RootKernelIdentityWeights

/-! # The graph projections are isomorphisms over an algebraically closed field

The differential of each projection of the reductive comparison graph is injective, one
torus weight space at a time. Injectivity of the differential makes the four unipotent factor
maps isomorphisms, which proves `AlgClosedGraphProjectionIsomorphisms`. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.LeviGluing

variable {k : Type u} [Field k]

section TrivialKernel

variable {H G : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {p : H ⟶ G} {i : T.toGrp ⟶ G} (t : T.toGrp ⟶ H) (ht : t ≫ p = i)
    (ν : cocharacterLattice T)

/-- The cocharacter of the fibre product `H ×_G T` induced by a cocharacter of `T`. -/
def intersectionCocharacter :
    (Gm (Spec (CommRingCat.of k))).toGrp ⟶ subgroupIntersection p i :=
  pullback.lift (CommGroupScheme.groupHom ν ≫ t) (CommGroupScheme.groupHom ν)
    (by rw [Category.assoc, ht])

@[reassoc (attr := simp)]
theorem intersectionCocharacter_fst :
    intersectionCocharacter t ht ν ≫ subgroupIntersectionFst p i =
      CommGroupScheme.groupHom ν ≫ t :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem intersectionCocharacter_snd :
    intersectionCocharacter t ht ν ≫ subgroupIntersectionSnd p i =
      CommGroupScheme.groupHom ν :=
  pullback.lift_snd _ _ _

variable [IsAffineHom H.X.hom] [LocallyOfFiniteType H.X.hom] [IsAffineHom G.X.hom]
    (hi : IsClosedSubgroup i)

include ht hi in
/-- If the differential of `p` is injective, then a point of the dynamic unipotent
subgroup `U_H(ν)` killed by `p` is trivial, on every test scheme. -/
theorem eq_one_of_mem_unipotent_of_comp_eq_one
    (hinj : ∀ x : lieKernel H k, Lie.targetMap p k x = 1 → x = 1)
    {W : Over (Spec (CommRingCat.of k))} {g : W ⟶ H.X}
    (hg : g ∈ (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ t)).carrier W)
    (hp : g ≫ p.hom.hom = 1) : g = 1 := by
  have hfst : IsClosedSubgroup (subgroupIntersectionFst p i) :=
    isClosedSubgroup_subgroupIntersectionFst p hi
  let : IsAffineHom (subgroupIntersection p i).X.hom := hfst.isAffineHom
  let : IsAffine (subgroupIntersection p i).X.left :=
    isAffine_of_isAffineHom (subgroupIntersection p i).X.hom
  let : IsAffineHom T.toGrp.X.hom := hi.isAffineHom
  let χ := intersectionCocharacter t ht ν
  let K := Dynamic.Affine.unipotentScheme χ
  let κ := Dynamic.Affine.unipotentHom χ
  have hκ : (Dynamic.unipotent χ).IsRepresentedBy κ :=
    Dynamic.Affine.isRepresentedBy_unipotentHom χ
  have hκf : IsClosedSubgroup (κ ≫ subgroupIntersectionFst p i) :=
    (Dynamic.Affine.isClosedSubgroup_unipotentHom χ).comp hfst
  let : IsClosedImmersion (κ ≫ subgroupIntersectionFst p i).hom.hom.left := hκf
  let : Mono (κ ≫ subgroupIntersectionFst p i).hom.hom := Over.mono_of_mono_left _
  let : IsAffineHom K.X.hom := hκf.isAffineHom
  let : LocallyOfFiniteType K.X.hom := by
    rw [← Over.w (κ ≫ subgroupIntersectionFst p i).hom.hom]
    infer_instance
  let : ConnectedSpace K.X.left :=
    DynamicConnected.connectedSpace_of_isRepresentedBy_unipotent (subgroupIntersection p i) χ hκ
  have hsnd : ∀ (W' : Over (Spec (CommRingCat.of k))) (z : W' ⟶ K.X),
      z ≫ κ.hom.hom ≫ (subgroupIntersectionSnd p i).hom.hom = 1 := by
    intro W' z
    have hz : z ≫ κ.hom.hom ∈ (Dynamic.unipotent χ).carrier W' := by
      rw [← hκ.2]
      exact SubgroupFunctor.mem_range.mpr ⟨z, rfl⟩
    have h := Dynamic.unipotent_le_comap χ (subgroupIntersectionSnd p i) W' hz
    rw [SubgroupFunctor.mem_comap, intersectionCocharacter_snd,
      Dynamic.unipotent_eq_bot_of_centralizer_eq_top _
        (Dynamic.centralizer_eq_top_of_commutative T _)] at h
    simpa only [SubgroupFunctor.bot_carrier, Subgroup.mem_bot, Category.assoc] using h
  have hcond : (κ ≫ subgroupIntersectionFst p i).hom.hom ≫ p.hom.hom =
      κ.hom.hom ≫ (subgroupIntersectionSnd p i).hom.hom ≫ i.hom.hom := by
    have h := congrArg (fun f => f.hom.hom) (subgroupIntersection_condition p i)
    simp only [Grp.comp_hom_hom] at h ⊢
    rw [Category.assoc, h]
  have hone : ∀ x : lieKernel K k, x = 1 := by
    intro x
    apply lieKernelHom_injective (κ ≫ subgroupIntersectionFst p i)
    rw [map_one]
    apply hinj
    apply Subtype.ext
    change (x.val ≫ (κ ≫ subgroupIntersectionFst p i).hom.hom) ≫ p.hom.hom = 1
    rw [Category.assoc, hcond, ← Category.assoc, ← Category.assoc,
      Category.assoc x.val, hsnd, MonObj.one_comp]
  let : Subsingleton (lieKernel K k) := ⟨fun x y => (hone x).trans (hone y).symm⟩
  have hpb := subgroupIntersection_isPullback p i
  let m : W ⟶ (subgroupIntersection p i).X := hpb.lift g 1 (by rw [hp, MonObj.one_comp])
  have hmg : m ≫ (subgroupIntersectionFst p i).hom.hom = g := hpb.lift_fst _ _ _
  have hm : m ∈ (Dynamic.unipotent χ).carrier W := by
    rw [Dynamic.unipotent_eq_comap_of_isClosedSubgroup χ _ hfst, SubgroupFunctor.mem_comap,
      intersectionCocharacter_fst, hmg]
    exact hg
  rw [← hκ.2] at hm
  obtain ⟨w, hw⟩ := SubgroupFunctor.mem_range.mp hm
  have hw1 : w = 1 := Lie.points_eq_one_of_subsingleton_lieKernel K W w
  rw [← hmg, ← hw, hw1, MonObj.one_comp, MonObj.one_comp]

include ht hi in
/-- A faithfully flat restriction to the canonical target unipotent factor is an
isomorphism once the ambient projection is injective on Lie algebras. -/
theorem UnipotentProjectionData.isIso_of_lieKernel {A : GroupScheme (Spec (CommRingCat.of k))}
    {a : A ⟶ H}
    (ha : (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ t)).IsRepresentedBy a)
    (X : UnipotentProjectionData p a ν i)
    (hinj : ∀ x : lieKernel H k, Lie.targetMap p k x = 1 → x = 1) : IsIso X.hom := by
  obtain ⟨hflat, hsurj, -, hqc⟩ := X.geometry
  let : Flat X.hom.hom.hom.left := hflat
  let : Surjective X.hom.hom.hom.left := hsurj
  let : QuasiCompact X.hom.hom.hom.left := hqc
  let : Mono a.hom.hom := ha.1
  apply TorusUnipotentExtension.isIso_of_trivial_kernel X.hom
  apply SubgroupFunctor.ext
  intro W
  apply le_antisymm _ bot_le
  intro y hy
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hy
  change y ≫ 𝟙 _ = 1
  rw [Category.comp_id]
  have hk : (y ≫ (kernelι X.hom).hom.hom) ≫ X.hom.hom.hom = 1 :=
    (mem_range_kernelι_iff X.hom _).mp (SubgroupFunctor.mem_range.mpr ⟨y, rfl⟩)
  have hg : (y ≫ (kernelι X.hom).hom.hom) ≫ a.hom.hom ∈
      (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ t)).carrier W := by
    rw [← ha.2]
    exact SubgroupFunctor.mem_range.mpr ⟨_, rfl⟩
  have hp : ((y ≫ (kernelι X.hom).hom.hom) ≫ a.hom.hom) ≫ p.hom.hom = 1 := by
    have hc := congrArg (fun f => f.hom.hom) X.comp
    simp only [Grp.comp_hom_hom] at hc
    rw [Category.assoc, ← hc, ← Category.assoc, hk, MonObj.one_comp]
  have h1 := eq_one_of_mem_unipotent_of_comp_eq_one t ht ν hi hinj hg hp
  apply (cancel_mono ((kernelι X.hom).hom.hom ≫ a.hom.hom)).mp
  rw [← Category.assoc, h1, MonObj.one_comp]

end TrivialKernel

section Weights

variable {H G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom H.X.hom] [IsAffineHom G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of k))} (p : H ⟶ G) (t : T.toGrp ⟶ H)

/-- The differential of `p` kills no nonzero vector of the `χ`-weight space of `t`. -/
def WeightKernelTrivial (χ : characterLattice T) : Prop :=
  ∀ X ∈ weightSpace t χ, Lie.targetMapLinear p (CommRingCat.of k) X = 0 → X = 0

omit [IsAffineHom H.X.hom] in
/-- A dual-number Lie vector is zero exactly when its underlying point is the identity. -/
theorem lieVector_eq_zero_iff (X : Additive (lieKernel H (CommRingCat.of k))) :
    X = 0 ↔ X.toMul.val = 1 :=
  ⟨by rintro rfl; rfl, fun h => Additive.toMul.injective (Subtype.ext h)⟩

/-- The differential kills a Lie vector exactly when the composite point is the identity. -/
theorem targetMapLinear_eq_zero_iff (X : Additive (lieKernel H (CommRingCat.of k))) :
    Lie.targetMapLinear p (CommRingCat.of k) X = 0 ↔ X.toMul.val ≫ p.hom.hom = 1 :=
  lieVector_eq_zero_iff _

/-- Weights that are neither zero nor roots have zero weight space. -/
theorem weightKernelTrivial_of_not_mem_roots {χ : characterLattice T} (hz : χ ≠ 0)
    (hr : χ ∉ roots t) : WeightKernelTrivial p t χ := by
  intro X hX _
  have hbot : weightSpace t χ = ⊥ := by
    by_contra hb
    exact hr ⟨hz, hb⟩
  rw [hbot, Submodule.mem_bot] at hX
  exact hX

/-- A rational point normalizing `t` through `σ` transports the triviality of the kernel
on the `χ`-weight space to the weight `σ⁻¹ ≫ χ`. -/
theorem weightKernelTrivial_of_normalizing
    {n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X} {σ : T ≅ T}
    (hn : IsNormalizingPoint t n σ) {χ : characterLattice T}
    (h : WeightKernelTrivial p t χ) : WeightKernelTrivial p t (σ.inv ≫ χ) := by
  intro X hX hpX
  have hY : basePointAdjoint n⁻¹ X ∈ weightSpace t χ := by
    have h' := hn.inv.adjoint_mem_weightSpace hX
    rwa [Iso.symm_inv, Iso.hom_inv_id_assoc] at h'
  have hpY : Lie.targetMapLinear p (CommRingCat.of k) (basePointAdjoint n⁻¹ X) = 0 := by
    rw [basePointAdjoint, lieKernelHomLinear_adjoint, hpX, map_zero]
  have hY0 := h _ hY hpY
  calc X = basePointAdjoint n (basePointAdjoint n⁻¹ X) := by
        rw [← Module.End.mul_apply, basePointAdjoint_mul_inv, Module.End.one_apply]
    _ = 0 := by rw [hY0, map_zero]

/-- The zero weight space of a self-centralizing torus lies in the tangent space of the
torus, so the differential kills none of its nonzero vectors once `t ≫ p` is a
monomorphism. -/
theorem weightKernelTrivial_zero [IsAffineHom T.toGrp.X.hom] {i : T.toGrp ⟶ G}
    (ht : t ≫ p = i) [Mono i.hom.hom]
    (hself : torusCentralizer t = SubgroupFunctor.range t) :
    WeightKernelTrivial p t 0 := by
  intro X hX hpX
  have hmem :=
    RelativeRoot.weightSpace_zero_le_tangentSubmodule_range_of_selfCentralizing t hself hX
  rw [RelativeRoot.mem_tangentSubmodule] at hmem
  obtain ⟨s, hs⟩ := SubgroupFunctor.mem_range.mp hmem
  rw [targetMapLinear_eq_zero_iff] at hpX
  rw [lieVector_eq_zero_iff]
  have hs1 : s = 1 := by
    apply (cancel_mono i.hom.hom).mp
    rw [MonObj.one_comp, ← ht, Grp.comp_hom_hom, ← Category.assoc, hs, hpX]
  rw [← hs, hs1, MonObj.one_comp]

set_option synthInstance.maxHeartbeats 200000 in
/-- On a one-dimensional weight space, the differential kills no nonzero vector as soon
as it does not kill one vector of that weight space. -/
theorem weightKernelTrivial_of_finrank_eq_one {χ : characterLattice T}
    (hdim : Module.finrank k (weightSpace t χ) = 1)
    {X₀ : Additive (lieKernel H (CommRingCat.of k))} (hX₀ : X₀ ∈ weightSpace t χ)
    (hp : Lie.targetMapLinear p (CommRingCat.of k) X₀ ≠ 0) :
    WeightKernelTrivial p t χ := by
  intro X hX hpX
  have hne : (⟨X₀, hX₀⟩ : weightSpace t χ) ≠ 0 := by
    intro h
    apply hp
    rw [show X₀ = 0 from congrArg Subtype.val h, map_zero]
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hne).mp hdim ⟨X, hX⟩
  have hcX : c • X₀ = X := congrArg Subtype.val hc
  by_cases hc0 : c = 0
  · rw [← hcX, hc0, zero_smul]
  · exfalso
    apply hp
    have hker : c⁻¹ • X ∈ LinearMap.ker (Lie.targetMapLinear p (CommRingCat.of k)) :=
      Submodule.smul_mem _ _ (LinearMap.mem_ker.mpr hpX)
    rw [← hcX, inv_smul_smul₀ hc0, LinearMap.mem_ker] at hker
    exact hker

/-- A linear map between internal direct sums which maps each summand into the
corresponding summand is injective once it is injective on every summand. -/
theorem injective_of_isInternal_of_blocks {I R V W : Type*} [DecidableEq I] [Ring R]
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    (A : I → Submodule R V) (B : I → Submodule R W) (hA : DirectSum.IsInternal A)
    (hB : DirectSum.IsInternal B) (f : V →ₗ[R] W) (hmap : ∀ i, ∀ x ∈ A i, f x ∈ B i)
    (hker : ∀ i, ∀ x ∈ A i, f x = 0 → x = 0) : Function.Injective f := by
  let g : ∀ i, A i →ₗ[R] B i := fun i =>
    (f.comp (A i).subtype).codRestrict (B i) (fun x => hmap i x x.2)
  have hg : ∀ i, Function.Injective (g i) := by
    intro i
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    exact Subtype.ext (hker i x.1 x.2 (congrArg Subtype.val hx))
  have hcomm : ∀ d : DirectSum I (fun i => A i),
      DirectSum.coeLinearMap B (DirectSum.lmap g d) = f (DirectSum.coeLinearMap A d) := by
    intro d
    induction d using DirectSum.induction_on with
    | zero => simp only [map_zero]
    | of i x =>
      rw [DirectSum.lmap_of, DirectSum.coeLinearMap_of, DirectSum.coeLinearMap_of]
      rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  have hA' : Function.Bijective (DirectSum.coeLinearMap A) := hA
  have hB' : Function.Bijective (DirectSum.coeLinearMap B) := hB
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  obtain ⟨d, rfl⟩ := hA'.2 x
  rw [← hcomm] at hx
  have h0 : DirectSum.lmap g d = 0 := hB'.1 (by rw [hx, map_zero])
  rw [(DirectSum.lmap_injective g).mpr hg (h0.trans (map_zero _).symm), map_zero]

/-- For a split torus, the differential is injective once it is injective on every
weight space: the weight decompositions of both Lie algebras are internal direct sums
and the differential maps each weight space into the same weight space. -/
theorem targetMapLinear_injective_of_weightKernelTrivial
    [LocallyOfFiniteType H.X.hom] [LocallyOfFiniteType G.X.hom]
    (hT : IsSplitTorus T.toGrp) (h : ∀ χ, WeightKernelTrivial p t χ) :
    Function.Injective (Lie.targetMapLinear p (CommRingCat.of k)) := by
  classical
  exact injective_of_isInternal_of_blocks (weightSpace t) (weightSpace (t ≫ p))
    (isInternal_weightSpace_of_isSplitTorus k H T hT t)
    (isInternal_weightSpace_of_isSplitTorus k G T hT (t ≫ p))
    (Lie.targetMapLinear p (CommRingCat.of k))
    (fun χ _ hX => lieKernelHomLinear_mem_weightSpace p t χ hX) h

/-- Injectivity of the differential in the form used for unipotent factor maps. -/
theorem eq_one_of_targetMap_eq_one
    (hinj : Function.Injective (Lie.targetMapLinear p (CommRingCat.of k)))
    (x : lieKernel H k) (hx : Lie.targetMap p k x = 1) : x = 1 := by
  have h : Lie.targetMapLinear p (CommRingCat.of k) (Additive.ofMul x) =
      Lie.targetMapLinear p (CommRingCat.of k) 0 := by
    rw [map_zero]
    change Additive.ofMul (Lie.targetMap p _ x) = 0
    rw [hx]
    rfl
  exact congrArg Additive.toMul (hinj h)

end Weights

section Graph

variable {G₁ G₂ : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G₁.X.hom] [Smooth G₁.X.hom] [IsAffineHom G₂.X.hom] [Smooth G₂.X.hom]
    {i₁ : T.toGrp ⟶ G₁} {i₂ : T.toGrp ⟶ G₂}

namespace SimpleComparisonGraph

variable (D : SimpleComparisonGraph i₁ i₂)

omit [Smooth G₁.X.hom] [Smooth G₂.X.hom] in
/-- Along a simple root `a`, a weight orthogonal to the direction of `a` has a
one-dimensional weight space in the reductive graph which contains the nonzero image of
the corresponding weight space of the local Levi. A projection restricting to a
monomorphism on that Levi therefore kills no nonzero vector of this weight space. -/
theorem weightKernelTrivial_of_orthogonal [IsAlgClosed k]
    (hG₁ : IsConnectedReductive G₁) (hmax₁ : IsMaximalTorus i₁)
    (hroots : roots i₁ = roots i₂)
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
    exact ⟨D.roots_subset_first hroots hχ, hχa⟩
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

/-- Every weight space of the graph torus meets the kernel of the differential of a
projection trivially, when the projection restricts to monomorphisms on the local Levis
and on the torus. Induction over the positive roots starts at the simple roots and their
doubles, which are orthogonal to the directions of their local Levis, and uses the simple
reflections. -/
theorem weightKernelTrivial [IsAlgClosed k] (E : D.GraphDynamicFactors)
    (hG₁ : IsConnectedReductive G₁) (hmax₁ : IsMaximalTorus i₁) {J₁ : Type*}
    {P₁ : RootDatum J₁ (characterLattice T) (cocharacterLattice T)}
    (hP₁ : IsRootDatumOf i₁ P₁) (hroots : roots i₁ = roots i₂)
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
      rw [← map_neg]
      exact D.weightKernelTrivial_reflection hP₁ p hj hψ.2⟩)
  by_cases h0 : χ = 0
  · subst h0
    exact weightKernelTrivial_zero p _ ht E.torus_selfCentralizing
  by_cases hχ : χ ∈ roots D.envelope.torusLift
  · have hχ₁ := D.roots_subset_first hroots hχ
    rcases lt_trichotomy 0 (latticePairing T χ D.directions.chamber) with h | h | h
    · exact (hpos χ ⟨hχ₁, h⟩).1
    · exact absurd h.symm (D.directions.generic χ hχ₁)
    · have h' := (hpos (-χ) ⟨neg_mem_roots hP₁ hχ₁, by
        rw [map_neg, LinearMap.neg_apply]
        omega⟩).2
      rwa [neg_neg] at h'
  · exact weightKernelTrivial_of_not_mem_roots p _ h0 hχ

end SimpleComparisonGraph

end Graph

/-- **The graph projections are isomorphisms over an algebraically closed field.** The
four unipotent factor maps of the graph are faithfully flat; each is an isomorphism because
the corresponding projection is injective on the Lie algebra of the reductive graph, which
is checked one torus weight space at a time. -/
theorem algClosedGraphProjectionIsomorphisms : AlgClosedGraphProjectionIsomorphisms.{u} := by
  intro k _ _ G₁ G₂ hG₁ hG₂ T i₁ i₂ hmax₁ hmax₂
  let := hG₁.isAffineHom
  let := hG₁.smooth
  let := hG₂.isAffineHom
  let := hG₂.smooth
  intro J₁ J₂ P₁ P₂ hP₁ hP₂ hroots D
  let E := D.graphDynamicFactorsOfReductive P₁ P₂ hP₁ hP₂ hroots hG₁ hmax₁
  let F := D.graphFactorProjectionsOfReductive E P₁ P₂ hP₁ hP₂ hroots hG₁ hG₂ hmax₁ hmax₂
  have hH := D.isConnectedReductive P₁ P₂ hP₁ hP₂ hroots hG₁ hG₂ hmax₁ hmax₂
  have htmax := E.isMaximalTorus hmax₁.2.1
  let : IsClosedImmersion i₁.hom.hom.left := hmax₁.2.1
  let : IsClosedImmersion i₂.hom.hom.left := hmax₂.2.1
  let : Mono i₁.hom.hom := Over.mono_of_mono_left _
  let : Mono i₂.hom.hom := Over.mono_of_mono_left _
  have hfirst := D.weightKernelTrivial E hG₁ hmax₁ hP₁ hroots hH htmax D.envelope.first
    D.envelope.torusLift_first (fun a => by
      rw [D.envelope.localLift_first]
      exact (D.comparisons a).leftRep.1)
  have hsecond := D.weightKernelTrivial E hG₁ hmax₁ hP₁ hroots hH htmax D.envelope.second
    D.envelope.torusLift_second (fun a => by
      rw [D.envelope.localLift_second]
      have : IsIso (D.comparisons a).iso.hom.hom.hom :=
        (inferInstance : IsIso ((Grp.forget _).mapIso (D.comparisons a).iso).hom)
      have : Mono (D.comparisons a).rightInclusion.hom.hom := (D.comparisons a).rightRep.1
      change Mono ((D.comparisons a).iso.hom.hom.hom ≫ (D.comparisons a).rightInclusion.hom.hom)
      infer_instance)
  have hinj₁ := eq_one_of_targetMap_eq_one D.envelope.first
    (targetMapLinear_injective_of_weightKernelTrivial D.envelope.first D.envelope.torusLift
      D.split hfirst)
  have hinj₂ := eq_one_of_targetMap_eq_one D.envelope.second
    (targetMapLinear_injective_of_weightKernelTrivial D.envelope.second D.envelope.torusLift
      D.split hsecond)
  have hneg : (Dynamic.unipotent (CommGroupScheme.groupHom (-D.directions.chamber) ≫
      D.envelope.torusLift)).IsRepresentedBy E.negative.inclusion := by
    rw [groupHom_neg_comp_eq_oppositeCocharacter]
    exact E.negativeRep
  have : IsIso F.positiveFirst.hom := UnipotentProjectionData.isIso_of_lieKernel
    D.envelope.torusLift D.envelope.torusLift_first D.directions.chamber hmax₁.2.1
    E.positiveRep F.positiveFirst hinj₁
  have : IsIso F.negativeFirst.hom := UnipotentProjectionData.isIso_of_lieKernel
    D.envelope.torusLift D.envelope.torusLift_first (-D.directions.chamber) hmax₁.2.1
    hneg F.negativeFirst hinj₁
  have : IsIso F.positiveSecond.hom := UnipotentProjectionData.isIso_of_lieKernel
    D.envelope.torusLift D.envelope.torusLift_second D.directions.chamber hmax₂.2.1
    E.positiveRep F.positiveSecond hinj₂
  have : IsIso F.negativeSecond.hom := UnipotentProjectionData.isIso_of_lieKernel
    D.envelope.torusLift D.envelope.torusLift_second (-D.directions.chamber) hmax₂.2.1
    hneg F.negativeSecond hinj₂
  exact ⟨E.isIso_first_of_factorIsomorphisms F hG₁ hmax₁,
    E.isIso_second_of_factorIsomorphisms F hG₂ hmax₂ hroots⟩

end Langlands.GroupScheme.LeviGluing
