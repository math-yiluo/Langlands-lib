import Langlands.GroupScheme.Reductive.RankOneWeylCriterionStatement
import Langlands.GroupScheme.Reductive.RankOneCentralizerDetection
import Langlands.GroupScheme.SubgroupFunctor.SmoothConnectedNormalProductExistenceProof
import Langlands.GroupScheme.Rational.CrossTorusLieTransport
import Langlands.GroupScheme.Rational.SplitTorusVectorCocycle
import Langlands.GroupScheme.InnerAutomorphismHom

/-! # Rank-one reductivity from an actual Weyl inversion

A smooth connected unipotent normal subgroup `H` of `G` has no zero weight in
its Lie algebra, because the split torus is self-centralizing. A nonzero
weight of `Lie(H)` is `α` or `-α`. Since both root lines are one-dimensional
and conjugation by the Weyl point swaps them, either weight forces both
root lines into `Lie(H)`. The fppf product of `H` and the torus then has the
whole Lie algebra of `G`, so it is `G`. Writing the Weyl point fppf-locally as
a product and using that `H` meets the torus trivially shows that the Weyl
inversion is the identity. Then `α = -α`, contradicting `α ≠ 0` in the
torsion-free character lattice. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace RankOneWeylCriterion

section Points

variable {R : CommRingCat.{u}} {G H : GroupScheme (Spec R)}

/-- An all-test transporter given by an affine base point conjugates the
second homomorphism into the first. -/
theorem comp_innerIso_hom_of_isTransporter (i₁ i₂ : H ⟶ G) (n : Lie.AffinePoints G R)
    (hn : PointwiseSchemeAction.IsTransporter i₁ i₂ n) :
    i₂ ≫ (G.innerIso ((Lie.affineSelfTestIso R).inv ≫ n)).hom = i₁ := by
  refine hom_ext_points fun T x => ?_
  rw [Grp.comp_hom_hom, ← Category.assoc, comp_innerIso_hom]
  have h := hn T (Over.homMk T.hom (by simp) ≫ (Lie.affineSelfTestIso R).inv) x
  rw [Category.assoc] at h
  change (x ≫ i₁.hom.hom) * G.constantPoint _ T = G.constantPoint _ T * (x ≫ i₂.hom.hom) at h
  rw [← h, mul_inv_cancel_right]

/-- An isomorphism of the underlying group scheme of a commutative group
scheme, as an isomorphism of commutative group schemes. -/
def commIso {T : CommGroupScheme (Spec R)} (c : T.toGrp ≅ T.toGrp) : T ≅ T where
  hom := Additive.ofMul c.hom
  inv := Additive.ofMul c.inv
  hom_inv_id := congrArg Additive.ofMul c.hom_inv_id
  inv_hom_id := congrArg Additive.ofMul c.inv_hom_id

/-- If conjugation by a base point restricts along `i` to `c`, and the base
point is fppf-locally a product of a point of a normal subgroup `H` meeting
the image of `i` trivially and a point of the image of `i`, then `c` fixes
every point of `T`. -/
theorem comp_eq_self_of_constantPoint_eq_mul {T : CommGroupScheme (Spec R)}
    (i : T.toGrp ⟶ G) (j : H ⟶ G) (hn : (SubgroupFunctor.range j).IsNormal)
    (hbot : SubgroupFunctor.range (subgroupIntersectionSnd j i) = ⊥)
    (c : T.toGrp ≅ T.toGrp) (g : Over.mk (𝟙 (Spec R)) ⟶ G.X)
    (hg : i ≫ (G.innerIso g).hom = c.hom ≫ i) {V : Over (Spec R)} (s : V ⟶ T.toGrp.X)
    (h t : V ⟶ G.X) (hh : h ∈ (SubgroupFunctor.range j).carrier V)
    (ht : t ∈ (SubgroupFunctor.range i).carrier V) (hP : G.constantPoint g V = h * t) :
    s ≫ c.hom.hom.hom = s := by
  obtain ⟨t', rfl⟩ := SubgroupFunctor.mem_range.mp ht
  have ha : (s ≫ c.hom.hom.hom) ≫ i.hom.hom =
      G.constantPoint g V * (s ≫ i.hom.hom) * (G.constantPoint g V)⁻¹ := by
    rw [← comp_innerIso_hom, Category.assoc, Category.assoc, ← Grp.comp_hom_hom,
      ← Grp.comp_hom_hom, hg]
  have hcomm : (t' ≫ i.hom.hom) * (s ≫ i.hom.hom) = (s ≫ i.hom.hom) * (t' ≫ i.hom.hom) := by
    rw [← MonObj.mul_comp, ← MonObj.mul_comp, mul_comm]
  have ha' : (s ≫ c.hom.hom.hom) ≫ i.hom.hom = h * (s ≫ i.hom.hom) * h⁻¹ := by
    rw [ha, hP, mul_inv_rev, mul_assoc h, hcomm]
    simp only [mul_assoc, mul_inv_cancel_left]
  have hy : ((s ≫ c.hom.hom.hom) * s⁻¹) ≫ i.hom.hom ∈ (SubgroupFunctor.range j).carrier V := by
    rw [MonObj.mul_comp, GrpObj.inv_comp, ha']
    have he : h * (s ≫ i.hom.hom) * h⁻¹ * (s ≫ i.hom.hom)⁻¹ =
        h * ((s ≫ i.hom.hom) * h⁻¹ * (s ≫ i.hom.hom)⁻¹) := by
      simp only [mul_assoc]
    rw [he]
    exact Subgroup.mul_mem _ hh (hn V _ _ (Subgroup.mem_top _) (Subgroup.inv_mem _ hh))
  obtain ⟨X, hX⟩ := SubgroupFunctor.mem_range.mp hy
  let hpb := subgroupIntersection_isPullback j i
  have hm : (s ≫ c.hom.hom.hom) * s⁻¹ ∈
      (SubgroupFunctor.range (subgroupIntersectionSnd j i)).carrier V :=
    ⟨hpb.lift X _ hX, hpb.lift_snd _ _ _⟩
  rw [hbot, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hm
  exact mul_inv_eq_one.mp hm

end Points

section LieRanges

variable {R : CommRingCat.{u}} {G H P : GroupScheme (Spec R)}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom] [IsAffineHom P.X.hom]
  {A : Type u} [CommRing A] [Algebra R A]

/-- An infinitesimal point whose underlying point factors through a
monomorphic subgroup lies in the image of its differential. -/
theorem mem_range_targetMapLinear (j : H ⟶ G) [Mono j.hom.hom]
    (x : Additive (lieKernel G A))
    (hx : x.toMul.val ∈ (SubgroupFunctor.range j).carrier
      ((algSpec R).obj (Opposite.op (CommAlgCat.of R (DualNumber A))))) :
    x ∈ LinearMap.range (Lie.targetMapLinear j A) := by
  obtain ⟨Y, hY⟩ := SubgroupFunctor.mem_range.mp hx
  have hYk : Y ∈ lieKernel H A := by
    apply mem_lieKernel_of_comp j Y
    rw [hY]
    exact x.toMul.property
  exact ⟨Additive.ofMul ⟨Y, hYk⟩, Additive.toMul.injective (Subtype.ext hY)⟩

/-- Containment of subgroup images gives containment of differential images. -/
theorem range_targetMapLinear_le (j : H ⟶ G) (p : P ⟶ G) [Mono p.hom.hom]
    (h : SubgroupFunctor.range j ≤ SubgroupFunctor.range p) (A : Type u) [CommRing A]
    [Algebra R A] :
    LinearMap.range (Lie.targetMapLinear j A) ≤ LinearMap.range (Lie.targetMapLinear p A) := by
  rintro _ ⟨X, rfl⟩
  exact mem_range_targetMapLinear p _ (h _ ⟨X.toMul.val, rfl⟩)

/-- Conjugation by a base point preserves the differential image of a normal
monomorphic subgroup. -/
theorem targetMapLinear_innerIso_mem_range (j : H ⟶ G) [Mono j.hom.hom]
    (hn : (SubgroupFunctor.range j).IsNormal) (g : Over.mk (𝟙 (Spec R)) ⟶ G.X)
    (X : Additive (lieKernel G A)) (hX : X ∈ LinearMap.range (Lie.targetMapLinear j A)) :
    Lie.targetMapLinear (G.innerIso g).hom A X ∈ LinearMap.range (Lie.targetMapLinear j A) := by
  obtain ⟨Y, rfl⟩ := hX
  apply mem_range_targetMapLinear j
  change (Y.toMul.val ≫ j.hom.hom) ≫ (G.innerIso g).hom.hom.hom ∈ _
  rw [comp_innerIso_hom]
  exact hn _ _ _ (Subgroup.mem_top _) ⟨Y.toMul.val, rfl⟩

end LieRanges

/-- A one-dimensional subspace meeting a submodule nontrivially lies in it. -/
theorem le_of_finrank_eq_one {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {W M : Submodule K V} (hW : Module.finrank K W = 1) {Y : V} (hYW : Y ∈ W)
    (hY : Y ≠ 0) (hYM : Y ∈ M) : W ≤ M := by
  intro Z hZ
  obtain ⟨a, ha⟩ := (finrank_eq_one_iff_of_nonzero' (⟨Y, hYW⟩ : W)
    (by simpa using hY)).mp hW ⟨Z, hZ⟩
  have hZ' : a • Y = Z := congrArg Subtype.val ha
  rw [← hZ']
  exact M.smul_mem a hYM

/-- The character lattice of a split torus has no element of order two. -/
theorem eq_zero_of_eq_neg {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))} (hT : IsSplitTorus T.toGrp)
    (α : characterLattice T) (h : α = -α) : α = 0 := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let φ : characterLattice T ≃+ (I → ℤ) :=
    (characterLattice.comapIso
      (T' := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I) e).symm.trans
      (splitTorus.characterLatticeEquiv k I)
  apply φ.injective
  rw [map_zero]
  funext x
  have hx := congrFun (congrArg φ h) x
  rw [map_neg, Pi.neg_apply] at hx
  rw [Pi.zero_apply]
  omega

section Main

variable {k : Type u} [Field k] [IsAlgClosed k]
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
  {T : CommGroupScheme (Spec (CommRingCat.of k))} (i : T.toGrp ⟶ G)
  (hT : IsSplitTorus T.toGrp) (hi : IsClosedSubgroup i)
  (hself : torusCentralizer i = SubgroupFunctor.range i)

include hT hi hself

/-- The rank-one data with an actual Weyl inversion leave no smooth connected
unipotent normal subgroup. -/
theorem hasTrivialUnipotentRadical (α : characterLattice T) (hα : α ≠ 0)
    (hroots : ∀ β : characterLattice T, β ∈ roots i ↔ β = α ∨ β = -α)
    (hdimα : Module.finrank k (weightSpace i α) = 1)
    (hdimneg : Module.finrank k (weightSpace i (-α)) = 1)
    (c : T.toGrp ≅ T.toGrp) (n : Lie.AffinePoints G k)
    (hc : c.hom ≫ CommGroupScheme.groupHom α = CommGroupScheme.groupHom (-α))
    (hn : PointwiseSchemeAction.IsTransporter (c.hom ≫ i) i n) :
    HasTrivialUnipotentRadical G := by
  classical
  let : IsAffineHom T.toGrp.X.hom := hT.isAffineHom
  let : Smooth T.toGrp.X.hom := hT.smooth
  let : ConnectedSpace T.toGrp.X.left := hT.connectedSpace
  let : IsClosedImmersion i.hom.hom.left := hi
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  intro H j hj hs hcH hu hnorm
  let := hs
  let := hcH
  let : IsAffineHom H.X.hom := hj.isAffineHom
  let : IsClosedImmersion j.hom.hom.left := hj
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  have hnT : (SubgroupFunctor.range j).IsNormalizedBy (SubgroupFunctor.range i) :=
    fun V g x _ hx => hnorm V g x (Subgroup.mem_top _) hx
  let a := AutomorphicAction.ofNormalizedConjugation j i hnT
  let ζ := centralizingCocharacter hT i
  have hrep : (Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i)).IsRepresentedBy i := by
    rw [centralizingCocharacter_spec hT i, hself]
    exact ⟨inferInstance, rfl⟩
  have hbot : SubgroupFunctor.range (subgroupIntersectionSnd j i) = ⊥ :=
    range_normalUnipotentCentralizer_eq_bot (CommGroupScheme.groupHom ζ ≫ i) j i hj hrep hi
      hnorm hu hT.hasTrivialUnipotentRadical
  -- The Weyl point as a base point, and the inversion as a torus automorphism.
  let g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X := (Lie.affineSelfTestIso _).inv ≫ n
  have hg : i ≫ (G.innerIso g).hom = c.hom ≫ i :=
    comp_innerIso_hom_of_isTransporter _ _ n hn
  let σ : T ≅ T := commIso c
  have hσ : i ≫ (G.innerIso g).hom = CommGroupScheme.groupHom σ.hom ≫ i := hg
  have hσα : σ.hom ≫ α = -α := congrArg Additive.ofMul hc
  have hcongr_neg : characterLattice.congr σ (-α) = α := by
    rw [characterLattice.congr_apply, ← hσα, Iso.inv_hom_id_assoc]
  have hcongr : characterLattice.congr σ α = -α := by
    have h1 := map_neg (characterLattice.congr σ) α
    rw [hcongr_neg] at h1
    exact neg_eq_iff_eq_neg.mp h1.symm
  -- A nonzero root vector in `Lie(H)` is impossible.
  have hcontra (β : characterLattice T) (hβ : β = α ∨ β = -α)
      (Y : Additive (lieKernel G k)) (hYβ : Y ∈ weightSpace i β) (hY0 : Y ≠ 0)
      (hYj : Y ∈ LinearMap.range (Lie.targetMapLinear j k)) : False := by
    have hdim : Module.finrank k (weightSpace i β) = 1 := by
      rcases hβ with rfl | rfl
      exacts [hdimα, hdimneg]
    have hβle : weightSpace i β ≤ LinearMap.range (Lie.targetMapLinear j k) :=
      le_of_finrank_eq_one hdim hYβ hY0 hYj
    have hβσ : characterLattice.congr σ β = -β := by
      rcases hβ with rfl | rfl
      · exact hcongr
      · rw [hcongr_neg, neg_neg]
    have hnegle : weightSpace i (-β) ≤ LinearMap.range (Lie.targetMapLinear j k) := by
      intro Z hZ
      rw [← hβσ, ← weightSpace_map_of_transport σ (G.innerIso g) hσ β] at hZ
      obtain ⟨W, hW, rfl⟩ := hZ
      exact targetMapLinear_innerIso_mem_range j hnorm g W (hβle hW)
    have hαle : weightSpace i α ≤ LinearMap.range (Lie.targetMapLinear j k) ∧
        weightSpace i (-α) ≤ LinearMap.range (Lie.targetMapLinear j k) := by
      rcases hβ with rfl | rfl
      · exact ⟨hβle, hnegle⟩
      · rw [neg_neg] at hnegle
        exact ⟨hnegle, hβle⟩
    -- The fppf product of `H` and the torus.
    obtain ⟨P, p, hprod, hPs, hPc⟩ :=
      SubgroupFunctor.exists_smoothConnected_fppfProduct j i hj hi hnT
    let := hPs
    let := hPc
    let : IsAffineHom P.X.hom := hprod.isClosedSubgroup.isAffineHom
    let : IsClosedImmersion p.hom.hom.left := hprod.isClosedSubgroup
    let : Mono p.hom.hom := Over.mono_of_mono_left _
    have hjp := range_targetMapLinear_le j p hprod.left_le k
    have hip := range_targetMapLinear_le i p hprod.right_le k
    have hχ (χ : characterLattice T) :
        weightSpace i χ ≤ LinearMap.range (Lie.targetMapLinear p k) := by
      by_cases h0 : χ = 0
      · subst h0
        intro X hX
        obtain ⟨t, ht⟩ := Lie.zeroWeightMap_surjective_of_selfCentralizing i hself ⟨X, hX⟩
        exact hip ⟨t, congrArg Subtype.val ht⟩
      · by_cases hr : χ ∈ roots i
        · rcases (hroots χ).mp hr with rfl | rfl
          · exact hαle.1.trans hjp
          · exact hαle.2.trans hjp
        · have hχbot : weightSpace i χ = ⊥ := by
            by_contra hne
            exact hr ⟨h0, hne⟩
          rw [hχbot]
          exact bot_le
    have hdec := isInternal_weightSpace_of_isSplitTorus k G T hT i
    have hsurj : Function.Surjective (Lie.targetMapLinear p k) := by
      intro X
      have hX : X ∈ (⊤ : Submodule k (Additive (lieKernel G k))) := trivial
      rw [← hdec.submodule_iSup_eq_top] at hX
      exact (iSup_le hχ) hX
    have hiso : IsIso p :=
      Lie.isIso_of_surjective_targetMapLinear p hprod.isClosedSubgroup hsurj
    -- The Weyl inversion is trivial.
    have hc1 : c.hom = 𝟙 T.toGrp := by
      refine hom_ext_points fun T₀ x => ?_
      have hmem : G.constantPoint g T₀ ∈ (SubgroupFunctor.range p).carrier T₀ :=
        SubgroupFunctor.mem_range.mpr ⟨G.constantPoint g T₀ ≫ (inv p).hom.hom, by
          rw [Category.assoc, ← Grp.comp_hom_hom, IsIso.inv_hom_id, Grp.id_hom_hom,
            Category.comp_id]⟩
      obtain ⟨V, v, hfl, hsu, -, h, t, hh, ht, hv⟩ := (hprod.mem_range_iff T₀ _).mp hmem
      rw [constantPoint_naturality] at hv
      have hfix := comp_eq_self_of_constantPoint_eq_mul i j hnorm hbot c g hg (v ≫ x) h t
        hh ht hv
      let : Flat v.left := hfl
      let : Surjective v.left := hsu
      let : Epi v.left := Flat.epi_of_flat_of_surjective _
      let : Epi v := Over.epi_of_epi_left _
      rw [Grp.id_hom_hom, Category.comp_id]
      exact (cancel_epi v).mp (by rw [← Category.assoc, hfix])
    have hαα : α = -α := by
      have h1 := hc
      rw [hc1, Category.id_comp] at h1
      exact Additive.toMul.injective h1
    exact hα (eq_zero_of_eq_neg hT α hαα)
  -- Every weight space of `Lie(H)` vanishes.
  have hweight (β : characterLattice T) (X : Additive (lieKernel H k))
      (hX : X ∈ a.lieWeightSpace (𝟙 T.toGrp) β) : X = 0 := by
    apply Lie.targetMapLinear_injective j k
    rw [map_zero]
    have hY := Lie.normalizedConjugation_mem_weightSpace i j hnT β hX
    by_cases hβ : β = 0
    · subst β
      exact RankOneCentralizerDetection.normal_weight_zero_of_centralizer j hj hnorm hu i ζ i
        hrep hi hT.hasTrivialUnipotentRadical 0 (by simp) X hY
    · by_contra hzero
      have hroot : β ∈ roots i := ⟨hβ, fun hb =>
        hzero (by simpa only [hb, Submodule.mem_bot] using hY)⟩
      exact hcontra β ((hroots β).mp hroot) _ hY hzero ⟨X, rfl⟩
  have hwbot (β : characterLattice T) : a.lieWeightSpace (𝟙 T.toGrp) β = ⊥ :=
    eq_bot_iff.mpr (fun X hX => hweight β X hX)
  have hdec := AutomorphicAction.isInternal_lieWeightSpace_of_isSplitTorus
    k H T hT a (𝟙 T.toGrp)
  have htop : (⊤ : Submodule k (Additive (lieKernel H k))) = ⊥ := by
    apply le_antisymm ?_ bot_le
    rw [← hdec.submodule_iSup_eq_top]
    exact iSup_le (fun β => (hwbot β).le)
  let : Subsingleton (Additive (lieKernel H k)) := by
    have hz (X : Additive (lieKernel H k)) : X = 0 := by
      have hx : X ∈ (⊤ : Submodule k (Additive (lieKernel H k))) := trivial
      rwa [htop, Submodule.mem_bot] at hx
    exact ⟨fun X Y => (hz X).trans (hz Y).symm⟩
  have hunit : IsClosedSubgroup (kernelUnit H) := kernelUnit_isClosedSubgroup H
  let : Smooth (Grp.trivial (Over (Spec (CommRingCat.of k)))).X.hom := by
    change Smooth (𝟙 (Spec (CommRingCat.of k)))
    infer_instance
  let : IsAffineHom (Grp.trivial (Over (Spec (CommRingCat.of k)))).X.hom := by
    change IsAffineHom (𝟙 (Spec (CommRingCat.of k)))
    infer_instance
  have : IsIso (kernelUnit H) :=
    Lie.isIso_of_surjective_targetMapLinear (kernelUnit H) hunit
      (fun X => ⟨0, Subsingleton.elim _ _⟩)
  have hcomp : kernelUnit H ≫ j = kernelUnit G := by
    apply (Grp.forget _).map_injective
    exact IsMonHom.one_hom j.hom.hom
  rw [← SubgroupFunctor.range_iso_comp (asIso (kernelUnit H)) j]
  change SubgroupFunctor.range (kernelUnit H ≫ j) = ⊥
  rw [hcomp, range_kernelUnit]

end Main

end RankOneWeylCriterion

/-- Rank-one reductivity from an actual Weyl inversion. -/
theorem rankOneWeylReductivity : RankOneWeylReductivityStatement.{u} := by
  intro k _ _ G _ _ _ T i hsplit hself α hα hroots hdimα hdimneg c n hc hn
  have hG : IsPseudoReductive G :=
    ⟨inferInstance, inferInstance, inferInstance,
      RankOneWeylCriterion.hasTrivialUnipotentRadical i hsplit.1 hsplit.2 hself α hα hroots
        hdimα hdimneg c n hc hn⟩
  exact hG.isConnectedReductive_of_isAlgClosed

end Langlands.GroupScheme
