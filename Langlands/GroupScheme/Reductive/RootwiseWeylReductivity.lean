import Langlands.GroupScheme.Reductive.RankOneWeylCriterionProof
import Langlands.GroupScheme.Reductive.FiniteCentralizerNeighbourhood
import Langlands.GroupScheme.Rational.RootOrthogonalCentralizer
import Langlands.GroupScheme.Rational.KernelCentralizerClassical
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.Rational.CrossTorusLieTransport
import Langlands.GroupScheme.Dynamic.ParabolicLieCriterion
import Langlands.GroupScheme.Dynamic.SmoothProof
import Langlands.GroupScheme.Reductive.ToPseudoReductive

/-! # Reductivity from rootwise Weyl inversions

Over an algebraically closed field, a smooth connected affine group with a closed
self-centralizing split torus is connected reductive when its root spaces are lines, its
roots are reduced, and each root is inverted by a point normalizing the torus whose action
fixes the cocharacters orthogonal to that root. For each root `α`, the centralizer of a
cocharacter orthogonal to `α` and generic otherwise has root set `{α, -α}`. By the
published rank-one criterion `rankOneWeylReductivity` it is reductive. The published
`RadicalFreeRootCentralizerData.isConnectedReductive` then concludes.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

namespace RootwiseWeyl

variable {K : Type u} [Field K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  {T : CommGroupScheme (Spec (CommRingCat.of K))}

section Inversion

variable [IsAffineHom G.X.hom] (i : T.toGrp ⟶ G)

/-- A Weyl inversion of a root `α`: an automorphism `c` of `T` sending `α` to `-α` and
fixing every cocharacter orthogonal to `α`, realized by conjugation with a point `n`. -/
def IsWeylInversion (α : characterLattice T) (c : T.toGrp ≅ T.toGrp)
    (n : Lie.AffinePoints G K) : Prop :=
  c.hom ≫ CommGroupScheme.groupHom α = CommGroupScheme.groupHom (-α) ∧
    (∀ ν : cocharacterLattice T, latticePairing T α ν = 0 →
      CommGroupScheme.groupHom ν ≫ c.hom = CommGroupScheme.groupHom ν) ∧
    PointwiseSchemeAction.IsTransporter (c.hom ≫ i) i n

variable {i}

/-- A Weyl inversion carries the weight space of `α` onto that of `-α`. -/
theorem IsWeylInversion.map_weightSpace {α : characterLattice T} {c : T.toGrp ≅ T.toGrp}
    {n : Lie.AffinePoints G K} (h : IsWeylInversion i α c n) :
    (weightSpace i α).map
        (Lie.targetMapLinear (G.innerIso ((Lie.affineSelfTestIso _).inv ≫ n)).hom _) =
      weightSpace i (-α) := by
  let g : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ G.X := (Lie.affineSelfTestIso _).inv ≫ n
  have hg : i ≫ (G.innerIso g).hom = c.hom ≫ i :=
    RankOneWeylCriterion.comp_innerIso_hom_of_isTransporter _ _ n h.2.2
  let σ : T ≅ T := RankOneWeylCriterion.commIso c
  have hσ : i ≫ (G.innerIso g).hom = CommGroupScheme.groupHom σ.hom ≫ i := hg
  have hσα : σ.hom ≫ α = -α := congrArg Additive.ofMul h.1
  have hcongr_neg : characterLattice.congr σ (-α) = α := by
    rw [characterLattice.congr_apply, ← hσα, Iso.inv_hom_id_assoc]
  have hcongr : characterLattice.congr σ α = -α := by
    have h1 := AddEquiv.map_neg (characterLattice.congr σ) α
    rw [hcongr_neg] at h1
    exact neg_eq_iff_eq_neg.mp h1.symm
  rw [← hcongr]
  exact weightSpace_map_of_transport σ (G.innerIso g) hσ α

/-- A Weyl inversion of a root makes its negative a root of the same dimension. -/
theorem IsWeylInversion.neg_mem_roots {α : characterLattice T} {c : T.toGrp ≅ T.toGrp}
    {n : Lie.AffinePoints G K} (h : IsWeylInversion i α c n) (hα : α ∈ roots i) :
    -α ∈ roots i ∧
      Module.finrank K (weightSpace i (-α)) = Module.finrank K (weightSpace i α) := by
  let f := Lie.targetMapLinear (G.innerIso ((Lie.affineSelfTestIso _).inv ≫ n)).hom
    (CommRingCat.of K)
  have hf : Function.Injective f := Lie.targetMapLinear_injective _ _
  have hmap := h.map_weightSpace
  have hfin : Module.finrank K (weightSpace i (-α)) = Module.finrank K (weightSpace i α) := by
    rw [← hmap]
    exact (Submodule.equivMapOfInjective f hf (weightSpace i α)).finrank_eq.symm
  refine ⟨⟨neg_ne_zero.mpr hα.1, fun hbot => hα.2 ?_⟩, hfin⟩
  rw [← hmap] at hbot
  exact Submodule.map_injective_of_injective hf (hbot.trans (Submodule.map_bot f).symm)

end Inversion

section Centralizer

variable [IsAffineHom G.X.hom]

/-- A root-orthogonal cocharacter: it annihilates `α`, and every root it annihilates is
proportional to `α`. -/
theorem exists_orthogonalCocharacter [LocallyOfFiniteType G.X.hom]
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G) {α : characterLattice T} (hα : α ≠ 0) :
    ∃ ζ : cocharacterLattice T, latticePairing T α ζ = 0 ∧
      ∀ β ∈ roots i, latticePairing T β ζ = 0 → ∃ m n : ℤ, m ≠ 0 ∧ m • β = n • α := by
  obtain ⟨ν, hν⟩ := hT.exists_pairings_ne_zero {α} (Set.finite_singleton α)
    (fun x hx => (Set.mem_singleton_iff.mp hx) ▸ hα)
  have hαν : latticePairing T α ν ≠ 0 := hν α rfl
  obtain ⟨ζ, hζα, hζ⟩ := hT.exists_rootOrthogonalCocharacter i α ν
  exact ⟨ζ, hζα, fun β hβ h0 => ⟨_, _, hαν, hζ β hβ h0⟩⟩

variable [Smooth G.X.hom] (i : T.toGrp ⟶ G)

/-- A weight of the torus inside a centralizer of `ζ` pairs to zero with `ζ`. -/
theorem pairing_eq_zero_of_mem_roots (ζ : cocharacterLattice T)
    {M : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom M.X.hom] {m : M ⟶ G}
    (hm : (Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i)).IsRepresentedBy m)
    (t : T.toGrp ⟶ M) (ht : t ≫ m = i) {β : characterLattice T} (hβ : β ∈ roots t) :
    latticePairing T β ζ = 0 := by
  have : Mono m.hom.hom := hm.1
  obtain ⟨Y, hY, hY0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hβ.2
  have hX : Lie.targetMapLinear m _ Y ∈ weightSpace i β := by
    have h := lieKernelHomLinear_mem_weightSpace m t β hY
    rwa [ht] at h
  have hX0 : Lie.targetMapLinear m _ Y ≠ 0 := by
    intro h
    apply hY0
    apply Lie.targetMapLinear_injective m _
    rw [h, map_zero]
  have hcent := (hm.mem_range_lieKernelHomLinear (Lie.targetMapLinear m _ Y)).mp ⟨Y, rfl⟩
  have h0 := (dynamicLie K G (CommGroupScheme.groupHom ζ ≫ i)
    (Lie.targetMapLinear m _ Y).toMul).1.mp hcent
  have hn := weightSpace_le_weightSpace_cocharacter ζ i β hX
  by_contra hne
  have hdis := weightSpace_disjoint isSplitTorus_gm (CommGroupScheme.groupHom ζ ≫ i)
    (χ := Gm.powerHom _ (latticePairing T β ζ)) (χ' := Gm.powerHom _ 0)
    (fun h => hne (Gm.powerHom_injective K h))
  exact hX0 ((Submodule.disjoint_def.mp hdis) _ hn h0)

omit [IsAffineHom G.X.hom] [Smooth G.X.hom] in
/-- The Weyl point of a root inversion lies in the centralizer of every cocharacter
orthogonal to the root, and it transports the torus there. -/
theorem IsWeylInversion.exists_lift {α : characterLattice T} {c : T.toGrp ≅ T.toGrp}
    {n : Lie.AffinePoints G K} (h : IsWeylInversion i α c n) {ζ : cocharacterLattice T}
    (hζα : latticePairing T α ζ = 0) {M : GroupScheme (Spec (CommRingCat.of K))} {m : M ⟶ G}
    (hm : (Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i)).IsRepresentedBy m)
    (t : T.toGrp ⟶ M) (ht : t ≫ m = i) :
    ∃ n' : Lie.AffinePoints M K, PointwiseSchemeAction.IsTransporter (c.hom ≫ t) t n' := by
  have : Mono m.hom.hom := hm.1
  have hfix : CommGroupScheme.groupHom ζ ≫ c.hom = CommGroupScheme.groupHom ζ := h.2.1 ζ hζα
  have hmem : n ∈ (Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i)).carrier _ := by
    rw [Dynamic.mem_centralizer, Dynamic.orbit]
    have htr := h.2.2 _ (CartesianMonoidalCategory.fst _ (Gm (Spec (CommRingCat.of K))).X)
      (CartesianMonoidalCategory.snd _ (Gm (Spec (CommRingCat.of K))).X ≫
        (CommGroupScheme.groupHom ζ).hom.hom)
    have hc : (CommGroupScheme.groupHom ζ).hom.hom ≫ (c.hom ≫ i).hom.hom =
        (CommGroupScheme.groupHom ζ ≫ i).hom.hom := by
      rw [← Grp.comp_hom_hom, ← Category.assoc, hfix]
    rw [Category.assoc, hc] at htr
    rw [htr]
    simp only [Grp.comp_hom_hom, Category.assoc, mul_inv_cancel_right]
  rw [← hm.2] at hmem
  obtain ⟨n', hn'⟩ := SubgroupFunctor.mem_range.mp hmem
  refine ⟨n', fun T' b x => ?_⟩
  apply (cancel_mono m.hom.hom).mp
  have htr := h.2.2 T' b x
  rw [MonObj.mul_comp, MonObj.mul_comp]
  simp only [Category.assoc, ← Grp.comp_hom_hom, ht, hn']
  simpa only [Grp.comp_hom_hom, Category.assoc] using htr

/-- **The rank-one centralizer is reductive.** Let `ζ` annihilate a root `α`, with every
root annihilated by `ζ` proportional to `α`. Under the rootwise hypotheses, every closed
representative of the centralizer of `ζ` is connected reductive. -/
theorem isConnectedReductive_centralizer [IsAlgClosed K] [ConnectedSpace G.X.left]
    (hT : IsSplitTorus T.toGrp) (hi : IsClosedSubgroup i)
    (hself : torusCentralizer i = SubgroupFunctor.range i)
    (hdim : ∀ α ∈ roots i, Module.finrank K (weightSpace i α) = 1)
    (hred : ∀ α ∈ roots i, ∀ β ∈ roots i,
      (∃ m n : ℤ, m ≠ 0 ∧ m • β = n • α) → β = α ∨ β = -α)
    {α : characterLattice T} (hα : α ∈ roots i) {c : T.toGrp ≅ T.toGrp}
    {n : Lie.AffinePoints G K} (hw : IsWeylInversion i α c n) {ζ : cocharacterLattice T}
    (hζα : latticePairing T α ζ = 0)
    (hζ : ∀ β ∈ roots i, latticePairing T β ζ = 0 → ∃ m n : ℤ, m ≠ 0 ∧ m • β = n • α)
    {M : GroupScheme (Spec (CommRingCat.of K))} {m : M ⟶ G}
    (hm : (Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ i)).IsRepresentedBy m)
    (hmc : IsClosedSubgroup m) :
    IsConnectedReductive M := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : Mono m.hom.hom := hm.1
  have : Smooth M.X.hom := (dynamicSmooth K G (CommGroupScheme.groupHom ζ ≫ i) M m).2.1 hm
  have : ConnectedSpace M.X.left :=
    DynamicConnected.connectedSpace_of_isRepresentedBy_centralizer G _ hm
  have : IsAffineHom M.X.hom := hmc.isAffineHom
  let t : T.toGrp ⟶ M := hm.liftOfLE i (range_le_centralizer_groupHom_comp i ζ)
  have ht : t ≫ m = i := hm.liftOfLE_comp i _
  have hsplit : IsSplitSubtorus t := ⟨hT, IsClosedSubgroup.of_comp hmc (ht.symm ▸ hi)⟩
  have hself' : torusCentralizer t = SubgroupFunctor.range t :=
    RelativeRoot.torusCentralizer_eq_range_of_comp_mono t m (by rw [ht]; exact hself)
  obtain ⟨hneg, hdimneg⟩ := hw.neg_mem_roots hα
  have hzero_neg : latticePairing T (-α) ζ = 0 := by rw [map_neg, LinearMap.neg_apply, hζα, neg_zero]
  have hfin (β : characterLattice T) (hβ : latticePairing T β ζ = 0) :
      Module.finrank K (weightSpace t β) = Module.finrank K (weightSpace i β) := by
    have hmap := map_weightSpace_of_pairing_eq_zero i ζ hm t ht hβ
    rw [← hmap]
    exact (Submodule.equivMapOfInjective _ (Lie.targetMapLinear_injective m _)
      (weightSpace t β)).finrank_eq
  have hroots (β : characterLattice T) : β ∈ roots t ↔ β = α ∨ β = -α := by
    constructor
    · intro hβ
      have hβi : β ∈ roots i := by
        have h := roots_subset_comp m t hβ
        rwa [ht] at h
      exact hred α hα β hβi (hζ β hβi (pairing_eq_zero_of_mem_roots i ζ hm t ht hβ))
    · rintro (rfl | rfl)
      · exact mem_relativeRoots_of_pairing_eq_zero i ζ hm t ht hα hζα
      · exact mem_relativeRoots_of_pairing_eq_zero i ζ hm t ht hneg hzero_neg
  obtain ⟨n', hn'⟩ := hw.exists_lift i hζα hm t ht
  exact rankOneWeylReductivity K M T t hsplit hself' α hα.1 hroots
    ((hfin α hζα).trans (hdim α hα)) ((hfin (-α) hzero_neg).trans (hdim (-α) hneg)) c n'
    hw.1 hn'

end Centralizer

section Criterion

variable [IsAlgClosed K] [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]

/-- **The radical-free centralizer of a root.** For a root `α`, the centralizer of a
root-orthogonal cocharacter `ζ` (`exists_orthogonalCocharacter`), represented by the fixed
affine construction `Dynamic.Affine.centralizerScheme`, is connected reductive by
`isConnectedReductive_centralizer`; this packages it as `RadicalFreeRootCentralizerData`. -/
def rootCentralizerData (i : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp)
    (hi : IsClosedSubgroup i) (hself : torusCentralizer i = SubgroupFunctor.range i)
    (hdim : ∀ α ∈ roots i, Module.finrank K (weightSpace i α) = 1)
    (hred : ∀ α ∈ roots i, ∀ β ∈ roots i,
      (∃ m n : ℤ, m ≠ 0 ∧ m • β = n • α) → β = α ∨ β = -α)
    (α : characterLattice T) (hα : α ∈ roots i)
    (hweyl : ∃ (c : T.toGrp ≅ T.toGrp) (n : Lie.AffinePoints G K), IsWeylInversion i α c n) :
    RadicalFreeRootCentralizerData i α :=
  letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  { cocharacter := (exists_orthogonalCocharacter hT i hα.1).choose
    groupScheme := Dynamic.Affine.centralizerScheme
      (CommGroupScheme.groupHom (exists_orthogonalCocharacter hT i hα.1).choose ≫ i)
    inclusion := Dynamic.Affine.centralizerHom _
    represents := Dynamic.Affine.isRepresentedBy_centralizerHom _
    annihilates := (exists_orthogonalCocharacter hT i hα.1).choose_spec.1
    radical :=
      (isConnectedReductive_centralizer i hT hi hself hdim hred hα
        hweyl.choose_spec.choose_spec
        (exists_orthogonalCocharacter hT i hα.1).choose_spec.1
        (exists_orthogonalCocharacter hT i hα.1).choose_spec.2
        (Dynamic.Affine.isRepresentedBy_centralizerHom _)
        (Dynamic.Affine.isClosedSubgroup_centralizerHom _)).hasTrivialUnipotentRadical }

/-- **Reductivity from rootwise Weyl inversions.** Over an algebraically closed field, a
smooth connected affine group with a closed self-centralizing split torus is connected
reductive if its root spaces are lines, its roots are reduced, and each root `α` has a Weyl
inversion: an automorphism `c` of the torus with `α ∘ c = -α` fixing the cocharacters
orthogonal to `α`, realized by conjugation with a point `n`. -/
theorem isConnectedReductive_of_rootwiseWeyl (i : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp)
    (hi : IsClosedSubgroup i) (hself : torusCentralizer i = SubgroupFunctor.range i)
    (hdim : ∀ α ∈ roots i, Module.finrank K (weightSpace i α) = 1)
    (hred : ∀ α ∈ roots i, ∀ β ∈ roots i,
      (∃ m n : ℤ, m ≠ 0 ∧ m • β = n • α) → β = α ∨ β = -α)
    (hweyl : ∀ α ∈ roots i, ∃ (c : T.toGrp ≅ T.toGrp) (n : Lie.AffinePoints G K),
      c.hom ≫ CommGroupScheme.groupHom α = CommGroupScheme.groupHom (-α) ∧
        (∀ ν : cocharacterLattice T, latticePairing T α ν = 0 →
          CommGroupScheme.groupHom ν ≫ c.hom = CommGroupScheme.groupHom ν) ∧
        PointwiseSchemeAction.IsTransporter (c.hom ≫ i) i n) :
    IsConnectedReductive G :=
  RadicalFreeRootCentralizerData.isConnectedReductive i hT hi hself fun α hα =>
    ⟨rootCentralizerData i hT hi hself hdim hred α hα (hweyl α hα)⟩

end Criterion

end RootwiseWeyl

end Langlands.GroupScheme
