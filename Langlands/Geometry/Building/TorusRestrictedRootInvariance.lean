import Langlands.Geometry.Building.KPUnramifiedScaledRootDepth
import Langlands.Geometry.Building.RootValueTorusRestriction
import Langlands.Geometry.Building.IntegerCentralizer
import Langlands.Geometry.Building.RootFunctionGaloisAction
import Langlands.GroupScheme.Torus.GaloisCharacterFunctor
import Langlands.GroupScheme.Reductive.RootDatumGaloisRoots

/-! # Invariance properties of torus-restricted root functions

For a valuation `φ` of the root datum of `(G, T)` and a homomorphism `f : S ⟶ T` of split tori,
`torusRestrictedRootFunctionFamily` is the family of root functions of `(G, S)` whose level
sets are the depth subgroups `torusRestrictedRootDepthSubgroup`. This module proves three
properties of that family on a root group `U_α`:

* an ultrametric inequality `min (ψ_α g) (ψ_α h) ≤ ψ_α (g h⁻¹)`;
* invariance under coefficient conjugation by `σ ∈ Aut(K/k)`, when `φ` is fixed by the Galois
  action and `α` comes from `k`;
* invariance under conjugation by points of `S` at which every rational character has
  valuation one, when `φ` satisfies V6 on the centralizer of `T`.

The last two both follow from one fact: a group endomorphism that preserves every depth
subgroup of `α` preserves `ψ_α`.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.BruhatTits

namespace Langlands.Geometry.Building

section Generic

variable {k : Type u} [Field k]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : T.toGrp ⟶ G} [IsAffineHom G.X.hom] [Mono i.hom.hom.left] [Smooth G.X.hom]
  {φ : RootFunctionFamily T G}

/-- **Ultrametric inequality** for the torus-restricted root functions on an actual root
group: `min (ψ_α g) (ψ_α h) ≤ ψ_α (g h⁻¹)`. -/
theorem torusRestrictedRootFunctionFamily_min_le_mul_inv
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs i) (hφ : IsRootDatumValuation i φ)
    (f : S ⟶ T) (α : characterLattice S)
    (hα : α ∈ relativeRoots (CommGroupScheme.groupHom f ≫ i))
    (g h : rationalPoints G)
    (hg : g ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ i) α)
    (hh : h ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ i) α) :
    min (torusRestrictedRootFunctionFamily hS hT hE hφ f α g)
        (torusRestrictedRootFunctionFamily hS hT hE hφ f α h) ≤
      torusRestrictedRootFunctionFamily hS hT hE hφ f α (g * h⁻¹) := by
  have hgh : g * h⁻¹ ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ i) α :=
    Subgroup.mul_mem _ hg (Subgroup.inv_mem _ hh)
  refine WithTop.forall_coe_le_iff_le.mp fun r hr => ?_
  rw [le_min_iff] at hr
  have h1 := (le_torusRestrictedRootFunctionFamily_iff hS hT hE hφ f α hα g hg r).mp hr.1
  have h2 := (le_torusRestrictedRootFunctionFamily_iff hS hT hE hφ f α hα h hh r).mp hr.2
  exact (le_torusRestrictedRootFunctionFamily_iff hS hT hE hφ f α hα _ hgh r).mpr
    (Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ h2))

/-- A group endomorphism `e` of `G(k)` that preserves membership in every depth subgroup of
`α` preserves the torus-restricted root function `ψ_α` at every point. -/
theorem torusRestrictedRootFunctionFamily_apply_eq_of_depth_iff
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs i) (hφ : IsRootDatumValuation i φ)
    (f : S ⟶ T) (α : characterLattice S) (e : rationalPoints G →* rationalPoints G)
    (he : ∀ (r : ℝ) (g : rationalPoints G),
      e g ∈ torusRestrictedRootDepthSubgroup hφ f α r ↔
        g ∈ torusRestrictedRootDepthSubgroup hφ f α r)
    (g : rationalPoints G) :
    torusRestrictedRootFunctionFamily hS hT hE hφ f α (e g) =
      torusRestrictedRootFunctionFamily hS hT hE hφ f α g := by
  by_cases hα : α ∈ relativeRoots (CommGroupScheme.groupHom f ≫ i)
  · have hU : ∀ g : rationalPoints G,
        e g ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ i) α ↔
          g ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ i) α := by
      intro g
      rw [mem_rootGroupPoints_iff_exists_torusRestrictedRootDepth hS hT hE hφ f α hα.1,
        mem_rootGroupPoints_iff_exists_torusRestrictedRootDepth hS hT hE hφ f α hα.1]
      exact exists_congr fun r => he r g
    by_cases hg : g ∈ rootGroupPoints (CommGroupScheme.groupHom f ≫ i) α
    · apply WithTop.eq_of_forall_coe_le_iff
      intro r
      rw [le_torusRestrictedRootFunctionFamily_iff hS hT hE hφ f α hα _ ((hU g).mpr hg) r,
        le_torusRestrictedRootFunctionFamily_iff hS hT hE hφ f α hα g hg r]
      exact he r g
    · rw [torusRestrictedRootFunctionFamily_eq_top_of_not_mem hS hT hE hφ f α g hg,
        torusRestrictedRootFunctionFamily_eq_top_of_not_mem hS hT hE hφ f α _
          (fun h => hg ((hU g).mp h))]
  · rw [torusRestrictedRootFunctionFamily_eq_top_of_not_mem_roots hS hT hE hφ f α hα,
      torusRestrictedRootFunctionFamily_eq_top_of_not_mem_roots hS hT hE hφ f α hα]

omit [Smooth G.X.hom] in
/-- Under V6, conjugation `u ↦ z⁻¹ u z` by a centralizer point `z` at which every rational
character of the centralizer has valuation one maps each depth subgroup into itself. -/
theorem torusRestrictedRootDepthSubgroup_conj_mem_of_mem_characterValuationKernel
    (v : Valuation k (WithZero (Multiplicative ℤ)))
    {Z : GroupScheme (Spec (CommRingCat.of k))} (j : Z ⟶ G) (s : T.toGrp ⟶ Z)
    (h : Function.Bijective (Cartan.restrictionEvaluation s))
    (hj : (torusCentralizer i).IsRepresentedBy j)
    (hφ : IsRootDatumValuation i φ)
    (hV : IntegerValuation.IsCentralizerCompatible v i j s h φ)
    {z : rationalPoints Z} (hz : z ∈ characterValuationKernel v Z)
    (f : S ⟶ T) (α : characterLattice S) (r : ℝ) {g : rationalPoints G}
    (hg : g ∈ torusRestrictedRootDepthSubgroup hφ f α r) :
    (rationalPoints.map j z)⁻¹ * g * rationalPoints.map j z ∈
      torusRestrictedRootDepthSubgroup hφ f α r := by
  have htr : IntegerValuation.centralizerTranslation v s h z = 1 := by
    rw [← MonoidHom.mem_ker, IntegerValuation.centralizerTranslation_ker]
    exact hz
  have hmap : (torusRestrictedRootDepthSubgroup hφ f α r).map
      (MulAut.conj (rationalPoints.map j z)⁻¹).toMonoidHom ≤
        torusRestrictedRootDepthSubgroup hφ f α r := by
    unfold torusRestrictedRootDepthSubgroup
    simp only [Subgroup.map_iSup]
    refine iSup_le fun χ => iSup_le fun hχ => iSup_le fun m =>
      iSup_le fun hm => iSup_le fun heq => ?_
    refine le_iSup_of_le χ (le_iSup_of_le hχ (le_iSup_of_le m
      (le_iSup_of_le hm (le_iSup_of_le heq ?_))))
    rintro _ ⟨u, ⟨huU, hur⟩, rfl⟩
    have hconjU : (rationalPoints.map j z)⁻¹ * u * rationalPoints.map j z ∈
        rootGroupPoints i χ := by
      have hc := conj_mem_rootGroupPoints (centralizerToNormalizer i j hj z⁻¹) huU
      rwa [weylAction_centralizerToNormalizer hj, LinearEquiv.coe_one, id,
        coe_centralizerToNormalizer, map_inv, inv_inv] at hc
    change (rationalPoints.map j z)⁻¹ * u * ((rationalPoints.map j z)⁻¹)⁻¹ ∈
      rootFiltration i φ χ (m * r)
    rw [inv_inv]
    refine ⟨hconjU, ?_⟩
    rw [hV χ hχ z u huU, htr, toAdd_one, map_zero, WithTop.coe_zero, add_zero]
    exact hur
  refine hmap ⟨g, hg, ?_⟩
  change (rationalPoints.map j z)⁻¹ * g * ((rationalPoints.map j z)⁻¹)⁻¹ = _
  rw [inv_inv]

/-- Under V6 for `φ`, conjugation by the image `t ∈ G(k)` of a point of `S` at which every
rational character of `S` has valuation one preserves the torus-restricted root functions:
`ψ_α (t g t⁻¹) = ψ_α g`. -/
theorem torusRestrictedRootFunctionFamily_conj_of_mem_characterValuationKernel
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs i) (hφ : IsRootDatumValuation i φ)
    (v : Valuation k (WithZero (Multiplicative ℤ)))
    {Z : GroupScheme (Spec (CommRingCat.of k))} (j : Z ⟶ G) (s : T.toGrp ⟶ Z)
    (h : Function.Bijective (Cartan.restrictionEvaluation s))
    (hj : (torusCentralizer i).IsRepresentedBy j) (hsj : s ≫ j = i)
    (hV : IntegerValuation.IsCentralizerCompatible v i j s h φ)
    (f : S ⟶ T) {t : rationalPoints S.toGrp} (ht : t ∈ characterValuationKernel v S.toGrp)
    (α : characterLattice S) (g : rationalPoints G) :
    torusRestrictedRootFunctionFamily hS hT hE hφ f α
        (rationalPoints.map (CommGroupScheme.groupHom f ≫ i) t * g *
          (rationalPoints.map (CommGroupScheme.groupHom f ≫ i) t)⁻¹) =
      torusRestrictedRootFunctionFamily hS hT hE hφ f α g := by
  have hpt : ∀ y : rationalPoints S.toGrp,
      rationalPoints.map j (rationalPoints.map (CommGroupScheme.groupHom f ≫ s) y) =
        rationalPoints.map (CommGroupScheme.groupHom f ≫ i) y := by
    intro y
    rw [rationalPoints.map_apply, rationalPoints.map_apply, rationalPoints.map_apply]
    rw [← hsj]
    rfl
  have hz : rationalPoints.map (CommGroupScheme.groupHom f ≫ s) t ∈
      characterValuationKernel v Z :=
    IntegerValuation.map_mem_characterValuationKernel v _ ht
  have hz' : rationalPoints.map (CommGroupScheme.groupHom f ≫ s) t⁻¹ ∈
      characterValuationKernel v Z :=
    IntegerValuation.map_mem_characterValuationKernel v _ (Subgroup.inv_mem _ ht)
  set p := rationalPoints.map (CommGroupScheme.groupHom f ≫ i) t with hp
  refine torusRestrictedRootFunctionFamily_apply_eq_of_depth_iff hS hT hE hφ f α
    (MulAut.conj p).toMonoidHom (fun r g => ⟨fun hg => ?_, fun hg => ?_⟩) g
  · have hc := torusRestrictedRootDepthSubgroup_conj_mem_of_mem_characterValuationKernel
      v j s h hj hφ hV hz f α r hg
    rw [hpt] at hc
    change p⁻¹ * (p * g * p⁻¹) * p ∈ _ at hc
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hc
  · have hc := torusRestrictedRootDepthSubgroup_conj_mem_of_mem_characterValuationKernel
      v j s h hj hφ hV hz' f α r hg
    rw [hpt, map_inv, ← hp, inv_inv] at hc
    exact hc

end Generic

section Galois

private instance torusRestrictedInvarianceAffineHom {F : Type u} [Field F]
    {K : Type u} [Field K] [Algebra F K]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom] :
    IsAffineHom (baseChanged F K G).X.hom := by
  change IsAffineHom
    (CategoryTheory.Limits.pullback.snd G.X.hom (baseMap F K))
  infer_instance

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G)
  [Mono ((GroupScheme.baseChange (algebraBaseMap k K)).map i).hom.hom.left]

/-- **Galois invariance** of the torus-restricted root functions: if the upper valuation
`φ` is fixed by every `σ ∈ Aut(K/k)`, then for a character `a_K` coming from `k`,
`ψ_{a_K} (σ g) = ψ_{a_K} g` at every point `g`. -/
theorem torusRestrictedRootFunctionFamily_rationalConjugate
    [Smooth (baseChanged k K G).X.hom]
    {φ : RootFunctionFamily ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
      (baseChanged k K G)}
    (hS : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj S).toGrp)
    (hT : IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T).toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs
      ((GroupScheme.baseChange (algebraBaseMap k K)).map i))
    (hφ : IsRootDatumValuation ((GroupScheme.baseChange (algebraBaseMap k K)).map i) φ)
    (f : S ⟶ T)
    (hfixed : ∀ σ : K ≃ₐ[k] K, RootFunctionFamily.galoisAction k K T G σ φ = φ)
    (σ : K ≃ₐ[k] K) (a : characterLattice S) (g : rationalPoints (baseChanged k K G)) :
    torusRestrictedRootFunctionFamily hS hT hE hφ
        ((CommGroupScheme.baseChange (algebraBaseMap k K)).map f)
        (characterLattice.baseChange (algebraBaseMap k K) S a)
        (rationalConjugate k K G σ g) =
      torusRestrictedRootFunctionFamily hS hT hE hφ
        ((CommGroupScheme.baseChange (algebraBaseMap k K)).map f)
        (characterLattice.baseChange (algebraBaseMap k K) S a) g := by
  refine torusRestrictedRootFunctionFamily_apply_eq_of_depth_iff hS hT hE hφ _ _
    (rationalConjugate k K G σ).toMonoidHom (fun r g => ⟨fun hg => ?_, fun hg => ?_⟩) g
  · have hc := scaledRootDepth_galois_map_le k K i hφ f σ⁻¹
      (hfixed σ⁻¹) a r _ hg
    change rationalConjugate k K G σ⁻¹ (rationalConjugate k K G σ g) ∈ _ at hc
    rwa [← rationalConjugate_mul, inv_mul_cancel, rationalConjugate_one] at hc
  · exact scaledRootDepth_galois_map_le k K i hφ f σ (hfixed σ) a r
      g hg

end Galois

end Langlands.Geometry.Building
