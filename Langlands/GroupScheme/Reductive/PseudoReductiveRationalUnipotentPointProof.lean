import Langlands.GroupScheme.Reductive.PseudoReductiveRationalUnipotentPointStatement
import Langlands.GroupScheme.Derived.FieldBaseChangeProof
import Langlands.GroupScheme.SmoothConnectedNormalClosure
import Langlands.GroupScheme.UnipotentClosedSubgroupProof
import Langlands.GroupScheme.Unipotent.FieldReflectionProof
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.Dynamic.Uniqueness
import Langlands.GroupScheme.Torus.SplitReductiveProof
import Langlands.GroupScheme.Torus.GeometricallyIntegral
import Langlands.GroupScheme.Torus.Lattice

/-! # Rational points of dynamic unipotent subgroups in unipotent normal subgroups

Proof of `PseudoReductiveRationalUnipotentPointStatement`. The closed normal
subgroup `H` of `G_K` is descended to the closed normal `k`-subgroup of points
landing in `H` after base change. The morphism `t ↦ χ(t) u χ(t)⁻¹ u⁻¹` on `𝔾_m`
generates a smooth connected subgroup there, whose smooth connected normal
closure is unipotent because its base change is a closed subgroup of `H`.
Pseudo-reductivity kills it, so `u` centralizes `χ`; uniqueness of limits then
gives `u = 1`.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace PseudoReductiveRationalUnipotentPoint

/-- The restriction core of a normal subgroup functor is normal. -/
theorem restrictionCore_isNormal {S S' : Scheme.{u}} (b : S' ⟶ S) {G : GroupScheme S}
    {F : SubgroupFunctor ((GroupScheme.baseChange b).obj G)} (hF : F.IsNormal) :
    (SubgroupFunctor.restrictionCore b F).IsNormal := by
  intro T g x _ hx T' c
  rw [MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv, map_mul, map_mul, map_inv]
  exact hF T' _ _ trivial (hx T' c)

/-- A rational point whose base change factors through `j` lies in the
restriction core of the range of `j`. -/
theorem mem_restrictionCore_of_baseChange {k K : Type u} [Field k] [Field K] [Algebra k K]
    {G : GroupScheme (Spec (CommRingCat.of k))} {H : GroupScheme (Spec (CommRingCat.of K))}
    (j : H ⟶ (GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G)
    (u : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
    (y : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ H.X)
    (hy : baseChangePointsEquiv (Spec.map (CommRingCat.ofHom (algebraMap k K))) G
        (Over.mk (𝟙 (Spec (CommRingCat.of K)))) (y ≫ j.hom.hom) = toUnit _ ≫ u) :
    u ∈ (SubgroupFunctor.restrictionCore (Spec.map (CommRingCat.ofHom (algebraMap k K)))
      (SubgroupFunctor.range j)).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
  intro T' c
  have hc : c = (Over.map (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map
      (toUnit T') ≫ toUnit _ :=
    toUnit_unique _ _
  have hy' : baseChangePointsEquiv (Spec.map (CommRingCat.ofHom (algebraMap k K))) G
      (𝟙_ (Over (Spec (CommRingCat.of K)))) (y ≫ j.hom.hom) = toUnit _ ≫ u := hy
  rw [hc, Category.assoc, ← hy', ← baseChangePointsEquiv_naturality, MulEquiv.symm_apply_apply]
  exact SubgroupFunctor.mem_range.2 ⟨toUnit T' ≫ y, Category.assoc _ _ _⟩

end PseudoReductiveRationalUnipotentPoint

open PseudoReductiveRationalUnipotentPoint in
/-- A rational point of `U_G(χ)` of a pseudo-reductive group whose base change
lies in a closed unipotent normal subgroup of `G_K` is trivial. -/
theorem pseudoReductiveRationalUnipotentPoint :
    PseudoReductiveRationalUnipotentPointStatement.{u} := by
  intro k K _ _ _ G hG χ H j hj hHu hHn u hu ⟨y, hy⟩
  let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have : Smooth G.X.hom := hG.smooth
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : ConnectedSpace G.X.left := hG.connectedSpace
  have : IsClosedImmersion j.hom.hom.left := hj
  -- Descend `H` to a closed normal subgroup `Z` of `G` containing `u`.
  let F := SubgroupFunctor.restrictionCore b (SubgroupFunctor.range j)
  have hrepj : (SubgroupFunctor.range j).IsRepresentedBy j :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  obtain ⟨Z, z, hz, hzclosed⟩ :=
    SubgroupFunctor.restrictionCore_isClosedRepresentable b _ ⟨H, j, hrepj, hj⟩
  have hFn : F.IsNormal := restrictionCore_isNormal b hHn
  have huF : u ∈ F.carrier (Over.mk (𝟙 _)) := mem_restrictionCore_of_baseChange j u y hy
  -- The pointed commutator morphism `t ↦ χ(t) u χ(t)⁻¹ u⁻¹` on `𝔾_m`.
  let V := (Gm (Spec (CommRingCat.of k))).X
  have hgm : IsSplitTorus (Gm (Spec (CommRingCat.of k))).toGrp := isSplitTorus_gm
  have : Smooth V.hom := hgm.smooth
  have : IsAffineHom V.hom := hgm.isAffineHom
  have hVint : GeometricallyIntegral V.hom := hgm.isTorus.geometricallyIntegral
  let w : V ⟶ G.X := toUnit V ≫ u
  let f : V ⟶ G.X := χ.hom.hom * w * χ.hom.hom⁻¹ * w⁻¹
  have hv₀ : (1 : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ V) ≫ f = 1 := by
    simp only [f, MonObj.comp_mul, GrpObj.comp_inv, MonObj.one_comp, one_mul, inv_one,
      mul_one, mul_inv_cancel]
  have hfF : f ∈ F.carrier V := by
    have hw : w ∈ F.carrier V := F.comp_mem _ huF
    exact (F.carrier V).mul_mem (hFn V _ _ trivial hw) ((F.carrier V).inv_mem hw)
  -- The generated smooth connected subgroup and its smooth connected normal closure.
  obtain ⟨C, hC⟩ := ImageGeneration.pointedImageGeneration k G inferInstance inferInstance
    V inferInstance inferInstance hVint 1 f hv₀
  have : Smooth C.group.X.hom := hC.1
  have : IsAffineHom C.group.X.hom := hC.2.1
  have : GeometricallyConnected C.group.X.hom := hC.2.2.1
  have : Subsingleton (Spec (CommRingCat.of k)) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum k))
  have : ConnectedSpace C.group.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton C.group.X.hom
  have hzn : (SubgroupFunctor.range z).IsNormal := by
    rw [hz.2]
    exact hFn
  have hCz : SubgroupFunctor.range C.inclusion ≤ SubgroupFunctor.range z :=
    C.range_le z hzclosed ((factorsThrough_iff_containsImage f z).2
      ((SubgroupFunctor.containsImage_iff _ f).2 (by rw [hz.2]; exact hfF)))
  let D := smoothConnectedNormalClosure C.inclusion
  have hDz : SubgroupFunctor.range D.inclusion ≤ SubgroupFunctor.range z :=
    D.range_le z hzclosed hzn hCz
  have : Smooth D.group.X.hom := D.hasSmoothConnectedGeneration.1
  have : IsAffineHom D.group.X.hom := D.hasSmoothConnectedGeneration.2.1
  have : GeometricallyConnected D.group.X.hom := D.hasSmoothConnectedGeneration.2.2.1
  have : ConnectedSpace D.group.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton D.group.X.hom
  -- `D` is unipotent: its base change is a closed subgroup of `H`.
  have : IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom := by
    change IsAffineHom (pullback.snd G.X.hom b)
    infer_instance
  have : LocallyOfFiniteType ((GroupScheme.baseChange b).obj G).X.hom := by
    change LocallyOfFiniteType (pullback.snd G.X.hom b)
    infer_instance
  have : IsAffineHom H.X.hom := by
    rw [← Over.w j.hom.hom]
    infer_instance
  have : LocallyOfFiniteType H.X.hom := by
    rw [← Over.w j.hom.hom]
    infer_instance
  let iK := (GroupScheme.baseChange b).map D.inclusion
  have hiK : SubgroupFunctor.range iK ≤ SubgroupFunctor.range j := by
    rw [SubgroupFunctor.range_baseChangeHom]
    intro T x hx
    apply SubgroupFunctor.restrictionCore_baseChange_le b _ T
    have hxz := hDz _ hx
    rw [hz.2] at hxz
    exact hxz
  let v := SubgroupFunctor.IsRepresentedBy.factorHom hrepj iK hiK
  have hv : v ≫ j = iK := SubgroupFunctor.IsRepresentedBy.factorHom_comp hrepj iK hiK
  have hvclosed : IsClosedSubgroup v :=
    IsClosedSubgroup.of_comp hj (by rw [hv]; exact D.closed.baseChange b)
  have hDu : IsUnipotent D.group :=
    IsUnipotent.of_baseChange (k := k) (K := K)
      (unipotentClosedSubgroup K H _ v hvclosed hHu)
  -- Pseudo-reductivity kills `D`, hence `f = 1`.
  have hDbot := hG.hasTrivialUnipotentRadical D.group D.inclusion D.closed inferInstance
    inferInstance hDu D.isNormal
  have hf1 : f = 1 := by
    have hfC : f ∈ (SubgroupFunctor.range C.inclusion).carrier V :=
      SubgroupFunctor.mem_range.2 ⟨C.factor, C.factor_comp⟩
    have hfD : f ∈ (SubgroupFunctor.range D.inclusion).carrier V := D.contains V hfC
    rw [hDbot, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hfD
    exact hfD
  -- So `u` centralizes `χ`, its limit is `u` itself, and uniqueness gives `u = 1`.
  have hcomm : χ.hom.hom * w * χ.hom.hom⁻¹ = w := mul_inv_eq_one.1 hf1
  have hcent : u ∈ (Dynamic.centralizer χ).carrier (Over.mk (𝟙 _)) := by
    rw [Dynamic.mem_centralizer, Dynamic.orbit]
    have h := congrArg (fun e => snd (Over.mk (𝟙 (Spec (CommRingCat.of k)))) V ≫ e) hcomm
    simp only [MonObj.comp_mul, GrpObj.comp_inv] at h
    have ht : snd (Over.mk (𝟙 (Spec (CommRingCat.of k)))) V ≫ w =
        fst (Over.mk (𝟙 (Spec (CommRingCat.of k)))) V ≫ u := by
      simp only [w, ← Category.assoc]
      congr 1
      exact toUnit_unique _ _
    rw [ht] at h
    exact h
  have : IsSeparated G.X.hom := IsSeparated.of_isAffineHom G.X.hom
  exact Dynamic.HasLimit.unique χ (Dynamic.hasLimit_of_mem_centralizer χ hcent) hu

end Langlands.GroupScheme
