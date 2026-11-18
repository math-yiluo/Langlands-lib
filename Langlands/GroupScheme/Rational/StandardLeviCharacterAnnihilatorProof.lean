import Langlands.GroupScheme.Rational.LeviCentralCompatibilityStatements
import Langlands.GroupScheme.Rational.StandardRootSubsetWeyl
import Langlands.GroupScheme.Rational.RootKernelTorus
import Langlands.GroupScheme.Rational.StandardLeviRealDecompositionProof
import Langlands.GroupScheme.Rational.SplitComponentProof
import Langlands.GroupScheme.Rational.RenardLeviCentralDecompositionProof

/-! # The real character image of a standard Levi -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

namespace Langlands.GroupScheme

open RealTorusSpace

/-- A normalizing point that factors through the subgroup fixes the restricted
real characters of that subgroup. -/
private theorem relativeWeylFullRealAction_restrict_of_mem_range
    {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G L : GroupScheme (Spec (CommRingCat.of k))}
    {i : T.toGrp ⟶ G} {t : T.toGrp ⟶ L} {j : L ⟶ G}
    [Mono i.hom.hom.left] [Mono t.hom.hom.left] [Mono j]
    (ht : t ≫ j = i) (n : normalizerPoints i)
    (hn : n.val ∈ (SubgroupFunctor.range j).carrier (Over.mk (𝟙 _)))
    (x : ℝ ⊗[ℤ] rationalCharacters L) :
    relativeWeylFullRealAction i (QuotientGroup.mk n) (rationalCharacterRestrictReal t x) =
      rationalCharacterRestrictReal t x := by
  obtain ⟨p, hp⟩ := SubgroupFunctor.mem_range.mp hn
  obtain ⟨σ, hσ⟩ := n.property
  have hpσ : IsNormalizingPoint t p σ := by
    change t ≫ (L.innerIso p).hom = CommGroupScheme.groupHom σ.hom ≫ t
    apply (cancel_mono j).mp
    calc
      (t ≫ (L.innerIso p).hom) ≫ j = i ≫ (G.innerIso n.val).hom := by
        rw [Category.assoc, innerIso_hom_comp, hp, ← Category.assoc, ht]
      _ = CommGroupScheme.groupHom σ.hom ≫ i := hσ
      _ = (CommGroupScheme.groupHom σ.hom ≫ t) ≫ j := by rw [Category.assoc, ht]
  let m : normalizerPoints t := ⟨p, σ, hpσ⟩
  have hm : normalizerPointsMap t j i ht m = n := Subtype.ext hp
  induction x using TensorProduct.inductionOn with
  | tmul r χ =>
    change r ⊗ₜ[ℤ] weylAction i n (torusCharacterRestrict t χ) =
      r ⊗ₜ[ℤ] torusCharacterRestrict t χ
    rw [← hm, weylAction_normalizerPointsMap, weylAction_torusCharacterRestrict]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- The image of real rational characters of a standard Levi in the maximal
split torus is the annihilator of the selected simple coroots. -/
theorem standardLeviCharacterAnnihilator : StandardLeviCharacterAnnihilatorStatement.{u} := by
  intro k _ G hG T i hi
  let := hG.isAffineHom
  let := hi.isSplitSubtorus.mono
  intro ν hν J hJ L j hjc hj t ht D
  let : Mono j := (Grp.forget _).mono_of_mono_map (f := j) hj.1
  let : Mono t.hom.hom.left := by
    have : Mono (t.hom.hom.left ≫ j.hom.hom.left) := by
      change Mono (t ≫ j).hom.hom.left
      rw [ht]
      infer_instance
    exact mono_of_mono _ j.hom.hom.left
  have hrange : (rationalCharacterRestrictReal t).range ≤ corootAnnihilator i D J := by
    rintro _ ⟨x, rfl⟩
    apply (mem_corootAnnihilator i D J _).mpr
    intro α hα
    have hw : (QuotientGroup.mk (D.representative α) : relativeWeylGroup i) ∈
        standardRelativeWeylGroup i ν J := by
      rw [← rootSubsetWeylGroup_standardLevi hG i hi (relativeRoots i)
        (Or.inl rfl) ν hν J hJ]
      apply Subgroup.subset_closure
      exact ⟨α.val, subset_rootClosure _ (Or.inl hα), D.coroot α, D.pair_self α, D.action α⟩
    obtain ⟨n, hn, hclass⟩ := (mem_standardRelativeWeylGroup_iff i ν).mp hw
    have hn' : n.val ∈ (SubgroupFunctor.range j).carrier (Over.mk (𝟙 _)) := by
      rw [hj.2]
      exact hn
    have hfix := relativeWeylFullRealAction_restrict_of_mem_range ht n hn' x
    rw [hclass, D.real_reflection i] at hfix
    exact (smul_eq_zero.mp (sub_eq_self.mp hfix)).resolve_right (D.one_tmul_ne_zero i α)
  have hcentral := standardLeviCentralDirections.2 k G hG T i hi ν hν J hJ L j hjc hj
  obtain ⟨A, a, ha⟩ := (splitComponentStatement k L hcentral.1).1
  obtain ⟨_, f, hf, _, _, hfimage, _⟩ := hcentral.2 A a ha
  have hft : CommGroupScheme.groupHom f ≫ t = a := by
    apply (cancel_mono j).mp
    rw [Category.assoc, ht, hf]
  have hsurj := (renardLeviCentralDecomposition k L L (𝟙 L) hcentral.1 hcentral.1 A A
    a a (𝟙 A) ha ha (by change (𝟙 A.toGrp) ≫ a ≫ 𝟙 L = a; simp)).1.surjective
  have hcomp : (rationalCharacterRestrictReal (CommGroupScheme.groupHom f)).comp
      (rationalCharacterRestrictReal t) = rationalCharacterRestrictReal a := by
    rw [← hft]
    apply AlgebraTensorModule.ext
    intro r χ
    change r ⊗ₜ[ℤ] characterRestrict (CommGroupScheme.groupHom f) (characterRestrict t χ) =
      r ⊗ₜ[ℤ] characterRestrict (CommGroupScheme.groupHom f ≫ t) χ
    rw [characterRestrict_comp, AddMonoidHom.comp_apply]
  have hker := ker_restrictReal_eq_rootSpan_of_range ha.1.1.1 hi.isSplitSubtorus.1 f J hfimage
  have hcompl := ((standardLeviRealDecomposition k G hG T i hi ν hν D).2.2.2
    J J le_rfl hJ).1
  have hinj : Set.InjOn (rationalCharacterRestrictReal (CommGroupScheme.groupHom f))
      (corootAnnihilator i D J : Set (Vstar T)) := by
    apply LinearMap.injOn_of_disjoint_ker subset_rfl
    rw [hker]
    exact hcompl.disjoint
  refine le_antisymm hrange ?_
  intro x hx
  obtain ⟨y, hy⟩ := hsurj (rationalCharacterRestrictReal (CommGroupScheme.groupHom f) x)
  have hres : rationalCharacterRestrictReal (CommGroupScheme.groupHom f)
      (rationalCharacterRestrictReal t y) =
        rationalCharacterRestrictReal (CommGroupScheme.groupHom f) x :=
    (LinearMap.congr_fun hcomp y).trans hy
  exact ⟨y, hinj (hrange ⟨y, rfl⟩) hx hres⟩

end Langlands.GroupScheme
