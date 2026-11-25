/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.Algebra.Homology.FlatTruncationTower
import WeilConjectures.Algebra.Homology.KFlatTelescopeClosure
import WeilConjectures.Algebra.Homology.FlatTruncationTelescopeComparison
import WeilConjectures.FromJoel.Algebra.Homology.Embedding.CochainComplex

/-!
# K-flat resolutions on a ringed site

Source: Stacks Project, Cohomology on Sites, Lemma 06YS
(`sites-cohomology-lemma-K-flat-resolution`) (blueprint: lem-pc-kflat-resolution).
-/

@[expose] public section

universe u

open CategoryTheory

namespace CochainComplex

private theorem flat_of_iso
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J CommRingCat.{u}}
    {X Y : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)}
    (e : X ≅ Y) (hY : SheafOfModules.IsFlat Y) : SheafOfModules.IsFlat X := by
  let := SheafOfModules.monoidalCategory R
  change exactFunctor _ _ (MonoidalCategory.tensorRight Y) at hY
  change exactFunctor _ _ (MonoidalCategory.tensorRight X)
  exact ObjectProperty.prop_of_iso _ ((MonoidalCategory.curriedTensor _).flip.mapIso e.symm) hY

private theorem flat_small_coproduct
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J CommRingCat.{u}} {I : Type}
    (M : I → SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R))
    (hM : ∀ j : I, SheafOfModules.IsFlat (M j)) [Countable I] :
    SheafOfModules.IsFlat (∐ M) := by
  have h := (kFlat_closure R).2.2.2.2 (ULift.{u} I)
    (fun j ↦ M j.down) (fun j ↦ hM j.down)
  exact flat_of_iso (Limits.Sigma.reindex (Equiv.ulift : ULift.{u} I ≃ I) M).symm h

private theorem flat_terms_mappingCone
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J CommRingCat.{u}}
    {F G : CochainComplex
      (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ}
    (φ : F ⟶ G) (hF : ∀ i : ℤ, SheafOfModules.IsFlat (F.X i))
    (hG : ∀ i : ℤ, SheafOfModules.IsFlat (G.X i))
    (i : ℤ) : SheafOfModules.IsFlat ((mappingCone φ).X i) := by
  let M : Limits.WalkingPair → SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R) :=
    fun j ↦ Limits.WalkingPair.casesOn j (F.X (i + 1)) (G.X i)
  have hM : ∀ j : Limits.WalkingPair, SheafOfModules.IsFlat (M j) := by
    intro j
    cases j
    · exact hF (i + 1)
    · exact hG i
  have hsum := flat_small_coproduct M hM
  exact flat_of_iso
    (HomologicalComplex.homotopyCofiber.XIsoBiprod φ i (i + 1) rfl ≪≫
      Limits.biprod.isoCoprod (F.X (i + 1)) (G.X i)) hsum

/-- Every complex of modules over a sheaf of commutative rings on a site admits a K-flat
resolution with flat terms and a degreewise surjective augmentation. Surjectivity is in the
category of sheaves of modules, i.e. an epimorphism, rather than surjectivity on all sections.
Source: Stacks Project, Lemma 06YS (blueprint: lem-pc-kflat-resolution).

Proof outline recorded in the blueprint:
1. Replace each good truncation of `G` by a bounded-above flat complex with a termwise
   surjective quasi-isomorphism, compatibly with the transition maps
   (`lem-pc-kflat-bounded-flat-replacement`).
2. Form the telescope, the cone of one minus the shift on the countable direct sum of these
   replacements. Bounded-above flat complexes, their sums and their cones are K-flat;
   their terms are flat (`lem-pc-kflat-closure`). The induced map to the telescope of the
   truncations is degreewise surjective. Its composite with the augmentation to `G` is
   degreewise surjective, since the truncations agree with `G` in each fixed degree eventually.
3. Direct sums of the replacement quasi-isomorphisms are quasi-isomorphisms, by exactness of
   filtered colimits of finite sums (`lem-pc-kflat-hocolim-truncations`). The long exact
   cohomology sequences of the cones and the five lemma give a quasi-isomorphism on
   telescopes. The telescope of truncations maps quasi-isomorphically to `G` by the same node.
4. The composite is the desired degreewise surjective quasi-isomorphism from a K-flat
   complex with flat terms. -/
theorem exists_isKFlatResolution
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J CommRingCat.{u}}
    (G : CochainComplex
      (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ) :
    ∃ (K : CochainComplex
      (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ)
      (f : K ⟶ G), K.IsKFlatTensor ∧ (∀ i : ℤ, SheafOfModules.IsFlat (K.X i)) ∧
        QuasiIso f ∧ (∀ i : ℤ, Epi (f.f i)) := by
  obtain ⟨E, t, q, hbounded, hflat, hq, hepi, hcompat⟩ := exists_flat_truncation_tower G
  let s : (∐ E) ⟶ G := Limits.Sigma.desc (fun n : ℕ ↦ q n ≫ G.ιTruncLE (n : ℤ))
  let φ : (∐ E) ⟶ (∐ E) :=
    𝟙 (∐ E) - Limits.Sigma.desc (fun n : ℕ ↦ t n ≫ Limits.Sigma.ι E (n + 1))
  have hzero : φ ≫ s = 0 := by
    dsimp [φ, s]
    rw [Preadditive.sub_comp, Category.id_comp]
    apply sub_eq_zero.mpr
    apply Limits.Sigma.hom_ext
    intro n
    simp only [Category.assoc, Limits.Sigma.ι_comp_desc_assoc, Limits.Sigma.ι_comp_desc]
    exact (hcompat n).symm
  have hdesc : HomComplex.δ (-1) 0 (0 : HomComplex.Cochain (∐ E) G (-1)) =
      HomComplex.Cochain.ofHom (φ ≫ s) := by
    rw [hzero]
    simp
  let f : mappingCone φ ⟶ G := mappingCone.desc φ 0 s hdesc
  have hinr : mappingCone.inr φ ≫ f = s := mappingCone.inr_desc φ 0 s hdesc
  have hinl : (mappingCone.inl φ).comp (HomComplex.Cochain.ofHom f) (add_zero _) = 0 :=
    mappingCone.inl_desc φ 0 s hdesc
  have hk : (mappingCone φ).IsKFlatTensor := by
    apply (kFlat_closure R).2.2.2.1 E t
    intro n
    exact (kFlat_closure R).1 (E n) (hbounded n) (hflat n)
  have hsum : ∀ i : ℤ, SheafOfModules.IsFlat ((∐ E).X i) := by
    intro i
    exact flat_of_iso
      (Limits.PreservesCoproduct.iso (HomologicalComplex.eval _ (ComplexShape.up ℤ) i) E)
      (flat_small_coproduct (fun n ↦ (E n).X i) (fun n ↦ hflat n i))
  refine ⟨mappingCone φ, f, hk, flat_terms_mappingCone φ hsum hsum, ?_, ?_⟩
  · exact quasiIso_flat_truncation_telescope G E t q hq hcompat f hinr hinl
  · intro i
    let n : ℕ := i.toNat + 1
    have hi : i < (n : ℤ) := by dsimp [n]; omega
    have : Epi ((q n).f i) := hepi n i
    have : IsIso ((G.ιTruncLE (n : ℤ)).f i) := G.isIso_ιTruncLE_f (n : ℤ) i hi
    have hcomp : (Limits.Sigma.ι E n).f i ≫ (mappingCone.inr φ).f i ≫ f.f i =
        (q n).f i ≫ (G.ιTruncLE (n : ℤ)).f i := by
      have h := congrArg (fun g ↦ g.f i)
        (show Limits.Sigma.ι E n ≫ mappingCone.inr φ ≫ f = q n ≫ G.ιTruncLE (n : ℤ) by
          rw [hinr]
          exact Limits.Sigma.ι_comp_desc _ _)
      exact h
    have : Epi (((Limits.Sigma.ι E n).f i ≫ (mappingCone.inr φ).f i) ≫ f.f i) := by
      rw [Category.assoc, hcomp]
      infer_instance
    exact epi_of_epi ((Limits.Sigma.ι E n).f i ≫ (mappingCone.inr φ).f i) (f.f i)

end CochainComplex
