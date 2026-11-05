import Langlands.GroupScheme.Rational.ParabolicRootPresentationSimpleRoots
import Langlands.Representation.Plancherel.RenardUniformizerSection
import Langlands.Representation.Plancherel.SplitTorusRealPartLaws

/-! # Split-component lifts modulo the compact norm kernel -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.ParabolicRootPresentation

variable {k : Type u} [Field k]
  {A : CommGroupScheme (Spec (CommRingCat.of k))}
  {G M P : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (pres : ParabolicRootPresentation p l a)

/-- Every integral cocharacter annihilating the selected roots lifts through
the specified split component, including boundary directions. -/
theorem exists_cocharacter_lift_of_annihilates
    (c : cocharacterLattice pres.data.T)
    (hc : ∀ α ∈ pres.data.J, latticePairing pres.data.T α c = 0) :
    ∃ b : cocharacterLattice A, RealTorusSpace.cocharacterMapInt pres.data.f b = c := by
  have : IsAffineHom M.X.hom := pres.isCompatible.levi.isConnectedReductive.isAffineHom
  have hjc : IsClosedSubgroup (l ≫ p) :=
    pres.isCompatible.levi.isClosedSubgroup.comp pres.isCompatible.parabolic.isClosedSubgroup
  let := hjc.mono
  have : Mono (l ≫ p).hom.hom := Over.mono_of_mono_left _
  have hj : (standardLevi pres.data.i pres.data.ν pres.data.J).IsRepresentedBy (l ≫ p) :=
    ⟨inferInstance, pres.isCompatible.levi_eq⟩
  let t := standardLeviTorusFactor pres.data.i pres.data.ν pres.data.J hj
  have ht : t ≫ (l ≫ p) = pres.data.i :=
    standardLeviTorusFactor_comp pres.data.i pres.data.ν pres.data.J hj
  have htmax : IsMaximalSplitTorus t :=
    pres.isCompatible.maximalSplit.isMaximalSplitTorus_standardLeviTorusFactor
      pres.data.i pres.data.ν pres.data.J hj hjc
  have : Mono t.hom.hom.left := htmax.isSplitSubtorus.mono
  have hft : CommGroupScheme.groupHom pres.data.f ≫ t = a :=
    hj.hom_ext (by rw [Category.assoc, ht]; exact pres.isCompatible.factor_comp)
  have hcentral : c ∈ centralCocharacters t :=
    isCentral_standardLeviTorusFactor_of_annihilates pres.data.i pres.data.ν pres.data.J hj
      pres.finite_simpleRoots pres.exists_standardCocharacter c hc
  rw [← pres.isCompatible.splitComponent.range_cocharacterMapInt_eq_centralCocharacters
    pres.data.f hft] at hcentral
  exact hcentral

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/-- A torus point whose selected-root orders vanish has a split-component
uniformizer representative modulo the actual common norm kernel. -/
theorem exists_splitComponent_point_mod_normKernel
    (t : rationalPoints pres.data.T.toGrp)
    (ht : ∀ α ∈ pres.data.J,
      (Plancherel.rationalCharacterValuation pres.data.T.toGrp t).toAdd
        ((rationalCharacters.equivCharacterLattice pres.data.T).symm α) = 0) :
    ∃ b : cocharacterLattice A,
      t * (rationalPoints.map (CommGroupScheme.groupHom pres.data.f)
        (CocharacterUniformizer.latticeSection k A (.ofAdd b)))⁻¹ ∈
          Plancherel.rationalCommonNormKernel pres.data.T.toGrp := by
  obtain ⟨c, hc, _⟩ := (CocharacterUniformizer.isUniformizerLatticeSection k pres.data.T
    pres.isCompatible.maximalSplit.isSplitSubtorus.1).2.2 t
  have hval := (CocharacterUniformizer.mem_normKernel_mul_section_inv_iff
    k pres.data.T t c).mp hc
  obtain ⟨b, hb⟩ := pres.exists_cocharacter_lift_of_annihilates c.toAdd
    (fun α hα => (hval α).symm.trans (ht α hα))
  refine ⟨b, ?_⟩
  have heq : rationalPoints.map (CommGroupScheme.groupHom pres.data.f)
      (CocharacterUniformizer.latticeSection k A (.ofAdd b)) =
        CocharacterUniformizer.latticeSection k pres.data.T c := by
    change rationalPoints.map (CommGroupScheme.groupHom pres.data.f)
      (Plancherel.RenardCartan.uniformizerSection A (.ofAdd b)) =
        Plancherel.RenardCartan.uniformizerSection pres.data.T c
    rw [Plancherel.RenardCartan.uniformizerSection_naturality]
    exact congrArg (fun d : cocharacterLattice pres.data.T =>
      Plancherel.RenardCartan.uniformizerSection pres.data.T (.ofAdd d)) hb
  rw [heq]
  exact hc

/-- A chosen actual split-component point representing the ambient torus
point modulo the common norm kernel. -/
def splitComponentPointRepresentative
    (t : rationalPoints pres.data.T.toGrp)
    (ht : ∀ α ∈ pres.data.J,
      (Plancherel.rationalCharacterValuation pres.data.T.toGrp t).toAdd
        ((rationalCharacters.equivCharacterLattice pres.data.T).symm α) = 0) :
    rationalPoints A.toGrp :=
  CocharacterUniformizer.latticeSection k A
    (.ofAdd (pres.exists_splitComponent_point_mod_normKernel t ht).choose)

/-- The chosen representative has the required equality modulo the
actual ambient torus's compact norm kernel. -/
theorem splitComponentPointRepresentative_mod_normKernel
    (t : rationalPoints pres.data.T.toGrp)
    (ht : ∀ α ∈ pres.data.J,
      (Plancherel.rationalCharacterValuation pres.data.T.toGrp t).toAdd
        ((rationalCharacters.equivCharacterLattice pres.data.T).symm α) = 0) :
    t * (rationalPoints.map (CommGroupScheme.groupHom pres.data.f)
      (pres.splitComponentPointRepresentative t ht))⁻¹ ∈
        Plancherel.rationalCommonNormKernel pres.data.T.toGrp :=
  (pres.exists_splitComponent_point_mod_normKernel t ht).choose_spec

end Langlands.GroupScheme.ParabolicRootPresentation

namespace Langlands.Plancherel.SplitTorus

open GroupScheme Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))} [IsAffine T.X.left]

local instance liftTorusPointTopology : TopologicalSpace (rationalPoints T.toGrp) :=
  rationalPointTopology k T.X

/-- A smooth character of a closed subgroup of a split torus has norm one
on its intersection with the common norm kernel. -/
theorem norm_eq_one_of_closedSubgroup_mem_commonNormKernel
    (hT : IsSplitTorus T.toGrp)
    (H : Subgroup (rationalPoints T.toGrp)) (hH : IsClosed (H : Set (rationalPoints T.toGrp)))
    (χ : H →* ℂˣ) (hχ : IsOpen (χ.ker : Set H))
    (t : H) (ht : (t : rationalPoints T.toGrp) ∈ rationalCommonNormKernel T.toGrp) :
    ‖(χ t : ℂ)‖ = 1 := by
  let : Smooth T.X.hom := hT.smooth
  let : IsTopologicalGroup (rationalPoints T.toGrp) :=
    rationalPoint_isTopologicalGroup k T.toGrp
  let K := (rationalCommonNormKernel T.toGrp).subgroupOf H
  have hK : IsCompact (K : Set H) := by
    apply (Topology.IsEmbedding.isCompact_iff
      (f := fun t : H => (t : rationalPoints T.toGrp))
      Topology.IsEmbedding.subtypeVal).mpr
    have heq : Subtype.val '' (K : Set H) =
        (H : Set (rationalPoints T.toGrp)) ∩
          (rationalCommonNormKernel T.toGrp : Set (rationalPoints T.toGrp)) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y.property, hy⟩
      · rintro ⟨hxH, hxK⟩
        exact ⟨⟨x, hxH⟩, hxK, rfl⟩
    rw [heq, Set.inter_comm]
    exact (isCompact_commonNormKernel hT).inter_right hH
  exact norm_eq_one_on_compact_subgroup χ hχ K hK ht

/-- Smooth characters of any closed torus subgroup have equal moduli at
points differing by the compact common norm kernel. -/
theorem norm_eq_of_closedSubgroup_mul_inv_mem_commonNormKernel
    (hT : IsSplitTorus T.toGrp)
    (H : Subgroup (rationalPoints T.toGrp)) (hH : IsClosed (H : Set (rationalPoints T.toGrp)))
    (χ : H →* ℂˣ) (hχ : IsOpen (χ.ker : Set H))
    (s t : H)
    (hst : (s : rationalPoints T.toGrp) * (t : rationalPoints T.toGrp)⁻¹ ∈
      rationalCommonNormKernel T.toGrp) :
    ‖(χ s : ℂ)‖ = ‖(χ t : ℂ)‖ := by
  have hn := norm_eq_one_of_closedSubgroup_mem_commonNormKernel hT H hH χ hχ
    (s * t⁻¹) hst
  have hd : ‖(χ s : ℂ)‖ / ‖(χ t : ℂ)‖ = 1 := by
    simpa only [map_mul, map_inv, Units.val_mul, Units.val_inv_eq_inv_val, norm_mul,
      norm_inv, div_eq_mul_inv] using hn
  exact (div_eq_one_iff_eq (norm_ne_zero_iff.mpr (Units.ne_zero _))).mp hd

end Langlands.Plancherel.SplitTorus
