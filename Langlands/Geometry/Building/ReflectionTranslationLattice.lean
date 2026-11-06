import Langlands.Geometry.Building.ActualAffineRootLocalFiniteness
import Langlands.Geometry.Building.NormalizerApartmentActionKernel
import Langlands.GroupScheme.Rational.RootGeneratedWeylRepresentatives

/-! # Actual centralizer translations realized by reflection products -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building.ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (B : ValuationBuildingData G)

/-- The actual centralizer translation, projected to the reduced apartment. -/
def reducedCentralizerTranslation :
    rationalPoints B.centralizer.Z →* Multiplicative (TranslationSpace B.i) :=
  ((rootAnnihilator B.i).mkQ.toAddMonoidHom.toMultiplicative).comp
    B.centralizer.translation

@[simp]
theorem reducedCentralizerTranslation_apply (z : rationalPoints B.centralizer.Z) :
    (B.reducedCentralizerTranslation z).toAdd =
      (Submodule.Quotient.mk (B.centralizer.translation z).toAdd : TranslationSpace B.i) :=
  rfl

/-- Every reduced translation supplied by an actual centralizer point. -/
def centralizerTranslationLattice : AddSubgroup (TranslationSpace B.i) :=
  B.reducedCentralizerTranslation.range.toAddSubgroup'

/-- Translations supplied by centralizer points that are products of actual
opposite-pair reflection representatives. -/
def reflectionTranslationLattice : AddSubgroup (TranslationSpace B.i) :=
  ((B.reflectionNormalizer.comap B.centralizer.toNormalizer).map
    B.reducedCentralizerTranslation).toAddSubgroup'

theorem mem_reflectionTranslationLattice_iff (v : TranslationSpace B.i) :
    v ∈ B.reflectionTranslationLattice ↔
      ∃ z : rationalPoints B.centralizer.Z,
        B.centralizer.toNormalizer z ∈ B.reflectionNormalizer ∧
          (B.reducedCentralizerTranslation z).toAdd = v := by
  rfl

theorem reflectionTranslationLattice_le_centralizerTranslationLattice :
    B.reflectionTranslationLattice ≤ B.centralizerTranslationLattice := by
  rintro v ⟨z, _, hz⟩
  exact ⟨z, hz⟩

/-- Equality of reduced translations is exactly equality of the actual
centralizer actions on the supplied apartment. -/
theorem reducedCentralizerTranslation_eq_iff
    (z w : rationalPoints B.centralizer.Z) :
    B.reducedCentralizerTranslation z = B.reducedCentralizerTranslation w ↔
      B.apartment.normalizerAffineEquiv (B.centralizer.toNormalizer z) =
        B.apartment.normalizerAffineEquiv (B.centralizer.toNormalizer w) := by
  constructor
  · intro h
    apply AffineEquiv.ext
    intro x
    change B.centralizer.toNormalizer z • x = B.centralizer.toNormalizer w • x
    rw [B.isOmegaCompatible.smul_eq_vadd, B.isOmegaCompatible.smul_eq_vadd]
    exact congrArg (fun v : TranslationSpace B.i => v +ᵥ x)
      (congrArg Multiplicative.toAdd h)
  · intro h
    let x : B.Apartment := Classical.arbitrary _
    have hx := congrArg (fun e : B.Apartment ≃ᵃ[ℝ] B.Apartment => e x) h
    change B.centralizer.toNormalizer z • x = B.centralizer.toNormalizer w • x at hx
    rw [B.isOmegaCompatible.smul_eq_vadd, B.isOmegaCompatible.smul_eq_vadd] at hx
    exact congrArg Multiplicative.ofAdd ((vadd_right_cancel_iff x).mp hx)

/-- A represented centralizer point with trivial apartment action has zero
reduced translation. -/
theorem reducedCentralizerTranslation_eq_one_iff (z : rationalPoints B.centralizer.Z) :
    B.reducedCentralizerTranslation z = 1 ↔
      B.apartment.normalizerAffineEquiv (B.centralizer.toNormalizer z) = 1 := by
  simpa only [map_one] using B.reducedCentralizerTranslation_eq_iff z 1

/-- The centralizer inclusion represents every actual centralizer point of
the normalizer. -/
theorem exists_centralizer_lift (n : normalizerPoints B.i)
    (hn : n.val ∈ centralizerPoints B.i) :
    ∃ z : rationalPoints B.centralizer.Z, B.centralizer.toNormalizer z = n := by
  rw [← torusCentralizer_carrier_base, ← B.centralizer.isRepresentedBy.2] at hn
  obtain ⟨z, hz⟩ := hn
  exact ⟨z, Subtype.ext hz⟩

/-- A centralizer point acts through reflection products precisely when its
reduced translation is realized by a centralizing reflection product. -/
theorem centralizer_mem_reflections_sup_ker_iff
    (z : rationalPoints B.centralizer.Z) :
    B.centralizer.toNormalizer z ∈
        B.reflectionNormalizer ⊔ B.apartment.normalizerAffineEquiv.ker ↔
      (B.reducedCentralizerTranslation z).toAdd ∈ B.reflectionTranslationLattice := by
  constructor
  · intro hz
    obtain ⟨r, hr, k, hk, heq⟩ := Subgroup.mem_sup_of_normal_right.mp hz
    have hkC := B.mem_centralizerPoints_of_normalizerAffineEquiv_eq_one k hk
    have hrC : r.val ∈ centralizerPoints B.i := by
      have he : r = B.centralizer.toNormalizer z * k⁻¹ := by
        rw [← heq]
        group
      rw [he, Subgroup.coe_mul, Subgroup.coe_inv]
      exact (centralizerPoints B.i).mul_mem
        (map_mem_centralizerPoints B.centralizer.isRepresentedBy z)
        ((centralizerPoints B.i).inv_mem hkC)
    obtain ⟨w, hw⟩ := B.exists_centralizer_lift r hrC
    apply (B.mem_reflectionTranslationLattice_iff _).mpr
    refine ⟨w, hw.symm ▸ hr, ?_⟩
    apply congrArg Multiplicative.toAdd
    apply (B.reducedCentralizerTranslation_eq_iff w z).mpr
    rw [hw, ← heq, map_mul, MonoidHom.mem_ker.mp hk, mul_one]
  · intro hz
    obtain ⟨w, hw, he⟩ := (B.mem_reflectionTranslationLattice_iff _).mp hz
    have heA := (B.reducedCentralizerTranslation_eq_iff w z).mp
      (congrArg Multiplicative.ofAdd he)
    have hk : (B.centralizer.toNormalizer w)⁻¹ * B.centralizer.toNormalizer z ∈
        B.apartment.normalizerAffineEquiv.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, heA, inv_mul_cancel]
    have hmem := Subgroup.mul_mem_sup hw hk
    simpa only [mul_inv_cancel_left] using hmem

variable {a : relativeRoots B.i} {g₀ g : rationalPoints G}
    {p₀ p : rationalPoints G × rationalPoints G}

/-- The complete translation vector of a same-root correction is the root-value
difference times the actual reduced coroot. -/
theorem exists_translation_eq_rootValueDifference_smul_coroot
    (hg₀ : g₀ ∈ B.rootGroup a) (hg₀1 : g₀ ≠ 1)
    (hg : g ∈ B.rootGroup a) (hg1 : g ≠ 1)
    (hp₀ : RelativeRoot.IsOppositeFactorPair B.i (a : characterLattice B.S) g₀ p₀)
    (hp : RelativeRoot.IsOppositeFactorPair B.i (a : characterLattice B.S) g p)
    (x : B.Apartment) :
    ∃ z : rationalPoints B.centralizer.Z,
      B.centralizer.toNormalizer z = (B.reflectionElement hp₀)⁻¹ * B.reflectionElement hp ∧
        (B.reducedCentralizerTranslation z).toAdd =
          (B.reflectionFunctional a g x - B.reflectionFunctional a g₀ x) •
            B.reflectionCoroot hg₀ hg₀1 hp₀ := by
  obtain ⟨z, hz⟩ := B.exists_centralizer_reflection_correction hg₀ hg₀1 hg hg1 hp₀ hp
  refine ⟨z, hz, ?_⟩
  have hc : B.reflectionCoroot hg hg1 hp = B.reflectionCoroot hg₀ hg₀1 hp₀ := by
    unfold reflectionCoroot
    rw [B.reflectionPair_coroot_eq hg hg1 hg₀ hg₀1 hp hp₀]
  have hinv : B.apartment.normalizerAffineEquiv (B.reflectionElement hp₀)⁻¹ =
      B.apartment.normalizerAffineEquiv (B.reflectionElement hp₀) := by
    rw [map_inv, B.normalizerAffineEquiv_reflectionElement hg₀ hg₀1 hp₀]
    exact inv_eq_of_mul_eq_one_left (AffineRootSystem.affineReflection_mul_self _ _)
  have he := B.isOmegaCompatible.smul_eq_vadd z x
  rw [hz, mul_smul] at he
  change B.apartment.normalizerAffineEquiv (B.reflectionElement hp₀)⁻¹
    (B.apartment.normalizerAffineEquiv (B.reflectionElement hp) x) = _ at he
  rw [hinv, B.normalizerAffineEquiv_reflectionElement hg₀ hg₀1 hp₀,
    B.normalizerAffineEquiv_reflectionElement hg hg1 hp] at he
  change (-B.reflectionFunctional a g₀
      ((-B.reflectionFunctional a g x) • B.reflectionCoroot hg hg1 hp +ᵥ x)) •
        B.reflectionCoroot hg₀ hg₀1 hp₀ +ᵥ
      ((-B.reflectionFunctional a g x) • B.reflectionCoroot hg hg1 hp +ᵥ x) = _ at he
  rw [AffineMap.map_vadd, reflectionFunctional_linear, map_smul,
    B.rootForm_reflectionCoroot hg hg1 hp, smul_eq_mul, vadd_eq_add,
    hc, vadd_vadd, ← add_smul] at he
  have hs : -( (-B.reflectionFunctional a g x) * 2 + B.reflectionFunctional a g₀ x) +
      -B.reflectionFunctional a g x =
      B.reflectionFunctional a g x - B.reflectionFunctional a g₀ x := by ring
  rw [hs] at he
  exact ((vadd_right_cancel_iff x).mp he).symm

/-- Every same-root root-value difference times its actual coroot belongs to
the realized reflection translation lattice. -/
theorem rootValueDifference_smul_coroot_mem_reflectionTranslationLattice
    (hg₀ : g₀ ∈ B.rootGroup a) (hg₀1 : g₀ ≠ 1)
    (hg : g ∈ B.rootGroup a) (hg1 : g ≠ 1)
    (hp₀ : RelativeRoot.IsOppositeFactorPair B.i (a : characterLattice B.S) g₀ p₀)
    (hp : RelativeRoot.IsOppositeFactorPair B.i (a : characterLattice B.S) g p)
    (x : B.Apartment) :
    (B.reflectionFunctional a g x - B.reflectionFunctional a g₀ x) •
      B.reflectionCoroot hg₀ hg₀1 hp₀ ∈ B.reflectionTranslationLattice := by
  obtain ⟨z, hz, he⟩ :=
    B.exists_translation_eq_rootValueDifference_smul_coroot hg₀ hg₀1 hg hg1 hp₀ hp x
  apply (B.mem_reflectionTranslationLattice_iff _).mpr
  refine ⟨z, ?_, he⟩
  rw [hz]
  exact B.reflectionNormalizer.mul_mem
    (B.reflectionNormalizer.inv_mem
      (B.reflectionElement_mem_reflectionNormalizer hg₀ hg₀1 hp₀))
    (B.reflectionElement_mem_reflectionNormalizer hg hg1 hp)

/-- The actual finite relative-Weyl projection restricted to reflection products. -/
def reflectionRelativeWeylMap : B.reflectionNormalizer →* relativeWeylGroup B.i :=
  (QuotientGroup.mk' ((centralizerPoints B.i).subgroupOf (normalizerPoints B.i))).comp
    B.reflectionNormalizer.subtype

/-- Opposite pairs and an actual relative-root-system realization ensure that
reflection products supply every finite relative-Weyl class. -/
theorem reflectionRelativeWeylMap_surjective
    (hF : RelativeRoot.HasOppositeFactorPairs B.i)
    (hroot : HasRelativeRootSystem B.i) :
    Function.Surjective B.reflectionRelativeWeylMap := by
  have : Smooth G.X.hom := B.isConnectedReductive.smooth
  let hT := B.isMaximalSplitTorus.isSplitSubtorus.1
  have hex : ∀ a : relativeRoots B.i, ∃ n : normalizerPoints B.i,
      n ∈ B.reflectionNormalizer ∧ weylAction B.i n a.val = -a.val ∧
        n.val ∈ (RelativeRoot.kernelCentralizer B.i a.val).carrier (Over.mk (𝟙 _)) := by
    intro a
    obtain ⟨g, hg, hg1⟩ := RelativeRoot.exists_rootPoint_actual hT B.i a.property
    obtain ⟨p, hp⟩ := hF a.val a.property g hg hg1
    exact ⟨B.reflectionElement hp, B.reflectionElement_mem_reflectionNormalizer hg hg1 hp,
      hp.weylAction_eq_neg B.i hT a.property.1 hg hg1,
      hp.mem_kernelCentralizer B.i hg⟩
  choose n hn hflip hc using hex
  let D := RelativeRootReflectionData.ofKernelCentralizingRepresentatives B.i hT n hflip hc
  have hgen := D.closure_representatives_eq_top hT
    (hroot.finite_relativeRoots B.i hT) hroot
  apply MonoidHom.range_eq_top.mp
  apply top_unique
  rw [← hgen, Subgroup.closure_le]
  rintro _ ⟨a, rfl⟩
  exact ⟨⟨n a, hn a⟩, rfl⟩

/-- Finite relative-Weyl surjectivity is exactly enough to factor each normalizer
point as a reflection product followed by an actual centralizer point. -/
theorem exists_reflection_mul_centralizer
    (hW : Function.Surjective B.reflectionRelativeWeylMap)
    (n : normalizerPoints B.i) :
    ∃ r ∈ B.reflectionNormalizer, ∃ z : rationalPoints B.centralizer.Z,
      n = r * B.centralizer.toNormalizer z := by
  obtain ⟨r, hr⟩ := hW (QuotientGroup.mk n)
  change (QuotientGroup.mk r.val : relativeWeylGroup B.i) = QuotientGroup.mk n at hr
  have hcN : r.val⁻¹ * n ∈
      (centralizerPoints B.i).subgroupOf (normalizerPoints B.i) :=
    QuotientGroup.eq.mp hr
  have hc : (r.val⁻¹ * n).val ∈ centralizerPoints B.i := hcN
  obtain ⟨z, hz⟩ := B.exists_centralizer_lift (r.val⁻¹ * n) hc
  exact ⟨r.val, r.property, z, by rw [hz, mul_inv_cancel_left]⟩

/-- Once all finite relative-Weyl classes are realized, full normalizer
generation modulo the action kernel is equivalent to equality of the actual
translation lattices. -/
theorem reflections_sup_ker_eq_top_iff_translationLattice_eq
    (hW : Function.Surjective B.reflectionRelativeWeylMap) :
    B.reflectionNormalizer ⊔ B.apartment.normalizerAffineEquiv.ker = ⊤ ↔
      B.reflectionTranslationLattice = B.centralizerTranslationLattice := by
  constructor
  · intro h
    apply le_antisymm B.reflectionTranslationLattice_le_centralizerTranslationLattice
    rintro v ⟨z, hz⟩
    have hz' : (B.reducedCentralizerTranslation z).toAdd = v :=
      congrArg Multiplicative.toAdd hz
    rw [← hz']
    apply (B.centralizer_mem_reflections_sup_ker_iff z).mp
    rw [h]
    trivial
  · intro h
    apply top_unique
    intro n _
    obtain ⟨r, hr, z, rfl⟩ := B.exists_reflection_mul_centralizer hW n
    apply (B.reflectionNormalizer ⊔ B.apartment.normalizerAffineEquiv.ker).mul_mem
      (Subgroup.mem_sup_left hr)
    apply (B.centralizer_mem_reflections_sup_ker_iff z).mpr
    rw [h]
    exact ⟨z, rfl⟩

/-- The finite relative-Weyl premise of the lattice criterion follows from
actual opposite pairs and the full actual relative-root-system predicate. -/
theorem reflections_sup_ker_eq_top_iff_translationLattice_eq_of_oppositePairs
    (hF : RelativeRoot.HasOppositeFactorPairs B.i)
    (hroot : HasRelativeRootSystem B.i) :
    B.reflectionNormalizer ⊔ B.apartment.normalizerAffineEquiv.ker = ⊤ ↔
      B.reflectionTranslationLattice = B.centralizerTranslationLattice :=
  B.reflections_sup_ker_eq_top_iff_translationLattice_eq
    (B.reflectionRelativeWeylMap_surjective hF hroot)

/-- Equality of the actual translation lattices completes the facet-fixing
reduction once opposite pairs and finite relative-Weyl surjectivity are supplied. -/
theorem normalizer_facet_fixing_of_translationLattice_eq
    (hF : RelativeRoot.HasOppositeFactorPairs B.i)
    (hW : Function.Surjective B.reflectionRelativeWeylMap)
    (hL : B.reflectionTranslationLattice = B.centralizerTranslationLattice)
    {Fa : Set B.Apartment} (hFa : AffineRootSystem.IsFacet B.affineRoots Fa)
    (n : normalizerPoints B.i)
    (hfix : (fun x : B.Apartment => n • x) '' Fa = Fa) :
    ∀ x ∈ Fa, n • x = x := by
  apply B.normalizer_facet_fixing_of_reflections_sup_ker_of_oppositePairs hF hFa n
  · rw [(B.reflections_sup_ker_eq_top_iff_translationLattice_eq hW).mpr hL]
    trivial
  · exact hfix

end Langlands.Geometry.Building.ValuationBuildingData
