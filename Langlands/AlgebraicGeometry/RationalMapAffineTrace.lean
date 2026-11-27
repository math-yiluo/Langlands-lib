import Langlands.AlgebraicGeometry.FactorialAffineExtension
import Langlands.AlgebraicGeometry.ConnectedLocallyNoetherianDomainStalksIntegralProof

/-! # Detecting affine extension along a morphism at a factorial stalk -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Topology

namespace Langlands.AlgebraicGeometry

open FactorialAffineExtension

set_option backward.isDefEq.respectTransparency false

private theorem mem_domain_of_overlap {Y Z : Scheme.{u}} (r : Y.PartialMap Z)
    (W : Y.Opens) {y : Y} (hy : y ∈ W) (b : W.toScheme ⟶ Z)
    (h : Y.homOfLE (inf_le_left : r.domain ⊓ W ≤ r.domain) ≫ r.hom =
      Y.homOfLE (inf_le_right : r.domain ⊓ W ≤ W) ≫ b) :
    y ∈ r.toRationalMap.domain := by
  let O : Bool → Y.Opens := fun t => cond t r.domain W
  let D := Scheme.Opens.iSupOpenCover O
  let g : ∀ t, D.X t ⟶ Z := fun t => Bool.rec (motive := fun t => (O t).toScheme ⟶ Z) b r.hom t
  have h' (i j : Bool) : Y.homOfLE (inf_le_left : O i ⊓ O j ≤ O i) ≫ g i =
      Y.homOfLE (inf_le_right : O i ⊓ O j ≤ O j) ≫ g j := by
    cases i <;> cases j
    · rfl
    · let e := Y.isoOfEq (inf_comm W r.domain)
      have hb : e.inv ≫ Y.homOfLE (inf_le_left : W ⊓ r.domain ≤ W) =
          Y.homOfLE (inf_le_right : r.domain ⊓ W ≤ W) := by
        rw [← cancel_mono W.ι, Category.assoc, Scheme.homOfLE_ι, Scheme.homOfLE_ι]
        simp [e]
      have ha : e.inv ≫ Y.homOfLE (inf_le_right : W ⊓ r.domain ≤ r.domain) =
          Y.homOfLE (inf_le_left : r.domain ⊓ W ≤ r.domain) := by
        rw [← cancel_mono r.domain.ι, Category.assoc, Scheme.homOfLE_ι, Scheme.homOfLE_ι]
        simp [e]
      change Y.homOfLE (inf_le_left : W ⊓ r.domain ≤ W) ≫ b =
        Y.homOfLE (inf_le_right : W ⊓ r.domain ≤ r.domain) ≫ r.hom
      apply (cancel_epi e.inv).mp
      rw [← Category.assoc, ← Category.assoc, hb, ha]
      exact h.symm
    · exact h
    · rfl
  have hglue : ∀ i j, pullback.fst (D.f i) (D.f j) ≫ g i = pullback.snd _ _ ≫ g j := by
    intro i j
    let P := isPullback_opens_inf_le (le_iSup O i) (le_iSup O j)
    change pullback.fst (Y.homOfLE (le_iSup O i)) (Y.homOfLE (le_iSup O j)) ≫ g i =
      pullback.snd _ _ ≫ g j
    apply (cancel_epi P.isoPullback.hom).mp
    rw [IsPullback.isoPullback_hom_fst_assoc, IsPullback.isoPullback_hom_snd_assoc]
    exact h' i j
  let v : Y.PartialMap Z := ⟨_, r.dense_domain.mono (le_iSup O true), D.glueMorphisms g hglue⟩
  have hv : v.toRationalMap = r.toRationalMap := by
    apply Scheme.PartialMap.toRationalMap_eq_iff.mpr
    exact ⟨r.domain, r.dense_domain, le_iSup O true, le_rfl, by
      change D.f true ≫ D.glueMorphisms g hglue = Y.homOfLE (le_rfl : r.domain ≤ r.domain) ≫ r.hom
      rw [Scheme.homOfLE_rfl, Category.id_comp]
      exact D.ι_glueMorphisms g hglue true⟩
  exact hv ▸ v.le_domain_toRationalMap (le_iSup O false hy)

/-- A local representative agreeing on the overlap is the restriction of the maximal
representative on a reduced source with separated target. -/
theorem rationalMap_extends_of_overlap {Y Z : Scheme.{u}} [IsReduced Y] [Z.IsSeparated]
    (r : Y.PartialMap Z) (W : Y.Opens) (b : W.toScheme ⟶ Z)
    (h : Y.homOfLE (inf_le_left : r.domain ⊓ W ≤ r.domain) ≫ r.hom =
      Y.homOfLE (inf_le_right : r.domain ⊓ W ≤ W) ≫ b) :
    ∃ hW : W ≤ r.toRationalMap.domain,
      Y.homOfLE hW ≫ r.toRationalMap.toPartialMap.hom = b := by
  have hW : W ≤ r.toRationalMap.domain := fun _ hy => mem_domain_of_overlap r W hy b h
  let r' := r.toRationalMap.toPartialMap
  have hrr : Y.homOfLE r.le_domain_toRationalMap ≫ r'.hom = r.hom :=
    r.toPartialMap_toRationalMap_restrict
  refine ⟨hW, ?_⟩
  let j := Y.homOfLE (inf_le_right : r.domain ⊓ W ≤ W)
  have : IsDominant j := by
    constructor
    change Dense (Set.range j)
    rw [← Scheme.Hom.coe_opensRange, Scheme.opensRange_homOfLE]
    have hEq : (W.ι ⁻¹ᵁ (r.domain ⊓ W) : W.toScheme.Opens) = W.ι ⁻¹ᵁ r.domain := by
      ext z
      exact ⟨fun hz => hz.1, fun hz => ⟨hz, z.2⟩⟩
    rw [hEq]
    exact r.dense_domain.preimage W.ι.isOpenEmbedding.isOpenMap
  apply AlgebraicGeometry.ext_of_isDominant j
  rw [← h, ← hrr, ← Category.assoc, ← Category.assoc,
    Scheme.homOfLE_homOfLE, Scheme.homOfLE_homOfLE]

/-- Let `a : X ⟶ Y`. Suppose a partial map on `Y` is defined at the images of the generic and
principal prime points of `Spec 𝒪_{X,x}`, with values in a single affine open of the target.
If the two stalks at `x` and `a x` are factorial, the partial map extends at `a x`. -/
theorem rationalMap_mem_domain_of_affineTrace {S X Y Z : Scheme.{u}}
    [S.IsSeparated] [IsLocallyNoetherian Y] [IsReduced Y] [Z.IsSeparated]
    (pY : Y ⟶ S) (pZ : Z ⟶ S) [LocallyOfFiniteType pZ]
    (r : Y.PartialMap Z) (hr : r.hom ≫ pZ = r.domain.ι ≫ pY)
    (a : X ⟶ Y) (x : X) [IsDomain (X.presheaf.stalk x)]
    [UniqueFactorizationMonoid (X.presheaf.stalk x)] [IsDomain (Y.presheaf.stalk (a x))]
    [UniqueFactorizationMonoid (Y.presheaf.stalk (a x))]
    (H : Z.Opens) (hH : IsAffineOpen H)
    (htrace : ∀ p : PrimeSpectrum (X.presheaf.stalk x), IsGenericOrPrimeElement p →
      ∃ h : a (X.fromSpecStalk x p) ∈ r.domain,
        r.hom ⟨a (X.fromSpecStalk x p), h⟩ ∈ H) :
    a x ∈ r.toRationalMap.domain := by
  let y := a x
  let V₀ := r.hom ⁻¹ᵁ H
  let V := r.domain.ι ''ᵁ V₀
  have hVU : V ≤ r.domain := r.domain.ι_image_le V₀
  let c : V.toScheme ⟶ H.toScheme := (r.domain.ι.isoImage V₀).inv ≫ r.hom ∣_ H
  have hc : c ≫ H.ι = Y.homOfLE hVU ≫ r.hom := by
    dsimp only [c]
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc]
    rw [Scheme.Opens.isoImage_ι_inv_ι]
  let D := Y.fromSpecStalk y ⁻¹ᵁ V
  have hD : ∀ p : PrimeSpectrum (Y.presheaf.stalk y), IsGenericOrPrimeElement p → p ∈ D := by
    apply contains_primes_of_localMap (a.stalkMap x)
    intro p hp
    change Y.fromSpecStalk y (Spec.map (a.stalkMap x) p) ∈ V
    rw [← Scheme.Hom.comp_apply, Scheme.SpecMap_stalkMap_fromSpecStalk,
      Scheme.Hom.comp_apply]
    obtain ⟨h, hh⟩ := htrace p hp
    exact ⟨⟨_, h⟩, hh, rfl⟩
  have : IsAffine H.toScheme := hH
  obtain ⟨φ, hφ⟩ := exists_extension D hD ((Y.fromSpecStalk y ∣_ V) ≫ c)
  let b := φ ≫ H.ι
  have hb : D.ι ≫ b = (Y.fromSpecStalk y ∣_ V) ≫ Y.homOfLE hVU ≫ r.hom := by
    rw [← Category.assoc, hφ, Category.assoc, hc]
  have hgen : (⊥ : PrimeSpectrum (Y.presheaf.stalk y)) ∈ D := hD ⊥ (Or.inl rfl)
  have hbS : b ≫ pZ = Y.fromSpecStalk y ≫ pY := by
    have : IsDominant D.ι := Opens.isDominant_ι (X := Spec (Y.presheaf.stalk y))
      (by apply D.isOpen.dense; exact ⟨_, hgen⟩)
    apply AlgebraicGeometry.ext_of_isDominant D.ι
    rw [← Category.assoc, hb, Category.assoc, Category.assoc, hr, Scheme.homOfLE_ι_assoc,
      morphismRestrict_ι_assoc]
  obtain ⟨W₀, hyW₀, g₀, hg₀, -⟩ := spread_out_of_isGermInjective' pY pZ b hbS
  obtain ⟨N, hyN, hirr⟩ := exists_irreducible_open Y y inferInstance inferInstance
  let W := W₀ ⊓ N
  have hyW : y ∈ W := ⟨hyW₀, hyN⟩
  let g := Y.homOfLE (inf_le_left : W ≤ W₀) ≫ g₀
  have hg : b = W.fromSpecStalkOfMem y hyW ≫ g := by
    rw [hg₀, ← Category.assoc]
    congr 1
    rw [← cancel_mono W₀.ι, Category.assoc, Scheme.homOfLE_ι,
      Scheme.Opens.fromSpecStalkOfMem_ι, Scheme.Opens.fromSpecStalkOfMem_ι]
  have : IrreducibleSpace N := (isIrreducible_iff_irreducibleSpace (s := (N : Set Y))).mp hirr
  have : IrreducibleSpace W := by
    let i := Y.homOfLE (inf_le_right : W ≤ N)
    have : Nonempty W := ⟨⟨y, hyW⟩⟩
    exact i.isOpenEmbedding.irreducibleSpace
  let η : Y := W.ι (genericPoint W.toScheme)
  have hηW : η ∈ W := (genericPoint W.toScheme).2
  have hηy : η ⤳ y := (genericPoint_specializes (α := W.toScheme) ⟨y, hyW⟩).map W.ι.continuous
  have hηV : η ∈ V := by
    let z := Y.fromSpecStalk y (⊥ : PrimeSpectrum (Y.presheaf.stalk y))
    have hzV : z ∈ V := hgen
    have hzy : z ⤳ y := by
      have hz : z ∈ Set.range (Y.fromSpecStalk y) := Set.mem_range_self _
      rwa [Scheme.range_fromSpecStalk] at hz
    have hzW := hzy.mem_open W.isOpen hyW
    exact ((genericPoint_specializes (α := W.toScheme) ⟨z, hzW⟩).map W.ι.continuous).mem_open
      V.isOpen hzV
  let I := r.domain ⊓ W
  have hηI : η ∈ I := ⟨hVU hηV, hηW⟩
  let j := I.fromSpecStalkOfMem η hηI
  have hj : IsDominant j := by
    constructor
    intro z
    have hspec : (⟨η, hηI⟩ : I.toScheme) ⤳ z := by
      apply (Y.homOfLE (inf_le_right : I ≤ W)).isEmbedding.specializes_iff.mp
      have he : Y.homOfLE (inf_le_right : I ≤ W) (⟨η, hηI⟩ : I.toScheme) =
          genericPoint W.toScheme := by
        apply W.ι.isEmbedding.injective
        rw [← Scheme.Hom.comp_apply, Scheme.homOfLE_ι]
        rfl
      rw [he]
      exact genericPoint_specializes (α := W.toScheme) _
    apply closure_mono _ hspec.mem_closure
    rw [Set.singleton_subset_iff]
    refine ⟨IsLocalRing.closedPoint (Y.presheaf.stalk η), ?_⟩
    apply I.ι.isEmbedding.injective
    simp [← Scheme.Hom.comp_apply, j]
  have hglue : Y.homOfLE (inf_le_left : I ≤ r.domain) ≫ r.hom =
      Y.homOfLE (inf_le_right : I ≤ W) ≫ g := by
    apply AlgebraicGeometry.ext_of_isDominant j
    have hjU : j ≫ Y.homOfLE (inf_le_left : I ≤ r.domain) =
        r.domain.fromSpecStalkOfMem η (hVU hηV) := by
      simp [← cancel_mono r.domain.ι, j]
    have hjW : j ≫ Y.homOfLE (inf_le_right : I ≤ W) =
        Spec.map (Y.presheaf.stalkSpecializes hηy) ≫ W.fromSpecStalkOfMem y hyW := by
      simp [← cancel_mono W.ι, j, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    let k : Spec (Y.presheaf.stalk η) ⟶ D.toScheme := IsOpenImmersion.lift D.ι
      (Spec.map (Y.presheaf.stalkSpecializes hηy)) (by
        rintro _ ⟨z, rfl⟩
        rw [Scheme.Opens.range_ι]
        change Y.fromSpecStalk y (Spec.map (Y.presheaf.stalkSpecializes hηy) z) ∈ V
        rw [← Scheme.Hom.comp_apply, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
        have hz : Y.fromSpecStalk η z ∈ Set.range (Y.fromSpecStalk η) := Set.mem_range_self _
        rw [Scheme.range_fromSpecStalk] at hz
        exact hz.mem_open V.isOpen hηV)
    have hkfac : k ≫ D.ι = Spec.map (Y.presheaf.stalkSpecializes hηy) :=
      IsOpenImmersion.lift_fac _ _ _
    have hk : k ≫ (Y.fromSpecStalk y ∣_ V) ≫ Y.homOfLE hVU =
        r.domain.fromSpecStalkOfMem η (hVU hηV) := by
      rw [← cancel_mono r.domain.ι]
      simp only [Category.assoc, Scheme.homOfLE_ι, morphismRestrict_ι,
        Scheme.Opens.fromSpecStalkOfMem_ι]
      rw [← Category.assoc k, hkfac, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    rw [← Category.assoc j, hjU, ← Category.assoc j, hjW, Category.assoc, ← hg,
      ← hkfac, Category.assoc, hb]
    have e := congrArg (fun t => t ≫ r.hom) hk
    simpa only [Category.assoc] using e.symm
  exact mem_domain_of_overlap r W hyW g hglue

end Langlands.AlgebraicGeometry
