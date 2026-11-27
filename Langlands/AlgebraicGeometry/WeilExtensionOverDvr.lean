import Langlands.AlgebraicGeometry.DenseDivisionComparison
import Langlands.AlgebraicGeometry.RationalMapAffineTrace
import Langlands.AlgebraicGeometry.SmoothDvrCodimensionOneOpen

/-! # Weil extension for a partial morphism defined on the generic fibre -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory Topology TopologicalSpace
open scoped CategoryTheory.MonObj

namespace Langlands.AlgebraicGeometry

open SmoothDvrCodimensionOneOpen

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

set_option maxHeartbeats 1000000 in
/-- Weil extension over a DVR for a morphism from a fibre-dense open containing the generic
fibre of a smooth scheme. -/
theorem weilExtensionOverDvr (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [Smooth f] [QuasiCompact f]
    (G : Langlands.GroupScheme (Spec (CommRingCat.of R))) [IsSeparated G.X.hom]
    [LocallyOfFiniteType G.X.hom]
    (U : X.Opens) (hU : FibreGenerizationDense f (U : Set X)) (hη : f ⁻¹ᵁ genericOpen R ≤ U)
    (u : U.toScheme ⟶ G.X.left) (hu : u ≫ G.X.hom = U.ι ≫ f) :
    ∃ τ : X ⟶ G.X.left, U.ι ≫ τ = u ∧ τ ≫ G.X.hom = f := by
  let A := Over.mk f
  let U₀ := Over.mk (U.ι ≫ f)
  let i : U₀ ⟶ A := Over.homMk U.ι rfl
  let u₀ : U₀ ⟶ G.X := Over.homMk u hu
  let P := pullback f f
  let p₁ := pullback.fst f f
  let p₂ := pullback.snd f f
  let p := p₁ ≫ f
  have : IsOpenImmersion i.left := inferInstanceAs (IsOpenImmersion U.ι)
  let k : (U₀ ⊗ U₀).left ⟶ P := (i ⊗ₘ i).left
  have : IsOpenImmersion k := MorphismProperty.pullbackMap (P := @IsOpenImmersion)
    ‹IsOpenImmersion i.left› ‹IsOpenImmersion i.left› i.w.symm i.w.symm
  let D := k.opensRange
  have hD (z : P) : z ∈ D ↔ p₁ z ∈ U ∧ p₂ z ∈ U := by
    constructor
    · rintro ⟨t, rfl⟩
      have e₁ : k ≫ p₁ = (fst U₀ U₀).left ≫ U.ι := congrArg Over.Hom.left (tensorHom_fst i i)
      have e₂ : k ≫ p₂ = (snd U₀ U₀).left ≫ U.ι := congrArg Over.Hom.left (tensorHom_snd i i)
      rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, e₁, e₂]
      exact ⟨((fst U₀ U₀).left t).2, ((snd U₀ U₀).left t).2⟩
    · rintro ⟨h₁, h₂⟩
      exact InvertibleTranslations.mem_range_tensorHom i i z ⟨⟨p₁ z, h₁⟩, rfl⟩
        ⟨⟨p₂ z, h₂⟩, rfl⟩
  have hdD : Dense (D : Set P) := by
    have hp₁ : Smooth p₁ := inferInstanceAs (Smooth (pullback.fst f f))
    have hp₂ : Smooth p₂ := inferInstanceAs (Smooth (pullback.snd f f))
    have h₁ : Dense ((p₁ ⁻¹ᵁ U : P.Opens) : Set P) := hU.dense.preimage p₁.isOpenMap
    have h₂ : Dense ((p₂ ⁻¹ᵁ U : P.Opens) : Set P) := hU.dense.preimage p₂.isOpenMap
    have hEq : (D : Set P) = (↑(p₁ ⁻¹ᵁ U) : Set P) ∩ (↑(p₂ ⁻¹ᵁ U) : Set P) := Set.ext hD
    rw [hEq]
    exact h₁.inter_of_isOpen_left h₂ (p₁ ⁻¹ᵁ U).isOpen
  let d : U₀ ⊗ U₀ ⟶ G.X := (fst U₀ U₀ ≫ u₀) * (snd U₀ U₀ ≫ u₀)⁻¹
  let r : P.PartialMap G.X.left := ⟨D, hdD, k.isoOpensRange.inv ≫ d.left⟩
  have hr : r.hom ≫ G.X.hom = D.ι ≫ p := by
    have hk : k.isoOpensRange.inv ≫ k = D.ι := by
      calc
        _ = k.isoOpensRange.inv ≫ k.isoOpensRange.hom ≫ D.ι :=
          congrArg (fun t => k.isoOpensRange.inv ≫ t) k.isoOpensRange_hom_ι.symm
        _ = D.ι := Iso.inv_hom_id_assoc _ _
    change (k.isoOpensRange.inv ≫ d.left) ≫ G.X.hom = _
    rw [Category.assoc, d.w, ← hk, Category.assoc]
    exact congrArg (fun s => k.isoOpensRange.inv ≫ s) (i ⊗ₘ i).w.symm
  have hkr : k.isoOpensRange.hom ≫ r.hom = d.left := by
    change k.isoOpensRange.hom ≫ k.isoOpensRange.inv ≫ d.left = _
    rw [Iso.hom_inv_id_assoc]
  have hp₁ : Smooth p₁ := inferInstanceAs (Smooth (pullback.fst f f))
  have hp : Smooth p := by dsimp [p]; infer_instance
  have : IsLocallyNoetherian P := LocallyOfFiniteType.isLocallyNoetherian p
  have : IsReduced P := SmoothReducedBase.isReduced_of_smooth_of_isReduced p
  have : G.X.left.IsSeparated := separatedScheme_of_separated_over G.X.hom
  let δ : A ⟶ A ⊗ A := lift (𝟙 A) (𝟙 A)
  let Δ : X ⟶ P := δ.left
  let δU : U₀ ⟶ U₀ ⊗ U₀ := lift (𝟙 U₀) (𝟙 U₀)
  have hδ₁ : Δ ≫ p₁ = 𝟙 X := congrArg Over.Hom.left (lift_fst (𝟙 A) (𝟙 A))
  have hδU : δU.left ≫ k = U.ι ≫ Δ := by
    have e : δU ≫ (i ⊗ₘ i) = i ≫ δ := by
      simp only [δU, δ, lift_map, comp_lift, Category.id_comp, Category.comp_id]
    exact congrArg Over.Hom.left e
  have hdiff : δU.left ≫ d.left = (U.ι ≫ f) ≫ η[G.X].left := by
    have e : δU ≫ d = toUnit U₀ ≫ η[G.X] := by
      rw [show d = (fst U₀ U₀ ≫ u₀) * (snd U₀ U₀ ≫ u₀)⁻¹ from rfl,
        MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, ← Category.assoc]
      simp only [δU, lift_fst, lift_snd, Category.id_comp, mul_inv_cancel, Hom.one_def]
    exact congrArg Over.Hom.left e
  have hΔ (x : X) : Δ x ∈ r.toRationalMap.domain := by
    obtain ⟨H, hH, hxH, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤)
      (x := η[G.X].left (f x)) (by trivial)
    let : IsDomain (X.presheaf.stalk x) := isDomain_stalk R f x
    let : UniqueFactorizationMonoid (X.presheaf.stalk x) := factorial_stalk R f x
    let : IsDomain (P.presheaf.stalk (Δ x)) := isDomain_stalk R p (Δ x)
    let : UniqueFactorizationMonoid (P.presheaf.stalk (Δ x)) := factorial_stalk R p (Δ x)
    apply rationalMap_mem_domain_of_affineTrace p G.X.hom r hr Δ x H hH
    intro z hz
    let y := X.fromSpecStalk x z
    have hy : y ∈ U := smallPrime_mem R f U hU hη x z hz
    let y₀ : U.toScheme := ⟨y, hy⟩
    have he : k (δU.left y₀) = Δ y := by
      rw [← Scheme.Hom.comp_apply, hδU, Scheme.Hom.comp_apply]
      rfl
    have hMem : Δ y ∈ r.domain := ⟨_, he⟩
    refine ⟨hMem, ?_⟩
    have hpoint : k.isoOpensRange.hom (δU.left y₀) = (⟨Δ y, hMem⟩ : D.toScheme) := by
      apply D.ι.isEmbedding.injective
      rw [← Scheme.Hom.comp_apply, Scheme.Hom.isoOpensRange_hom_ι, he]
      rfl
    rw [← hpoint, ← Scheme.Hom.comp_apply, hkr, ← Scheme.Hom.comp_apply, hdiff]
    have hyx : y ⤳ x := by
      have hf : y ∈ Set.range (X.fromSpecStalk x) := Set.mem_range_self z
      rwa [Scheme.range_fromSpecStalk] at hf
    exact (hyx.map (f ≫ η[G.X].left).continuous).mem_open H.isOpen hxH
  let v := r.toRationalMap.toPartialMap
  let M := r.toRationalMap.domain
  let jD : D.toScheme ⟶ M.toScheme := P.homOfLE r.le_domain_toRationalMap
  have hjD : jD ≫ M.ι = D.ι := P.homOfLE_ι _
  have hvD : jD ≫ v.hom = r.hom := r.toPartialMap_toRationalMap_restrict
  have hvS : v.hom ≫ G.X.hom = M.ι ≫ p := by
    have : IsDominant jD := Opens.isDominant_homOfLE hdD _
    apply AlgebraicGeometry.ext_of_isDominant jD
    rw [← Category.assoc jD v.hom, hvD, hr, ← Category.assoc jD M.ι, hjD]
  let V := p₂ ⁻¹ᵁ U
  let W := M ⊓ V
  let q := W.ι ≫ p₁
  have : Smooth q := by dsimp [q]; infer_instance
  have hV : FibreGenerizationDense p₁ (V : Set P) :=
    hU.preimage_of_isPullback (IsPullback.of_hasPullback f f).flip
  have : Surjective q := by
    constructor
    intro x
    obtain ⟨z, hz, hzx, hsp⟩ := hV (Δ x)
    refine ⟨⟨z, hsp.mem_open M.isOpen (hΔ x), hz⟩, ?_⟩
    have h := congrArg (fun g : X ⟶ X => g x) hδ₁
    exact hzx.trans h
  have : QuasiCompact p := by dsimp [p, p₁]; infer_instance
  have : CompactSpace P := QuasiCompact.compactSpace_of_compactSpace p
  have : IsNoetherian P := {}
  have : QuasiCompact q := by
    have : NoetherianSpace W.toScheme := W.ι.isEmbedding.isInducing.noetherianSpace
    infer_instance
  let c : W.toScheme ⟶ U.toScheme := P.homOfLE (inf_le_right : W ≤ V) ≫ p₂ ∣_ U
  have hc : c ≫ U.ι = W.ι ≫ p₂ := by
    dsimp only [c]
    rw [Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι_assoc]
  let W₀ := Over.mk (q ≫ f)
  let w : W₀ ⟶ A ⊗ A := Over.homMk W.ι rfl
  let c₀ : W₀ ⟶ U₀ := Over.homMk c (by
    change c ≫ U.ι ≫ f = q ≫ f
    rw [← Category.assoc, hc, Category.assoc, ← pullback.condition, ← Category.assoc])
  let t : W.toScheme ⟶ M.toScheme := P.homOfLE (inf_le_left : W ≤ M)
  have ht : t ≫ M.ι = W.ι := P.homOfLE_ι _
  let v₀ : W₀ ⟶ G.X := Over.homMk (t ≫ v.hom) (by
    change (t ≫ v.hom) ≫ G.X.hom = (W.ι ≫ p₁) ≫ f
    rw [Category.assoc, hvS, ← Category.assoc, ht, Category.assoc])
  let g : W₀ ⟶ G.X := v₀ * (c₀ ≫ u₀)
  have hcomp ⦃T : Scheme.{u}⦄ (a : T ⟶ W.toScheme) (b : T ⟶ U.toScheme)
      (h : a ≫ q = b ≫ U.ι) : a ≫ g.left = b ≫ u := by
    let T₀ := Over.mk (a ≫ (q ≫ f))
    let a₀ : T₀ ⟶ W₀ := Over.homMk a rfl
    let b₀ : T₀ ⟶ U₀ := Over.homMk b (by
      change b ≫ U.ι ≫ f = a ≫ q ≫ f
      rw [← Category.assoc, ← h, Category.assoc])
    let ab := lift b₀ (a₀ ≫ c₀)
    have hab : ab ≫ (i ⊗ₘ i) = a₀ ≫ w := by
      apply CartesianMonoidalCategory.hom_ext
      · apply Over.OverMorphism.ext
        simp only [ab, lift_map, lift_fst, Category.assoc]
        exact h.symm
      · apply Over.OverMorphism.ext
        simp only [ab, lift_map, lift_snd, Category.assoc]
        change a ≫ c ≫ U.ι = a ≫ W.ι ≫ p₂
        rw [hc]
    have hab' : ab.left ≫ k.isoOpensRange.hom ≫ jD = a ≫ t := by
      apply (cancel_mono M.ι).mp
      have hk : k.isoOpensRange.hom ≫ D.ι = k := k.isoOpensRange_hom_ι
      simp only [Category.assoc, hjD, ht, hk]
      exact congrArg Over.Hom.left hab
    have ha : a₀ ≫ v₀ = ab ≫ d := by
      apply Over.OverMorphism.ext
      change a ≫ t ≫ v.hom = ab.left ≫ d.left
      rw [← Category.assoc a, ← hab', Category.assoc, Category.assoc, hvD, hkr]
    have hh : a₀ ≫ g = b₀ ≫ u₀ := by
      rw [show g = v₀ * (c₀ ≫ u₀) from rfl, MonObj.comp_mul, ha]
      simp [d, ab, MonObj.comp_mul, GrpObj.comp_inv, Category.assoc]
    exact congrArg Over.Hom.left hh
  have : IsDominant U.ι := Opens.isDominant_ι hU.dense
  obtain ⟨τ, hτ, hτU⟩ := exists_hom_of_agrees_over_dense_open f q U.ι g.left u hcomp
  refine ⟨τ, hτU, ?_⟩
  apply (cancel_epi q).mp
  rw [← Category.assoc, hτ]
  exact g.w

end Langlands.AlgebraicGeometry
