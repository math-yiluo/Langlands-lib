import Langlands.Geometry.Building.UnramifiedFixedCentralizerAux
import Langlands.Geometry.Building.UnramifiedFixedLocusStatement
import Langlands.Geometry.Building.UnramifiedFixedNormalizerTransportReduction
import Langlands.Geometry.Building.UnramifiedApartmentDescentTorsor
import Langlands.Geometry.Building.CentralizerDatumBaseChange
import Langlands.Geometry.Building.KPZeroNormKernel
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.Rational.MaximalSplitTorusCentralizer
import Langlands.GroupScheme.Rational.TorusSplitPartTransfer
import Langlands.GroupScheme.Rational.RootGaloisOrbits
import Langlands.GroupScheme.Rational.CharacterBaseChange
import Langlands.GroupScheme.Rational.ScalarExtensionNaturality
import Langlands.GroupScheme.Torus.CentralizerSmoothProof

/-! # V 6 at Galois-fixed points from Levi transport -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.GaloisPointComparison
open Langlands.GroupScheme.RealTorusSpace
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

section Unramified

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

local notation "𝕂" => inertiaFixedField F
local notation "bF" => algebraBaseMap F (inertiaFixedField F)

private instance v6ReductionAffineHom {G : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffineHom G.X.hom] : IsAffineHom (baseChanged F 𝕂 G).X.hom := by
  change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom bF)
  infer_instance

private instance v6ReductionSmooth {G : GroupScheme (Spec (CommRingCat.of F))}
    [Smooth G.X.hom] : Smooth (baseChanged F 𝕂 G).X.hom := by
  change Smooth (CategoryTheory.Limits.pullback.snd G.X.hom bF)
  infer_instance

private instance v6ReductionLFT {G : GroupScheme (Spec (CommRingCat.of F))}
    [Smooth G.X.hom] : LocallyOfFiniteType (baseChanged F 𝕂 G).X.hom := by
  change LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd G.X.hom bF)
  infer_instance

set_option maxHeartbeats 8000000 in
/-- **The descended translation of `z ∈ Z(F)` is `ν(z)` on the roots.** -/
theorem eval_eq_centralizerTranslation_of_leviTransport
    {G : GroupScheme (Spec (CommRingCat.of F))} (hG : IsConnectedReductive G)
    [IsAffineHom G.X.hom] [Smooth G.X.hom]
    {S T : CommGroupScheme (Spec (CommRingCat.of F))} {iS : S.toGrp ⟶ G}
    (hiS : IsMaximalSplitTorus iS) [Mono iS.hom.hom.left] {iT : T.toGrp ⟶ G} {f : S ⟶ T}
    (hf : CommGroupScheme.groupHom f ≫ iT = iS)
    (hiT : IsMaximalSplitTorus (T := (CommGroupScheme.baseChange bF).obj T)
      ((GroupScheme.baseChange bF).map iT))
    [Mono ((GroupScheme.baseChange bF).map iT).hom.hom.left]
    (D : KPApartmentData (S := (CommGroupScheme.baseChange bF).obj T)
      ((GroupScheme.baseChange bF).map iT)
      (IntegerValuation.order (MaximalUnramified.valuation F)))
    (C : CentralizerDatum (S := (CommGroupScheme.baseChange bF).obj T)
      ((GroupScheme.baseChange bF).map iT))
    (hDC : IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C)
    (CS : CentralizerDatum iS) (z : rationalPoints CS.Z)
    {h : rationalPoints ((GroupScheme.baseChange bF).obj G)} (x : D.Apartment)
    (hlevi : h ∈ ⨆ (χ : characterLattice ((CommGroupScheme.baseChange bF).obj T))
      (_ : χ ∈ relativeRoots (T := (CommGroupScheme.baseChange bF).obj T)
        ((GroupScheme.baseChange bF).map iT))
      (_ : (CommGroupScheme.baseChange bF).map f ≫ χ = 0), D.filtration x χ 0)
    (w : normalizerPoints (T := (CommGroupScheme.baseChange bF).obj T)
      ((GroupScheme.baseChange bF).map iT))
    (hw : (w : rationalPoints ((GroupScheme.baseChange bF).obj G)) =
      rationalExtend F 𝕂 G (rationalPoints.map CS.j z) * h)
    (v : V S)
    (hv : w • x.val = descentCocharacterMap F 𝕂 f hiS.isSplitSubtorus.1 v +ᵥ x.val)
    {a : characterLattice S} (ha : a ∈ relativeRoots iS) :
    eval S a v = eval S a (CS.translation z).toAdd := by
  classical
  obtain ⟨hTa, hTlft, hTtorus, ht⟩ := unramifiedTorus_structure hG hiS hf hiT
  have hS : IsSplitTorus S.toGrp := hiS.isSplitSubtorus.1
  have hTK := hiT.isSplitSubtorus.1
  -- an integral character `χ` of `Z = Z_G(S)` restricting to `m • a`
  obtain ⟨χ, m, hm, hχ⟩ := exists_characterRestriction_eq_nsmul hS CS.s CS.bijective a
  -- `T ⊆ Z`
  have hrange : SubgroupFunctor.range iT ≤ torusCentralizer iS :=
    range_le_torusCentralizer_of_factor iS iT (CommGroupScheme.groupHom f) hf
  let τ : T.toGrp ⟶ CS.Z := SubgroupFunctor.IsRepresentedBy.factorHom CS.isRepresentedBy iT hrange
  have hτ : τ ≫ CS.j = iT := SubgroupFunctor.IsRepresentedBy.factorHom_comp _ _ _
  have hjmono : Mono CS.j := (Grp.forget _).mono_of_mono_map (f := CS.j) CS.isRepresentedBy.1
  have hfτ : CommGroupScheme.groupHom f ≫ τ = CS.s := by
    rw [← cancel_mono CS.j, Category.assoc, hτ, hf, CS.comp_eq]
  -- the character `ξ = χ|_T` and its base change `β'`
  set ξ : characterLattice T := torusCharacterRestrict τ χ with hξ
  have hfξ : f ≫ ξ = m • a := by
    rw [← hχ, ← hfτ, BruhatTits.Cartan.characterRestriction, AddMonoidHom.comp_apply,
      characterRestrict_comp, AddMonoidHom.comp_apply]
    rfl
  set β' : characterLattice ((CommGroupScheme.baseChange bF).obj T) :=
    characterLattice.baseChange bF T ξ with hβ'
  have hβ'fix : ∀ σ : 𝕂 ≃ₐ[F] 𝕂, characterLattice.galoisRepresentation F 𝕂 T σ β' = β' :=
    fun σ => characterLattice.galoisRepresentation_baseChange F 𝕂 T σ ξ
  have hfβ' : (CommGroupScheme.baseChange bF).map f ≫ β' =
      m • characterLattice.baseChange bF S a := by
    rw [hβ', ← characterLattice.baseChange_precomp, hfξ, map_nsmul]
  -- a root `b` of `T_K` over `a` and its Galois orbit sum `β`
  have haR : a ∈ roots (CommGroupScheme.groupHom f ≫ iT) := by
    rw [hf]
    exact ha
  set bR := splittingFieldRootLift (k := F) (K := 𝕂) hS hTK f iT ⟨a, haR⟩ with hbRdef
  have hbR : (CommGroupScheme.baseChange bF).map f ≫ (bR : characterLattice _) =
      characterLattice.baseChange bF S a :=
    splittingFieldRootLift_restriction (k := F) (K := 𝕂) hS hTK f iT ⟨a, haR⟩
  have hfinR : Finite (relativeRoots (T := (CommGroupScheme.baseChange bF).obj T)
      ((GroupScheme.baseChange bF).map iT)) :=
    (hTK.finite_relativeRoots _).to_subtype
  have hbspan : (bR : characterLattice _) ∈ Submodule.span ℤ
      (relativeRoots (T := (CommGroupScheme.baseChange bF).obj T)
        ((GroupScheme.baseChange bF).map iT)) :=
    Submodule.subset_span bR.2
  have hfin := finite_range_galoisRepresentation F 𝕂 iT hbspan
  set O := hfin.toFinset with hOdef
  have hmem : ∀ {ψ}, ψ ∈ O ↔ ∃ σ : 𝕂 ≃ₐ[F] 𝕂,
      characterLattice.galoisRepresentation F 𝕂 T σ (bR : characterLattice _) = ψ := by
    intro ψ
    rw [hOdef, Set.Finite.mem_toFinset, Set.mem_range]
  set β := ∑ ψ ∈ O, ψ with hβdef
  have hβfix : ∀ τ : 𝕂 ≃ₐ[F] 𝕂, characterLattice.galoisRepresentation F 𝕂 T τ β = β := by
    intro τ
    rw [hβdef, map_sum]
    refine Finset.sum_nbij' (fun ψ => characterLattice.galoisRepresentation F 𝕂 T τ ψ)
      (fun ψ => characterLattice.galoisRepresentation F 𝕂 T τ⁻¹ ψ) ?_ ?_ ?_ ?_ ?_
    · intro ψ hψ
      obtain ⟨σ, rfl⟩ := hmem.1 hψ
      exact hmem.2 ⟨τ * σ, by rw [map_mul]; rfl⟩
    · intro ψ hψ
      obtain ⟨σ, rfl⟩ := hmem.1 hψ
      exact hmem.2 ⟨τ⁻¹ * σ, by rw [map_mul]; rfl⟩
    · intro ψ _
      exact Representation.inv_self_apply _ τ ψ
    · intro ψ _
      exact Representation.self_inv_apply _ τ ψ
    · intro ψ _
      rfl
  have hβspan : β ∈ Submodule.span ℤ
      (relativeRoots (T := (CommGroupScheme.baseChange bF).obj T)
        ((GroupScheme.baseChange bF).map iT)) := by
    refine Submodule.sum_mem _ fun ψ hψ => ?_
    obtain ⟨σ, rfl⟩ := hmem.1 hψ
    exact Submodule.subset_span ((mem_roots_galois_iff F 𝕂 iT σ bR.val).mpr bR.property)
  have hfβ : (CommGroupScheme.baseChange bF).map f ≫ β =
      O.card • characterLattice.baseChange bF S a := by
    rw [hβdef, Preadditive.comp_sum]
    have hterm : ∀ ψ ∈ O, (CommGroupScheme.baseChange bF).map f ≫ ψ =
        characterLattice.baseChange bF S a := by
      intro ψ hψ
      obtain ⟨σ, rfl⟩ := hmem.1 hψ
      rw [← characterLattice.galoisRepresentation_precompose, hbR,
        characterLattice.galoisRepresentation_baseChange]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const]
  -- `|O| β' = m β`, so `β'` vanishes on the common kernel of the roots of `T_K`
  set θ := O.card • β' - m • β with hθdef
  have hθfix : ∀ σ : 𝕂 ≃ₐ[F] 𝕂, characterLattice.galoisRepresentation F 𝕂 T σ θ = θ := by
    intro σ
    rw [hθdef, map_sub, map_nsmul, map_nsmul, hβ'fix, hβfix]
  have hθres : characterRestrict ((GroupScheme.baseChange bF).map
      (CommGroupScheme.groupHom f)) θ = 0 := by
    change (CommGroupScheme.baseChange bF).map f ≫ θ = 0
    rw [hθdef, Preadditive.comp_sub, Preadditive.comp_nsmul, Preadditive.comp_nsmul, hfβ', hfβ,
      smul_smul, smul_smul, mul_comm, sub_self]
  have hθ0 : θ = 0 :=
    IsLargestSplitSubtorus.galoisInvariant_character_eq_zero F 𝕂 ht hTtorus θ hθfix hθres
  have hOcard : (O.card : ℝ) ≠ 0 := by
    have : (bR : characterLattice _) ∈ O := hmem.2 ⟨1, by rw [map_one]; rfl⟩
    exact Nat.cast_ne_zero.2 (Finset.card_ne_zero_of_mem this)
  have hker : ∀ r ∈ rootAnnihilator (S := (CommGroupScheme.baseChange bF).obj T)
      ((GroupScheme.baseChange bF).map iT),
      eval ((CommGroupScheme.baseChange bF).obj T) β' r = 0 := by
    intro r hr
    have hβr := eval_eq_zero_of_mem_span F 𝕂 iT hβspan hr
    have h1 := congrArg (evalAt 𝕂 ((CommGroupScheme.baseChange bF).obj T) r) hθ0
    rw [hθdef, map_sub, map_nsmul, map_nsmul, map_zero, evalAt_apply, evalAt_apply,
      nsmul_eq_mul, nsmul_eq_mul, hβr, mul_zero, sub_zero] at h1
    exact (mul_eq_zero.1 h1).resolve_left hOcard
  -- the base-changed centralizer `Z_K` of `S_K`
  set jK := (GroupScheme.baseChange bF).map CS.j with hjKdef
  set τK := (GroupScheme.baseChange bF).map τ with hτKdef
  set χK := rationalCharacters.baseChange bF χ with hχKdef
  have hjK : (torusCentralizer (T := (CommGroupScheme.baseChange bF).obj S)
      ((GroupScheme.baseChange bF).map iS)).IsRepresentedBy jK :=
    CS.isRepresentedBy_baseChange
  have hjKc : IsClosedSubgroup jK := CS.isClosedSubgroup.baseChange bF
  have hτK : τK ≫ jK = (GroupScheme.baseChange bF).map iT := by
    rw [hτKdef, hjKdef, ← Functor.map_comp, hτ]
  have hfK : CommGroupScheme.groupHom ((CommGroupScheme.baseChange bF).map f) ≫
      (GroupScheme.baseChange bF).map iT = (GroupScheme.baseChange bF).map iS := by
    rw [← hf, Functor.map_comp]
    rfl
  have hjK' : (torusCentralizer (CommGroupScheme.groupHom ((CommGroupScheme.baseChange bF).map f) ≫
      (GroupScheme.baseChange bF).map iT)).IsRepresentedBy jK := by
    rw [hfK]
    exact hjK
  have hjKmono : Mono jK.hom.hom := hjK.1
  have hSKtorus : IsTorus ((GroupScheme.baseChange bF).obj S.toGrp) :=
    (hS.baseChange bF).isTorus
  have hiSKc : IsClosedSubgroup ((GroupScheme.baseChange bF).map iS) :=
    hiS.isSplitSubtorus.2.baseChange bF
  have : IsAffineHom ((GroupScheme.baseChange bF).obj CS.Z).X.hom := hjKc.isAffineHom
  have : Smooth ((GroupScheme.baseChange bF).obj CS.Z).X.hom :=
    torusCentralizerSmooth 𝕂 _ _ _ hSKtorus hiSKc _ jK hjK hjKc
  -- `h` is the image of a point of `Z_K` killed by `χ_K`
  obtain ⟨mh, hmh, hχmh⟩ := exists_map_eq_and_eval_eq_one_of_mem_iSup hTK
    ((GroupScheme.baseChange bF).map iT) ((CommGroupScheme.baseChange bF).map f) τK jK hτK hjK'
    hjKc χK (fun χ' => D.filtration x χ' 0) (fun χ' => D.filtration_le_rootGroupPoints x χ' 0)
    hlevi
  set zK := rationalExtend F 𝕂 CS.Z z with hzKdef
  have hzK : rationalExtend F 𝕂 G (rationalPoints.map CS.j z) = rationalPoints.map jK zK :=
    rationalExtend_map F 𝕂 CS.j z
  have hw' : (w : rationalPoints ((GroupScheme.baseChange bF).obj G)) =
      rationalPoints.map jK (zK * mh) := by
    rw [hw, hzK, ← hmh, map_mul]
  -- Weyl invariance of `β'`
  have hβ'eq : β' = torusCharacterRestrict τK χK :=
    characterLattice.baseChange_torusCharacterRestrict bF τ χ
  have hpt : (zK * mh)⁻¹ ≫ jK.hom.hom =
      ((w⁻¹ : normalizerPoints (T := (CommGroupScheme.baseChange bF).obj T)
        ((GroupScheme.baseChange bF).map iT)) :
        rationalPoints ((GroupScheme.baseChange bF).obj G)) := by
    rw [Subgroup.coe_inv, hw', ← map_inv]
    rfl
  have hinv : weylAction (T := (CommGroupScheme.baseChange bF).obj T)
      ((GroupScheme.baseChange bF).map iT) w⁻¹ β' = β' := by
    rw [hβ'eq]
    exact weylAction_torusCharacterRestrict_of_comp (B := Spec (CommRingCat.of 𝕂))
      (T := (CommGroupScheme.baseChange bF).obj T) τK jK hτK w⁻¹ (zK * mh)⁻¹ hpt χK
  -- a power of `w` lies in the centralizer `C` of `T_K`
  obtain ⟨N, hN, hNc⟩ := exists_pow_mem_centralizerPoints hTK
    ((GroupScheme.baseChange bF).map iT) hiT.isSplitSubtorus.2 w
  obtain ⟨sN, hsN⟩ := exists_comp_eq_of_mem_centralizerPoints C.isRepresentedBy hNc
  have hup := IntegerValuation.IsCentralizerCompatible.smul_eq_vadd
    (v := MaximalUnramified.valuation F) C.isRepresentedBy x.isValuation (hDC x.val x.mem) sN
  have hNx : w ^ N • x.val = (IntegerValuation.centralizerTranslation
      (MaximalUnramified.valuation F) C.s C.bijective sN).toAdd +ᵥ x.val := by
    refine Eq.trans ?_ hup
    congr 1
    apply Subtype.ext
    exact hsN.symm
  have hmain := natCast_mul_eval_eq_of_pow_smul x.isValuation w hv hNx hker hinv
  -- the left side: `β'` on the descended translation
  rw [eval_descentCocharacterMap, hfβ', ← evalAt_apply, map_nsmul, evalAt_apply,
    eval_splitCocharacterBaseChange, nsmul_eq_mul] at hmain
  -- the right side: upstairs V 6 through `κ : C.Z → Z_K`
  have hrangeC : SubgroupFunctor.range C.j ≤
      torusCentralizer (T := (CommGroupScheme.baseChange bF).obj S)
        ((GroupScheme.baseChange bF).map iS) := by
    rw [C.isRepresentedBy.2]
    exact torusCentralizer_le_of_factor _ _ _ hfK
  set κ := SubgroupFunctor.IsRepresentedBy.factorHom hjK C.j hrangeC with hκdef
  have hκ : κ ≫ jK = C.j := SubgroupFunctor.IsRepresentedBy.factorHom_comp _ _ _
  have hjKmono' : Mono jK := (Grp.forget _).mono_of_mono_map (f := jK) hjKmono
  have hsκ : C.s ≫ κ = τK := by
    rw [← cancel_mono jK, Category.assoc, hκ, C.comp_eq, hτK]
  have hβ'C : BruhatTits.Cartan.characterRestriction C.s (characterRestrict κ χK) = β' := by
    rw [hβ'eq, BruhatTits.Cartan.characterRestriction, AddMonoidHom.comp_apply,
      ← AddMonoidHom.comp_apply (characterRestrict C.s), ← characterRestrict_comp, hsκ]
    rfl
  have hνK := IntegerValuation.eval_centralizerTranslation (MaximalUnramified.valuation F)
    C.s C.bijective sN (characterRestrict κ χK)
  rw [hβ'C, rationalCharacterEval_characterRestrict] at hνK
  have hκs : rationalPoints.map κ sN = (zK * mh) ^ N := by
    have h1 : rationalPoints.map jK (rationalPoints.map κ sN) =
        rationalPoints.map jK ((zK * mh) ^ N) := by
      rw [map_pow, ← hw', ← SubgroupClass.coe_pow, ← hsN, rationalPoints.map_apply,
        rationalPoints.map_apply, Category.assoc, ← Grp.comp_hom_hom, hκ]
    exact (cancel_mono jK.hom.hom).1 h1
  rw [hκs, map_pow, map_mul, hχmh, mul_one] at hνK
  have hzχ : rationalCharacterEval χK zK =
      Units.map (algebraMap F 𝕂).toMonoidHom (rationalCharacterEval χ z) :=
    rationalCharacterEval_extend F 𝕂 CS.Z χ z
  rw [hzχ] at hνK
  have hord : IntegerValuation.order (MaximalUnramified.valuation F)
      ((Units.map (algebraMap F 𝕂).toMonoidHom (rationalCharacterEval χ z)) ^ N) =
      (N : ℝ) * ((Plancherel.fieldOrderUnits F (rationalCharacterEval χ z)).toAdd : ℝ) := by
    unfold IntegerValuation.order
    rw [map_pow, toAdd_pow, MaximalUnramified.orderUnits_base_eq_fieldOrderUnits, nsmul_eq_mul,
      Int.cast_mul, Int.cast_natCast]
  rw [hord] at hνK
  rw [hνK] at hmain
  -- the original side: `ν(z)` through `χ`
  have hF := eval_centralizerTranslation CS.s CS.bijective z χ
  rw [hχ, ← evalAt_apply, map_nsmul, evalAt_apply, nsmul_eq_mul,
    Plancherel.rationalCharacterValuation_apply] at hF
  have hNpos : (0 : ℝ) < N := Nat.cast_pos.2 hN
  have hmpos : (0 : ℝ) < m := Nat.cast_pos.2 hm
  change eval S a v = eval S a (centralizerTranslation CS.s CS.bijective z).toAdd
  have key : (N : ℝ) * (m : ℝ) * eval S a v =
      (N : ℝ) * (m : ℝ) * eval S a (centralizerTranslation CS.s CS.bijective z).toAdd := by
    rw [mul_assoc, hmain, mul_assoc, hF]
    ring
  exact mul_left_cancel₀ (mul_pos hNpos hmpos).ne' key

set_option maxHeartbeats 8000000 in
/-- **V 6 at a Galois-fixed point from Levi transport, for fixed data.** -/
theorem unramifiedFixedCentralizerCompatibility_core
    (hQ : UnramifiedFixedLeviTransportStatement.{u})
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
    [IsAffineHom G.X.hom] [Smooth G.X.hom]
    (S : CommGroupScheme (Spec (CommRingCat.of F))) (iS : S.toGrp ⟶ G)
    (hiS : IsMaximalSplitTorus iS) [Mono iS.hom.hom.left]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (iT : T.toGrp ⟶ G) (f : S ⟶ T)
    (hf : CommGroupScheme.groupHom f ≫ iT = iS)
    (hiT : IsMaximalSplitTorus (T := (CommGroupScheme.baseChange bF).obj T)
      ((GroupScheme.baseChange bF).map iT))
    [Mono ((GroupScheme.baseChange bF).map iT).hom.hom.left]
    (hE : RelativeRoot.HasOppositeFactorPairs (T := (CommGroupScheme.baseChange bF).obj T)
      ((GroupScheme.baseChange bF).map iT))
    (D : KPApartmentData (S := (CommGroupScheme.baseChange bF).obj T)
      ((GroupScheme.baseChange bF).map iT)
      (IntegerValuation.order (MaximalUnramified.valuation F)))
    (C : CentralizerDatum (S := (CommGroupScheme.baseChange bF).obj T)
      ((GroupScheme.baseChange bF).map iT))
    (hDC : IntegerValuation.IsOmegaCompatible (MaximalUnramified.valuation F) D C)
    (CS : CentralizerDatum iS) (x : D.Apartment)
    (hx : ∀ σ : 𝕂 ≃ₐ[F] 𝕂, RootFunctionFamily.galoisAction F 𝕂 T G σ x.val = x.val) :
    IsCentralizerCompatible iS CS.j CS.s CS.bijective
      (torusFieldRestrictedRootFunctionFamily (k := F) (K := 𝕂)
        hiS.isSplitSubtorus.1 hiT.isSplitSubtorus.1 hE (D.isRootDatumValuation_of_mem x.mem)
        ((CommGroupScheme.baseChange bF).map f)) := by
  intro a ha z u hu
  obtain ⟨h, hh, hlevi, hw, hy⟩ := hQ F G hG S iS hiS T iT f hf hiT D C hDC (CS.toNormalizer z) x hx
  have hφ := (D.leviTransport_apartmentMap_torusFieldRestricted hf hiS.isSplitSubtorus.1
    hiT.isSplitSubtorus.1 hE (CS.toNormalizer z) x hh hlevi hw).2
  obtain ⟨v, hv⟩ := unramified_exists_descent_vadd_of_galoisFixed hG hiS hf hiT D x
    ((⟨_, hw⟩ : normalizerPoints (T := (CommGroupScheme.baseChange bF).obj T)
      ((GroupScheme.baseChange bF).map iT)) • x) hx hy
  have hφv := torusFieldRestricted_eq_vadd_of_eq_descent_vadd hiS.isSplitSubtorus.1
    hiT.isSplitSubtorus.1 hE x.isValuation (D.isRootDatumValuation_of_mem
      ((⟨_, hw⟩ : normalizerPoints (T := (CommGroupScheme.baseChange bF).obj T)
        ((GroupScheme.baseChange bF).map iT)) • x).mem) v hv
  have key := hφ.symm.trans hφv
  have hval := eval_eq_centralizerTranslation_of_leviTransport hG hiS hf hiT D C hDC CS z x hlevi
    ⟨_, hw⟩ rfl v hv ha
  have hu' := congrArg (fun ψ : RootFunctionFamily S G => ψ a u) key
  simp only [RootFunctionFamily.smul_apply, RootFunctionFamily.vadd_apply] at hu'
  have hw1 : weylAction iS (CS.toNormalizer z)⁻¹ = 1 := by
    rw [← map_inv]
    exact weylAction_centralizerToNormalizer CS.isRepresentedBy z⁻¹
  rw [hw1, LinearEquiv.coe_one, id, hval] at hu'
  exact hu'

set_option maxHeartbeats 8000000 in
/-- **V 6 at the Galois-fixed points from Levi transport.** The Levi transport statement
`UnramifiedFixedLeviTransportStatement` implies `UnramifiedFixedCentralizerCompatibilityStatement`:
at every `Aut(K/F)`-fixed point of the apartment of `D`, the restricted family `φ x` satisfies
the full axiom V 6 on `Z_G(S)(F)`. -/
theorem unramifiedFixedCentralizerCompatibility_of_leviTransport
    (hQ : UnramifiedFixedLeviTransportStatement.{u}) :
    UnramifiedFixedCentralizerCompatibilityStatement.{u} := by
  intro F _ _ _ _ G hG S iS hiS T iT f hf
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  have := mono_of_isMaximalSplitTorus hiS
  intro hiT
  have : Mono ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map
    iT).hom.hom.left := mono_of_isMaximalSplitTorus hiT
  intro hE D C hDC fixed φ CS x hx
  exact unramifiedFixedCentralizerCompatibility_core hQ G hG S iS hiS T iT f hf hiT hE D C hDC CS
    x hx

end Unramified

/-- Internal proposition packaging the implication proved above: the Levi transport statement
`UnramifiedFixedLeviTransportStatement` implies V 6 on `Z_G(S)(F)` at the Galois-fixed points,
`UnramifiedFixedCentralizerCompatibilityStatement`. Neither side is proved here. -/
def UnramifiedFixedCentralizerCompatibilityReductionStatement : Prop :=
  UnramifiedFixedLeviTransportStatement.{u} → UnramifiedFixedCentralizerCompatibilityStatement.{u}

/-- The packaged implication `UnramifiedFixedCentralizerCompatibilityReductionStatement` holds; it is
`unramifiedFixedCentralizerCompatibility_of_leviTransport`. -/
theorem unramifiedFixedCentralizerCompatibilityReduction :
    UnramifiedFixedCentralizerCompatibilityReductionStatement.{u} :=
  unramifiedFixedCentralizerCompatibility_of_leviTransport

end Langlands.Geometry.Building
