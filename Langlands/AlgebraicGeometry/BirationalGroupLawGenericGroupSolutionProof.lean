import Langlands.AlgebraicGeometry.BirationalGroupLawGenericGroupSolutionStatement
import Langlands.AlgebraicGeometry.BirationalGroupLawFullSolution
import Langlands.AlgebraicGeometry.WeilExtensionOverDvr
import Langlands.AlgebraicGeometry.SmoothDvrInverseExtension

/-! # Extending a solution when the generic law is total -/

noncomputable section

universe u

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Topology TopologicalSpace

namespace Langlands.AlgebraicGeometry

open SmoothDvrCodimensionOneOpen FactorialAffineExtension
open Langlands.GroupScheme.RelativeIdentityComponent (overPullback_isPullback)

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

private theorem point_of_inverse_chart {X Y T : Scheme.{u}} (τ : X ⟶ Y) (r : Y.PartialMap X)
    (i : T ⟶ X) (j : T ⟶ r.domain.toScheme) (hi : j ≫ r.domain.ι = i ≫ τ)
    (hj : j ≫ r.hom = i) (t : T) :
    ∃ h : τ (i t) ∈ r.domain, r.hom ⟨τ (i t), h⟩ = i t := by
  have he := congrArg (fun a : T ⟶ Y => a t) hi
  change r.domain.ι (j t) = τ (i t) at he
  have h : τ (i t) ∈ r.domain := he ▸ (j t).2
  have ht : (⟨τ (i t), h⟩ : r.domain.toScheme) = j t := r.domain.ι.isEmbedding.injective he.symm
  refine ⟨h, ?_⟩
  rw [ht]
  exact congrArg (fun a : T ⟶ X => a t) hj

set_option maxHeartbeats 1100000 in
/-- From a supplied solution and totality of the generic group law, construct a solution
whose embedding is defined on all of `X`. -/
theorem birationalGroupLawGenericGroupSolution : BirationalGroupLawGenericGroupSolutionStatement.{u} := by
  intro R _ _ _ X f hf hsep _ hqc _ m hGen hSol
  let : Smooth f := hf
  let : IsSeparated f := hsep
  let : QuasiCompact f := hqc
  obtain ⟨σ⟩ := hSol
  let Y := σ.group.X.left
  let g := σ.group.X.hom
  let U := σ.domain
  let j := σ.embedding
  have : IsOpenImmersion j := σ.isOpenImmersion_embedding
  have : Smooth g := σ.smooth
  have : IsSeparated g := σ.isSeparated
  have : LocallyOfFiniteType g := σ.locallyOfFiniteType
  have : IsReduced X := SmoothReducedBase.isReduced_of_smooth_of_isReduced f
  have : IsReduced Y := SmoothReducedBase.isReduced_of_smooth_of_isReduced g
  have : X.IsSeparated := separatedScheme_of_separated_over f
  have : Y.IsSeparated := separatedScheme_of_separated_over g
  let B := genericOpen R
  let J := j.opensRange
  let iJ := j.isoOpensRange
  have hfacJ : iJ.hom ≫ J.ι = j := j.isoOpensRange_hom_ι
  have hfacJ' : iJ.inv ≫ j = J.ι := by
    calc
      _ = iJ.inv ≫ iJ.hom ≫ J.ι := congrArg (fun c => iJ.inv ≫ c) hfacJ.symm
      _ = _ := Iso.inv_hom_id_assoc _ _
  let Xk := f ⁻¹ᵁ B
  let Yk := g ⁻¹ᵁ B
  obtain ⟨e₀, he₀⟩ := BirationalGroupLaw.Solution.exists_iso_over_open m σ B (fun p hp => hGen p hp)
  let eX := pullbackRestrictIsoRestrict f B
  let eY := pullbackRestrictIsoRestrict g B
  let e : Xk.toScheme ≅ Yk.toScheme := eX.symm ≪≫ e₀ ≪≫ eY
  have hbase {T : Scheme.{u}} (v : T ⟶ U.toScheme) (d : T ⟶ B.toScheme)
      (hd : v ≫ U.ι ≫ f = d ≫ B.ι) :
      ∃ w : T ⟶ Xk.toScheme, w ≫ Xk.ι = v ≫ U.ι ∧ w ≫ e.hom ≫ Yk.ι = v ≫ j := by
    let F := Over.pullback B.ι
    let c := pullback.lift v d hd
    let i₁ := (F.map σ.firstChart).left
    let i₂ := (F.map σ.secondChart).left
    have hi₁ : i₁ ≫ pullback.fst f B.ι = pullback.fst (U.ι ≫ f) B.ι ≫ U.ι :=
      (overPullback_isPullback B.ι σ.firstChart).w
    have hi₂ : i₂ ≫ pullback.fst g B.ι = pullback.fst (U.ι ≫ f) B.ι ≫ j :=
      (overPullback_isPullback B.ι σ.secondChart).w
    have he : i₁ ≫ e₀.hom = i₂ := he₀
    have heX : eX.hom ≫ Xk.ι = pullback.fst f B.ι := pullbackRestrictIsoRestrict_hom_ι _ _
    have heY : eY.hom ≫ Yk.ι = pullback.fst g B.ι := pullbackRestrictIsoRestrict_hom_ι _ _
    refine ⟨c ≫ i₁ ≫ eX.hom, ?_, ?_⟩
    · simp only [Category.assoc, heX]
      rw [hi₁, ← Category.assoc, pullback.lift_fst]
    · simp only [e, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc, heY]
      rw [← Category.assoc i₁, he, hi₂, ← Category.assoc, pullback.lift_fst]
  let r : X.PartialMap Y := ⟨U, σ.domain_dense.dense, j⟩
  let s : Y.PartialMap X := ⟨J, by simpa only [J, Scheme.Hom.coe_opensRange] using
    σ.embedding_dense.dense, iJ.inv ≫ U.ι⟩
  have hs : s.hom ≫ f = J.ι ≫ g := by
    change (iJ.inv ≫ U.ι) ≫ f = J.ι ≫ g
    rw [Category.assoc, ← σ.embedding_comp, ← Category.assoc, hfacJ']
  have hX : X.homOfLE (inf_le_left : U ⊓ Xk ≤ U) ≫ r.hom =
      X.homOfLE (inf_le_right : U ⊓ Xk ≤ Xk) ≫ (e.hom ≫ Yk.ι) := by
    let l := X.homOfLE (inf_le_left : U ⊓ Xk ≤ U)
    let k := X.homOfLE (inf_le_right : U ⊓ Xk ≤ Xk)
    let d := k ≫ f ∣_ B
    have hd : l ≫ U.ι ≫ f = d ≫ B.ι := by
      dsimp only [d]
      rw [Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι_assoc, Scheme.homOfLE_ι_assoc]
    obtain ⟨w, hw, hw'⟩ := hbase l d hd
    have heq : w = k := (cancel_mono Xk.ι).mp (by rw [hw, Scheme.homOfLE_ι, Scheme.homOfLE_ι])
    exact (heq ▸ hw').symm
  have hY : Y.homOfLE (inf_le_left : J ⊓ Yk ≤ J) ≫ s.hom =
      Y.homOfLE (inf_le_right : J ⊓ Yk ≤ Yk) ≫ (e.inv ≫ Xk.ι) := by
    let l := Y.homOfLE (inf_le_left : J ⊓ Yk ≤ J)
    let k := Y.homOfLE (inf_le_right : J ⊓ Yk ≤ Yk)
    let v := l ≫ iJ.inv
    let d := k ≫ g ∣_ B
    have hv : v ≫ j = k ≫ Yk.ι := by
      dsimp only [v]
      rw [Category.assoc, hfacJ', Scheme.homOfLE_ι, Scheme.homOfLE_ι]
    have hd : v ≫ U.ι ≫ f = d ≫ B.ι := by
      dsimp only [d]
      rw [← σ.embedding_comp, ← Category.assoc v, hv, Category.assoc, Category.assoc, morphismRestrict_ι]
    obtain ⟨w, hw, hw'⟩ := hbase v d hd
    have heq : w ≫ e.hom = k := (cancel_mono Yk.ι).mp (by rw [Category.assoc, hw', hv])
    have heq' : w = k ≫ e.inv := e.eq_comp_inv.mpr heq
    change l ≫ iJ.inv ≫ U.ι = k ≫ e.inv ≫ Xk.ι
    rw [← Category.assoc l, ← hw, heq', Category.assoc]
  obtain ⟨hkX, hkX'⟩ := rationalMap_extends_of_overlap r Xk (e.hom ≫ Yk.ι) hX
  obtain ⟨hkY, hkY'⟩ := rationalMap_extends_of_overlap s Yk (e.inv ≫ Xk.ι) hY
  let D := r.toRationalMap.domain
  let E := s.toRationalMap.domain
  let r' := r.toRationalMap.toPartialMap
  let s' := s.toRationalMap.toPartialMap
  let iD : U.toScheme ⟶ D.toScheme := X.homOfLE r.le_domain_toRationalMap
  let iE : J.toScheme ⟶ E.toScheme := Y.homOfLE s.le_domain_toRationalMap
  have hDr : iD ≫ r'.hom = r.hom := r.toPartialMap_toRationalMap_restrict
  have hEs : iE ≫ s'.hom = s.hom := s.toPartialMap_toRationalMap_restrict
  have hiD : iD ≫ D.ι = U.ι := X.homOfLE_ι _
  have hiE : iE ≫ E.ι = J.ι := Y.homOfLE_ι _
  have hDr' : r'.hom ≫ g = D.ι ≫ f := by
    have : IsDominant iD := Opens.isDominant_homOfLE r.dense_domain _
    apply AlgebraicGeometry.ext_of_isDominant iD
    rw [← Category.assoc iD r'.hom, hDr, ← Category.assoc iD D.ι, hiD]
    exact σ.embedding_comp
  have hEs' : s'.hom ≫ f = E.ι ≫ g := by
    have : IsDominant iE := Opens.isDominant_homOfLE s.dense_domain _
    apply AlgebraicGeometry.ext_of_isDominant iE
    rw [← Category.assoc iE s'.hom, hEs, ← Category.assoc iE E.ι, hiE]
    exact hs
  have hD : FibreGenerizationDense f (D : Set X) := by
    intro x
    obtain ⟨y, hy, hfy, hyx⟩ := σ.domain_dense x
    exact ⟨y, r.le_domain_toRationalMap hy, hfy, hyx⟩
  obtain ⟨τ, hτD, hτ⟩ := weilExtensionOverDvr R f σ.group D hD hkX r'.hom hDr'
  have hτU : U.ι ≫ τ = j := by rw [← hiD, Category.assoc, hτD, hDr]
  have hτK : Xk.ι ≫ τ = e.hom ≫ Yk.ι := by
    let iK := X.homOfLE hkX
    have hiK : iK ≫ D.ι = Xk.ι := X.homOfLE_ι _
    rw [← hiK, Category.assoc, hτD]
    exact hkX'
  have hdom : FibreGenerizationDense f (↑(U ⊔ Xk) : Set X) := by
    intro x
    obtain ⟨y, hy, hfy, hyx⟩ := σ.domain_dense x
    exact ⟨y, Opens.mem_sup.mpr (Or.inl hy), hfy, hyx⟩
  let bU := iJ.hom ≫ iE
  have hbU : bU ≫ E.ι = U.ι ≫ τ := by
    dsimp only [bU]
    rw [Category.assoc, hiE, hfacJ, hτU]
  have hvU : bU ≫ s'.hom = U.ι := by
    dsimp only [bU]
    rw [Category.assoc, hEs]
    exact iJ.hom_inv_id_assoc _
  let bK := e.hom ≫ Y.homOfLE hkY
  have hbK : bK ≫ E.ι = Xk.ι ≫ τ := by
    dsimp only [bK]
    rw [Category.assoc, Scheme.homOfLE_ι, hτK]
  have hvK : bK ≫ s'.hom = Xk.ι := by
    dsimp only [bK]
    rw [Category.assoc, hkY', Iso.hom_inv_id_assoc]
  have : IsDominant U.ι := Opens.isDominant_ι σ.domain_dense.dense
  have : IsDominant iE := Opens.isDominant_homOfLE s.dense_domain _
  have : IsDominant bU := inferInstanceAs (IsDominant (iJ.hom ≫ iE))
  have : IsOpenImmersion τ := by
    apply isOpenImmersion_of_inverse_at_stalk_primes R f g τ s' hEs' U.ι bU hbU.symm hvU
    intro x p hp
    have hm := smallPrime_mem R f (U ⊔ Xk) hdom le_sup_right x p hp
    rcases Opens.mem_sup.mp hm with hU | hK
    · exact point_of_inverse_chart τ s' U.ι bU hbU hvU ⟨_, hU⟩
    · exact point_of_inverse_chart τ s' Xk.ι bK hbK hvK ⟨_, hK⟩
  exact σ.exists_full_of_extension τ hτ hτU

end Langlands.AlgebraicGeometry
