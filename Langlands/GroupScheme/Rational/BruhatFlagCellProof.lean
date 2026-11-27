import Langlands.GroupScheme.Rational.BruhatFlagCellStatement
import Langlands.GroupScheme.Rational.BruhatCellProof
import Langlands.GroupScheme.Rational.RationalBruhatProof
import Langlands.GroupScheme.Dynamic.FlagQuotientProof

/-! # Locally closed rational Bruhat cells in a flag quotient -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace BruhatFlagCell

variable {k : Type u} [Field k] {G P U V : GroupScheme (Spec (CommRingCat.of k))}
  (p : P ⟶ G) (u : U ⟶ G) (v : V ⟶ G)
  {Q : Over (Spec (CommRingCat.of k))} (q : G.X ⟶ Q)
  (hfib : ∀ (X : Over (Spec (CommRingCat.of k))) (g h : X ⟶ G.X),
    g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range p).carrier X)
  (n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)

include hfib in
private theorem quotient_mul {X : Over (Spec (CommRingCat.of k))} (g : X ⟶ G.X)
    {a : X ⟶ G.X} (ha : a ∈ (SubgroupFunctor.range p).carrier X) :
    (g * a) ≫ q = g ≫ q := by
  symm
  apply (hfib X g (g * a)).mpr
  simpa only [inv_mul_cancel_left] using ha

include hfib in
/-- The flag parametrization is the composite of the group Bruhat cell with
its flag projection on every point of the cell product. -/
theorem lift_groupParametrization_comp {X : Over (Spec (CommRingCat.of k))}
    (a : X ⟶ (BruhatCell.factor u v n).X) (b : X ⟶ P.X) :
    lift a b ≫ BruhatCell.parametrization u v p n ≫ q = a ≫ parametrization u v q n := by
  let j := subgroupIntersectionFst (v ≫ (G.innerIso n).hom) u
  let l := (a ≫ j.hom.hom) ≫ v.hom.hom
  let t := (Dynamic.rationalLeftTranslation k G n).hom
  have hl : l ≫ t = (a ≫ (subgroupIntersectionHom (v ≫ (G.innerIso n).hom) u).hom.hom) *
      G.constantPoint n X := by
    rw [Dynamic.comp_rationalLeftTranslation]
    have hj : a ≫ (subgroupIntersectionHom (v ≫ (G.innerIso n).hom) u).hom.hom =
        l ≫ (G.innerIso n).hom.hom.hom := by
      simp only [j, l, subgroupIntersectionHom, Grp.comp_hom_hom, Category.assoc]
    rw [hj, comp_innerIso_hom]
    change G.constantPoint n X * l = _
    group
  rw [← Category.assoc, BruhatCell.lift_parametrization, ← hl,
    quotient_mul p q hfib _ (SubgroupFunctor.mem_range.mpr ⟨b, rfl⟩)]
  simp only [parametrization, l, j, t, Category.assoc]

include hfib in
private theorem parametrization_isImmersion [Mono p.hom.hom]
    [Smooth q.left] [Surjective q.left] [QuasiCompact q.left]
    (hu : IsClosedSubgroup u)
    [IsOpenImmersion (QuotientCell.multiplication p v.hom.hom).left] :
    IsImmersion (parametrization u v q n).left := by
  let j := subgroupIntersectionFst (v ≫ (G.innerIso n).hom) u
  let e := Dynamic.flagQuotientTranslation k G (SubgroupFunctor.range p) q hfib n
  have hj : IsClosedImmersion j.hom.hom.left := isClosedSubgroup_subgroupIntersectionFst _ hu
  have hvq : IsOpenImmersion (v.hom.hom ≫ q).left := QuotientCell.isOpenImmersion p v.hom.hom q hfib
  have he : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
  have h : parametrization u v q n = j.hom.hom ≫ (v.hom.hom ≫ q) ≫ e.hom := by
    rw [parametrization, Category.assoc v.hom.hom q e.hom, Dynamic.fac_flagQuotientTranslation]
  rw [h]
  change IsImmersion (j.hom.hom.left ≫ (v.hom.hom ≫ q).left ≫ e.hom.left)
  infer_instance

end BruhatFlagCell

/-- The locally closed flag cells identify their rational images with the
parabolic orbits, and the relative Weyl group indexes their partition. -/
theorem rationalBruhatFlagCell : RationalBruhatFlagCellStatement.{u} := by
  intro k _ G hG T i hi ν
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : Smooth G.X.hom := hG.smooth
  dsimp only
  intro hν Q q _ _ _ hfib
  let S₀ : Over (Spec (CommRingCat.of k)) := Over.mk (𝟙 _)
  let χ := CommGroupScheme.groupHom ν ≫ i
  let χminus := CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ χ
  let p := Dynamic.Affine.parabolicHom χ
  let u := Dynamic.Affine.unipotentHom χ
  let v := Dynamic.Affine.unipotentHom χminus
  let F := Dynamic.parabolic χ
  have hp := Dynamic.Affine.isRepresentedBy_parabolicHom χ
  have hu := Dynamic.Affine.isRepresentedBy_unipotentHom χ
  have hv := Dynamic.Affine.isRepresentedBy_unipotentHom χminus
  have hpc := Dynamic.Affine.isClosedSubgroup_parabolicHom χ
  have huc := Dynamic.Affine.isClosedSubgroup_unipotentHom χ
  have hpmono : Mono p.hom.hom := hp.1
  have hf : ∀ (X : Over (Spec (CommRingCat.of k))) (g h : X ⟶ G.X),
      g ≫ q = h ≫ q ↔ g⁻¹ * h ∈ (SubgroupFunctor.range p).carrier X := by
    rw [hp.2]
    exact hfib
  have hopen : IsOpenImmersion (QuotientCell.multiplication p v.hom.hom).left :=
    oppositeCellStatement k G χ _ _ v p hv hp
  have hLift : ∀ x : S₀ ⟶ Q, ∃ g : S₀ ⟶ G.X, g ≫ q = x := by
    have hLiftRing : ∀ x : RingPoint k Q k, ∃ g : RingPoint k G.X k, g ≫ q = x := by
      rcases finite_or_infinite k with hfin | hinf
      · let : Finite k := hfin
        have hP : IsParabolicSubgroup p :=
          isParabolicSubgroup_of_range_eq_dynamicParabolic hG p hpc χ hp.2
        let : Smooth (Dynamic.Affine.parabolicScheme χ).X.hom := hP.smooth
        let : IsClosedImmersion p.hom.hom.left := hpc
        let : IsAffineHom (Dynamic.Affine.parabolicScheme χ).X.hom := by
          rw [← Over.w p.hom.hom]
          infer_instance
        let : ConnectedSpace G.X.left := hG.connectedSpace
        exact Dynamic.rational_lifts_of_finite_torsor k G _ q p hf
          finiteFieldTorsorPointStatement
          (DynamicConnected.connectedSpace_of_isRepresentedBy_parabolic G χ hp)
      · let : Infinite k := hinf
        let seed := Dynamic.flagQuotientCell k p v q hf
        have hseed := Dynamic.range_identity_subset_flagQuotientCell k p v q hf
        rw [rationalPointEquiv_left] at hseed
        exact Dynamic.rational_lifts_of_reductive_density k G (SubgroupFunctor.range p) q hf
          reductiveRationalPointDensity hG seed.1 seed.2 hseed
          (Dynamic.flagQuotientCell_comp k p v q hf)
    intro x
    obtain ⟨g, hg⟩ := hLiftRing (rationalPointEquiv k Q x)
    refine ⟨(rationalPointEquiv k G.X).symm g, (rationalPointEquiv k Q).injective ?_⟩
    rw [rationalPointEquiv_natural, Equiv.apply_symm_apply, hg]
  let cell (n : normalizerPoints i) : Set (S₀ ⟶ Q) :=
    Set.range (fun a => a ≫ BruhatFlagCell.parametrization u v q n.val)
  have horbit (n : normalizerPoints i) (x : S₀ ⟶ Q) : x ∈ cell n ↔
      ∃ a ∈ F.carrier S₀, (a * n.val) ≫ q = x := by
    have H := (rationalBruhatCell k G hG T i hi ν hν _ _ _ p u v hp hu huc hv n).2
    constructor
    · rintro ⟨c, hc⟩
      let g := lift c (1 : S₀ ⟶ (Dynamic.Affine.parabolicScheme χ).X) ≫
        BruhatCell.parametrization u v p n.val
      have hg : g ≫ q = x := by
        simpa only [g, Category.assoc, BruhatFlagCell.lift_groupParametrization_comp p u v q hf]
          using hc
      obtain ⟨a, b, hg'⟩ := (H g).mp ⟨lift c 1, rfl⟩
      refine ⟨a ≫ p.hom.hom, (hp.pointsEquiv S₀ a).property, ?_⟩
      rw [hg', BruhatFlagCell.quotient_mul p q hf _ (SubgroupFunctor.mem_range.mpr ⟨b, rfl⟩)] at hg
      exact hg
    · rintro ⟨a, ha, hx⟩
      let a' := (hp.pointsEquiv S₀).symm ⟨a, ha⟩
      have ha' : a' ≫ p.hom.hom = a := hp.pointsEquiv_symm_comp _
      obtain ⟨d, hd⟩ := (H (a * n.val)).mpr ⟨a', 1, by rw [ha', MonObj.one_comp, mul_one]⟩
      let b := d ≫ snd _ _
      let c := d ≫ fst _ _
      have hpair : d = lift c b := (lift_comp_fst_snd d).symm
      refine ⟨c, ?_⟩
      change c ≫ BruhatFlagCell.parametrization u v q n.val = x
      rw [← BruhatFlagCell.lift_groupParametrization_comp p u v q hf n.val c b,
        ← hpair, ← Category.assoc, hd, hx]
  have hEq (n n' : normalizerPoints i) (he : (QuotientGroup.mk n : relativeWeylGroup i) =
      QuotientGroup.mk n') : cell n = cell n' := by
    have hz := (relativeWeyl_eq_iff_inv_mul_mem_centralizerPoints i n n').mp he
    have hpar := centralizerPoints_le_dynamicParabolic i (CommGroupScheme.groupHom ν) hz
    have hleft (a : S₀ ⟶ G.X) : (a * n.val) ≫ q = (a * n'.val) ≫ q := by
      apply (hfib S₀ _ _).mpr
      have h : (a * n.val)⁻¹ * (a * n'.val) = n.val⁻¹ * n'.val := by group
      rw [h]
      exact hpar
    ext x
    rw [horbit, horbit]
    exact ⟨fun ⟨a, ha, hx⟩ => ⟨a, ha, (hleft a).symm.trans hx⟩,
      fun ⟨a, ha, hx⟩ => ⟨a, ha, (hleft a).trans hx⟩⟩
  have hbr := rationalBruhat k G hG T i hi ν hν
  have hSep (n n' : normalizerPoints i) (x : S₀ ⟶ Q) (hx : x ∈ cell n) (hx' : x ∈ cell n') :
      (QuotientGroup.mk n : relativeWeylGroup i) = QuotientGroup.mk n' := by
    obtain ⟨a, ha, hax⟩ := (horbit n x).mp hx
    obtain ⟨b, hb, hbx⟩ := (horbit n' x).mp hx'
    let d := (a * n.val)⁻¹ * (b * n'.val)
    have hd : d ∈ F.carrier S₀ := (hfib S₀ _ _).mp (hax.trans hbx.symm)
    apply (hbr.2 n n').mp
    refine ⟨b⁻¹ * a, mul_mem (inv_mem hb) ha, d, hd, ?_⟩
    change n'.val = (b⁻¹ * a) * n.val * d
    dsimp only [d]
    group
  refine ⟨fun n => ⟨BruhatFlagCell.parametrization_isImmersion p u v q hf n.val huc, horbit n⟩, ?_⟩
  let cells : relativeWeylGroup i → Set (S₀ ⟶ Q) :=
    Quotient.lift cell (fun n n' h => hEq n n' (Quotient.sound h))
  refine ⟨cells, fun n => rfl, ?_⟩
  intro x
  obtain ⟨g, hg⟩ := hLift x
  obtain ⟨n, hn, a, ha, b, hb, hab⟩ := hbr.1 g
  let m : normalizerPoints i := ⟨n, hn⟩
  have hx : x ∈ cell m := (horbit m x).mpr ⟨a, ha, by
    have hqg : (a * n * b) ≫ q = x := hab ▸ hg
    have hb' : b ∈ (SubgroupFunctor.range p).carrier S₀ := by rwa [hp.2]
    rw [BruhatFlagCell.quotient_mul p q hf _ hb'] at hqg
    exact hqg⟩
  refine ⟨QuotientGroup.mk m, hx, ?_⟩
  intro w hw
  obtain ⟨n', rfl⟩ := QuotientGroup.mk_surjective w
  exact (hSep m n' x hx hw).symm

end Langlands.GroupScheme
