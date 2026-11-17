import Langlands.GroupScheme.Absolute.SolvableUnipotentFactorizationProof
import Langlands.GroupScheme.Absolute.SolvableMaximalTorusSemidirectOfSection
import Langlands.GroupScheme.Absolute.SolvableTorusQuotientProof
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof
import Langlands.GroupScheme.Torus.SplitOfDomination
import Langlands.GroupScheme.Torus.WeylGroupSchemeQuotientPoints

/-! # Images of maximal tori in solvable groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.QuotientTorusImage

variable {k : Type u} [Field k]

/-- A maximal torus and its maximal-torus image under a homomorphism, with a surjective
factor map realizing the commuting image square. -/
def IsMaximalTorusImage
    {B C : GroupScheme (Spec (CommRingCat.of k))}
    {T S : CommGroupScheme (Spec (CommRingCat.of k))}
    (q : B ⟶ C) (t : T.toGrp ⟶ B) (s : S.toGrp ⟶ C) : Prop :=
  IsMaximalTorus t ∧ IsMaximalTorus s ∧
    ∃ f : T.toGrp ⟶ S.toGrp, Surjective f.hom.hom.left ∧ t ≫ q = f ≫ s

variable [IsAlgClosed k]

/-- A smooth closed image of a maximal torus under a surjective homomorphism of smooth
connected solvable affine groups is a maximal torus. -/
theorem isMaximalTorus_image_solvable
    {B C : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth B.X.hom] [IsAffineHom B.X.hom] [ConnectedSpace B.X.left]
    [Smooth C.X.hom] [IsAffineHom C.X.hom] [ConnectedSpace C.X.left]
    (hB : IsSolvableGroupScheme B) (hC : IsSolvableGroupScheme C)
    (q : B ⟶ C) (hq : Surjective q.hom.hom.left)
    {T S : CommGroupScheme (Spec (CommRingCat.of k))}
    (t : T.toGrp ⟶ B) (s : S.toGrp ⟶ C) (f : T.toGrp ⟶ S.toGrp)
    (hs : IsClosedSubgroup s) (hSsm : Smooth S.X.hom)
    (hf : Surjective f.hom.hom.left) (hcomm : t ≫ q = f ≫ s)
    (ht : IsMaximalTorus t) : IsMaximalTorus s := by
  let : Smooth S.X.hom := hSsm
  let : IsAffineHom S.X.hom := hs.isAffineHom
  let : IsReduced S.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field k S.X.left S.X.hom
  let : Surjective f.hom.hom.left := hf
  have hT := ht.1.isSplitTorus_of_finiteGaloisSplitting torusFiniteGaloisSplitting
  have hS : IsSplitTorus S.toGrp := hT.of_schematicallyDominant_hom f
    (IsSchemeTheoreticallyDominant.of_isDominant _)
  obtain ⟨U, D, a, d, ha, hUsm, hUconn, hU, hn, hd, hD⟩ :=
    solvableTorusQuotient k C hC
  let : IsAffineHom U.X.hom := ha.isAffineHom
  let : LocallyOfFiniteType U.X.hom := ha.locallyOfFiniteType
  let : Smooth D.X.hom := hD.smooth
  have hker := hd.2.2.2
  have hsmono : Mono s.hom.hom := by
    let : Mono s.hom.hom.left := hs.mono
    exact Over.mono_of_mono_left _
  have hsDmono : Mono (s ≫ d).hom.hom :=
    mono_comp_of_inf_eq_bot hsmono hker
      (range_inf_eq_bot_of_isSplitTorus_of_isUnipotent unipotentClosedSubgroup s hs hS a hU)
  have hsDsurj : Function.Surjective (rationalPoints.map (s ≫ d)) := by
    intro z
    obtain ⟨c, hc⟩ := rationalPoints.map_surjective_of_surjective d hd.2.1 z
    obtain ⟨b, hb⟩ := rationalPoints.map_surjective_of_surjective q hq c
    obtain ⟨V, v, hv, hVsm, hVconn, hV, hvn, hfac⟩ :=
      solvableUnipotentFactorization k B hB T t ht
    obtain ⟨x, y, hxy⟩ := hfac b
    refine ⟨y ≫ f.hom.hom, ?_⟩
    have hzero := hV.comp_eq_one_of_isSplitTorus hD (v ≫ q ≫ d)
      (Over.mk (𝟙 (Spec (CommRingCat.of k)))) x
    have hprod := congrArg (fun b => b ≫ q.hom.hom ≫ d.hom.hom) hxy
    simp only [MonObj.mul_comp, Category.assoc] at hprod
    change (x ≫ (v ≫ q ≫ d).hom.hom) * (y ≫ (t ≫ q ≫ d).hom.hom) =
      b ≫ q.hom.hom ≫ d.hom.hom at hprod
    rw [hzero, one_mul] at hprod
    have hpath : f ≫ s ≫ d = t ≫ q ≫ d := by
      rw [← Category.assoc f s d, ← hcomm, Category.assoc]
    change y ≫ f.hom.hom ≫ (s ≫ d).hom.hom = z
    rw [← Grp.comp_hom_hom, hpath, hprod]
    change (rationalPoints.map q b) ≫ d.hom.hom = z
    rw [hb]
    exact hc
  let : IsIso (s ≫ d) :=
    hS.isIso_of_mono_of_rationalPoints_surjective hD (s ≫ d) hsDmono hsDsurj
  refine ⟨hS.isTorus, hs, ?_⟩
  intro S' s' f' hS' hs' hfac
  have hS'split := hS'.isSplitTorus_of_finiteGaloisSplitting torusFiniteGaloisSplitting
  have hs'mono : Mono s'.hom.hom := by
    let : Mono s'.hom.hom.left := hs'.mono
    exact Over.mono_of_mono_left _
  have hs'Dmono : Mono (s' ≫ d).hom.hom :=
    mono_comp_of_inf_eq_bot hs'mono hker
      (range_inf_eq_bot_of_isSplitTorus_of_isUnipotent unipotentClosedSubgroup s' hs'
        hS'split a hU)
  let : Mono (s' ≫ d) := (Grp.forget _).mono_of_mono_map hs'Dmono
  let : IsSplitEpi (s' ≫ d) := IsSplitEpi.mk' ⟨inv (s ≫ d) ≫ f', by
    rw [Category.assoc, ← Category.assoc f' s' d, hfac, IsIso.inv_hom_id]⟩
  let : IsIso (s' ≫ d) := isIso_of_mono_of_isSplitEpi _
  have heq : f' = (s ≫ d) ≫ inv (s' ≫ d) := by
    apply (cancel_mono (s' ≫ d)).mp
    change f' ≫ (s' ≫ d) = (s ≫ d) ≫ inv (s' ≫ d) ≫ (s' ≫ d)
    rw [IsIso.inv_hom_id, Category.comp_id, ← Category.assoc f' s' d, hfac]
  rw [heq]
  infer_instance

/-- The solvable image theorem supplies the maximal-torus image relation with its given
surjective factor map. -/
theorem isMaximalTorusImage_solvable
    {B C : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth B.X.hom] [IsAffineHom B.X.hom] [ConnectedSpace B.X.left]
    [Smooth C.X.hom] [IsAffineHom C.X.hom] [ConnectedSpace C.X.left]
    (hB : IsSolvableGroupScheme B) (hC : IsSolvableGroupScheme C)
    (q : B ⟶ C) (hq : Surjective q.hom.hom.left)
    {T S : CommGroupScheme (Spec (CommRingCat.of k))}
    (t : T.toGrp ⟶ B) (s : S.toGrp ⟶ C) (f : T.toGrp ⟶ S.toGrp)
    (hs : IsClosedSubgroup s) (hSsm : Smooth S.X.hom)
    (hf : Surjective f.hom.hom.left) (hcomm : t ≫ q = f ≫ s)
    (ht : IsMaximalTorus t) : IsMaximalTorusImage q t s := by
  exact ⟨ht, isMaximalTorus_image_solvable hB hC q hq t s f hs hSsm hf hcomm ht,
    f, hf, hcomm⟩

end Langlands.GroupScheme.QuotientTorusImage
