import Langlands.GroupScheme.Torus.MultiplicativeTypeEtaleLiftStatement
import Langlands.GroupScheme.HomScheme.SmoothMultiplicativeTypeSubgroupRepresentabilityStatement
import Langlands.GroupScheme.RepresentedSubgroup
import Langlands.AlgebraicGeometry.SmoothPointedEtaleSectionConstruction

/-! # Multiplicative-type lifting from smooth subgroup moduli -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option backward.defeqAttrib.useBackward false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

open TorusSubgroupModuli MultiplicativeTypeSubgroupModuli

/-- Equality of actual subgroup functors recovers the exact fibre inclusion,
with no hypothesis that the source descends to the original base. -/
theorem recover_subgroup_fibre_inclusion {S : Scheme.{u}} {G : GroupScheme S}
    {U F : Scheme.{u}} (p : U ⟶ S) (c : F ⟶ S) (b : F ⟶ U)
    (hb : b ≫ p = c) (H : GroupScheme U) (H₀ : GroupScheme F)
    (i : H ⟶ (baseChange p).obj G) (i₀ : H₀ ⟶ (baseChange c).obj G)
    (hi : IsClosedSubgroup i) (hi₀ : IsClosedSubgroup i₀)
    (hr : evaluate i (show Over.mk c ⟶ Over.mk p from Over.homMk b hb) =
      SubgroupFunctor.range i₀) :
    ∃ e : (baseChange b).obj H ≅ H₀,
      (baseChange b).map i ≫ (baseChangeCompIso p b G).inv ≫
          (eqToIso (congrArg (fun f => (baseChange f).obj G) hb)).hom =
        e.hom ≫ i₀ := by
  let bU : Over.mk c ⟶ Over.mk p := Over.homMk b hb
  have hib : IsClosedSubgroup (familyHom i bU) :=
    @isClosedSubgroup_familyHom S G (Over.mk p) (Over.mk c) H i hi bU
  let : IsClosedImmersion (familyHom i bU).hom.hom.left := hib
  let : IsClosedImmersion i₀.hom.hom.left := hi₀
  have hr' : (SubgroupFunctor.range i₀).IsRepresentedBy (familyHom i bU) :=
    ⟨Over.mono_of_mono_left _, hr⟩
  have hi' : (SubgroupFunctor.range i₀).IsRepresentedBy i₀ :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  let e : (baseChange b).obj H ≅ H₀ := hr'.isoOfIsRepresentedBy hi'
  refine ⟨e, ?_⟩
  have he : e.hom ≫ i₀ = familyHom i bU := hr'.isoOfIsRepresentedBy_hom_comp hi'
  dsimp only [bU, familyHom, Descent.pullbackComparison, Iso.trans_hom, Iso.symm_hom,
    Over.mk_hom, Over.homMk_left, Over.Hom.left, Over.homMk,
    CostructuredArrow.homMk] at he
  simpa only [Category.assoc] using he.symm

/-- The actual fibre-source isomorphism supplied by equality of the two subgroup functors. -/
def subgroupFibreIso {S : Scheme.{u}} {G : GroupScheme S}
    {U F : Scheme.{u}} (p : U ⟶ S) (c : F ⟶ S) (b : F ⟶ U)
    (hb : b ≫ p = c) (H : GroupScheme U) (H₀ : GroupScheme F)
    (i : H ⟶ (baseChange p).obj G) (i₀ : H₀ ⟶ (baseChange c).obj G)
    (hi : IsClosedSubgroup i) (hi₀ : IsClosedSubgroup i₀)
    (hr : evaluate i (show Over.mk c ⟶ Over.mk p from Over.homMk b hb) =
      SubgroupFunctor.range i₀) : (baseChange b).obj H ≅ H₀ :=
  Classical.choose (recover_subgroup_fibre_inclusion p c b hb H H₀ i i₀ hi hi₀ hr)

/-- The chosen fibre-source isomorphism identifies the specified actual inclusions. -/
theorem subgroupFibreIso_hom_comp {S : Scheme.{u}} {G : GroupScheme S}
    {U F : Scheme.{u}} (p : U ⟶ S) (c : F ⟶ S) (b : F ⟶ U)
    (hb : b ≫ p = c) (H : GroupScheme U) (H₀ : GroupScheme F)
    (i : H ⟶ (baseChange p).obj G) (i₀ : H₀ ⟶ (baseChange c).obj G)
    (hi : IsClosedSubgroup i) (hi₀ : IsClosedSubgroup i₀)
    (hr : evaluate i (show Over.mk c ⟶ Over.mk p from Over.homMk b hb) =
      SubgroupFunctor.range i₀) :
    (baseChange b).map i ≫ (baseChangeCompIso p b G).inv ≫
        (eqToIso (congrArg (fun f => (baseChange f).obj G) hb)).hom =
      (subgroupFibreIso p c b hb H H₀ i i₀ hi hi₀ hr).hom ≫ i₀ :=
  Classical.choose_spec (recover_subgroup_fibre_inclusion p c b hb H H₀ i i₀ hi hi₀ hr)

/-- Smooth moduli of actual closed multiplicative-type subgroups give the exact
pointed étale lifting statement, including its fibre inclusion equation. -/
theorem multiplicativeTypeEtaleLift_of_smoothSubgroupModuli
    (hmod : SmoothMultiplicativeTypeSubgroupRepresentabilityStatement.{u}) :
    MultiplicativeTypeEtaleLiftStatement.{u} := by
  intro S G _ _ s H₀ hH₀ i₀ hi₀
  let c := S.fromSpecResidueField s
  obtain ⟨M, K, j, hj, hK, hM, huni⟩ := hmod S G
  let : Smooth M.hom := hM
  obtain ⟨x, hx, -⟩ :=
    huni (Over.mk c) (SubgroupFunctor.range i₀)
      (MultiplicativeTypeSubgroupModuli.isAdmissible_range i₀ hi₀ hH₀)
  obtain ⟨U, p, b, a, hp, hb, ha, hba⟩ :=
    Langlands.AlgebraicGeometry.exists_pointed_etale_section M.hom s x.left (Over.w x)
  let uM : Over.mk p ⟶ M := Over.homMk a ha
  let bU : Over.mk c ⟶ Over.mk p := Over.homMk b hb
  let H := (baseChange a).obj K
  let i : H ⟶ (baseChange p).obj G := familyHom j uM
  have hi : IsClosedSubgroup i := isClosedSubgroup_familyHom j hj uM
  have hbU : bU ≫ uM = x := by
    apply Over.OverMorphism.ext
    exact hba
  have hieval : evaluate i bU = SubgroupFunctor.range i₀ := by
    change evaluate (familyHom j uM) bU = _
    rw [evaluate_comp, hbU, hx]
  refine ⟨U, p, hp, b, hb, H, hK.baseChange a, i, hi, ?_⟩
  exact @recover_subgroup_fibre_inclusion S G U (Spec (S.residueField s))
    p c b hb H H₀ i i₀ hi hi₀ hieval

end Langlands.GroupScheme
