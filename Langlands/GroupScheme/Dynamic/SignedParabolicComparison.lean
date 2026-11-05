import Langlands.GroupScheme.Dynamic.SignedNoncontainment
import Langlands.GroupScheme.Dynamic.LeviCocharacterCombination

/-! # Signed dynamic parabolics from actual contracting subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic

set_option backward.isDefEq.respectTransparency false

section Centralizers

variable {S : Scheme.{u}} {G : GroupScheme S} {T : CommGroupScheme S}

/-- Reversing a cocharacter of a commutative group preserves its actual
centralizer on every test scheme. -/
theorem centralizer_groupHom_neg (i : T.toGrp ⟶ G) (ν : cocharacterLattice T) :
    centralizer (CommGroupScheme.groupHom (-ν) ≫ i) =
      centralizer (CommGroupScheme.groupHom ν ≫ i) := by
  have hle : ∀ eta : cocharacterLattice T,
      centralizer (CommGroupScheme.groupHom eta ≫ i) ≤
        centralizer (CommGroupScheme.groupHom (-eta) ≫ i) := by
    intro eta
    have heta : Gm.powerHom S (-1) ≫ eta = -eta := by
      simp only [Gm.powerHom_apply, neg_one_zsmul, Preadditive.neg_comp, Category.id_comp]
    have hc := centralizer_le_precomp (CommGroupScheme.groupHom eta ≫ i)
      (CommGroupScheme.groupHom (Gm.powerHom S (-1)))
    rw [← Category.assoc] at hc
    change centralizer (CommGroupScheme.groupHom eta ≫ i) ≤
      centralizer (CommGroupScheme.groupHom (Gm.powerHom S (-1) ≫ eta) ≫ i) at hc
    rwa [heta] at hc
  exact le_antisymm (by simpa only [neg_neg] using hle (-ν)) (hle ν)

end Centralizers

section OppositeTop

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [Smooth G.X.hom] [ConnectedSpace G.X.left]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- If one actual contracting subgroup is trivial, the opposite dynamic
parabolic is the entire smooth connected affine group. -/
theorem parabolic_neg_eq_top_of_unipotent_eq_bot
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
    (hU : unipotent (CommGroupScheme.groupHom ν ≫ i) = ⊥) :
    parabolic (CommGroupScheme.groupHom (-ν) ≫ i) = ⊤ := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let χ := CommGroupScheme.groupHom (-ν) ≫ i
  let P := Affine.parabolicScheme χ
  let p : P ⟶ G := Affine.parabolicHom χ
  have hp : (parabolic χ).IsRepresentedBy p := Affine.isRepresentedBy_parabolicHom χ
  have hpc : IsClosedSubgroup p := Affine.isClosedSubgroup_parabolicHom χ
  let : Mono p.hom.hom := hp.1
  let : IsAffineHom P.X.hom := hpc.isAffineHom
  let : Smooth P.X.hom := (dynamicSmooth k G χ P p).1 hp
  have htop : RelativeRoot.tangentSubmodule (SubgroupFunctor.range p) = ⊤ := by
    rw [hp.2]
    apply top_unique
    have hs := RelativeRoot.sup_signed_dynamic_tangentSubmodules hT i ν
    rw [hU, RelativeRoot.tangentSubmodule_bot, bot_sup_eq] at hs
    rw [← hs]
    apply sup_le
    · apply RelativeRoot.tangentSubmodule_mono
      rw [← centralizer_groupHom_neg i ν]
      exact centralizer_le_parabolic χ
    · exact RelativeRoot.tangentSubmodule_mono (unipotent_le_parabolic χ)
  let : IsIso p := Lie.isIso_of_surjective_targetMapLinear p hpc (by
    apply LinearMap.range_eq_top.mp
    rwa [← RelativeRoot.tangentSubmodule_range p])
  apply SubgroupFunctor.ext
  intro Y
  apply top_unique
  intro g _
  rw [← hp.2]
  refine SubgroupFunctor.mem_range.mpr ⟨g ≫ (inv p).hom.hom, ?_⟩
  rw [Category.assoc, ← Grp.comp_hom_hom, IsIso.inv_hom_id, Grp.id_hom_hom,
    Category.comp_id]

/-- The actual opposite parabolic representative is isomorphic to the ambient
smooth connected group when the positive contracting subgroup is trivial. -/
def negativeParabolicIsoOfUnipotentEqBot
    (hT : IsSplitTorus T.toGrp) (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
    (hU : unipotent (CommGroupScheme.groupHom ν ≫ i) = ⊥) :
    letI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    Affine.parabolicScheme (CommGroupScheme.groupHom (-ν) ≫ i) ≅ G := by
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hp : (⊤ : SubgroupFunctor G).IsRepresentedBy
      (Affine.parabolicHom (CommGroupScheme.groupHom (-ν) ≫ i)) := by
    rw [← parabolic_neg_eq_top_of_unipotent_eq_bot hT i ν hU]
    exact Affine.isRepresentedBy_parabolicHom _
  have hid : (⊤ : SubgroupFunctor G).IsRepresentedBy (𝟙 G) := by
    refine ⟨inferInstance, ?_⟩
    apply SubgroupFunctor.ext
    intro Y
    apply top_unique
    intro g _
    exact SubgroupFunctor.mem_range.mpr ⟨g, Category.comp_id g⟩
  exact hp.isoOfIsRepresentedBy hid

end OppositeTop

section LimitDecomposition

variable {S : Scheme.{u}} {G : GroupScheme S} [IsSeparated G.X.hom]

/-- Containment of the contracting subgroup and centralizer gives containment
of the dynamic parabolic on every original test scheme. -/
theorem parabolic_le_of_unipotent_le_of_centralizer_le
    (χ : (Gm S).toGrp ⟶ G) (F : SubgroupFunctor G)
    (hU : unipotent χ ≤ F) (hZ : centralizer χ ≤ F) : parabolic χ ≤ F := by
  intro Y g hg
  have hu := hU Y (mul_inv_limit_mem_unipotent χ ⟨g, hg⟩)
  have hz := hZ Y (limit_mem_centralizer χ ⟨g, hg⟩)
  simpa only [inv_mul_cancel_right] using (F.carrier Y).mul_mem hu hz

end LimitDecomposition

end Langlands.GroupScheme.Dynamic
