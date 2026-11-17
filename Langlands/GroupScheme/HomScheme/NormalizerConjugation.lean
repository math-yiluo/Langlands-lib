import Langlands.GroupScheme.HomScheme.ConjugationMap
import Langlands.GroupScheme.SubgroupFunctor.NormalizerBaseChange
import Langlands.GroupScheme.Torus.WeylPointTransport

/-! # Normalizer points as source automorphisms of conjugation families -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme.HomScheme

variable {S : Scheme.{u}} {G : GroupScheme S} {H : CommGroupScheme S}
  (i : H.toGrp ⟶ G) [Mono i.hom.hom.left] {T : Over S}

/-- A point normalizes the subgroup if and only if its conjugation family is
obtained by precomposing the fixed embedding with a source automorphism. -/
theorem exists_sourceIso_conjugationFamily_iff (g : T ⟶ G.X) :
    (∃ e : (GroupScheme.baseChange T.hom).obj H.toGrp ≅
        (GroupScheme.baseChange T.hom).obj H.toGrp,
      conjugationFamily i g = e.hom ≫ (GroupScheme.baseChange T.hom).map i) ↔
        g ∈ (torusNormalizer i).carrier T := by
  let B := GroupScheme.baseChange T.hom
  let A := (CommGroupScheme.baseChange T.hom).obj H
  let j : A.toGrp ⟶ B.obj G := B.map i
  let p := RelativeLevi.pulledBackPoint G T g
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  let : Mono j.hom.hom := by
    change Mono ((Over.pullback T.hom).map i.hom.hom)
    infer_instance
  have hp : p ∈ (torusNormalizer j).carrier (Over.mk (𝟙 T.left)) ↔
      g ∈ (torusNormalizer i).carrier T := by
    dsimp only [j]
    rw [torusNormalizer_baseChange, mem_baseChange_basePoints_iff,
      RelativeLevi.baseChangeBasePointsEquiv_pulledBackPoint]
    let g' : Over.mk T.hom ⟶ G.X := Over.homMk g.left (Over.w g)
    let t : Over.mk T.hom ≅ T := Over.isoMk (Iso.refl T.left) (by simp)
    change g' ∈ (torusNormalizer i).carrier _ ↔ g ∈ (torusNormalizer i).carrier T
    constructor
    · intro hg
      have ht : t.inv ≫ g' = g := Over.OverMorphism.ext (Category.id_comp _)
      rw [← ht]
      exact (torusNormalizer i).comp_mem t.inv hg
    · intro hg
      have ht : t.hom ≫ g = g' := Over.OverMorphism.ext (Category.id_comp _)
      rw [← ht]
      exact (torusNormalizer i).comp_mem t.hom hg
  constructor
  · rintro ⟨e, he⟩
    apply hp.mp
    apply normalizerPoints_le_torusNormalizer j
    let σ : A ≅ A :=
      { hom := Additive.ofMul e.hom
        inv := Additive.ofMul e.inv
        hom_inv_id := congrArg Additive.ofMul e.hom_inv_id
        inv_hom_id := congrArg Additive.ofMul e.inv_hom_id }
    exact ⟨σ, he⟩
  · intro hg
    let : Mono j.hom.hom.left := inferInstance
    obtain ⟨σ, hσ⟩ := torusNormalizer_le_normalizerPoints j (hp.mpr hg)
    let e : B.obj H.toGrp ≅ B.obj H.toGrp :=
      { hom := CommGroupScheme.groupHom σ.hom
        inv := CommGroupScheme.groupHom σ.inv
        hom_inv_id := congrArg CommGroupScheme.groupHom σ.hom_inv_id
        inv_hom_id := congrArg CommGroupScheme.groupHom σ.inv_hom_id }
    exact ⟨e, hσ⟩

/-- Choose the actual source automorphism induced by a full normalizer point. -/
def normalizerSourceIso (g : T ⟶ G.X) (hg : g ∈ (torusNormalizer i).carrier T) :
    {e : (GroupScheme.baseChange T.hom).obj H.toGrp ≅
        (GroupScheme.baseChange T.hom).obj H.toGrp //
      conjugationFamily i g = e.hom ≫ (GroupScheme.baseChange T.hom).map i} :=
  ⟨_, ((exists_sourceIso_conjugationFamily_iff i g).mpr hg).choose_spec⟩

end Langlands.GroupScheme.HomScheme
