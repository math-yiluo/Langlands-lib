import Langlands.GroupScheme.Rational.CrossTorusRootTransport
import Langlands.GroupScheme.Rational.CentralIsogenyRootPoints
import Langlands.GroupScheme.Rational.SplitTorusSurjection

/-! # Root subgroup transport through a supplied central-cover diagram -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

section ArbitraryBase

variable {B : Scheme.{u}} {S S' : CommGroupScheme B} {G H : GroupScheme B}
    (i : S.toGrp ⟶ G) (a : characterLattice S) (τ : S' ⟶ S)
    [Flat (CommGroupScheme.groupHom τ).hom.hom.left]
    [Surjective (CommGroupScheme.groupHom τ).hom.hom.left]

private abbrev flatSurjectiveProperty : MorphismProperty Scheme.{u} :=
  @Flat ⊓ @Surjective

set_option backward.isDefEq.respectTransparency false in
private theorem epi_whiskerLeft_torus_cover (U : Over B) :
    Epi (U ◁ (CommGroupScheme.groupHom τ).hom.hom) := by
  have hp : flatSurjectiveProperty (U ◁ (CommGroupScheme.groupHom τ).hom.hom).left := by
    exact MorphismProperty.pullbackMap (P := flatSurjectiveProperty)
      (by change flatSurjectiveProperty (𝟙 U.left); exact ⟨inferInstance, inferInstance⟩)
      ⟨inferInstance, inferInstance⟩
      (by simp) (Over.w (CommGroupScheme.groupHom τ).hom.hom).symm
  obtain ⟨hf, hs⟩ := hp
  let : Flat (U ◁ (CommGroupScheme.groupHom τ).hom.hom).left := hf
  let : Surjective (U ◁ (CommGroupScheme.groupHom τ).hom.hom).left := hs
  have : Epi (U ◁ (CommGroupScheme.groupHom τ).hom.hom).left :=
    Flat.epi_of_flat_of_surjective _
  exact Over.epi_of_epi_left _

/-- A flat surjective change of acting group preserves and reflects the same
full-torus orbit extension through the pulled-back character. -/
theorem isOrbitExtension_precomp_torus_hom_iff {U : Over B} {g : U ⟶ G.X}
    {v : U ⊗ AffineLine.scheme B ⟶ G.X} :
    IsOrbitExtension (CommGroupScheme.groupHom τ ≫ i) (τ ≫ a) g v ↔
      IsOrbitExtension i a g v := by
  constructor
  · intro hv
    have : Epi (U ◁ (CommGroupScheme.groupHom τ).hom.hom) :=
      epi_whiskerLeft_torus_cover τ U
    rw [IsOrbitExtension, orbit_precomp_torus_hom] at hv
    change U ◁ ((CommGroupScheme.groupHom τ).hom.hom ≫
      (CommGroupScheme.groupHom a).hom.hom ≫ AffineLine.unitInclusion B) ≫ v = _ at hv
    rw [whiskerLeft_comp, Category.assoc] at hv
    exact (cancel_epi (U ◁ (CommGroupScheme.groupHom τ).hom.hom)).mp hv
  · exact fun hv => hv.precomp_torus_hom i a τ

/-- The actual root subgroup functor is unchanged after a flat surjective
reparametrization of both the acting group and the character. -/
theorem subgroup_precomp_torus_hom :
    subgroup (CommGroupScheme.groupHom τ ≫ i) (τ ≫ a) = subgroup i a := by
  ext U g
  constructor
  · rintro ⟨v, hv, hv0⟩
    exact ⟨v, (isOrbitExtension_precomp_torus_hom_iff i a τ).mp hv, hv0⟩
  · exact mem_subgroup_precomp_torus_hom i a τ

/-- A commuting square with a flat surjective acting-group map carries source
root points to the target root subgroup on every test scheme. -/
theorem comp_mem_subgroup_of_flatSurjective_transport
    {j : S'.toGrp ⟶ H} (f : H ⟶ G)
    (h : j ≫ f = CommGroupScheme.groupHom τ ≫ i)
    {U : Over B} {g : U ⟶ H.X}
    (hg : g ∈ (subgroup j (τ ≫ a)).carrier U) :
    g ≫ f.hom.hom ∈ (subgroup i a).carrier U := by
  have hm := comp_mem_subgroup j (τ ≫ a) f hg
  rwa [h, subgroup_precomp_torus_hom i a τ] at hm

end ArbitraryBase

section Field

variable {k : Type u} [Field k]
    {S T : CommGroupScheme (Spec (CommRingCat.of k))}
    {C G : GroupScheme (Spec (CommRingCat.of k))}
    [C.X.left.IsSeparated] [G.X.left.IsSeparated]
    (q : C ⟶ G) (i : S.toGrp ⟶ C) (j : T.toGrp ⟶ G) (τ : S ⟶ T)
    [Flat (CommGroupScheme.groupHom τ).hom.hom.left]
    [Surjective (CommGroupScheme.groupHom τ).hom.hom.left]
    (h : i ≫ q = CommGroupScheme.groupHom τ ≫ j)
    (a : characterLattice T)

private theorem pullback_character_ne_zero (ha : a ≠ 0) : τ ≫ a ≠ 0 := by
  have : Epi (CommGroupScheme.groupHom τ).hom.hom.left :=
    Flat.epi_of_flat_of_surjective _
  have hinj := RealTorusSpace.characterRestrict_injective_of_epi τ
  intro hz
  apply ha
  apply hinj
  change τ ≫ a = τ ≫ (0 : characterLattice T)
  simpa using hz

/-- The actual central isogeny identifies rational root subgroups in a supplied
commuting diagram whose source acting group is a split torus and whose acting-group
map is flat and surjective. -/
def centralIsogenyRootTransportEquiv
    (hq : IsCentralIsogeny q) (hS : IsSplitTorus S.toGrp) (ha : a ≠ 0) :
    (subgroup i (τ ≫ a)).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) ≃*
      (subgroup j a).carrier (Over.mk (𝟙 _)) :=
  (centralIsogenyRootPointsEquiv q i (τ ≫ a) hq hS
    (pullback_character_ne_zero τ a ha)).trans
    (MulEquiv.subgroupCongr (congrArg
      (fun F : SubgroupFunctor G => F.carrier (Over.mk (𝟙 _))) (by
        rw [h]
        exact subgroup_precomp_torus_hom j a τ)))

@[simp] theorem centralIsogenyRootTransportEquiv_coe
    (hq : IsCentralIsogeny q) (hS : IsSplitTorus S.toGrp) (ha : a ≠ 0)
    (g : (subgroup i (τ ≫ a)).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k))))) :
    (centralIsogenyRootTransportEquiv q i j τ h a hq hS ha g :
      Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) =
      (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ C.X) ≫ q.hom.hom := rfl

end Field

end Langlands.GroupScheme.RelativeRoot
