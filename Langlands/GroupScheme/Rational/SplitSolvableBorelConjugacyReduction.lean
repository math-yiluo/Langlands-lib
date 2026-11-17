import Langlands.GroupScheme.Rational.SplitSolvableBorelConjugacyStatement
import Langlands.GroupScheme.IdentityComponent
import Langlands.GroupScheme.Absolute.BorelPromotion
import Langlands.GroupScheme.ConjugacyBaseChange
import Langlands.GroupScheme.Rational.LeviFactorization
import Langlands.GroupScheme.Rational.ParabolicAmbientTransport

/-! # Split Borel conjugacy: reduction to a connected ambient group

Clause (a) of `SplitSolvableBorelConjugacyStatement` for a smooth affine group `G` that need not
be connected follows from clause (a) for its identity component `G⁰`. Clause (b) follows from
clause (a) and the maximality of the second Borel subgroup.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace SplitSolvableBorelConjugacy

variable {k : Type u} [Field k]

/-- A geometric Borel subgroup of `G` with connected source factors through `G⁰`, and the
factorization is a geometric Borel subgroup of `G⁰`. -/
theorem isGeometricBorelSubgroup_factor (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] {B : GroupScheme (Spec (CommRingCat.of k))}
    [ConnectedSpace B.X.left] {b : B ⟶ G} (hb : IsGeometricBorelSubgroup b) :
    IsGeometricBorelSubgroup (IdentityComponent.factor G b) := by
  refine ⟨IsBorelSubgroup.of_comp (IdentityComponent.isClosedSubgroup_identityComponentι G)
    (by rw [IdentityComponent.factor_identityComponentι]; exact hb.1), ?_⟩
  let F := GroupScheme.baseChange (toAlgebraicClosure k)
  have hι : IsClosedSubgroup (F.map (identityComponentι G)) :=
    (inferInstance : IsClosedImmersion ((GroupScheme.baseChange
      (IdentityComponent.specMap (algebraMap k (AlgebraicClosure k)))).map
        (identityComponentι G)).hom.hom.left)
  refine IsBorelSubgroup.of_comp hι ?_
  rw [← F.map_comp, IdentityComponent.factor_identityComponentι]
  exact hb.2

/-- Clause (a) for a smooth affine group follows from clause (a) for its identity component. -/
theorem exists_range_le_of_identityComponent (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    {B : GroupScheme (Spec (CommRingCat.of k))} [ConnectedSpace B.X.left] {b : B ⟶ G}
    {H : GroupScheme (Spec (CommRingCat.of k))} [ConnectedSpace H.X.left] (h : H ⟶ G)
    (g₀ : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ (identityComponent G).X)
    (hg₀ : SubgroupFunctor.range (IdentityComponent.factor G h) ≤
      SubgroupFunctor.range (IdentityComponent.factor G b ≫
        ((identityComponent G).innerIso g₀).hom)) :
    SubgroupFunctor.range h ≤
      SubgroupFunctor.range (b ≫ (G.innerIso (g₀ ≫ (identityComponentι G).hom.hom)).hom) := by
  have h' := SubgroupFunctor.range_comp_mono hg₀ (identityComponentι G)
  rwa [IdentityComponent.factor_identityComponentι, Category.assoc, innerIso_hom_comp,
    ← Category.assoc, IdentityComponent.factor_identityComponentι] at h'

/-- Clause (b) from clause (a): if the second split Borel subgroup is contained in a conjugate
of the first, the two are equal by maximality of the second. -/
theorem range_eq_of_range_le {G B B' : GroupScheme (Spec (CommRingCat.of k))}
    {b : B ⟶ G} {b' : B' ⟶ G} (hb : IsBorelSubgroup b) (hb' : IsBorelSubgroup b')
    (g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)
    (hle : SubgroupFunctor.range b' ≤ SubgroupFunctor.range (b ≫ (G.innerIso g).hom)) :
    SubgroupFunctor.range (b ≫ (G.innerIso g).hom) = SubgroupFunctor.range b' := by
  let c := b ≫ (G.innerIso g).hom
  have hc : IsClosedSubgroup c := hb.isClosedSubgroup.comp_iso (G.innerIso g)
  have : IsClosedImmersion c.hom.hom.left := hc
  have : IsClosedImmersion b'.hom.hom.left := hb'.isClosedSubgroup
  have : Mono c.hom.hom := Over.mono_of_mono_left _
  have : Mono b'.hom.hom := Over.mono_of_mono_left _
  let f := SubgroupFunctor.factorOfRangeLE hle
  have hf : f ≫ c = b' := SubgroupFunctor.factorOfRangeLE_comp hle
  have : IsIso f := hb'.maximal B c f hc hb.smooth hb.connectedSpace hb.isSolvableGroupScheme hf
  refine le_antisymm (SubgroupFunctor.range_le_of_factor (inv f) ?_) hle
  rw [← hf, IsIso.inv_hom_id_assoc]

/-- The full statement follows from clause (a) for connected smooth affine groups. -/
theorem splitSolvableBorelConjugacy_of_connected
    (hconn : ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
      [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
      (B : GroupScheme (Spec (CommRingCat.of k))) (b : B ⟶ G),
      IsGeometricBorelSubgroup b → IsSplitSolvableGroupScheme B →
        ∀ (H : GroupScheme (Spec (CommRingCat.of k))) (h : H ⟶ G),
          IsClosedSubgroup h → IsSplitSolvableGroupScheme H →
            ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
              SubgroupFunctor.range h ≤ SubgroupFunctor.range (b ≫ (G.innerIso g).hom)) :
    SplitSolvableBorelConjugacyStatement.{u} := by
  intro k _ G _ _ B b hb hB
  have : ConnectedSpace B.X.left := hB.connectedSpace
  have ha : ∀ (H : GroupScheme (Spec (CommRingCat.of k))) (h : H ⟶ G),
      IsClosedSubgroup h → IsSplitSolvableGroupScheme H →
        ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
          SubgroupFunctor.range h ≤ SubgroupFunctor.range (b ≫ (G.innerIso g).hom) := by
    intro H h hh hH
    have : ConnectedSpace H.X.left := hH.connectedSpace
    have hh₀ : IsClosedSubgroup (IdentityComponent.factor G h) :=
      IsClosedSubgroup.of_comp (IdentityComponent.isClosedSubgroup_identityComponentι G)
        (by rw [IdentityComponent.factor_identityComponentι]; exact hh)
    obtain ⟨g₀, hg₀⟩ := hconn k (identityComponent G) B (IdentityComponent.factor G b)
      (isGeometricBorelSubgroup_factor G hb) hB H (IdentityComponent.factor G h) hh₀ hH
    exact ⟨g₀ ≫ (identityComponentι G).hom.hom,
      exists_range_le_of_identityComponent G h g₀ hg₀⟩
  refine ⟨ha, fun B' b' hb' hB' => ?_⟩
  obtain ⟨g, hg⟩ := ha B' b' hb'.1.isClosedSubgroup hB'
  exact ⟨g, range_eq_of_range_le hb.1 hb'.1 g hg⟩

end SplitSolvableBorelConjugacy

end Langlands.GroupScheme
