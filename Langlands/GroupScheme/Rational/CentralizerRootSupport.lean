import Langlands.GroupScheme.Rational.CentralRootRestriction
import Langlands.GroupScheme.Rational.TorusCentralizerFactorization
import Langlands.GroupScheme.Rational.RootAnnihilatorCentralityProof
import Langlands.GroupScheme.Lie.Functoriality
import Langlands.GroupScheme.Dynamic.ClosedSubgroup

/-! # Centralizer comparisons from actual zero-root support -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Represented

variable {S : Scheme.{u}} {G H : GroupScheme S} {T : CommGroupScheme S}
    {F : SubgroupFunctor G} {j : H ⟶ G} {i : T.toGrp ⟶ G}

/-- The subgroup functor centralizing both cocharacters of the same torus. -/
def cocharacterCentralizerIntersection (i : T.toGrp ⟶ G)
    (zeta eta : cocharacterLattice T) : SubgroupFunctor G :=
  Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i) ⊓
    Dynamic.centralizer (CommGroupScheme.groupHom eta ≫ i)

@[simp]
theorem mem_cocharacterCentralizerIntersection (i : T.toGrp ⟶ G)
    (zeta eta : cocharacterLattice T) {U : Over S} {g : U ⟶ G.X} :
    g ∈ (cocharacterCentralizerIntersection i zeta eta).carrier U ↔
      g ∈ (Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i)).carrier U ∧
        g ∈ (Dynamic.centralizer (CommGroupScheme.groupHom eta ≫ i)).carrier U :=
  Iff.rfl

/-- Centrality after factoring through a represented subgroup is equivalent to
containment of that subgroup in the ambient dynamic centralizer. -/
theorem isCentral_comp_iff_le_dynamicCentralizer
    (hj : F.IsRepresentedBy j) (iH : T.toGrp ⟶ H) (hcomp : iH ≫ j = i)
    (zeta : cocharacterLattice T) :
    IsCentral (CommGroupScheme.groupHom zeta ≫ iH) ↔
      F ≤ Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i) := by
  have : Mono j.hom.hom := hj.1
  rw [isCentral_iff_dynamicCentralizer_eq_top,
    Dynamic.centralizer_eq_comap_of_mono (CommGroupScheme.groupHom zeta ≫ iH) j,
    Category.assoc, hcomp,
    ← SubgroupFunctor.range_le_iff_comap_eq_top, hj.2]

end Represented

section Roots

variable {k : Type u} [Field k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    [LocallyOfFiniteType H.X.hom]
    {F : SubgroupFunctor G} {j : H ⟶ G} {i : T.toGrp ⟶ G}

omit [LocallyOfFiniteType H.X.hom] in
/-- A relative root of a represented subgroup is an ambient relative root when
the same torus acts through the subgroup. -/
theorem relativeRoots_subset_of_factor
    (hj : F.IsRepresentedBy j) (iH : T.toGrp ⟶ H) (hcomp : iH ≫ j = i) :
    relativeRoots iH ⊆ relativeRoots i := by
  have : Mono j.hom.hom := hj.1
  simpa only [relativeRoots, hcomp] using roots_subset_comp j iH

omit [IsAffineHom G.X.hom] in
/-- Every actual root of a subgroup contained in a cocharacter centralizer has
zero integral pairing with that cocharacter. -/
theorem relativeRoot_pairing_eq_zero_of_le_dynamicCentralizer
    (hj : F.IsRepresentedBy j) (iH : T.toGrp ⟶ H) (hcomp : iH ≫ j = i)
    (zeta : cocharacterLattice T)
    (hle : F ≤ Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i))
    {alpha : characterLattice T} (halpha : alpha ∈ relativeRoots iH) :
    latticePairing T alpha zeta = 0 := by
  have hc := (isCentral_comp_iff_le_dynamicCentralizer hj iH hcomp zeta).2 hle
  have hz := root_restrict_eq_zero_of_isCentral iH zeta isSplitTorus_gm hc halpha
  simp only [latticePairing_apply, hz, map_zero]

end Roots

section Comparison

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]

/-- Actual zero-root support controls containment of cocharacter centralizers
on every test scheme. Connectedness of dynamic centralizers is the explicit
structural input; root-annihilator centrality and smoothness are proved inputs. -/
theorem dynamicCentralizer_le_of_root_zero_imp
    (hConn : DynamicConnectedStatement.{u}) (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) (zeta eta : cocharacterLattice T)
    (hzero : ∀ alpha ∈ relativeRoots i,
      latticePairing T alpha zeta = 0 → latticePairing T alpha eta = 0) :
    Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i) ≤
      Dynamic.centralizer (CommGroupScheme.groupHom eta ≫ i) := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let H := Dynamic.Affine.centralizerScheme (CommGroupScheme.groupHom zeta ≫ i)
  let j : H ⟶ G := Dynamic.Affine.centralizerHom (CommGroupScheme.groupHom zeta ≫ i)
  have hj : (Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i)).IsRepresentedBy j :=
    Dynamic.Affine.isRepresentedBy_centralizerHom _
  have hjc : IsClosedSubgroup j := Dynamic.Affine.isClosedSubgroup_centralizerHom _
  have : IsClosedImmersion j.hom.hom.left := hjc
  have : Smooth H.X.hom := (dynamicSmooth k G _ H j).2.1 hj
  have : ConnectedSpace H.X.left := ((hConn k G _ H j).2 inferInstance).2 hj
  have : IsAffineHom H.X.hom := by
    rw [← Over.w j.hom.hom]
    infer_instance
  have ht : SubgroupFunctor.range i ≤
      Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i) :=
    (range_le_torusCentralizer i).trans (torusCentralizer_le_dynamicCentralizer i _)
  let iH : T.toGrp ⟶ H := hj.factorHom i ht
  have hcomp : iH ≫ j = i := hj.factorHom_comp i ht
  have hann : ∀ alpha ∈ relativeRoots iH, latticePairing T alpha eta = 0 := by
    intro alpha halpha
    exact hzero alpha (relativeRoots_subset_of_factor hj iH hcomp halpha)
      (relativeRoot_pairing_eq_zero_of_le_dynamicCentralizer hj iH hcomp zeta le_rfl halpha)
  exact (isCentral_comp_iff_le_dynamicCentralizer hj iH hcomp eta).1
    (rootAnnihilatorCentrality k H T hT iH eta hann)

/-- Simultaneous zero-root support controls containment of an intersection of
two cocharacter centralizers on every test scheme. -/
theorem dynamicCentralizer_inf_le_of_root_zero_imp
    (hConn : DynamicConnectedStatement.{u}) (hT : IsSplitTorus T.toGrp)
    (i : T.toGrp ⟶ G) (zeta eta theta : cocharacterLattice T)
    (hzero : ∀ alpha ∈ relativeRoots i,
      latticePairing T alpha zeta = 0 → latticePairing T alpha eta = 0 →
        latticePairing T alpha theta = 0) :
    cocharacterCentralizerIntersection i zeta eta ≤
      Dynamic.centralizer (CommGroupScheme.groupHom theta ≫ i) := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let H := Dynamic.Affine.centralizerScheme (CommGroupScheme.groupHom zeta ≫ i)
  let j : H ⟶ G := Dynamic.Affine.centralizerHom (CommGroupScheme.groupHom zeta ≫ i)
  have hj : (Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i)).IsRepresentedBy j :=
    Dynamic.Affine.isRepresentedBy_centralizerHom _
  have hjc : IsClosedSubgroup j := Dynamic.Affine.isClosedSubgroup_centralizerHom _
  have : IsClosedImmersion j.hom.hom.left := hjc
  have : Mono j.hom.hom := hj.1
  have : Smooth H.X.hom := (dynamicSmooth k G _ H j).2.1 hj
  have : ConnectedSpace H.X.left := ((hConn k G _ H j).2 inferInstance).2 hj
  have : IsAffineHom H.X.hom := by
    rw [← Over.w j.hom.hom]
    infer_instance
  have ht : SubgroupFunctor.range i ≤
      Dynamic.centralizer (CommGroupScheme.groupHom zeta ≫ i) :=
    (range_le_torusCentralizer i).trans (torusCentralizer_le_dynamicCentralizer i _)
  let iH : T.toGrp ⟶ H := hj.factorHom i ht
  have hcomp : iH ≫ j = i := hj.factorHom_comp i ht
  have hle := dynamicCentralizer_le_of_root_zero_imp hConn hT iH eta theta (by
    intro alpha halpha heta
    exact hzero alpha (relativeRoots_subset_of_factor hj iH hcomp halpha)
      (relativeRoot_pairing_eq_zero_of_le_dynamicCentralizer hj iH hcomp zeta le_rfl halpha)
      heta)
  have hrestrict (c : cocharacterLattice T) :
      Dynamic.centralizer (CommGroupScheme.groupHom c ≫ iH) =
        (Dynamic.centralizer (CommGroupScheme.groupHom c ≫ i)).comap j := by
    rw [Dynamic.centralizer_eq_comap_of_mono (CommGroupScheme.groupHom c ≫ iH) j,
      Category.assoc, hcomp]
  intro U g hg
  obtain ⟨x, hx⟩ := SubgroupFunctor.mem_range.mp (hj.2.symm ▸ hg.1)
  have hxeta : x ∈ (Dynamic.centralizer (CommGroupScheme.groupHom eta ≫ iH)).carrier U := by
    rw [hrestrict, SubgroupFunctor.mem_comap, hx]
    exact hg.2
  have hxtheta := hle U hxeta
  rw [hrestrict, SubgroupFunctor.mem_comap, hx] at hxtheta
  exact hxtheta

end Comparison

end Langlands.GroupScheme
