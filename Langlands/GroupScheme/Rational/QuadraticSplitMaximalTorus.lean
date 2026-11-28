import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.GroupScheme.Rational.QuadraticOppositeBorelExistence
import Langlands.GroupScheme.Rational.QuasiSplitAdaptedSplitTorus
import Langlands.GroupScheme.Rational.SolvableMaximalTorusConjugacyProof
import Langlands.GroupScheme.SplitSolvableCanonicalExtension
import Langlands.GroupScheme.Rational.TorusCentralizerQuasiSplit
import Langlands.GroupScheme.Torus.FiniteGaloisSplitMaximal

/-! # A maximal torus splitting over a quadratic splitting field -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000

section Borel

variable {k : Type u} [Field k] {D G : GroupScheme (Spec (CommRingCat.of k))}
  {T : CommGroupScheme (Spec (CommRingCat.of k))} {i : T.toGrp ⟶ G} {j : D ⟶ G}

private theorem maximalTorus_of_factor_closed (hj : IsClosedSubgroup j) (hi : IsMaximalTorus i)
    (f : T.toGrp ⟶ D) (hf : f ≫ j = i) : IsMaximalTorus f := by
  let : IsClosedImmersion j.hom.hom.left := hj
  have hclosed : IsClosedSubgroup (f ≫ j) := by
    rw [hf]
    exact hi.2.1
  refine ⟨hi.1, SplitSolvableCanonical.isClosedSubgroup_of_comp f j hclosed, ?_⟩
  intro T' t a hT ht ha
  apply hi.2.2 T' (t ≫ j) a hT (ht.comp hj)
  rw [← Category.assoc, ha, hf]

private theorem isSplitTorus_of_maximalTorus_in_geometricBorel
    (hG : IsConnectedReductive G) (hsp : HasSplitMaximalTorus G)
    (hB : IsGeometricBorelSubgroup j) (hi : IsMaximalTorus i)
    (hle : SubgroupFunctor.range i ≤ SubgroupFunctor.range j) : IsSplitTorus T.toGrp := by
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : ConnectedSpace G.X.left := hG.connectedSpace
  obtain ⟨S, s, hS, hs⟩ := hsp
  obtain ⟨A, a, ha, hca⟩ :=
    hB.exists_maximalSplitTorus_centralizer_le_range parabolicDynamic hG
  obtain ⟨g, e, he⟩ := smoothMaximalSplitTorusConjugacy k G S A s a
    (hs.isMaximalSplitTorus hS) ha
  have he' : a = e.inv ≫ s ≫ (G.innerIso g).hom := by
    rw [he, Iso.inv_hom_id_assoc]
  have ham : IsMaximalTorus a := hs.of_eq_iso_comp_comp_iso e.symm (G.innerIso g) he'
  let : IsClosedImmersion j.hom.hom.left := hB.1.isClosedSubgroup
  let : IsClosedImmersion i.hom.hom.left := hi.2.1
  let : IsClosedImmersion a.hom.hom.left := ham.2.1
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  let : Mono a.hom.hom := Over.mono_of_mono_left _
  obtain ⟨f, hf⟩ := SubgroupFunctor.exists_factor_of_range_le hle
  obtain ⟨v, hv⟩ := SubgroupFunctor.exists_factor_of_range_le ((range_le_torusCentralizer a).trans hca)
  let : Smooth D.X.hom := hB.1.smooth
  let : ConnectedSpace D.X.left := hB.1.connectedSpace
  let : IsAffineHom D.X.hom := BorelFieldExtension.isAffineHom_source hB.1.isClosedSubgroup
  obtain ⟨_, iso, _⟩ := solvableMaximalTorusConjugacy k D hB.1.isSolvableGroupScheme
    T A f v (maximalTorus_of_factor_closed hB.1.isClosedSubgroup hi f hf)
    (maximalTorus_of_factor_closed hB.1.isClosedSubgroup ham v hv)
  exact IsSplitTorus.of_iso iso ha.1.1

end Borel

/-- If an affine locally finite-type connected reductive group over an
infinite field splits over a quadratic Galois extension, it has a maximal
torus over the base field that splits over that extension. -/
def QuadraticSplitMaximalTorusStatement : Prop :=
  ∀ (F Q : Type u) [Field F] [Infinite F] [Field Q] [Algebra F Q]
    [FiniteDimensional F Q] [IsGalois F Q], Module.finrank F Q = 2 →
    ∀ (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
      [LocallyOfFiniteType G.X.hom], IsConnectedReductive G →
      HasSplitMaximalTorus ((GroupScheme.baseChange (algebraBaseMap F Q)).obj G) →
      ∃ (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G),
        IsMaximalTorus i ∧
        IsSplitTorus ((CommGroupScheme.baseChange (algebraBaseMap F Q)).obj T).toGrp

theorem quadraticSplitMaximalTorus : QuadraticSplitMaximalTorusStatement.{u} := by
  intro F Q _ _ _ _ _ _ hdeg G _ _ hG hsp
  let b := algebraBaseMap F Q
  let GQ := (GroupScheme.baseChange b).obj G
  let hGQ := connectedReductiveFieldExtensionStatement F Q G hG
  let : IsAffineHom GQ.X.hom := hGQ.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  have hqs : IsQuasiSplit GQ := by
    obtain ⟨S, s, hS, hs⟩ := hsp
    have hZ : (torusCentralizer s).IsRepresentedBy s := by
      let : IsClosedImmersion s.hom.hom.left := hs.2.1
      exact ⟨Over.mono_of_mono_left _, (maximalTorusCentralizer Q GQ hGQ S s hs).symm⟩
    exact hS.isQuasiSplit_of_torusCentralizer hGQ s s hZ hs.1
  obtain ⟨T, i, ht⟩ := exists_quadraticOppositeBorelTorus hdeg hG hqs
  obtain ⟨_, hi, σ, D, j, _, hB, he⟩ := ht
  let tQ : ((CommGroupScheme.baseChange b).obj T).toGrp ⟶ GQ := (GroupScheme.baseChange b).map i
  have hmax : IsMaximalTorus tQ := (maximalTorusBaseChange F Q G T i hi.1 hi.2.1).mp hi
  refine ⟨T, i, hi, isSplitTorus_of_maximalTorus_in_geometricBorel hGQ hsp hB hmax ?_⟩
  rw [← he]
  intro U x hx
  exact hx.1

end Langlands.GroupScheme
