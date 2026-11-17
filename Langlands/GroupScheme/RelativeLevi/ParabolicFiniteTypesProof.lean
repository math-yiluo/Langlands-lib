import Langlands.GroupScheme.RelativeLevi.ParabolicFiniteTypesStatement
import Langlands.GroupScheme.RelativeLevi.ParabolicUniformModels
import Langlands.GroupScheme.Reductive.EtaleLocalSplitProof
import Mathlib.Data.Fintype.EquivFin

/-! # Uniform finite parabolic types on an affine étale neighbourhood -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

namespace Langlands.GroupScheme

private theorem uniformFamily_classifies_point
    {R : Type u} [CommRing R] {I : Type u} [Fintype I]
    {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
    {i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
    (F : UniformStandardCocharacterFamily I G i) (hG : IsReductive G)
    (hi : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (k : Type u) [Field k] (x : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of R)) :
    ∀ (Q : GroupScheme (Spec (CommRingCat.of k)))
      (q : Q ⟶ (GroupScheme.baseChange x).obj G), IsParabolicSubgroup q →
      ∃! a : F.Index,
        ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ ((GroupScheme.baseChange x).obj G).X,
          SubgroupFunctor.range (q ≫ (((GroupScheme.baseChange x).obj G).innerIso g).hom) =
            SubgroupFunctor.range ((GroupScheme.baseChange x).map (F.inclusion a)) := by
  let : Algebra R k := (Spec.preimage x).hom.toAlgebra
  have hx : algebraBaseMap R k = x := Spec.map_preimage x
  rw [← hx]
  intro Q q hq
  exact F.classifies_field hG hi k Q q hq

/-- On an affine étale neighbourhood of every base point, one finite family
of relative parabolics represents all fieldwise rational conjugacy classes
without repetition. -/
theorem relativeParabolicEtaleLocalFiniteTypes :
    RelativeParabolicEtaleLocalFiniteTypesStatement.{u} := by
  classical
  intro S G hG s
  let : IsAffineHom G.X.hom := hG.isAffineHom
  obtain ⟨R, hR, f, hf, ⟨p, hp⟩, I, hI, i, _hi, hmax, J, P, hP, _hfree⟩ :=
    etaleLocalSplitReductive S G hG s
  let : CommRing R := hR
  let : Fintype I := hI
  let GR := (GroupScheme.baseChange f).obj G
  have hGR : IsReductive GR := hG.baseChange f
  let : IsAffineHom GR.X.hom := hGR.isAffineHom
  let k₀ := (Spec (CommRingCat.of R)).residueField p
  let : Algebra R k₀ :=
    (Spec.preimage ((Spec (CommRingCat.of R)).fromSpecResidueField p)).hom.toAlgebra
  let F := uniformStandardCocharacterFamily I GR i P hGR hmax hP k₀
  let e := Fintype.equivFin F.Index
  refine ⟨R, inferInstance, f, hf, ⟨p, hp⟩, Fintype.card F.Index,
    (fun a => F.parabolic (e.symm a)), (fun a => F.inclusion (e.symm a)),
    (fun a => F.relativeParabolic hGR (e.symm a)), ?_⟩
  intro k _ x Q q hq
  obtain ⟨a, ha, huniq⟩ := uniformFamily_classifies_point F hGR hmax k x Q q hq
  refine ⟨e a, ?_, ?_⟩
  · dsimp only
    rw [e.symm_apply_apply]
    exact ha
  · intro b hb
    apply e.symm.injective
    simpa only [Equiv.symm_apply_apply] using huniq (e.symm b) hb

end Langlands.GroupScheme
