import Langlands.GroupScheme.Rational.PseudoParabolicAmbientTransport
import Langlands.GroupScheme.Reductive.UnipotentRadicalQuotientProof
import Langlands.GroupScheme.RepresentedAction
import Langlands.GroupScheme.SchemeActionRationalPoints
import Langlands.GroupScheme.SmoothProducts

/-! # Smooth group actions on represented unipotent radicals -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace AutomorphicAction

variable {S : Scheme.{u}} {H G : GroupScheme S} (a : AutomorphicAction H G)

/-- A section of the acting group induces an actual automorphism of the target
scheme over the same base. -/
def sectionIso (h : Over.mk (𝟙 S) ⟶ H.X) : G ≅ G :=
  isoOfPoints (fun T => a.pointAut T (toUnit T ≫ h)) (by
    intro T T' b x
    change a.act (toUnit T' ≫ h) (b ≫ x) = b ≫ a.act (toUnit T ≫ h) x
    rw [a.naturality, comp_toUnit_assoc])

@[simp] theorem comp_sectionIso_hom (h : Over.mk (𝟙 S) ⟶ H.X)
    {T : Over S} (x : T ⟶ G.X) :
    x ≫ (a.sectionIso h).hom.hom.hom = a.act (toUnit T ≫ h) x := by
  exact comp_isoOfPoints_hom (fun T => a.pointAut T (toUnit T ≫ h)) (by
    intro T T' b x
    change a.act (toUnit T' ≫ h) (b ≫ x) = b ≫ a.act (toUnit T ≫ h) x
    rw [a.naturality, comp_toUnit_assoc]) T x

end AutomorphicAction

variable {k : Type u} [Field k] [IsAlgClosed k]
    {H G U : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth H.X.hom] [Smooth G.X.hom] [IsAffineHom G.X.hom]
    [ConnectedSpace G.X.left] {i : U ⟶ G}

/-- Smooth automorphic actions preserve the full represented unipotent radical,
including on nonreduced test schemes. -/
theorem IsUnipotentRadical.isStable (hi : IsUnipotentRadical i)
    (a : AutomorphicAction H G) : a.IsStable (SubgroupFunctor.range i) := by
  obtain ⟨Q, q, hq, hQ⟩ := unipotentRadicalQuotient k G U i hi
  let : IsAffineHom Q.X.hom := hQ.isAffineHom
  let : Smooth U.X.hom := hi.smooth
  let : Smooth (H.X ⊗ U.X).hom := smooth_tensor H.X U.X inferInstance hi.smooth
  let : IsReduced (H.X ⊗ U.X).left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      k (H.X ⊗ U.X).left (H.X ⊗ U.X).hom
  let F : H.X ⊗ U.X ⟶ G.X :=
    a.act (fst H.X U.X) (snd H.X U.X ≫ i.hom.hom)
  have hkill : F ≫ q.hom.hom = (1 : H.X ⊗ U.X ⟶ Q.X) := by
    apply hom_ext_rationalPoints
    intro z
    let h := z ≫ fst H.X U.X
    let x := z ≫ snd H.X U.X
    have hu : toUnit (Over.mk (𝟙 (Spec (CommRingCat.of k)))) = 𝟙 _ :=
      toUnit_unique _ _
    have heq : SubgroupFunctor.range (i ≫ (a.sectionIso h).hom) =
        SubgroupFunctor.range i := (hi.comp_iso (a.sectionIso h)).range_eq hi
    have hx : a.act h (x ≫ i.hom.hom) ∈
        (SubgroupFunctor.range i).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
      rw [← heq]
      apply SubgroupFunctor.mem_range.2
      refine ⟨x, ?_⟩
      rw [Grp.comp_hom_hom, ← Category.assoc, a.comp_sectionIso_hom, hu,
        Category.id_comp]
    have hk : a.act h (x ≫ i.hom.hom) ≫ q.hom.hom = 1 := by
      apply (mem_range_kernelι_iff q _).mp
      rw [hq.2.2.2]
      exact hx
    rw [← Category.assoc]
    change (z ≫ a.act (fst H.X U.X) (snd H.X U.X ≫ i.hom.hom)) ≫
      q.hom.hom = z ≫ 1
    rw [a.naturality, MonObj.comp_one]
    exact hk
  intro T h g hg
  obtain ⟨x, rfl⟩ := SubgroupFunctor.mem_range.1 hg
  rw [← hq.2.2.2]
  apply (mem_range_kernelι_iff q _).mpr
  have he := congrArg (fun f => lift h x ≫ f) hkill
  simpa only [F, ← Category.assoc, a.naturality, lift_fst, lift_snd,
    MonObj.comp_one] using he

/-- The actual action induced on a supplied represented unipotent radical. -/
def IsUnipotentRadical.action (hi : IsUnipotentRadical i)
    (a : AutomorphicAction H G) : AutomorphicAction H U := by
  let : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  let : Mono i.hom.hom := Over.mono_of_mono_left _
  exact a.onRepresentedSubgroup i ⟨inferInstance, rfl⟩ (hi.isStable a)

/-- The radical inclusion intertwines the induced and original actions on every test. -/
theorem IsUnipotentRadical.action_isEquivariant (hi : IsUnipotentRadical i)
    (a : AutomorphicAction H G) {T : Over (Spec (CommRingCat.of k))}
    (h : T ⟶ H.X) (x : T ⟶ U.X) :
    (hi.action a).act h x ≫ i.hom.hom = a.act h (x ≫ i.hom.hom) := by
  exact a.onRepresentedSubgroup_act_comp i _ (hi.isStable a) h x

end Langlands.GroupScheme
