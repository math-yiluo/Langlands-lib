import Langlands.GroupScheme.Absolute.RegularCocharacterBorelProof
import Langlands.GroupScheme.Dynamic.OppositeParabolicUniquenessProof
import Langlands.GroupScheme.Reductive.QuasiSplit
import Langlands.GroupScheme.SubgroupFunctor.FpqcDescent
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof
import Langlands.GroupScheme.Torus.SplitReflection

/-! # Uniqueness of an opposite Borel through a maximal torus over a field -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Two Borel subgroups whose intersections with a fixed Borel subgroup
are the same split maximal torus have equal image subgroup functors. -/
theorem oppositeBorel_range_eq_of_isSplitTorus
    {k : Type u} [Field k] {G B B₁ B₂ : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G)
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (t : T.toGrp ⟶ G) (hT : IsSplitTorus T.toGrp) (ht : IsMaximalTorus t)
    (i : B ⟶ G) (hi : IsBorelSubgroup i)
    (i₁ : B₁ ⟶ G) (hi₁ : IsBorelSubgroup i₁)
    (i₂ : B₂ ⟶ G) (hi₂ : IsBorelSubgroup i₂)
    (h₁ : SubgroupFunctor.range i₁ ⊓ SubgroupFunctor.range i = SubgroupFunctor.range t)
    (h₂ : SubgroupFunctor.range i₂ ⊓ SubgroupFunctor.range i = SubgroupFunctor.range t) :
    SubgroupFunctor.range i₁ = SubgroupFunctor.range i₂ := by
  have := hG.isAffineHom
  have : IsClosedImmersion i.hom.hom.left := hi.isClosedSubgroup
  have hirep : (SubgroupFunctor.range i).IsRepresentedBy i :=
    ⟨Over.mono_of_mono_left _, rfl⟩
  have hti : SubgroupFunctor.range t ≤ SubgroupFunctor.range i := by
    rw [← h₁]
    exact fun _ _ hx => hx.2
  obtain ⟨ν, hν, hrep⟩ := (regularCocharacterBorel k G hG T t hT ht).2.2
    B i (hirep.liftOfLE t hti) hi (hirep.liftOfLE_comp t hti)
  have hz := centralizer_comp_eq_range_of_isRegular hG hT t ht ν hν
  have hnegative : ∀ {C : GroupScheme (Spec (CommRingCat.of k))}
      (j : C ⟶ G), IsBorelSubgroup j →
      SubgroupFunctor.range j ⊓ SubgroupFunctor.range i = SubgroupFunctor.range t →
      SubgroupFunctor.range j =
        Dynamic.parabolic (Dynamic.oppositeCocharacter (CommGroupScheme.groupHom ν ≫ t)) := by
    intro C j hj hinter
    have : IsClosedImmersion j.hom.hom.left := hj.isClosedSubgroup
    have hjrep : (SubgroupFunctor.range j).IsRepresentedBy j :=
      ⟨Over.mono_of_mono_left _, rfl⟩
    have htj : SubgroupFunctor.range t ≤ SubgroupFunctor.range j := by
      rw [← hinter]
      exact fun _ _ hx => hx.1
    obtain ⟨ν', hν', hrep'⟩ := (regularCocharacterBorel k G hG T t hT ht).2.2
      C j (hjrep.liftOfLE t htj) hj (hjrep.liftOfLE_comp t htj)
    have hz' := centralizer_comp_eq_range_of_isRegular hG hT t ht ν' hν'
    have hcentralizer :
        Dynamic.centralizer (CommGroupScheme.groupHom ν' ≫ t) =
          Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ t) :=
      hz'.trans hz.symm
    have hinter' :
        Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ t) ⊓
            Dynamic.parabolic (CommGroupScheme.groupHom ν' ≫ t) =
          Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ t) := by
      rw [← hrep.2, ← hrep'.2, hz]
      apply SubgroupFunctor.ext
      intro U
      rw [SubgroupFunctor.inf_carrier, inf_comm]
      exact congrArg (fun F : SubgroupFunctor G => F.carrier U) hinter
    have hpoints := congrArg
      (fun F : SubgroupFunctor G => F.carrier (Over.mk (𝟙 (Spec (CommRingCat.of k))))) hinter'
    exact hrep'.2.trans
      (oppositeDynamicParabolicUniqueness k G hG _ _ hcentralizer hpoints).1
  exact (hnegative i₁ hi₁ h₁).trans (hnegative i₂ hi₂ h₂).symm

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- Uniqueness of the opposite geometric Borel over every field, allowing
the fixed maximal torus to be nonsplit. -/
theorem oppositeGeometricBorel_range_eq
    {k : Type u} [Field k] {G B B₁ B₂ : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsConnectedReductive G)
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (t : T.toGrp ⟶ G) (ht : IsMaximalTorus t)
    (i : B ⟶ G) (hi : IsGeometricBorelSubgroup i)
    (i₁ : B₁ ⟶ G) (hi₁ : IsGeometricBorelSubgroup i₁)
    (i₂ : B₂ ⟶ G) (hi₂ : IsGeometricBorelSubgroup i₂)
    (h₁ : SubgroupFunctor.range i₁ ⊓ SubgroupFunctor.range i = SubgroupFunctor.range t)
    (h₂ : SubgroupFunctor.range i₂ ⊓ SubgroupFunctor.range i = SubgroupFunctor.range t) :
    SubgroupFunctor.range i₁ = SubgroupFunctor.range i₂ := by
  have := hG.smooth
  have := hG.isAffineHom
  have : IsClosedImmersion i₁.hom.hom.left := hi₁.1.isClosedSubgroup
  have : IsClosedImmersion i₂.hom.hom.left := hi₂.1.isClosedSubgroup
  have : Mono i₁.hom.hom := Over.mono_of_mono_left _
  have : Mono i₂.hom.hom := Over.mono_of_mono_left _
  let b : Spec (CommRingCat.of (AlgebraicClosure k)) ⟶ Spec (CommRingCat.of k) :=
    toAlgebraicClosure k
  have hGK : IsConnectedReductive ((GroupScheme.baseChange b).obj G) :=
    connectedReductiveFieldExtensionStatement k (AlgebraicClosure k) G hG
  have htK : IsMaximalTorus (T := (CommGroupScheme.baseChange b).obj T)
      ((GroupScheme.baseChange b).map t) :=
    (maximalTorusBaseChange k (AlgebraicClosure k) G T t ht.1 ht.2.1).1 ht
  have hTK : IsSplitTorus ((CommGroupScheme.baseChange b).obj T).toGrp :=
    htK.1.isSplitTorus_of_finiteGaloisSplitting torusFiniteGaloisSplitting
  have hinter : ∀ {C : GroupScheme (Spec (CommRingCat.of k))} (j : C ⟶ G),
      SubgroupFunctor.range j ⊓ SubgroupFunctor.range i = SubgroupFunctor.range t →
      SubgroupFunctor.range ((GroupScheme.baseChange b).map j) ⊓
          SubgroupFunctor.range ((GroupScheme.baseChange b).map i) =
        SubgroupFunctor.range ((GroupScheme.baseChange b).map t) := by
    intro C j hj
    rw [SubgroupFunctor.range_baseChangeHom, SubgroupFunctor.range_baseChangeHom,
      ← SubgroupFunctor.inf_baseChange, hj, SubgroupFunctor.range_baseChangeHom]
  have hK := oppositeBorel_range_eq_of_isSplitTorus (T := (CommGroupScheme.baseChange b).obj T) hGK
    ((GroupScheme.baseChange b).map t) hTK htK
    ((GroupScheme.baseChange b).map i) hi.2
    ((GroupScheme.baseChange b).map i₁) hi₁.2
    ((GroupScheme.baseChange b).map i₂) hi₂.2 (hinter i₁ h₁) (hinter i₂ h₂)
  apply SubgroupFunctor.range_eq_of_baseChange_eq b i₁ i₂
  simpa only [SubgroupFunctor.range_baseChangeHom] using hK

end Langlands.GroupScheme
