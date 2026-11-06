import Langlands.GroupScheme.Absolute.BorelContainingFactor
import Langlands.GroupScheme.Absolute.BorelContainingSubgroupConnectedStatement
import Langlands.GroupScheme.Absolute.BorelStatement
import Langlands.GroupScheme.Absolute.BorelTransport
import Langlands.GroupScheme.IdentityComponent
import Langlands.GroupScheme.InnerAutomorphismHom
import Langlands.GroupScheme.HomConjugacy
import Langlands.GroupScheme.Rational.BruhatCoveringReduction
import Langlands.GroupScheme.Rational.LeviSplitComponentFactorization

/-! # Connectedness of subgroups containing a Borel, from conjugacy and the normalizer theorem -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace BorelContainingSubgroupConnected

variable {k : Type u} [Field k]

/-- On base points, the inner automorphism of `g` is conjugation by `g`. -/
theorem mul_mul_inv_eq_comp_innerIso {S : Scheme.{u}} (G : GroupScheme S)
    (g h : Over.mk (𝟙 S) ⟶ G.X) :
    g * h * g⁻¹ = h ≫ (G.innerIso g).hom.hom.hom := by
  rw [comp_innerIso_hom, constantPoint_self]

variable [IsAlgClosed k] {G P B : GroupScheme (Spec (CommRingCat.of k))}
  [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
  [Smooth P.X.hom] [IsAffineHom P.X.hom]

/-- Assuming Borel conjugacy and the normalizer theorem, every `k`-point of a smooth closed
subgroup `P` containing a Borel subgroup lies in the identity component `P⁰`. -/
theorem exists_comp_identityComponentι_eq
    (hconj : BorelConjugacyStatement.{u}) (hnorm : BorelNormalizerStatement.{u})
    {i : P ⟶ G} {j : B ⟶ G} {f : B ⟶ P} (hi : IsClosedSubgroup i)
    (hj : IsBorelSubgroup j) (hf : f ≫ i = j)
    (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ P.X) :
    ∃ y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ (identityComponent P).X,
      y ≫ (identityComponentι P).hom.hom = x := by
  have := hj.connectedSpace
  have : IsClosedImmersion i.hom.hom.left := hi
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have hei : IsClosedSubgroup (identityComponentι P ≫ i) :=
    (IdentityComponent.isClosedSubgroup_identityComponentι P).comp hi
  -- The given Borel subgroup, inside `P⁰`.
  obtain ⟨f₀, hf₀e⟩ : ∃ f₀ : B ⟶ identityComponent P, f₀ ≫ identityComponentι P = f :=
    ⟨_, IdentityComponent.factor_identityComponentι P f⟩
  have hf₀ : IsBorelSubgroup f₀ := IsBorelSubgroup.of_comp hei (by
    rw [reassoc_of% hf₀e, hf]
    exact hj)
  -- Its conjugate by `x`, inside `P⁰`.
  obtain ⟨fx, hfxe⟩ : ∃ fx : B ⟶ identityComponent P,
      fx ≫ identityComponentι P = f ≫ (P.innerIso x).hom :=
    ⟨_, IdentityComponent.factor_identityComponentι P _⟩
  obtain ⟨x', hx'⟩ : ∃ x', x ≫ i.hom.hom = x' := ⟨_, rfl⟩
  have hfx_comp : fx ≫ identityComponentι P ≫ i = j ≫ (G.innerIso x').hom := by
    rw [reassoc_of% hfxe, innerIso_hom_comp, reassoc_of% hf, hx']
  have hfx : IsBorelSubgroup fx := IsBorelSubgroup.of_comp hei (by
    rw [hfx_comp]
    exact hj.comp_iso _)
  -- Conjugacy of Borel subgroups in `P⁰`.
  obtain ⟨p, φ, hpφ⟩ := (hconj k (identityComponent P)).2 B B f₀ fx hf₀ hfx
  obtain ⟨q, hq'⟩ : ∃ q, p ≫ (identityComponentι P ≫ i).hom.hom = q := ⟨_, rfl⟩
  have hq : j ≫ (G.innerIso q).hom = φ.hom ≫ j ≫ (G.innerIso x').hom := by
    rw [← hfx_comp, ← reassoc_of% hpφ, innerIso_hom_comp (identityComponentι P ≫ i) p, hq',
      Category.assoc, reassoc_of% hf₀e, reassoc_of% hf]
  -- The point `w = x'⁻¹ q` of `G` normalizes the points of `B`.
  obtain ⟨w, hw_def⟩ : ∃ w, x'⁻¹ * q = w := ⟨_, rfl⟩
  have hw : j ≫ (G.innerIso w).hom = φ.hom ≫ j := by
    rw [← hw_def, innerIso_mul_hom, innerIso_inv_hom, reassoc_of% hq, Iso.hom_inv_id,
      Category.comp_id]
  have hw' : j ≫ (G.innerIso w).inv = φ.inv ≫ j := by
    rw [Iso.comp_inv_eq, Category.assoc, hw, Iso.inv_hom_id_assoc]
  have hwN : w ∈ Subgroup.normalizer
      ((SubgroupFunctor.range j).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) :
        Set (Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [SubgroupFunctor.mem_range, SubgroupFunctor.mem_range,
      mul_mul_inv_eq_comp_innerIso]
    constructor
    · rintro ⟨b, rfl⟩
      refine ⟨b ≫ φ.hom.hom.hom, ?_⟩
      have h' := congrArg (fun m => b ≫ m.hom.hom) hw
      simp only [Grp.comp_hom_hom] at h'
      simpa only [Category.assoc] using h'.symm
    · rintro ⟨b, hb⟩
      refine ⟨b ≫ φ.inv.hom.hom, ?_⟩
      have h' := congrArg (fun m => b ≫ m.hom.hom) hw'
      simp only [Grp.comp_hom_hom] at h'
      have hinv : (G.innerIso w).hom.hom.hom ≫ (G.innerIso w).inv.hom.hom = 𝟙 _ := by
        rw [← Grp.comp_hom_hom, Iso.hom_inv_id, Grp.id_hom_hom]
      rw [Category.assoc, ← h', ← Category.assoc, hb, Category.assoc, hinv, Category.comp_id]
  -- The normalizer theorem.
  rw [hnorm k G B j hj] at hwN
  obtain ⟨b, hb⟩ := SubgroupFunctor.mem_range.mp hwN
  refine ⟨p * (b ≫ f₀.hom.hom)⁻¹, ?_⟩
  have hbf : ((b ≫ f₀.hom.hom) ≫ (identityComponentι P).hom.hom) ≫ i.hom.hom = w := by
    rw [← hb, ← hf, ← hf₀e]
    simp only [Grp.comp_hom_hom, Category.assoc]
  have hpq : (p ≫ (identityComponentι P).hom.hom) ≫ i.hom.hom = q := by
    rw [← hq', Grp.comp_hom_hom, Category.assoc]
  rw [← cancel_mono i.hom.hom, MonObj.mul_comp, GrpObj.inv_comp, MonObj.mul_comp,
    GrpObj.inv_comp, hbf, hpq, hx', ← hw_def]
  group

/-- **Reduction** (Milne, Corollary 17.49, connectedness clause). Borel conjugacy and the
normalizer theorem imply that a smooth closed subgroup containing a Borel subgroup is
connected. -/
theorem borelContainingSubgroupConnected_of
    (hconj : BorelConjugacyStatement.{u}) (hnorm : BorelNormalizerStatement.{u}) :
    BorelContainingSubgroupConnectedStatement.{u} := by
  intro k _ _ G _ _ _ P B i j f hi hP hj hf
  have : IsAffineHom P.X.hom := hi.isAffineHom_source
  have : JacobsonSpace P.X.left := LocallyOfFiniteType.jacobsonSpace P.X.hom
  rw [connectedSpace_iff_connectedComponent]
  refine ⟨IdentityComponent.identityPoint P, ?_⟩
  by_contra hne
  obtain ⟨a, ha, hac⟩ := nonempty_inter_closedPoints (Set.nonempty_compl.mpr hne)
    (IdentityComponent.isClopen_identitySet P).isOpen.isClosed_compl.isLocallyClosed
  let x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ P.X :=
    Over.homMk (pointOfClosedPoint P.X.hom a hac) (by simp)
  obtain ⟨y, hy⟩ := exists_comp_identityComponentι_eq hconj hnorm hi hj hf x
  apply ha
  rw [← IdentityComponent.range_identityComponentι]
  refine ⟨y.left (IsLocalRing.closedPoint k), ?_⟩
  have h := congr(($hy).left (IsLocalRing.closedPoint k))
  rw [Over.comp_left, Scheme.Hom.comp_apply] at h
  rw [h]
  exact pointOfClosedPoint_apply P.X.hom a hac _

end BorelContainingSubgroupConnected

end Langlands.GroupScheme
