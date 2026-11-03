import Langlands.GroupScheme.Absolute.Borel
import Langlands.GroupScheme.Torus.MaximalTransport

/-! # The closed subgroup envelope of all ground-field tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
variable {G H K : GroupScheme (Spec (CommRingCat.of k))}

/-- Containment of every closed ground-field torus on every test scheme. -/
def SubgroupFunctor.ContainsTori (F : SubgroupFunctor G) : Prop :=
  ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G),
    IsTorus T.toGrp → IsClosedSubgroup i → SubgroupFunctor.range i ≤ F

/-- The intersection of all actual closed subgroups containing all
ground-field tori. Representability and smoothness are separate obligations. -/
def closedTorusEnvelope (G : GroupScheme (Spec (CommRingCat.of k))) :
    SubgroupFunctor G where
  carrier U :=
    { carrier := {x | ∀ (H : GroupScheme (Spec (CommRingCat.of k))) (j : H ⟶ G),
        IsClosedSubgroup j → (SubgroupFunctor.range j).ContainsTori →
          x ∈ (SubgroupFunctor.range j).carrier U}
      one_mem' := fun _ j _ _ => ((SubgroupFunctor.range j).carrier U).one_mem
      mul_mem' := fun hx hy H j hj ht =>
        ((SubgroupFunctor.range j).carrier U).mul_mem (hx H j hj ht) (hy H j hj ht)
      inv_mem' := fun hx H j hj ht =>
        ((SubgroupFunctor.range j).carrier U).inv_mem (hx H j hj ht) }
  comp_mem a _x hx H j hj ht := (SubgroupFunctor.range j).comp_mem a (hx H j hj ht)

/-- Every closed ground-field torus lies in the closed torus envelope. -/
theorem closedTorusEnvelope_containsTori (G : GroupScheme (Spec (CommRingCat.of k))) :
    (closedTorusEnvelope G).ContainsTori := by
  intro T i hT hi U x hx H j hj ht
  exact ht T i hT hi U hx

/-- Minimality among actual closed subgroups containing all ground-field tori. -/
theorem closedTorusEnvelope_le (j : H ⟶ G) (hj : IsClosedSubgroup j)
    (ht : (SubgroupFunctor.range j).ContainsTori) :
    closedTorusEnvelope G ≤ SubgroupFunctor.range j :=
  fun _ _ hx => hx H j hj ht

/-- The closed envelope of all ground-field tori is the entire group. -/
def IsTorusGenerated (G : GroupScheme (Spec (CommRingCat.of k))) : Prop :=
  closedTorusEnvelope G = ⊤

/-- An actual representative of the closed envelope of all ground-field tori.
This data asserts no existence, smoothness or connectedness theorem. -/
structure TorusGeneratedEnvelope (G : GroupScheme (Spec (CommRingCat.of k))) where
  group : GroupScheme (Spec (CommRingCat.of k))
  inclusion : group ⟶ G
  closed : IsClosedSubgroup inclusion
  represents : (closedTorusEnvelope G).IsRepresentedBy inclusion

namespace TorusGeneratedEnvelope

variable (D : TorusGeneratedEnvelope G)

private theorem represents_range (j : H ⟶ G) (hj : IsClosedSubgroup j) :
    (SubgroupFunctor.range j).IsRepresentedBy j := by
  let : IsClosedImmersion j.hom.hom.left := hj
  exact ⟨Over.mono_of_mono_left _, rfl⟩

/-- The canonical actual factor of a closed torus through its envelope. -/
def torusFactor {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ G) (hT : IsTorus T.toGrp) (hi : IsClosedSubgroup i) :
    T.toGrp ⟶ D.group :=
  D.represents.factorHom i (closedTorusEnvelope_containsTori G T i hT hi)

theorem torusFactor_comp {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ G) (hT : IsTorus T.toGrp) (hi : IsClosedSubgroup i) :
    D.torusFactor i hT hi ≫ D.inclusion = i :=
  D.represents.factorHom_comp _ _

theorem torusFactor_closed {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ G) (hT : IsTorus T.toGrp) (hi : IsClosedSubgroup i) :
    IsClosedSubgroup (D.torusFactor i hT hi) :=
  IsClosedSubgroup.of_comp D.closed (by rwa [D.torusFactor_comp])

/-- An ambient maximal torus remains maximal in the envelope. -/
theorem torusFactor_maximal {T : CommGroupScheme (Spec (CommRingCat.of k))}
    (i : T.toGrp ⟶ G) (hi : IsMaximalTorus i) :
    IsMaximalTorus (D.torusFactor i hi.1 hi.2.1) :=
  IsMaximalTorus.of_comp D.closed (by rwa [D.torusFactor_comp])

/-- Universal minimality as an actual group-scheme homomorphism. -/
def minimalHom (j : H ⟶ G) (hj : IsClosedSubgroup j)
    (ht : (SubgroupFunctor.range j).ContainsTori) : D.group ⟶ H :=
  (represents_range j hj).factorHom D.inclusion (by
    rw [D.represents.2]
    exact closedTorusEnvelope_le j hj ht)

theorem minimalHom_comp (j : H ⟶ G) (hj : IsClosedSubgroup j)
    (ht : (SubgroupFunctor.range j).ContainsTori) :
    D.minimalHom j hj ht ≫ j = D.inclusion :=
  (represents_range j hj).factorHom_comp _ _

theorem minimalHom_unique (j : H ⟶ G) (hj : IsClosedSubgroup j)
    (ht : (SubgroupFunctor.range j).ContainsTori)
    (f : D.group ⟶ H) (hf : f ≫ j = D.inclusion) :
    f = D.minimalHom j hj ht :=
  (represents_range j hj).hom_ext (hf.trans (D.minimalHom_comp j hj ht).symm)

/-- Two representatives of the closed torus envelope are isomorphic over `G`. -/
def iso (D' : TorusGeneratedEnvelope G) : D.group ≅ D'.group :=
  D.represents.isoOfIsRepresentedBy D'.represents

theorem iso_hom_comp (D' : TorusGeneratedEnvelope G) :
    (D.iso D').hom ≫ D'.inclusion = D.inclusion :=
  D.represents.isoOfIsRepresentedBy_hom_comp D'.represents

/-- The representing group is itself generated by its ground-field tori. -/
theorem isTorusGenerated : IsTorusGenerated D.group := by
  apply SubgroupFunctor.ext
  intro U
  apply le_antisymm
  · exact le_top
  · intro x _ K j hj ht
    have hcontains : (SubgroupFunctor.range (j ≫ D.inclusion)).ContainsTori := by
      intro T i hT hi V y hy
      obtain ⟨t, rfl⟩ := SubgroupFunctor.mem_range.mp hy
      obtain ⟨z, hz⟩ := SubgroupFunctor.mem_range.mp
        (ht T (D.torusFactor i hT hi) hT (D.torusFactor_closed i hT hi)
          V (show t ≫ (D.torusFactor i hT hi).hom.hom ∈
            (SubgroupFunctor.range (D.torusFactor i hT hi)).carrier V from ⟨t, rfl⟩))
      refine SubgroupFunctor.mem_range.mpr ⟨z, ?_⟩
      rw [Grp.comp_hom_hom, ← Category.assoc, hz, Category.assoc,
        ← Grp.comp_hom_hom, D.torusFactor_comp]
    let a := D.minimalHom (j ≫ D.inclusion) (hj.comp D.closed) hcontains
    have ha : a ≫ j = 𝟙 D.group := by
      apply D.represents.hom_ext
      simpa only [Category.assoc, Category.id_comp] using
        D.minimalHom_comp (j ≫ D.inclusion) (hj.comp D.closed) hcontains
    refine SubgroupFunctor.mem_range.mpr ⟨x ≫ a.hom.hom, ?_⟩
    rw [Category.assoc, ← Grp.comp_hom_hom, ha, Grp.id_hom_hom, Category.comp_id]

/-- Rational conjugacy of maximal tori inside the envelope gives the same
unrestricted conclusion in the original ambient group. -/
theorem maximalToriAreConjugate (hD : MaximalToriAreConjugate D.group) :
    MaximalToriAreConjugate G := by
  intro T T' i i' hi hi'
  have h := (hD T T' (D.torusFactor i hi.1 hi.2.1)
    (D.torusFactor i' hi'.1 hi'.2.1)
    (D.torusFactor_maximal i hi) (D.torusFactor_maximal i' hi')).postcomp D.inclusion
  simpa only [D.torusFactor_comp] using h

end TorusGeneratedEnvelope

/-- Solvability of geometric point groups is inherited along a monomorphism. -/
theorem IsSolvableGroupScheme.of_mono (hG : IsSolvableGroupScheme G)
    (j : H ⟶ G) [Mono j.hom.hom] : IsSolvableGroupScheme H := by
  let j' := (GroupScheme.baseChange (toAlgebraicClosure k)).map j
  have : Mono j'.hom.hom := by
    change Mono ((Over.pullback (toAlgebraicClosure k)).map j.hom.hom)
    infer_instance
  let U := Over.mk (𝟙 (Spec (CommRingCat.of (AlgebraicClosure k))))
  let φ :
      (U ⟶ ((GroupScheme.baseChange (toAlgebraicClosure k)).obj H).X) →*
        (U ⟶ ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G).X) :=
    ((pointsMap j').app (op U)).hom
  let : Group.IsSolvable (U ⟶ ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G).X) :=
    hG
  exact Group.isSolvable_of_isSolvable_injective (f := φ)
    (fun _ _ h => (cancel_mono j'.hom.hom).mp h)

namespace TorusGeneratedEnvelope

variable (D : TorusGeneratedEnvelope G)

/-- Affineness of the envelope group follows from closedness of its inclusion. -/
theorem isAffineHom [IsAffineHom G.X.hom] : IsAffineHom D.group.X.hom := by
  let : IsClosedImmersion D.inclusion.hom.hom.left := D.closed
  rw [← Over.w D.inclusion.hom.hom]
  infer_instance

/-- A represented torus envelope in a solvable group is solvable. -/
theorem isSolvableGroupScheme (hG : IsSolvableGroupScheme G) :
    IsSolvableGroupScheme D.group := by
  let : Mono D.inclusion.hom.hom := D.represents.1
  exact hG.of_mono D.inclusion

end TorusGeneratedEnvelope

end Langlands.GroupScheme
