import Langlands.GroupScheme.Torus.OrderedProjectorSubgroupComparison
import Langlands.GroupScheme.Torus.OrderedProjectorChartBaseChange
import Langlands.GroupScheme.Torus.DiagonalizableAutomorphismTestLocality

/-! # Local weight matchings for equal projector subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.OrderedProjectorScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {R : CommRingCat.{u}} {Λ Λ' : Type u} [AddCommGroup Λ] [AddCommGroup Λ']
variable {J K n : Type} [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
  [Fintype n] [DecidableEq n]
variable {w : J → Λ} {v : K → Λ'} {T : Over (Spec R)}

/-- A family with generating weights is a closed subgroup over any test scheme. -/
theorem isClosedSubgroup_subgroupHom (P : Family J n Γ(T.left, ⊤))
    (hw : AddSubgroup.closure (Set.range w) = ⊤) :
    IsClosedSubgroup (subgroupHom w T P) := by
  let C := scheme J n R
  let x : T ⟶ C := (pointsEquiv J n R T).symm P
  let U := pointsEquiv J n R C (𝟙 C)
  have hP : P = U.map x.left.appTop.hom := by
    have h := pointsEquiv_naturality J n R x (𝟙 C)
    rw [Category.comp_id] at h
    simpa only [x, Equiv.apply_symm_apply] using h
  rw [hP, ← pullHom_subgroupHom x w U]
  let j := chartFamily (n := n) (R := R) w
  have h : IsClosedImmersion ((baseChange x.left).map j).hom.hom.left :=
    IsClosedSubgroup.baseChange x.left (isClosedSubgroup_chartFamily w hw)
  let e := Descent.pullbackComparison C.hom x.left T.hom (Over.w x)
    (Diagonalizable.groupScheme R Λ).toGrp
  let e' := Descent.pullbackComparison C.hom x.left T.hom (Over.w x)
    (GeneralLinear.groupScheme n R)
  change IsClosedImmersion (e.inv.hom.hom.left ≫ ((baseChange x.left).map j).hom.hom.left ≫
    e'.hom.hom.hom.left)
  exact MorphismProperty.IsStableUnderComposition.comp_mem (P := @IsClosedImmersion) _ _
    (IsClosedSubgroup.of_iso e.symm)
    (MorphismProperty.IsStableUnderComposition.comp_mem (P := @IsClosedImmersion) _ _
      h (IsClosedSubgroup.of_iso e'))

private theorem mono_of_closed {S : Scheme.{u}} {G H : GroupScheme S} (j : G ⟶ H)
    (hj : IsClosedSubgroup j) : Mono j.hom.hom := by
  have h : IsClosedImmersion j.hom.hom.left := hj
  let : SurjectiveOnStalks j.hom.hom.left := h.toSurjectiveOnStalks
  let : Mono j.hom.hom.left := SurjectiveOnStalks.mono_of_injective h.isClosedEmbedding.injective
  exact Over.mono_of_mono_left _

/-- Distinct matchings cannot yield the same relabelling on a nonempty base when the
subgroup defined by the projectors is closed. -/
theorem eq_of_relabel_eq [Nonempty T.left] (Q : Family K n Γ(T.left, ⊤))
    (hv : Function.Injective v) (hgen : AddSubgroup.closure (Set.range v) = ⊤)
    (e e' : WeightEquivalence w v) (h : Q.relabel e.labels = Q.relabel e'.labels) : e = e' := by
  have hh := (subgroupHom_eq_of_relabel T e Q).symm.trans
    ((congrArg (subgroupHom w T) h).trans (subgroupHom_eq_of_relabel T e' Q))
  let j := subgroupHom v T Q
  let : Mono j.hom.hom := mono_of_closed j (isClosedSubgroup_subgroupHom Q hgen)
  have hmap : (baseChange T.hom).map (Diagonalizable.restrictMap R e.lattice.toAddMonoidHom) =
      (baseChange T.hom).map (Diagonalizable.restrictMap R e'.lattice.toAddMonoidHom) := by
    apply Grp.hom_ext
    apply (cancel_mono j.hom.hom).mp
    exact congrArg (fun f => f.hom.hom) hh
  have hlat := Diagonalizable.restrictEquiv_baseChange_injective T hmap
  refine WeightEquivalence.ext hlat ?_
  ext i
  apply hv
  apply e.lattice.injective
  rw [← e.weight_eq i, hlat, ← e'.weight_eq i]

/-- A neighborhood where a common subgroup of the general linear group has a single matching
of the two systems of weight projectors. -/
structure LocalWeightMatching (P : Family J n Γ(T.left, ⊤)) (Q : Family K n Γ(T.left, ⊤))
    (x : T.left) where
  scheme : Over (Spec R)
  map : scheme ⟶ T
  openImmersion : IsOpenImmersion map.left
  contains : x ∈ Set.range map.left
  matching : WeightEquivalence w v
  projectors_eq : P.map map.left.appTop.hom = (Q.map map.left.appTop.hom).relabel matching.labels

/-- Equal closed projector subgroups admit a single weight matching near every point. -/
theorem nonempty_localWeightMatching [AddMonoid.FG Λ']
    (P : Family J n Γ(T.left, ⊤)) (Q : Family K n Γ(T.left, ⊤))
    (hw : Function.Injective w) (hv : Function.Injective v)
    (hwgen : AddSubgroup.closure (Set.range w) = ⊤) (hvgen : AddSubgroup.closure (Set.range v) = ⊤)
    (h : SubgroupFunctor.range (subgroupHom w T P) = SubgroupFunctor.range (subgroupHom v T Q))
    (x : T.left) : Nonempty (LocalWeightMatching (w := w) (v := v) P Q x) := by
  let j := subgroupHom w T P
  let j' := subgroupHom v T Q
  have hj : (SubgroupFunctor.range j).IsRepresentedBy j :=
    ⟨mono_of_closed j (isClosedSubgroup_subgroupHom P hwgen), rfl⟩
  have hj' : (SubgroupFunctor.range j).IsRepresentedBy j' :=
    ⟨mono_of_closed j' (isClosedSubgroup_subgroupHom Q hvgen), h.symm⟩
  let e := hj.isoOfIsRepresentedBy hj'
  have he : e.hom ≫ j' = j := hj.isoOfIsRepresentedBy_hom_comp hj'
  obtain ⟨W, a, g, ha, ⟨y, hy⟩, hg⟩ :=
    Diagonalizable.exists_open_neighborhood_eq_restrictMap_on_test T e x
  obtain ⟨k, z, hz⟩ := W.left.affineCover.exists_eq y
  let c := HomScheme.affineCoverHom W k
  let b : Spec _ ⟶ Spec R := (HomScheme.affineCoverOver W k).hom
  let p : Over.mk b ⟶ T := c ≫ a
  have hp : IsOpenImmersion p.left := by
    let : IsOpenImmersion a.left := ha
    change IsOpenImmersion (W.left.affineCover.f k ≫ a.left)
    infer_instance
  have hpx : x ∈ Set.range p.left := ⟨z, by
    change a.left (W.left.affineCover.f k z) = x
    rw [hz, hy]⟩
  have hg' : HomScheme.evaluate p e.hom =
      (baseChange b).map (Diagonalizable.restrictMap R g.toAddMonoidHom) := by
    change HomScheme.evaluate (c ≫ a) e.hom = _
    rw [HomScheme.evaluate_comp, hg]
    exact Descent.pullHom_map c.left W.hom b (Over.w c) _
  have hh := congrArg (HomScheme.evaluate p) he
  change Descent.pullHom p.left (Over.w p) (Over.w p) (e.hom ≫ subgroupHom v T Q) =
    Descent.pullHom p.left (Over.w p) (Over.w p) (subgroupHom w T P) at hh
  rw [Descent.pullHom_comp, pullHom_subgroupHom, pullHom_subgroupHom] at hh
  change HomScheme.evaluate p e.hom ≫ subgroupHom v (Over.mk b) (Q.map p.left.appTop.hom) =
    subgroupHom w (Over.mk b) (P.map p.left.appTop.hom) at hh
  rw [hg'] at hh
  let : Nontrivial _ := PrimeSpectrum.nontrivial z
  obtain ⟨d, _, hd⟩ := exists_weightEquivalence_of_subgroupHom_comp b g
    (P.map p.left.appTop.hom) (Q.map p.left.appTop.hom) hw hv hh.symm
  exact ⟨⟨Over.mk b, p, hp, hpx, d, hd⟩⟩

end Langlands.GroupScheme.OrderedProjectorScheme
