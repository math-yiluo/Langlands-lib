import Langlands.GroupScheme.Dynamic.ParabolicLieCriterion
import Langlands.GroupScheme.HomScheme.ChartCoverTransport
import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreCriterionStatement
import Langlands.GroupScheme.Derived.RelativeMaximalTorusProduct
import Langlands.GroupScheme.HomScheme.AdicClosedSubgroupContainment
import Langlands.GroupScheme.HomScheme.AdmissiblePresheaf
import Langlands.GroupScheme.Rational.LeviCentralizerExtension
import Langlands.GroupScheme.Rational.ParabolicAmbientTransport
import Langlands.GroupScheme.Rational.SplitRankTransport

/-! # Adic limits of torus subgroups pass to closed subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite IsLocalRing

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.TorusSubgroupModuli

open SubgroupFunctor Langlands.AlgebraicGeometry.UnramifiedFunctor

variable {S : Scheme.{u}} {H G : GroupScheme S}

private def pushAdmissible (i : H ⟶ G) (hi : IsClosedSubgroup i) (F : AdmissibleSubgroup H) :
    AdmissibleSubgroup G :=
  let r := admissibleRepresentative F
  ⟨range (r.hom ≫ i), isAdmissible_range _ (r.closed.comp hi) r.torus⟩

private theorem pushAdmissible_injective (i : H ⟶ G) (hi : IsClosedSubgroup i) :
    Function.Injective (pushAdmissible i hi) := by
  intro F F' h
  let r := admissibleRepresentative F
  let r' := admissibleRepresentative F'
  have hh : range (r.hom ≫ i) = range (r'.hom ≫ i) := congrArg Subtype.val h
  have : IsClosedImmersion i.hom.hom.left := hi
  have hm : Mono i.hom.hom := Over.mono_of_mono_left _
  apply Subtype.ext
  rw [← r.represents.2, ← r'.represents.2]
  exact le_antisymm ((range_comp_le_iff_of_mono _ _ i hm).mp hh.le)
    ((range_comp_le_iff_of_mono _ _ i hm).mp hh.ge)

private abbrev pushAt (i : H ⟶ G) (hi : IsClosedSubgroup i) (T : Over S) :=
  pushAdmissible ((baseChange T.hom).map i) (IsClosedSubgroup.baseChange T.hom hi)

private theorem pushAt_restrict (i : H ⟶ G) (hi : IsClosedSubgroup i) {U T : Over S}
    (a : U ⟶ T) (F : AdmissibleSubgroup ((baseChange T.hom).obj H)) :
    pushAt i hi U (restrict a F) = restrict a (pushAt i hi T F) := by
  let r := admissibleRepresentative F
  let r' := admissibleRepresentative (restrict a F)
  apply Subtype.ext
  have h : range r'.hom = range (familyHom r.hom a) :=
    r'.represents.2.trans (restrict_eq_evaluate F r.hom r.represents.2 a)
  change range (r'.hom ≫ (baseChange U.hom).map i) = (restrict a (pushAt i hi T F)).val
  rw [restrict_eq_evaluate (pushAt i hi T F) (r.hom ≫ (baseChange T.hom).map i) rfl a,
    evaluate, Langlands.GroupScheme.TorusSubgroupModuli.familyHom_postcomp]
  exact range_comp_eq_of_range_eq _ _ _ h

/-- A closed ambient inclusion induces an inclusion of the actual small torus
subgroup presheaves by composition of closed embeddings. -/
def smallAdmissibleClosedInclusion (i : H ⟶ G) (hi : IsClosedSubgroup i) :
    smallAdmissiblePresheaf H ⟶ smallAdmissiblePresheaf G where
  app T := TypeCat.ofHom fun x =>
    (smallAdmissibleEquiv G T.unop).symm (pushAt i hi T.unop (smallAdmissibleEquiv H T.unop x))
  naturality T U a := by
    apply TypeCat.homEquiv.injective
    funext x
    change (smallAdmissibleEquiv G U.unop).symm
        (pushAt i hi U.unop (smallAdmissibleEquiv H U.unop
          ((smallAdmissiblePresheaf H).map a x))) =
      (smallAdmissiblePresheaf G).map a ((smallAdmissibleEquiv G T.unop).symm
        (pushAt i hi T.unop (smallAdmissibleEquiv H T.unop x)))
    obtain ⟨T, rfl⟩ := Opposite.op_surjective T
    obtain ⟨U, rfl⟩ := Opposite.op_surjective U
    let b := a.unop
    have ha : b.op = a := Quiver.Hom.op_unop _
    rw [← ha]
    apply (smallAdmissibleEquiv G U).injective
    rw [Equiv.apply_symm_apply, smallAdmissibleEquiv_map b x,
      smallAdmissibleEquiv_map b, Equiv.apply_symm_apply]
    exact pushAt_restrict i hi b _

private theorem smallAdmissibleClosedInclusion_injective (i : H ⟶ G) (hi : IsClosedSubgroup i)
    (T : Over S) : Function.Injective ((smallAdmissibleClosedInclusion i hi).app (op T)) :=
  ((smallAdmissibleEquiv G T).symm.injective.comp
    (pushAdmissible_injective ((baseChange T.hom).map i) (hi.baseChange T.hom))).comp
    (smallAdmissibleEquiv H T).injective

private theorem inclusion_eval (i : H ⟶ G) (hi : IsClosedSubgroup i) {U T : Over S}
    (a : U ⟶ T) (x : (smallAdmissiblePresheaf G).obj (op T))
    (y : (smallAdmissiblePresheaf H).obj (op U))
    (h : (smallAdmissiblePresheaf G).map a.op x = (smallAdmissibleClosedInclusion i hi).app (op U) y) :
    evaluate (admissibleRepresentative (smallAdmissibleEquiv G T x)).hom a =
      range ((admissibleRepresentative (smallAdmissibleEquiv H U y)).hom ≫
        (baseChange U.hom).map i) := by
  have h' := congrArg (smallAdmissibleEquiv G U) h
  rw [smallAdmissibleEquiv_map a x] at h'
  change restrict a (smallAdmissibleEquiv G T x) = smallAdmissibleEquiv G U
    ((smallAdmissibleEquiv G U).symm (pushAt i hi U (smallAdmissibleEquiv H U y))) at h'
  rw [Equiv.apply_symm_apply] at h'
  let r := admissibleRepresentative (smallAdmissibleEquiv G T x)
  change evaluate r.hom a = (pushAt i hi U (smallAdmissibleEquiv H U y)).val
  rw [← restrict_eq_evaluate _ r.hom r.represents.2 a]
  exact congrArg Subtype.val h'

private theorem exists_closedInclusion_preimage (i : H ⟶ G) (hi : IsClosedSubgroup i)
    {T : Over S} (x : (smallAdmissiblePresheaf G).obj (op T))
    (hx : range (admissibleRepresentative (smallAdmissibleEquiv G T x)).hom ≤
      range ((baseChange T.hom).map i)) :
    ∃ y : (smallAdmissiblePresheaf H).obj (op T),
      (smallAdmissibleClosedInclusion i hi).app (op T) y = x := by
  let a := (baseChange T.hom).map i
  let r := admissibleRepresentative (smallAdmissibleEquiv G T x)
  have : IsClosedImmersion a.hom.hom.left := hi.baseChange T.hom
  let j := rangeFactor r.hom a hx
  have hj := rangeFactor_comp r.hom a hx
  have hc : IsClosedSubgroup j := by
    have h := congrArg (fun f => f.hom.hom.left) hj
    simp only [Grp.comp_hom_hom, Over.comp_left] at h
    have : IsClosedImmersion (j.hom.hom.left ≫ a.hom.hom.left) := h.symm ▸ r.closed
    exact IsClosedImmersion.of_comp_isClosedImmersion j.hom.hom.left a.hom.hom.left
  let F : AdmissibleSubgroup ((baseChange T.hom).obj H) := ⟨range j, isAdmissible_range j hc r.torus⟩
  refine ⟨(smallAdmissibleEquiv H T).symm F, (smallAdmissibleEquiv G T).injective ?_⟩
  change smallAdmissibleEquiv G T ((smallAdmissibleEquiv G T).symm
      (pushAt i hi T (smallAdmissibleEquiv H T ((smallAdmissibleEquiv H T).symm F)))) = _
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  apply Subtype.ext
  change range ((admissibleRepresentative F).hom ≫ a) = _
  exact (range_comp_eq_of_range_eq _ j a (admissibleRepresentative F).represents.2).trans
    ((congrArg SubgroupFunctor.range hj).trans r.represents.2)

/-- If the ambient presheaf of actual closed tori has adic limits, so does
that of an actual closed subgroup. -/
def AdicClosedSubgroupInheritanceStatement : Prop :=
  ∀ {S : Scheme.{u}} {H G : GroupScheme S} (i : H ⟶ G), IsClosedSubgroup i →
    AdicLimits (smallAdmissiblePresheaf G) → AdicLimits (smallAdmissiblePresheaf H)

set_option maxHeartbeats 1200000 in
/-- Lift the ambient system and test that its lifted torus factors through
the closed subgroup using all adic restrictions. -/
theorem adicLimits_of_closedSubgroup : AdicClosedSubgroupInheritanceStatement.{u} := by
  intro S H G i hi hadic A _ _ _ _ f
  let η := smallAdmissibleClosedInclusion i hi
  let M := Over.mk f
  let R (n : ℕ) := A ⧸ maximalIdeal A ^ n
  let T (n : ℕ) := algebraOver f (R n)
  let a (n : ℕ) : T n ⟶ M := algebraOverBase f (R n)
  let b (n : ℕ) : T n ⟶ T (n + 1) := algHomOver f
    (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right (I := maximalIdeal A) n.le_succ))
  have hnat {X Y : Over S} (d : X ⟶ Y) (z : (smallAdmissiblePresheaf H).obj (op Y)) :
      η.app (op X) ((smallAdmissiblePresheaf H).map d.op z) =
        (smallAdmissiblePresheaf G).map d.op (η.app (op Y) z) := by
    exact congrArg (fun m => m z) (η.naturality d.op)
  constructor
  · intro x y hx
    apply smallAdmissibleClosedInclusion_injective i hi M
    apply (hadic A f).1
    intro n
    rw [← hnat (a n) x, ← hnat (a n) y, hx n]
  · intro s hs
    obtain ⟨x, hx⟩ := (hadic A f).2 (fun n => η.app (op (T n)) (s n)) (fun n => by
      rw [← hnat (b n) (s (n + 1)), hs n])
    let r := admissibleRepresentative (smallAdmissibleEquiv G M x)
    let c := (baseChange f).map i
    have hc : IsClosedSubgroup c := hi.baseChange f
    have hle (n : ℕ) : range ((baseChange (a n).left).map r.hom) ≤
        range ((baseChange (a n).left).map c) := by
      let e := Descent.pullbackComparison M.hom (a n).left (T n).hom (a n).w G
      let eH := Descent.pullbackComparison M.hom (a n).left (T n).hom (a n).w H
      apply (range_comp_iso_le_iff _ _ e).mp
      have hh : (baseChange (a n).left).map c ≫ e.hom = eH.hom ≫ (baseChange (T n).hom).map i :=
        Descent.pullbackComparison_naturality M.hom (a n).left (T n).hom (a n).w i
      rw [hh, range_iso_comp]
      change evaluate r.hom (a n) ≤ _
      rw [inclusion_eval i hi (a n) x (s n) (hx n)]
      exact SubgroupFunctor.range_comp_le _ _
    have h := range_le_of_adic_restrictions (R := CommRingCat.of A) r.hom c r.torus hc hle
    obtain ⟨y, hy⟩ := exists_closedInclusion_preimage i hi x h
    refine ⟨y, fun n => smallAdmissibleClosedInclusion_injective i hi (T n) ?_⟩
    rw [hnat (a n) y, hy, hx n]

end Langlands.GroupScheme.TorusSubgroupModuli
