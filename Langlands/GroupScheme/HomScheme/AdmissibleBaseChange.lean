import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreBaseChangeBasic
import Langlands.GroupScheme.HomScheme.AdmissibleMatching
import Langlands.GroupScheme.HomScheme.ChartCoverTransport

/-! # Base change of the actual torus-subgroup presheaf -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Opposite IsLocalRing

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.TorusSubgroupModuli

open SubgroupFunctor

variable {S S' : Scheme.{u}} {G : GroupScheme S}

private def admissibleEquivOfIso {B : Scheme.{u}} {P Q : GroupScheme B} (e : P ≅ Q) :
    AdmissibleSubgroup P ≃ AdmissibleSubgroup Q where
  toFun F := ⟨F.val.comap e.inv, isAdmissible_comapIso F e.symm⟩
  invFun F := ⟨F.val.comap e.hom, isAdmissible_comapIso F e⟩
  left_inv F := by
    apply Subtype.ext
    change (F.val.comap e.inv).comap e.hom = F.val
    rw [← comap_comp, Iso.hom_inv_id, comap_id]
  right_inv F := by
    apply Subtype.ext
    change (F.val.comap e.hom).comap e.inv = F.val
    rw [← comap_comp, Iso.inv_hom_id, comap_id]

private abbrev baseChangeAdmissibleEquiv (f : S' ⟶ S) (T : Over S') :=
  admissibleEquivOfIso (Descent.pullbackComparison f T.hom (T.hom ≫ f) rfl G)

private theorem baseChangeAdmissibleEquiv_natural (f : S' ⟶ S) {U T : Over S'} (a : U ⟶ T)
    (F : AdmissibleSubgroup ((baseChange T.hom).obj ((baseChange f).obj G))) :
    baseChangeAdmissibleEquiv (G := G) f U (restrict a F) =
      restrict ((Over.map f).map a) (baseChangeAdmissibleEquiv (G := G) f T F) := by
  let r := admissibleRepresentative F
  let e := Descent.pullbackComparison f T.hom (T.hom ≫ f) rfl G
  let p := (Over.map f).map a
  let F' : AdmissibleSubgroup ((baseChange ((Over.map f).obj T).hom).obj G) :=
    baseChangeAdmissibleEquiv (G := G) f T F
  let j := pushFamily (G := G) f r.hom
  let eU := Descent.pullbackComparison f U.hom (U.hom ≫ f) rfl G
  have hpush : range j = F'.val :=
    (range_comp_iso r.hom e).trans (congrArg (comap e.inv) r.represents.2)
  have h₁ : (restrict a F).val = range (familyHom r.hom a) :=
    restrict_eq_evaluate F r.hom r.represents.2 a
  have h₂ : (restrict p F').val = range (familyHom j p) :=
    restrict_eq_evaluate F' j hpush p
  have h₃ : familyHom j p = familyHom r.hom a ≫ eU.hom := familyHom_pushFamily f r.hom a
  apply Subtype.ext
  change comap eU.inv (restrict a F).val = (restrict p F').val
  exact (congrArg (comap eU.inv) h₁).trans ((range_comp_iso (familyHom r.hom a) eU).symm.trans
    ((congrArg range h₃.symm).trans h₂.symm))

/-- On each test scheme, identify subgroups of the iterated ambient pullback
with subgroups of the direct ambient pullback. -/
def smallAdmissibleBaseChangeEquiv (f : S' ⟶ S) (T : Over S') :
    (smallAdmissiblePresheaf ((baseChange f).obj G)).obj (op T) ≃
      (smallAdmissiblePresheaf G).obj (op ((Over.map f).obj T)) :=
  (smallAdmissibleEquiv _ T).trans
    ((baseChangeAdmissibleEquiv (G := G) f T).trans (smallAdmissibleEquiv G ((Over.map f).obj T)).symm)

private theorem decode_baseChangeEquiv (f : S' ⟶ S) (T : Over S')
    (x : (smallAdmissiblePresheaf ((baseChange f).obj G)).obj (op T)) :
    smallAdmissibleEquiv G ((Over.map f).obj T) (smallAdmissibleBaseChangeEquiv f T x) =
      baseChangeAdmissibleEquiv (G := G) f T (smallAdmissibleEquiv _ T x) :=
  (smallAdmissibleEquiv G ((Over.map f).obj T)).apply_symm_apply _

set_option maxHeartbeats 800000 in
/-- The torus-subgroup presheaf of the actual pullback agrees naturally with
restriction of the original presheaf to the changed base. -/
def smallAdmissiblePresheafBaseChangeIso (f : S' ⟶ S) :
    smallAdmissiblePresheaf ((GroupScheme.baseChange f).obj G) ≅
      Langlands.AlgebraicGeometry.UnramifiedFunctor.baseChange f (smallAdmissiblePresheaf G) := by
  refine NatIso.ofComponents (fun T => ?_) ?_
  · exact Equiv.toIso (smallAdmissibleBaseChangeEquiv (G := G) f T.unop)
  · intro T U a
    obtain ⟨T, rfl⟩ := Opposite.op_surjective T
    obtain ⟨U, rfl⟩ := Opposite.op_surjective U
    let b := a.unop
    have hb : b.op = a := Quiver.Hom.op_unop _
    rw [← hb]
    apply TypeCat.homEquiv.injective
    funext x
    apply (smallAdmissibleEquiv G ((Over.map f).obj U)).injective
    change smallAdmissibleEquiv G ((Over.map f).obj U)
        ((smallAdmissibleBaseChangeEquiv (G := G) f U)
          ((smallAdmissiblePresheaf ((GroupScheme.baseChange f).obj G)).map b.op x)) =
      smallAdmissibleEquiv G ((Over.map f).obj U)
        ((smallAdmissiblePresheaf G).map ((Over.map f).map b).op
          ((smallAdmissibleBaseChangeEquiv (G := G) f T) x))
    rw [decode_baseChangeEquiv f U, smallAdmissibleEquiv_map b x,
      smallAdmissibleEquiv_map ((Over.map f).map b), decode_baseChangeEquiv f T x]
    exact baseChangeAdmissibleEquiv_natural f b (smallAdmissibleEquiv _ T x)

open Langlands.AlgebraicGeometry.UnramifiedFunctor

private theorem adicLimits_of_iso {P Q : (Over S)ᵒᵖ ⥤ Type u} (e : P ≅ Q) (h : AdicLimits Q) :
    AdicLimits P := by
  intro A _ _ _ _ f
  let M := Over.mk f
  let R (n : ℕ) := A ⧸ maximalIdeal A ^ n
  let T (n : ℕ) := algebraOver f (R n)
  let a (n : ℕ) : T n ⟶ M := algebraOverBase f (R n)
  let b (n : ℕ) : T n ⟶ T (n + 1) := algHomOver f
    (Ideal.Quotient.factorₐ A (Ideal.pow_le_pow_right (I := maximalIdeal A) n.le_succ))
  let E (V : Over S) := (e.app (op V)).toEquiv
  have hnat {U V : Over S} (p : U ⟶ V) (x : P.obj (op V)) :
      E U (P.map p.op x) = Q.map p.op (E V x) :=
    congrArg (fun a => a x) (e.hom.naturality p.op)
  constructor
  · intro x y hxy
    apply (E M).injective
    apply (h A f).1
    intro n
    rw [← hnat (a n), ← hnat (a n), hxy n]
  · intro r hr
    obtain ⟨x, hx⟩ := (h A f).2 (fun n => E (T n) (r n)) (fun n => by
      rw [← hnat (b n), hr n])
    refine ⟨(E M).symm x, fun n => (E (T n)).injective ?_⟩
    rw [hnat (a n), Equiv.apply_symm_apply, hx n]

/-- Adic-limit bijectivity for the actual torus-subgroup presheaf is preserved
by arbitrary base change in the fixed universe. -/
def AdmissibleAdicLimitsBaseChangeStatement : Prop :=
  ∀ {S S' : Scheme.{u}} (f : S' ⟶ S) (G : GroupScheme S),
    AdicLimits (smallAdmissiblePresheaf G) →
      AdicLimits (smallAdmissiblePresheaf ((GroupScheme.baseChange f).obj G))

theorem admissibleAdicLimits_baseChange : AdmissibleAdicLimitsBaseChangeStatement.{u} := by
  intro S S' f G h
  exact adicLimits_of_iso (smallAdmissiblePresheafBaseChangeIso (G := G) f)
    (BaseChange.adicLimits f (smallAdmissiblePresheaf G) h)

end Langlands.GroupScheme.TorusSubgroupModuli
