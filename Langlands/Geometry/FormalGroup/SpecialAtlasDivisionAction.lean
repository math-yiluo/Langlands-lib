import Langlands.Geometry.FormalGroup.SpecialAtlasDivisionTwist
import Langlands.Geometry.FormalGroup.SpecialAtlasClassBaseChangeAlong

/-! # Division units act on special formal atlases and their comparison classes -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u v w s

namespace Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction

variable {O : Type u} [CommRing O] {R : Type v} [CommRing R] [Algebra O R]
variable {A : Type w} [Ring A] [Algebra O A]
variable {σ τ : Type} [Finite σ] [Finite τ]
variable {X : BasicAtlas O R σ} {Y : BasicAtlas O R τ}
variable {E : OrderAction A X} {E' : OrderAction A Y} {h : X.opens = Y.opens}

attribute [local instance] coefficientAlgebra coefficientScalarTower

/-- Twisting the two order actions keeps the same underlying formal map. -/
def Hom.twist (f : Hom E E' h) (α : A ≃ₐ[O] A) : Hom (E.twist α) (E'.twist α) h :=
  ⟨f.val, fun B b hb a => f.commutes B b hb (α a)⟩

private theorem twist_inv_hom (f : Iso E E' h) (α : A ≃ₐ[O] A) :
    (f.inv.twist α).comp (f.hom.twist α) = Hom.id (E.twist α) := by
  apply Subtype.ext
  apply BasicAtlas.Hom.ext
  intro B b hb
  exact congrArg (fun m : Hom E E rfl => m.val.hom B b hb) f.inv_hom

/-- Twisting both actions keeps the same actual inverse integral maps. -/
def Iso.twist (f : Iso E E' h) (α : A ≃ₐ[O] A) : Iso (E.twist α) (E'.twist α) h where
  hom := f.hom.twist α
  inv := f.inv.twist α
  inv_hom := twist_inv_hom f α
  hom_inv := twist_inv_hom f.symm α

/-- Twisting a comparison keeps its two actual refinements and inverse integral maps. -/
def Comparison.twist (f : Comparison E E') (α : A ≃ₐ[O] A) :
    Comparison (E.twist α) (E'.twist α) where
  left := f.left
  right := f.right
  sameCover := f.sameCover
  coordinateIso := f.coordinateIso.twist α

end Langlands.FormalGroup.ModuleLaw.BasicAtlas.OrderAction

namespace Langlands.FormalGroup.LocalDivision

open CategoryTheory ValuativeRel ModuleLaw

variable (K D : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {R : Type v} [CommRing R] [Algebra 𝒪[K] R]
variable {σ : Type} [Finite σ] {X : BasicAtlas 𝒪[K] R σ}

attribute [local instance] coefficientAlgebra coefficientScalarTower

private theorem atlasOrderAction_eq {E E' : BasicAtlas.OrderAction (IntegerRing K D) X}
    (h : E.chart = E'.chart) : E = E' := by
  cases E
  cases E'
  cases h
  rfl

@[simp]
theorem atlasTwist_one (E : BasicAtlas.OrderAction (IntegerRing K D) X) :
    atlasTwist K D E 1 = E := by
  apply atlasOrderAction_eq K D
  funext b
  exact twist_one K D (E.chart b)

theorem atlasTwist_twist (E : BasicAtlas.OrderAction (IntegerRing K D) X) (g h : Dˣ) :
    atlasTwist K D (atlasTwist K D E g) h = atlasTwist K D E (h * g) := by
  apply atlasOrderAction_eq K D
  funext b
  exact twist_twist K D (E.chart b) g h

private theorem cast_atlasQuasiIsogeny_eq
    {E E' E'' : BasicAtlas.OrderAction (IntegerRing K D) X} (h : E' = E'')
    {f : BasicAtlas.OrderAction.QuasiIsogeny K E E' rfl}
    {f' : BasicAtlas.OrderAction.QuasiIsogeny K E E'' rfl} (hf : f.hom.val = f'.hom.val) :
    cast (congrArg (fun Y => BasicAtlas.OrderAction.QuasiIsogeny K E Y rfl) h) f = f' := by
  subst E''
  exact BasicAtlas.OrderAction.QuasiIsogeny.ext_hom (BasicAtlas.OrderAction.RationalHom.ext hf)

/-- The identity division unit gives the actual whole atlas identity quasi-isogeny. -/
theorem atlasTwistQuasiIsogeny_one (E : BasicAtlas.OrderAction (IntegerRing K D) X) :
    cast (congrArg (fun Y => BasicAtlas.OrderAction.QuasiIsogeny K E Y rfl) (atlasTwist_one K D E))
      (atlasTwistQuasiIsogeny K D E 1) = BasicAtlas.OrderAction.QuasiIsogeny.refl (F := K) E := by
  apply cast_atlasQuasiIsogeny_eq K D (atlasTwist_one K D E)
  change atlasRationalAction K D E (((1 : Dˣ)⁻¹ : Dˣ) : D) = 1
  simp

/-- Whole atlas quasi-isogenies compose under the exact identification of the target actions. -/
theorem atlasTwistQuasiIsogeny_mul (E : BasicAtlas.OrderAction (IntegerRing K D) X) (g h : Dˣ) :
    cast (congrArg (fun Y => BasicAtlas.OrderAction.QuasiIsogeny K E Y rfl)
      (atlasTwist_twist K D E g h))
      ((atlasTwistQuasiIsogeny K D E g).trans (atlasTwistQuasiIsogeny K D (atlasTwist K D E g) h)) =
      atlasTwistQuasiIsogeny K D E (h * g) := by
  apply cast_atlasQuasiIsogeny_eq K D (atlasTwist_twist K D E g h)
  change atlasRationalAction K D (atlasTwist K D E g) ((h⁻¹ : Dˣ) : D) *
    atlasRationalAction K D E ((g⁻¹ : Dˣ) : D) = atlasRationalAction K D E (((h * g)⁻¹ : Dˣ) : D)
  rw [atlasRationalAction_twist, AlgHom.comp_apply, AlgEquiv.toAlgHom_apply,
    divisionConjugation_apply, ← map_mul]
  simp [mul_assoc]

variable {K D}
variable {L : Type s} [Field L] [Algebra K L] {ι : L →ₐ[K] D}

namespace SpecialAtlas

private theorem eq_of_order {Y Z : SpecialAtlas K D ι R}
    (h : Y.atlas = Z.atlas) (he : HEq Y.order Z.order) : Y = Z := by
  cases Y
  cases Z
  cases h
  cases eq_of_heq he
  rfl

@[simp]
theorem twistDivisionUnit_one (Y : SpecialAtlas K D ι R) : Y.twistDivisionUnit 1 = Y :=
  eq_of_order rfl (heq_of_eq (atlasTwist_one K D Y.order))

theorem twistDivisionUnit_mul (Y : SpecialAtlas K D ι R) (g h : Dˣ) :
    Y.twistDivisionUnit (g * h) = (Y.twistDivisionUnit h).twistDivisionUnit g :=
  eq_of_order rfl (heq_of_eq (atlasTwist_twist K D Y.order h g).symm)

/-- The original formal comparison induces a comparison of the special twists. -/
def Comparison.twistDivisionUnit {Y Z : SpecialAtlas K D ι R} (f : Comparison Y Z) (g : Dˣ) :
    Comparison (Y.twistDivisionUnit g) (Z.twistDivisionUnit g) :=
  BasicAtlas.OrderAction.Comparison.twist f (conjugation K D g)

omit [Algebra 𝒪[K] R] in
theorem twistDivisionUnit_reAlgebra {α : Algebra 𝒪[K] R}
    (Y : (letI := α; SpecialAtlas K D ι R)) (g : Dˣ) (β : Algebra 𝒪[K] R) (e : α = β) :
    (letI := α; (Y.twistDivisionUnit g).reAlgebra β e) =
      (letI := β; (Y.reAlgebra β e).twistDivisionUnit g) := by
  cases e
  rfl

variable {S : Type v} [CommRing S] [Algebra 𝒪[K] S]

theorem twistDivisionUnit_baseChangeAlong (Y : SpecialAtlas K D ι R) (g : Dˣ)
    (f : R →ₐ[𝒪[K]] S) :
    (Y.twistDivisionUnit g).baseChangeAlong f = (Y.baseChangeAlong f).twistDivisionUnit g := by
  unfold baseChangeAlong
  rw [twistDivisionUnit_baseChange]
  exact twistDivisionUnit_reAlgebra _ g _ _

namespace HeightSquaredAtlas

variable {π : 𝒪[K]}

theorem twistDivisionUnit_one
    (Y : HeightSquaredAtlas (K := K) (D := D) (ι := ι) (R := R) π) :
    Y.twistDivisionUnit 1 = Y :=
  Subtype.ext (SpecialAtlas.twistDivisionUnit_one Y.val)

theorem twistDivisionUnit_mul
    (Y : HeightSquaredAtlas (K := K) (D := D) (ι := ι) (R := R) π) (g h : Dˣ) :
    Y.twistDivisionUnit (g * h) = (Y.twistDivisionUnit h).twistDivisionUnit g :=
  Subtype.ext (SpecialAtlas.twistDivisionUnit_mul Y.val g h)

namespace IsoClass

/-- Division-unit twists descend to the original height-certified comparison classes. -/
def twistDivisionUnit (g : Dˣ) (q : IsoClass (K := K) (D := D) (ι := ι) (R := R) π) :
    IsoClass (K := K) (D := D) (ι := ι) (R := R) π :=
  Quotient.map (fun Y => Y.twistDivisionUnit g)
    (fun Y Z h => by
      change Equivalent Y Z at h
      exact h.map (fun f => f.twistDivisionUnit g)) q

@[simp]
theorem twistDivisionUnit_classOf (g : Dˣ)
    (Y : HeightSquaredAtlas (K := K) (D := D) (ι := ι) (R := R) π) :
    (classOf Y).twistDivisionUnit g = classOf (Y.twistDivisionUnit g) := rfl

/-- The comparison classes of height-certified special atlases carry the target division-unit action. -/
@[instance_reducible]
def divisionUnitAction :
    MulAction Dˣ (IsoClass (K := K) (D := D) (ι := ι) (R := R) π) where
  smul g q := q.twistDivisionUnit g
  one_smul q := by
    refine Quotient.inductionOn q (fun Y => ?_)
    exact congrArg classOf (HeightSquaredAtlas.twistDivisionUnit_one Y)
  mul_smul g h q := by
    refine Quotient.inductionOn q (fun Y => ?_)
    exact congrArg classOf (HeightSquaredAtlas.twistDivisionUnit_mul Y g h)

/-- Coefficient extension of the original classes commutes with the division-unit action. -/
theorem twistDivisionUnit_baseChangeAlong
    (q : IsoClass (K := K) (D := D) (ι := ι) (R := R) π) (g : Dˣ) (f : R →ₐ[𝒪[K]] S) :
    (q.twistDivisionUnit g).baseChangeAlong f = (q.baseChangeAlong f).twistDivisionUnit g := by
  refine Quotient.inductionOn q (fun Y => ?_)
  apply congrArg classOf
  apply Subtype.ext
  exact SpecialAtlas.twistDivisionUnit_baseChangeAlong Y.val g f

/-- Integral units act trivially on the target comparison classes by the existing integral comparison. -/
theorem twistDivisionUnit_integerUnit
    (q : IsoClass (K := K) (D := D) (ι := ι) (R := R) π) (a : (IntegerRing K D)ˣ) :
    q.twistDivisionUnit (integerUnit K D a) = q := by
  refine Quotient.inductionOn q (fun Y => ?_)
  exact HeightSquaredAtlas.classOf_twistIntegerUnit Y a

end IsoClass
end HeightSquaredAtlas
end SpecialAtlas
end Langlands.FormalGroup.LocalDivision
