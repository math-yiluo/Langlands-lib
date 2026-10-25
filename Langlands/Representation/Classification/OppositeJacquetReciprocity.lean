import Langlands.Representation.Classification.OppositeSupportJacquetAdapter
import Mathlib.RepresentationTheory.Semisimple

/-! Orbit functions for the actual opposite normalized Jacquet action. -/

noncomputable section

namespace Langlands

universe uR uG uV uW

/-- An actual equivariant retraction of an injection into a semisimple action. -/
def semisimpleRetraction
    {R : Type uR} [Field R] {G : Type uG} [Monoid G]
    {V : Type uV} {W : Type uW}
    [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
    {ρ : Representation R G V} {τ : Representation R G W}
    (hτ : Representation.IsSemisimpleRepresentation τ)
    (j : ρ.IntertwiningMap τ) (hj : Function.Injective j) :
    {r : τ.IntertwiningMap ρ // r.comp j = Representation.IntertwiningMap.id ρ} := by
  letI : IsSemisimpleModule (MonoidAlgebra R G) τ.asModule :=
    (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule τ).mp hτ
  let J := Representation.IntertwiningMap.equivLinearMapAsModule ρ τ j
  let hex := IsSemisimpleModule.extension_property J hj
    (LinearMap.id : ρ.asModule →ₗ[MonoidAlgebra R G] ρ.asModule)
  let r := Classical.choose hex
  have hr := Classical.choose_spec hex
  refine ⟨(Representation.IntertwiningMap.equivLinearMapAsModule τ ρ).symm r, ?_⟩
  ext v
  exact congrArg (fun f : ρ.asModule →ₗ[MonoidAlgebra R G] ρ.asModule => f v) hr

end Langlands

namespace Langlands.OppositeSupport

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
variable (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)
variable {V : Type uV} {W : Type uW}
variable [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
variable (π : Representation ℂ (GeneralLinear n F.Carrier) V)
variable (σ : Representation ℂ (B.Levi F.Carrier) W)

/-- Every opposite-parabolic element acts on coinvariants by its Levi part. -/
theorem mk_oppositeParabolic (a : B.oppositeParabolic F.Carrier) (v : V) :
    Jacquet.mk π (B.oppositeUnipotentSubgroup F.Carrier) (π a v) =
      Jacquet.mk π (B.oppositeUnipotentSubgroup F.Carrier)
        (π (B.leviEmbedding F.Carrier (B.oppositeLeviProjection F.Carrier a)) v) := by
  let u := B.oppositeUnipotentPart F.Carrier a
  let u' : B.oppositeUnipotentSubgroup F.Carrier :=
    ⟨u.val.val, ⟨u.val, u.property, rfl⟩⟩
  have ha : (a : GeneralLinear n F.Carrier) =
      (u' : GeneralLinear n F.Carrier) *
        B.leviEmbedding F.Carrier (B.oppositeLeviProjection F.Carrier a) := by
    change (a : GeneralLinear n F.Carrier) =
      ((a : GeneralLinear n F.Carrier) *
        (B.leviEmbedding F.Carrier (B.oppositeLeviProjection F.Carrier a))⁻¹) *
          B.leviEmbedding F.Carrier (B.oppositeLeviProjection F.Carrier a)
    simp
  rw [ha, map_mul, Module.End.mul_apply]
  exact Jacquet.mk_apply_subgroup π _ u' _

/-- A map from the normalized quotient has opposite-half covariance on vectors. -/
theorem jacquetMap_covariance
    (A : (jacquetAction T B π).IntertwiningMap σ)
    (a : B.oppositeParabolic F.Carrier) (v : V) :
    A (Jacquet.mk π (B.oppositeUnipotentSubgroup F.Carrier) (π a v)) =
      (T.oppositeParabolicHalfModulus B a : ℂ) •
        σ (B.oppositeLeviProjection F.Carrier a)
          (A (Jacquet.mk π (B.oppositeUnipotentSubgroup F.Carrier) v)) := by
  rw [mk_oppositeParabolic]
  have h := Representation.IntertwiningMap.isIntertwining _ _ A
    (B.oppositeLeviProjection F.Carrier a)
    (Jacquet.mk π (B.oppositeUnipotentSubgroup F.Carrier) v)
  rw [jacquetAction_mk, map_smul] at h
  have hh := congrArg
    (fun w : W => (((T.leviHalfModulus B
      (B.oppositeLeviProjection F.Carrier a))⁻¹ : ℂˣ) : ℂ) • w) h
  simpa only [smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    one_smul, PadicField.TopologicalData.oppositeParabolicHalfModulus_apply] using hh

/-- The orbit function attached to a map out of the normalized opposite quotient. -/
def jacquetOrbitMap (A : (jacquetAction T B π).IntertwiningMap σ) :
    π.IntertwiningMap (Induction.equivariantAction
      (B.oppositeParabolic F.Carrier)
      (twist (T.oppositeParabolicHalfModulus B)
        (σ.comp (B.oppositeLeviProjection F.Carrier)))) where
  toLinearMap :=
    { toFun := fun v => ⟨fun g =>
        A (Jacquet.mk π (B.oppositeUnipotentSubgroup F.Carrier) (π g v)), by
        intro a g
        change A (Jacquet.mk π (B.oppositeUnipotentSubgroup F.Carrier)
          (π ((a : GeneralLinear n F.Carrier) * g) v)) = _
        rw [map_mul, Module.End.mul_apply]
        exact jacquetMap_covariance T B π σ A a (π g v)⟩
      map_add' := by intros; ext g; simp
      map_smul' := by intros; ext g; simp }
  isIntertwining' g := by
    ext v x
    change A (Jacquet.mk π (B.oppositeUnipotentSubgroup F.Carrier) (π x (π g v))) =
      A (Jacquet.mk π (B.oppositeUnipotentSubgroup F.Carrier) (π (x * g) v))
    rw [map_mul, Module.End.mul_apply]

/-- Smooth source vectors give uniformly smooth orbit functions in opposite induction. -/
def fromJacquet (hπ : letI := T.topology; IsSmooth π)
    (A : (jacquetAction T B π).IntertwiningMap σ) :
    letI := T.topology
    π.IntertwiningMap (T.normalizedOppositeParabolicInduced B σ) :=
  letI := T.topology
  letI := T.generalLinearTopologicalGroup n
  smoothLift hπ (jacquetOrbitMap T B π σ A)

@[simp]
theorem fromJacquet_apply (hπ : letI := T.topology; IsSmooth π)
    (A : (jacquetAction T B π).IntertwiningMap σ)
    (v : V) (g : GeneralLinear n F.Carrier) :
    ((fromJacquet T B π σ hπ A v).1.1) g =
      A (Jacquet.mk π (B.oppositeUnipotentSubgroup F.Carrier) (π g v)) := rfl

/-- Evaluation and the orbit construction are inverse linear maps. -/
def reciprocityEquiv (hπ : letI := T.topology; IsSmooth π) :
    letI := T.topology
    (π.IntertwiningMap (T.normalizedOppositeParabolicInduced B σ)) ≃ₗ[ℂ]
      ((jacquetAction T B π).IntertwiningMap σ) :=
  letI := T.topology
  { toFun := jacquetEvaluation T B π σ
    invFun := fromJacquet T B π σ hπ
    left_inv := by
      intro j
      ext v g
      change evaluation T B π σ j (π g v) = (j v).1.1 g
      exact evaluation_translate T B π σ j g v
    right_inv := by
      intro A
      ext v
      change A (Jacquet.mk π (B.oppositeUnipotentSubgroup F.Carrier) (π 1 v)) =
        A (Jacquet.mk π (B.oppositeUnipotentSubgroup F.Carrier) v)
      rw [map_one, Module.End.one_apply]
    map_add' := by intros; ext v; rfl
    map_smul' := by intros; ext v; rfl }

/-- A nonzero Jacquet map has a nonzero orbit-function intertwiner. -/
theorem fromJacquet_ne_zero (hπ : letI := T.topology; IsSmooth π)
    (A : (jacquetAction T B π).IntertwiningMap σ) (hA : A ≠ 0) :
    fromJacquet T B π σ hπ A ≠ 0 := by
  let := T.topology
  intro h
  apply hA
  ext v
  change A (Jacquet.mk π (B.oppositeUnipotentSubgroup F.Carrier) v) = 0
  have hv := congrArg (fun j : π.IntertwiningMap
    (T.normalizedOppositeParabolicInduced B σ) => (j v).1.1 1) h
  change A (Jacquet.mk π (B.oppositeUnipotentSubgroup F.Carrier) (π 1 v)) = 0 at hv
  simpa only [map_one, Module.End.one_apply] using hv

/-- For irreducible source the nonzero orbit map is injective. -/
theorem fromJacquet_injective (hπ : letI := T.topology; IsSmooth π)
    (hπirr : Representation.IsIrreducible π)
    (A : (jacquetAction T B π).IntertwiningMap σ) (hA : A ≠ 0) :
    Function.Injective (fromJacquet T B π σ hπ A) := by
  let := hπirr
  exact (Representation.IsIrreducible.injective_or_eq_zero
    (fromJacquet T B π σ hπ A)).resolve_right
      (fromJacquet_ne_zero T B π σ hπ A hA)

/-- A quotient of the actual opposite Jacquet representation gives an embedding
into the actual opposite normalized induction, and conversely. -/
theorem quotient_iff_embedding (hπ : letI := T.topology; IsSmooth π)
    (hπirr : Representation.IsIrreducible π) (hσirr : Representation.IsIrreducible σ) :
    (∃ A : (jacquetAction T B π).IntertwiningMap σ, Function.Surjective A) ↔
      (letI := T.topology
       ∃ j : π.IntertwiningMap (T.normalizedOppositeParabolicInduced B σ),
         Function.Injective j) := by
  let := T.topology
  constructor
  · rintro ⟨A, hA⟩
    let := hσirr
    have : Nontrivial W :=
      IsSimpleModule.nontrivial (MonoidAlgebra ℂ (B.Levi F.Carrier)) σ.asModule
    have hA0 : A ≠ 0 := by
      intro hz
      obtain ⟨w, hw⟩ := exists_ne (0 : W)
      obtain ⟨q, hq⟩ := hA w
      apply hw
      rw [hz] at hq
      exact hq.symm
    exact ⟨fromJacquet T B π σ hπ A,
      fromJacquet_injective T B π σ hπ hπirr A hA0⟩
  · rintro ⟨j, hj⟩
    let := hπirr
    have : Nontrivial V :=
      IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GeneralLinear n F.Carrier)) π.asModule
    have hj0 : j ≠ 0 := by
      intro hz
      obtain ⟨v, hv⟩ := exists_ne (0 : V)
      apply hv
      apply hj
      rw [hz]
      rfl
    exact ⟨jacquetEvaluation T B π σ j,
      jacquetEvaluation_surjective T B π σ hσirr j hj0⟩

/-- With opposite-induced semisimplicity supplied explicitly, the quotient gives
actual splitting maps. No analytic semisimplicity result is assumed implicitly. -/
theorem quotient_iff_summand (hπ : letI := T.topology; IsSmooth π)
    (hπirr : Representation.IsIrreducible π) (hσirr : Representation.IsIrreducible σ)
    (hss : letI := T.topology
      Representation.IsSemisimpleRepresentation (T.normalizedOppositeParabolicInduced B σ)) :
    (∃ A : (jacquetAction T B π).IntertwiningMap σ, Function.Surjective A) ↔
      (letI := T.topology
       ∃ (j : π.IntertwiningMap (T.normalizedOppositeParabolicInduced B σ))
         (r : (T.normalizedOppositeParabolicInduced B σ).IntertwiningMap π),
           r.comp j = Representation.IntertwiningMap.id π) := by
  let := T.topology
  rw [quotient_iff_embedding T B π σ hπ hπirr hσirr]
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨j, (semisimpleRetraction hss j hj).val,
      (semisimpleRetraction hss j hj).property⟩
  · rintro ⟨j, r, hr⟩
    refine ⟨j, ?_⟩
    intro v w hvw
    have h (x : V) : r (j x) = x :=
      congrArg (fun f : π.IntertwiningMap π => f x) hr
    rw [← h v, ← h w, hvw]

end Langlands.OppositeSupport
