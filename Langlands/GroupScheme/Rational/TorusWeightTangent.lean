import Langlands.GroupScheme.Rational.TorusWeightPrimitive
import Langlands.GroupScheme.GeneralLinearDualNumber
import Langlands.Algebra.GradedAugmentedVanishing

/-! # Weight tangent vectors and maximality of weight subgroups -/

noncomputable section

universe u

open CategoryTheory

namespace Langlands.GroupScheme.Corepresented

open GeneralLinear.DualNumber (coefficientAlgMap epsilonScaleAlg)
open AffineLinearEmbedding (counit)

section General

variable {R : CommRingCat.{u}} {F : CommAlgCat.{u} R ⥤ GrpCat.{u}} {B : CommAlgCat.{u} R}
  (e : (F ⋙ forget GrpCat).CorepresentableBy B)

section Tangent

/-- The reduction map from dual numbers. -/
abbrev dualReduction (A : CommAlgCat.{u} R) : CommAlgCat.of R (DualNumber A) ⟶ A :=
  CommAlgCat.ofHom (TrivSqZeroExt.fstHom R A A)

/-- The coordinates of a point over the dual numbers reducing to the identity. -/
theorem coord_eq_of_reduction {A : CommAlgCat.{u} R} {X : F.obj (CommAlgCat.of R (DualNumber A))}
    (hX : F.map (dualReduction A) X = 1) (f : B) :
    coord e X f = TrivSqZeroExt.inl (algebraMap R A (counit e f)) +
      TrivSqZeroExt.inr (coord e X f).snd := by
  have h := (eq_one_iff e).1 hX f
  rw [coord_map, AlgHom.comp_apply, CommAlgCat.hom_ofHom] at h
  apply TrivSqZeroExt.ext
  · rw [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero]
    exact h
  · rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]

/-- A point over the dual numbers reducing to the identity, whose infinitesimal coordinates
vanish, is the identity. -/
theorem eq_one_of_snd_eq_zero {A : CommAlgCat.{u} R}
    {X : F.obj (CommAlgCat.of R (DualNumber A))}
    (hX : F.map (dualReduction A) X = 1) (h : ∀ f, (coord e X f).snd = 0) : X = 1 := by
  refine (eq_one_iff e).2 fun f => ?_
  rw [coord_eq_of_reduction e hX f, h f, TrivSqZeroExt.inr_zero, add_zero,
    TrivSqZeroExt.algebraMap_eq_inl']

end Tangent

variable {I : Type u} [Fintype I] [DecidableEq I] (σ : TorusAction F I)

section Weights

/-- Algebra maps out of the representing algebra agree when they agree on all weight
components. -/
theorem algHom_ext_comp {A' : Type u} [CommRing A'] [Algebra R A'] {φ ψ : B →ₐ[R] A'}
    (h : ∀ m f, φ (comp e σ m f) = ψ (comp e σ m f)) : φ = ψ := by
  apply AlgHom.ext
  intro f
  rw [← sum_support_comp e σ f, map_sum, map_sum]
  exact Finset.sum_congr rfl fun m _ => h m f

/-- A tangent vector of weight `χ`: the torus acts on its coefficient extensions through the
character `χ`, by scaling the infinitesimal. -/
def IsWeightTangent (χ : I → ℤ) (X : F.obj (CommAlgCat.of R (DualNumber R))) : Prop :=
  ∀ (A : CommAlgCat.{u} R) (t : I → Aˣ),
    σ.act (fun i => Units.map (TrivSqZeroExt.inlAlgHom R A A).toMonoidHom (t i))
        (F.map (CommAlgCat.ofHom (coefficientAlgMap (Algebra.ofId R A))) X) =
      F.map (CommAlgCat.ofHom (epsilonScaleAlg (R := R)
          (splitTorus.exponentValue I t (Multiplicative.ofAdd χ) : A)))
        (F.map (CommAlgCat.ofHom (coefficientAlgMap (Algebra.ofId R A))) X)

omit [Fintype I] [DecidableEq I] in
theorem epsilonScaleAlg_fst {A : Type u} [CommRing A] [Algebra R A] (c : A) (z : DualNumber A) :
    (epsilonScaleAlg (R := R) c z).fst = z.fst :=
  GeneralLinear.DualNumber.epsilonScale_fst c z

omit [Fintype I] [DecidableEq I] in
theorem epsilonScaleAlg_snd {A : Type u} [CommRing A] [Algebra R A] (c : A) (z : DualNumber A) :
    (epsilonScaleAlg (R := R) c z).snd = c * z.snd :=
  GeneralLinear.DualNumber.epsilonScale_snd c z

omit [Fintype I] [DecidableEq I] in
theorem coefficientAlgMap_fst {A A' : Type u} [CommRing A] [Algebra R A] [CommRing A']
    [Algebra R A'] (g : A →ₐ[R] A') (z : DualNumber A) :
    (coefficientAlgMap g z).fst = g z.fst :=
  rfl

omit [Fintype I] [DecidableEq I] in
theorem coefficientAlgMap_snd {A A' : Type u} [CommRing A] [Algebra R A] [CommRing A']
    [Algebra R A'] (g : A →ₐ[R] A') (z : DualNumber A) :
    (coefficientAlgMap g z).snd = g z.snd :=
  rfl

omit [Fintype I] [DecidableEq I] in
theorem units_map_inlAlgHom {A : Type u} [CommRing A] [Algebra R A] (v : Aˣ) :
    ((Units.map (TrivSqZeroExt.inlAlgHom R A A).toMonoidHom v : (DualNumber A)ˣ) :
      DualNumber A) = TrivSqZeroExt.inl (v : A) :=
  rfl

/-- The coordinates at a homogeneous function of the torus action on a coefficient extension of
a tangent vector, and of the corresponding scaling. -/
theorem coord_act_coefficient {X : F.obj (CommAlgCat.of R (DualNumber R))}
    (A : CommAlgCat.{u} R) (t : I → Aˣ) {m : I → ℤ} {h : B} (hh : IsHomogeneous e σ m h) :
    coord e (σ.act (fun i => Units.map (TrivSqZeroExt.inlAlgHom R A A).toMonoidHom (t i))
        (F.map (CommAlgCat.ofHom (coefficientAlgMap (Algebra.ofId R A))) X)) h =
      coefficientAlgMap (Algebra.ofId R A) (coord e X h) *
        TrivSqZeroExt.inl (splitTorus.exponentValue I t (Multiplicative.ofAdd m) : A) := by
  rw [coord_act_of_isHomogeneous e σ _ _ hh, exponentValue_map, units_map_inlAlgHom, coord_map]
  rfl

theorem coord_scale_coefficient {X : F.obj (CommAlgCat.of R (DualNumber R))}
    (A : CommAlgCat.{u} R) (c : A) (h : B) :
    coord e (F.map (CommAlgCat.ofHom (epsilonScaleAlg (R := R) c))
        (F.map (CommAlgCat.ofHom (coefficientAlgMap (Algebra.ofId R A))) X)) h =
      epsilonScaleAlg (R := R) c (coefficientAlgMap (Algebra.ofId R A) (coord e X h)) := by
  rw [coord_map, coord_map]
  rfl

/-- A tangent vector whose infinitesimal coordinates are supported on the weight `χ` is a
tangent vector of weight `χ`. -/
theorem isWeightTangent_of_snd_comp {χ : I → ℤ} {X : F.obj (CommAlgCat.of R (DualNumber R))}
    (hX : F.map (dualReduction (CommAlgCat.of R R)) X = 1)
    (hD : ∀ f m, m ≠ χ → (coord e X (comp e σ m f)).snd = 0) : IsWeightTangent σ χ X := by
  intro A t
  apply coord_injective e
  apply algHom_ext_comp e σ
  intro m f
  have hh : IsHomogeneous e σ m (comp e σ m f) := isHomogeneous_comp e σ m f
  rw [coord_act_coefficient e σ A t hh, coord_scale_coefficient e A]
  have hfst : (coord e X (comp e σ m f)).fst = counit e (comp e σ m f) := by
    rw [coord_eq_of_reduction e hX (comp e σ m f), TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl,
      TrivSqZeroExt.fst_inr, add_zero]
    rfl
  apply TrivSqZeroExt.ext
  · rw [TrivSqZeroExt.fst_mul, TrivSqZeroExt.fst_inl, epsilonScaleAlg_fst, coefficientAlgMap_fst,
      hfst, counit_comp]
    by_cases hm : m = 0
    · subst hm
      rw [ofAdd_zero, map_one, Units.val_one, mul_one]
    · rw [ite_eq_right hm, map_zero, zero_mul]
  · rw [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_inl, smul_zero, zero_add, epsilonScaleAlg_snd,
      coefficientAlgMap_snd, TrivSqZeroExt.fst_inl, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op]
    by_cases hm : m = χ
    · subst hm
      rw [mul_comm]
    · rw [hD f m hm, map_zero, zero_mul, mul_zero]

/-- The infinitesimal coordinates of a tangent vector of weight `χ` are supported on `χ`. -/
theorem snd_comp_eq_zero_of_isWeightTangent {χ : I → ℤ}
    {X : F.obj (CommAlgCat.of R (DualNumber R))} (hW : IsWeightTangent σ χ X) (f : B)
    {m : I → ℤ} (hm : m ≠ χ) : (coord e X (comp e σ m f)).snd = 0 := by
  have h := congrArg (fun Y => coord e Y (comp e σ m f))
    (hW (laurent I (CommAlgCat.of R R)) (universalUnits I (CommAlgCat.of R R)))
  beta_reduce at h
  rw [coord_act_coefficient e σ (laurent I (CommAlgCat.of R R))
      (universalUnits I (CommAlgCat.of R R)) (isHomogeneous_comp e σ m f),
    coord_scale_coefficient e (laurent I (CommAlgCat.of R R)),
    exponentValue_universalUnits, exponentValue_universalUnits] at h
  have h2 := congrArg TrivSqZeroExt.snd h
  rw [TrivSqZeroExt.snd_mul, TrivSqZeroExt.snd_inl, smul_zero, zero_add, epsilonScaleAlg_snd,
    coefficientAlgMap_snd, TrivSqZeroExt.fst_inl, MulOpposite.smul_eq_mul_unop,
    MulOpposite.unop_op, splitTorus.exponentUnit_val, splitTorus.exponentUnit_val] at h2
  have h3 := congrArg (fun p : AddMonoidAlgebra R (I → ℤ) => p.coeff m) h2
  simp only [Algebra.ofId_apply, AddMonoidAlgebra.coe_algebraMap, Function.comp_apply,
    Algebra.algebraMap_self, RingHom.id_apply, AddMonoidAlgebra.single_mul_single, zero_add,
    add_zero, mul_one, one_mul, AddMonoidAlgebra.coeff_single, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne hm] at h3
  exact h3

/-- A tangent vector of `U_P` whose infinitesimal coordinates are supported on a weight
outside `P` is the identity. -/
theorem eq_one_of_mem_weightSubgroup_of_snd_comp (P : AddSubsemigroup (I → ℤ)) {χ : I → ℤ}
    (hχ : χ ∉ P) {A : CommAlgCat.{u} R} {X : F.obj (CommAlgCat.of R (DualNumber A))}
    (hX : F.map (dualReduction A) X = 1) (hXP : X ∈ weightSubgroup e σ P _)
    (hD : ∀ f m, m ≠ χ → (coord e X (comp e σ m f)).snd = 0) : X = 1 := by
  refine eq_one_of_snd_eq_zero e hX fun f => ?_
  have hm : ∀ m, (coord e X (comp e σ m f)).snd = 0 := by
    intro m
    by_cases hmχ : m = χ
    · subst hmχ
      rw [(mem_weightSubgroup e σ P X).1 hXP f m hχ, TrivSqZeroExt.algebraMap_eq_inl',
        TrivSqZeroExt.snd_inl]
    · exact hD f m hmχ
  rw [← sum_support_comp e σ f, map_sum, TrivSqZeroExt.snd_sum]
  exact Finset.sum_eq_zero fun m _ => hm m

end Weights

end General

section Maximality

variable {I : Type u} [Fintype I] [DecidableEq I] {k : Type u} [Field k] {F : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} (CommRingCat.of k)} (e : (F ⋙ forget GrpCat).CorepresentableBy B)
  (σ : TorusAction F I)

/-- Maximality of weight subgroups. Let `H` be a torus-stable family of subgroups cut out by an
ideal `J`, whose coordinate algebra `B ⧸ J` is noetherian without nontrivial idempotents. If every
tangent vector of `H` with infinitesimal coordinates supported on one weight outside `P` is
trivial, and `0 ∉ P`, then `H` lies in `U_P`. -/
theorem le_weightSubgroup {H : ∀ A : CommAlgCat.{u} (CommRingCat.of k), Subgroup (F.obj A)}
    {J : Ideal B} (hJ : IsCutOutBy e H J)
    (hH : ∀ {A : CommAlgCat.{u} (CommRingCat.of k)} (t : I → Aˣ) {x : F.obj A},
      x ∈ H A → σ.act t x ∈ H A)
    [IsNoetherianRing (B ⧸ J)]
    (hconn : ∀ c : B ⧸ J, IsIdempotentElem c → c = 0 ∨ c = 1)
    (P : AddSubsemigroup (I → ℤ)) (h0 : (0 : I → ℤ) ∉ P)
    (hrigid : ∀ χ ∉ P, ∀ X : (cutFunctor hJ).obj
        (CommAlgCat.of (CommRingCat.of k) (DualNumber (CommRingCat.of k))),
      (cutFunctor hJ).map (dualReduction (CommAlgCat.of (CommRingCat.of k) (CommRingCat.of k))) X
          = 1 →
        (∀ g m, m ≠ χ →
          (coord (cutCorepresentableBy hJ) X (comp (cutCorepresentableBy hJ) (σ.restrict hJ hH)
            m g)).snd = 0) → X = 1)
    {A : CommAlgCat.{u} (CommRingCat.of k)} {x : F.obj A} (hx : x ∈ H A) :
    x ∈ weightSubgroup e σ P A := by
  classical
  set eH := cutCorepresentableBy hJ
  set σH := σ.restrict hJ hH
  let _ : GradedAlgebra (homogeneousSubmodule eH σH) := weightGradedAlgebra eH σH
  have hε : ∀ χ ≠ 0, ∀ c ∈ homogeneousSubmodule eH σH χ, counit eH c = 0 :=
    fun χ hχ c hc => IsHomogeneous.counit_eq_zero hc hχ
  have hD : ∀ χ ∉ P, Langlands.Algebra.GradedAugmented.IsRigidInDegree
      (homogeneousSubmodule eH σH) (counit eH) χ := by
    intro χ hχ φ hφ hsupp c
    let D := CommAlgCat.of (CommRingCat.of k) (DualNumber (CommRingCat.of k))
    let X : (cutFunctor hJ).obj D := ofCoord eH (A := D) φ
    have hXc : coord eH X = φ := coord_ofCoord eH (A := D) φ
    have hX1 : (cutFunctor hJ).map
        (dualReduction (CommAlgCat.of (CommRingCat.of k) (CommRingCat.of k))) X = 1 := by
      refine (eq_one_iff eH).2 fun g => ?_
      rw [coord_map, hXc]
      exact AlgHom.congr_fun hφ g
    have hXD : ∀ g m, m ≠ χ → (coord eH X (comp eH σH m g)).snd = 0 := by
      intro g m hm
      rw [hXc]
      exact hsupp m hm _ (isHomogeneous_comp eH σH m g)
    have hX := hrigid χ hχ X hX1 hXD
    have hφ1 : φ = coord eH (1 : (cutFunctor hJ).obj D) := by rw [← hXc, hX]
    rw [hφ1, coord_one]
    rfl
  have hM := Langlands.Algebra.GradedAugmented.eq_zero_of_notMem
    (homogeneousSubmodule eH σH) (counit eH) hε hconn P h0 hD
  refine (mem_weightSubgroup e σ P x).2 fun f m hm => ?_
  have hc : Ideal.Quotient.mk J (comp e σ m f) -
      algebraMap (CommRingCat.of k) (B ⧸ J) (counit e (comp e σ m f)) = 0 := by
    apply hM m hm
    · by_cases hm0 : m = 0
      · subst hm0
        refine Submodule.sub_mem _ ?_ ?_
        · rw [← comp_restrict hJ hH]
          exact isHomogeneous_comp eH σH 0 _
        · exact isHomogeneous_algebraMap eH σH _
      · rw [counit_comp, ite_eq_right hm0, map_zero, sub_zero, ← comp_restrict hJ hH]
        exact isHomogeneous_comp eH σH m _
    · rw [map_sub, AlgHom.commutes, ← counit_cut_mk hJ]
      exact sub_self _
  rw [sub_eq_zero] at hc
  have h1 : coord e x (comp e σ m f) =
      coord eH ⟨x, hx⟩ (Ideal.Quotient.mk J (comp e σ m f)) := rfl
  rw [h1, hc, AlgHom.commutes]

end Maximality

end Langlands.GroupScheme.Corepresented
