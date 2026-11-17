import Langlands.GroupScheme.Torus.FlatDiagonalizableSubgroup
import Langlands.GroupScheme.AffineCoordinatesFiniteType
import Langlands.AbelianScheme.KernelBaseChange
import Langlands.GroupScheme.SubgroupBaseChange
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-! # Closed subgroups of bounded exponent in groups of multiplicative type -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry WithConv
open scoped CategoryTheory.MonObj TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

section Algebra

variable {R : Type u} [CommRing R] {A : Type v} [CommRing A] [HopfAlgebra R A]

/-- Evaluating a convolution power at a group-like element gives an ordinary power. -/
theorem convPow_apply_groupLike (f : WithConv (A →ₐ[R] A))
    {g : A} (hg : IsGroupLikeElem R g) (n : ℕ) :
    (f ^ n) g = (f g) ^ n := by
  induction n with
  | zero => simp [hg.counit_eq_one]
  | succ n ih =>
    rw [pow_succ, AlgHom.convMul_apply, hg.comul_eq_tmul_self]
    simp [ih, pow_succ]

/-- A finite-type Hopf algebra spanned by group-like elements is finite if one
positive convolution power of its identity is the counit. -/
theorem finite_of_span_groupLike_of_uniformPower
    [Algebra.FiniteType R A]
    (hspan : Submodule.span R {g : A | IsGroupLikeElem R g} = ⊤)
    (n : ℕ) (hn : 0 < n)
    (hpow : (toConv (AlgHom.id R A) : WithConv (A →ₐ[R] A)) ^ n = 1) :
    Module.Finite R A := by
  have hgpow (g : A) (hg : IsGroupLikeElem R g) : g ^ n = 1 := by
    have h := congrArg (fun f : WithConv (A →ₐ[R] A) => f g) hpow
    simpa only [convPow_apply_groupLike _ hg, AlgHom.id_apply,
      AlgHom.convOne_apply, hg.counit_eq_one, map_one] using h
  have hi : Algebra.IsIntegral R A := ⟨fun a => by
    have ha : a ∈ Submodule.span R {g : A | IsGroupLikeElem R g} := by
      rw [hspan]
      trivial
    induction ha using Submodule.span_induction with
    | mem g hg =>
      apply IsIntegral.of_pow hn
      rw [hgpow g hg]
      exact isIntegral_one
    | zero => exact isIntegral_zero
    | add x y _ _ hx hy => exact hx.add hy
    | smul r x _ hx => exact hx.smul r⟩
  let : Algebra.IsIntegral R A := hi
  exact Algebra.IsIntegral.finite

end Algebra

section Points

variable {S S' : Scheme.{u}} {K : GroupScheme S}

/-- A uniform power identity is preserved by arbitrary base change. -/
theorem uniformPower_baseChange (b : S' ⟶ S) (n : ℕ)
    (hpow : ∀ (T : Over S) (x : T ⟶ K.X), x ^ n = 1) :
    ∀ (T : Over S') (x : T ⟶ ((baseChange b).obj K).X), x ^ n = 1 := by
  intro T x
  apply (baseChangePointsEquiv b K T).injective
  rw [map_pow, map_one]
  exact hpow _ _

end Points

namespace Diagonalizable

variable {R : CommRingCat.{u}} {Λ : Type u} [AddCommGroup Λ]
    [AddGroup.FG Λ] {K : GroupScheme (Spec R)}

/-- A closed subgroup of a finite-type diagonalizable group over a ring is
finite whenever all its scheme-valued points have one positive exponent. -/
theorem isFinite_closedSubgroup_of_uniformPower
    (i : K ⟶ (groupScheme R Λ).toGrp) (hi : IsClosedSubgroup i)
    (n : ℕ) (hn : 0 < n)
    (hpow : ∀ (T : Over (Spec R)) (x : T ⟶ K.X), x ^ n = 1) :
    IsFinite K.X.hom := by
  have : IsClosedImmersion i.hom.hom.left := hi
  have : IsAffine (groupScheme R Λ).X.left :=
    isAffine_of_isAffineHom (groupScheme R Λ).X.hom
  have : IsAffine K.X.left := isAffine_of_isAffineHom i.hom.hom.left
  have : LocallyOfFiniteType K.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  let A := AffineCoordinates.hopfAlgebra K
  let e := AffineCoordinates.hopfSpecIso K
  let Y := (Spec (CommRingCat.of A)).asOver (Spec R)
  let f : Y ⟶ K.X := e.hom.hom.hom
  have : IsMonHom f := e.hom.hom.isMonHom_hom
  have hY : (𝟙 Y) ^ n = 1 := by
    apply (cancel_mono f).mp
    rw [MonObj.pow_comp, Category.id_comp, MonObj.one_comp]
    exact hpow Y f
  have hid : 𝟙 Y = Spec.mapMulEquiv (toConv (AlgHom.id R A)) := by
    ext1
    simp [Y, Spec.mapMulEquiv]
    rfl
  have hconv : (toConv (AlgHom.id R A) : WithConv (A →ₐ[R] A)) ^ n = 1 := by
    apply (Spec.mapMulEquiv (R := R) (S := A) (T := A)).injective
    rw [map_pow, map_one, ← hid]
    exact hY
  let : Algebra.FiniteType R A := AffineCoordinates.algebraFiniteType K
  let : Module.Finite R A :=
    finite_of_span_groupLike_of_uniformPower (span_groupLike_of_closedSubgroup i hi) n hn hconv
  have hfin : IsFinite (Spec.map (CommRingCat.ofHom (algebraMap R A))) := by
    apply (IsFinite.SpecMap_iff _).mpr
    exact RingHom.finite_algebraMap.mpr inferInstance
  have : IsFinite ((hopfSpec R).obj (Opposite.op A)).X.hom := hfin
  rw [← Over.w e.inv.hom.hom]
  infer_instance

end Diagonalizable

namespace RelativeMultiplicativeType

variable {S : Scheme.{u}} {H K : GroupScheme S}

/-- A closed subgroup of a split diagonalizable group over an arbitrary base
is finite if one positive power kills all its points. -/
theorem isFinite_diagonalizable_closedSubgroup_of_uniformPower
    (Λ : Type u) [AddCommGroup Λ] [AddGroup.FG Λ]
    (i : K ⟶ diagonalizable S Λ) (hi : IsClosedSubgroup i)
    (n : ℕ) (hn : 0 < n)
    (hpow : ∀ (T : Over S) (x : T ⟶ K.X), x ^ n = 1) :
    IsFinite K.X.hom := by
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsFinite) S.affineCover
  intro a
  let b := S.affineCover.f a
  let e := diagonalizableBaseChangeIso b Λ ≪≫
    Diagonalizable.baseChangeIso (Gm.toSpecZ _) Λ
  exact Diagonalizable.isFinite_closedSubgroup_of_uniformPower
    ((GroupScheme.baseChange b).map i ≫ e.hom) ((hi.baseChange b).comp_iso e)
    n hn (uniformPower_baseChange b n hpow)

/-- An actual diagonalizable presentation suffices for finiteness of a closed
subgroup of bounded exponent. -/
theorem IsDiagonalizable.isFinite_closedSubgroup_of_uniformPower
    (hH : IsDiagonalizable H) (i : K ⟶ H) (hi : IsClosedSubgroup i)
    (n : ℕ) (hn : 0 < n)
    (hpow : ∀ (T : Over S) (x : T ⟶ K.X), x ^ n = 1) :
    IsFinite K.X.hom := by
  obtain ⟨Λ, hΛ, hfg, ⟨e⟩⟩ := hH
  let : AddCommGroup Λ := hΛ
  let : AddGroup.FG Λ := hfg
  exact isFinite_diagonalizable_closedSubgroup_of_uniformPower Λ
    (i ≫ e.hom) (hi.comp_iso e) n hn hpow

set_option linter.defProp false in
/-- A closed subgroup of a group of multiplicative type is finite whenever one
positive integer kills all its points, with no flatness hypothesis. -/
@[instance_reducible]
def IsMultiplicativeType.isFinite_closedSubgroup_of_uniformPower
    (hH : IsMultiplicativeType H) (i : K ⟶ H) (hi : IsClosedSubgroup i)
    (n : ℕ) (hn : 0 < n)
    (hpow : ∀ (T : Over S) (x : T ⟶ K.X), x ^ n = 1) :
    IsFinite K.X.hom := by
  obtain ⟨𝒰, h𝒰⟩ := hH
  have : MorphismProperty.IsLocalAtTarget (@IsFinite : MorphismProperty Scheme.{u})
      Scheme.fppfPrecoverage :=
    Langlands.AlgebraicGeometry.FppfLocal.isLocalAtTarget_fppfPrecoverage _
  let 𝒱 : Scheme.Cover Scheme.fppfPrecoverage S := 𝒰
  apply MorphismProperty.IsLocalAtTarget.of_zeroHypercover 𝒱
  intro a
  exact (h𝒰 a).isFinite_closedSubgroup_of_uniformPower
    ((GroupScheme.baseChange (𝒰.f a)).map i) (hi.baseChange (𝒰.f a))
    n hn (uniformPower_baseChange (𝒰.f a) n hpow)

end RelativeMultiplicativeType

end Langlands.GroupScheme
