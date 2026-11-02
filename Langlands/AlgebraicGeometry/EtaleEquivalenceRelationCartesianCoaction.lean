import Langlands.AlgebraicGeometry.RingEtaleGroupoidLevel
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationGeometry

/-! # The coaction of an affine first level on a cartesian étale equivalence relation

Let `(f, g) : E ⟶ E₀` be a cartesian morphism of étale equivalence relations with `E.U`,
`E₀.U` and `E₀.R` affine. Write `B₀ = Γ(E₀.U)`, `C₀ = Γ(E₀.R)` (a `B₀`-algebra through the
source map) and `B = Γ(E.U)` (a `B₀`-algebra through `f`). The pullback square of `(f, g)`
identifies `Γ(E.R)` with `C₀ ⊗[B₀] B`, and the target map of `E` becomes a ring map
`B →+* C₀ ⊗[B₀] B`. It is a ring étale groupoid with source `b ↦ 1 ⊗ b`, its étale
equivalence relation receives a cartesian morphism from `E`, and it is a multiplicative
coaction of the ring étale groupoid of `E₀` on `B`.
-/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

namespace Langlands.AlgebraicGeometry.EtaleEquivalenceRelation

variable {E E₀ : EtaleEquivalenceRelation.{u}} {f : E.U ⟶ E₀.U} {g : E.R ⟶ E₀.R}

namespace IsCartesianHom

theorem isAffine_R (h : IsCartesianHom E E₀ f g) [IsAffine E.U] [IsAffine E₀.U]
    [IsAffine E₀.R] : IsAffine E.R :=
  IsAffine.of_isPullback h.2

variable (h : IsCartesianHom E E₀ f g) [IsAffine E.U] [IsAffine E₀.U] [IsAffine E₀.R]

/-- The ring of the relation scheme of `E` is the base change `Γ(E₀.R) ⊗[Γ(E₀.U)] Γ(E.U)`. -/
noncomputable def relationIso :
    letI := E₀.s.appTop.hom.toAlgebra
    letI := f.appTop.hom.toAlgebra
    CommRingCat.of (Γ(E₀.R, ⊤) ⊗[Γ(E₀.U, ⊤)] Γ(E.U, ⊤)) ≅ Γ(E.R, ⊤) :=
  letI := E₀.s.appTop.hom.toAlgebra
  letI := f.appTop.hom.toAlgebra
  (CommRingCat.isPushout_tensorProduct Γ(E₀.U, ⊤) Γ(E₀.R, ⊤) Γ(E.U, ⊤)).isoIsPushout _ _
    (isPushout_appTop_of_isPullback h.2)

theorem relationIso_hom_tmul_one :
    letI := E₀.s.appTop.hom.toAlgebra
    letI := f.appTop.hom.toAlgebra
    ∀ c : Γ(E₀.R, ⊤), h.relationIso.hom (c ⊗ₜ (1 : Γ(E.U, ⊤))) = g.appTop c := by
  let := E₀.s.appTop.hom.toAlgebra
  let := f.appTop.hom.toAlgebra
  intro c
  exact congrArg (fun φ => φ.hom c)
    ((CommRingCat.isPushout_tensorProduct Γ(E₀.U, ⊤) Γ(E₀.R, ⊤) Γ(E.U, ⊤)).inl_isoIsPushout_hom
      _ _ (isPushout_appTop_of_isPullback h.2))

theorem relationIso_hom_one_tmul :
    letI := E₀.s.appTop.hom.toAlgebra
    letI := f.appTop.hom.toAlgebra
    ∀ b : Γ(E.U, ⊤), h.relationIso.hom ((1 : Γ(E₀.R, ⊤)) ⊗ₜ b) = E.s.appTop b := by
  let := E₀.s.appTop.hom.toAlgebra
  let := f.appTop.hom.toAlgebra
  intro b
  exact congrArg (fun φ => φ.hom b)
    ((CommRingCat.isPushout_tensorProduct Γ(E₀.U, ⊤) Γ(E₀.R, ⊤) Γ(E.U, ⊤)).inr_isoIsPushout_hom
      _ _ (isPushout_appTop_of_isPullback h.2))

/-- The target map of `E` as a ring map `Γ(E.U) →+* Γ(E₀.R) ⊗[Γ(E₀.U)] Γ(E.U)`. -/
noncomputable def ringHom :
    letI := E₀.s.appTop.hom.toAlgebra
    letI := f.appTop.hom.toAlgebra
    Γ(E.U, ⊤) →+* Γ(E₀.R, ⊤) ⊗[Γ(E₀.U, ⊤)] Γ(E.U, ⊤) :=
  letI := E₀.s.appTop.hom.toAlgebra
  letI := f.appTop.hom.toAlgebra
  h.relationIso.inv.hom.comp E.t.appTop.hom

theorem relationIso_hom_ringHom (b : Γ(E.U, ⊤)) :
    h.relationIso.hom (h.ringHom b) = E.t.appTop b := by
  change (h.relationIso.inv ≫ h.relationIso.hom).hom (E.t.appTop b) = E.t.appTop b
  rw [Iso.inv_hom_id]
  rfl

theorem ringHom_algebraMap :
    letI := E₀.s.appTop.hom.toAlgebra
    letI := f.appTop.hom.toAlgebra
    ∀ b : Γ(E₀.U, ⊤), h.ringHom (algebraMap Γ(E₀.U, ⊤) Γ(E.U, ⊤) b) =
      E₀.t.appTop b ⊗ₜ (1 : Γ(E.U, ⊤)) := by
  let := E₀.s.appTop.hom.toAlgebra
  let := f.appTop.hom.toAlgebra
  intro b
  apply (ConcreteCategory.bijective_of_isIso h.relationIso.hom).1
  rw [relationIso_hom_ringHom, relationIso_hom_tmul_one]
  change (f.appTop ≫ E.t.appTop) b = (E₀.t.appTop ≫ g.appTop) b
  rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, h.1]

/-- The ring form of `E` over the first level: a ring étale groupoid on `Γ(E.U)` with relation
ring `Γ(E₀.R) ⊗[Γ(E₀.U)] Γ(E.U)` and source map `b ↦ 1 ⊗ b`. -/
theorem ringEtaleGroupoid :
    letI := E₀.s.appTop.hom.toAlgebra
    letI := f.appTop.hom.toAlgebra
    letI : Algebra Γ(E.U, ⊤) (Γ(E₀.R, ⊤) ⊗[Γ(E₀.U, ⊤)] Γ(E.U, ⊤)) :=
      Algebra.TensorProduct.rightAlgebra
    RingEtaleGroupoid h.ringHom := by
  let := E₀.s.appTop.hom.toAlgebra
  let := f.appTop.hom.toAlgebra
  let : Algebra Γ(E.U, ⊤) (Γ(E₀.R, ⊤) ⊗[Γ(E₀.U, ⊤)] Γ(E.U, ⊤)) :=
    Algebra.TensorProduct.rightAlgebra
  let : Algebra Γ(E.U, ⊤) Γ(E.R, ⊤) := E.s.appTop.hom.toAlgebra
  have := h.isAffine_R
  have hG := E.ringEtaleGroupoid
  let e := h.relationIso.commRingCatIsoToRingEquiv
  have he : e.symm.toRingHom.comp (algebraMap Γ(E.U, ⊤) Γ(E.R, ⊤)) =
      algebraMap Γ(E.U, ⊤) (Γ(E₀.R, ⊤) ⊗[Γ(E₀.U, ⊤)] Γ(E.U, ⊤)) := by
    ext b
    apply e.injective
    change e (e.symm (E.s.appTop b)) = h.relationIso.hom ((1 : Γ(E₀.R, ⊤)) ⊗ₜ b)
    rw [RingEquiv.apply_symm_apply, relationIso_hom_one_tmul]
  exact hG.ofRingEquiv e.symm he

/-- The cartesian morphism from `E` to the étale equivalence relation of its ring form. -/
theorem isCartesianHom_toScheme [IsAffine E.R] :
    letI := E₀.s.appTop.hom.toAlgebra
    letI := f.appTop.hom.toAlgebra
    letI : Algebra Γ(E.U, ⊤) (Γ(E₀.R, ⊤) ⊗[Γ(E₀.U, ⊤)] Γ(E.U, ⊤)) :=
      Algebra.TensorProduct.rightAlgebra
    IsCartesianHom E h.ringEtaleGroupoid.toScheme E.U.isoSpec.hom
      (E.R.isoSpec.hom ≫ Spec.map h.relationIso.hom) := by
  let := E₀.s.appTop.hom.toAlgebra
  let := f.appTop.hom.toAlgebra
  let : Algebra Γ(E.U, ⊤) (Γ(E₀.R, ⊤) ⊗[Γ(E₀.U, ⊤)] Γ(E.U, ⊤)) :=
    Algebra.TensorProduct.rightAlgebra
  constructor
  · change (E.R.isoSpec.hom ≫ Spec.map h.relationIso.hom) ≫
        Spec.map (CommRingCat.ofHom h.ringHom) = E.t ≫ E.U.isoSpec.hom
    have ht : CommRingCat.ofHom h.ringHom ≫ h.relationIso.hom = E.t.appTop := by
      ext b
      exact h.relationIso_hom_ringHom b
    rw [Category.assoc, ← Spec.map_comp, ht, Scheme.isoSpec_hom_naturality]
  · have hs : CommRingCat.ofHom
          (algebraMap Γ(E.U, ⊤) (Γ(E₀.R, ⊤) ⊗[Γ(E₀.U, ⊤)] Γ(E.U, ⊤))) ≫
        h.relationIso.hom = E.s.appTop := by
      ext b
      exact h.relationIso_hom_one_tmul b
    have : IsIso (X := E.U) (Y := h.ringEtaleGroupoid.toScheme.U) E.U.isoSpec.hom :=
      Iso.isIso_hom E.U.isoSpec
    have : IsIso (X := E.R) (Y := h.ringEtaleGroupoid.toScheme.R)
        (E.R.isoSpec.hom ≫ Spec.map h.relationIso.hom) :=
      inferInstanceAs (IsIso (E.R.isoSpec.hom ≫ Spec.map h.relationIso.hom))
    apply IsPullback.of_horiz_isIso
    constructor
    change (E.R.isoSpec.hom ≫ Spec.map h.relationIso.hom) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap Γ(E.U, ⊤) (Γ(E₀.R, ⊤) ⊗[Γ(E₀.U, ⊤)] Γ(E.U, ⊤)))) =
      E.s ≫ E.U.isoSpec.hom
    rw [Category.assoc, ← Spec.map_comp, hs, Scheme.isoSpec_hom_naturality]

/-- The coaction of the ring étale groupoid of `E₀` on `Γ(E.U)` given by the target map
of `E`. -/
noncomputable def coaction :
    letI := E₀.s.appTop.hom.toAlgebra
    letI := f.appTop.hom.toAlgebra
    GroupoidCoaction E₀.t.appTop.hom Γ(E.U, ⊤) :=
  letI := E₀.s.appTop.hom.toAlgebra
  letI := f.appTop.hom.toAlgebra
  letI : Algebra Γ(E.U, ⊤) (Γ(E₀.R, ⊤) ⊗[Γ(E₀.U, ⊤)] Γ(E.U, ⊤)) :=
    Algebra.TensorProduct.rightAlgebra
  E₀.ringEtaleGroupoid.coactionOfLevel h.ringHom h.ringHom_algebraMap h.ringEtaleGroupoid

theorem coaction_coaction (b : Γ(E.U, ⊤)) :
    letI := E₀.s.appTop.hom.toAlgebra
    letI := f.appTop.hom.toAlgebra
    h.coaction.coaction b = h.ringHom b :=
  rfl

theorem coaction_isMultiplicative :
    letI := E₀.s.appTop.hom.toAlgebra
    letI := f.appTop.hom.toAlgebra
    h.coaction.IsMultiplicative :=
  letI := E₀.s.appTop.hom.toAlgebra
  letI := f.appTop.hom.toAlgebra
  { map_one := map_one h.ringHom
    map_mul := map_mul h.ringHom }

end IsCartesianHom


/-- For morphisms `f' : E'.U ⟶ E.U` and `f : E.U ⟶ E₀.U`, the map `f'.appTop` as an algebra
map over `Γ(E₀.U)`. -/
def appTopAlgHom {E' : EtaleEquivalenceRelation.{u}} (f' : E'.U ⟶ E.U) (f : E.U ⟶ E₀.U) :
    letI := f.appTop.hom.toAlgebra
    letI := (f' ≫ f).appTop.hom.toAlgebra
    Γ(E.U, ⊤) →ₐ[Γ(E₀.U, ⊤)] Γ(E'.U, ⊤) :=
  letI := f.appTop.hom.toAlgebra
  letI := (f' ≫ f).appTop.hom.toAlgebra
  { toRingHom := f'.appTop.hom
    commutes' := fun _ => rfl }

theorem appTopAlgHom_apply {E' : EtaleEquivalenceRelation.{u}} (f' : E'.U ⟶ E.U)
    (f : E.U ⟶ E₀.U) (b : Γ(E.U, ⊤)) : appTopAlgHom f' f b = f'.appTop b :=
  rfl

namespace IsCartesianHom

/-- The map on global sections of the object schemes of a cartesian morphism `E' ⟶ E` over
`E₀` is equivariant for the coactions of `Γ(E₀.R)`. -/
theorem ringHom_comp_appTop {E' : EtaleEquivalenceRelation.{u}} {f' : E'.U ⟶ E.U}
    {g' : E'.R ⟶ E.R} (h' : IsCartesianHom E' E f' g') (h : IsCartesianHom E E₀ f g)
    [IsAffine E'.U] [IsAffine E.U] [IsAffine E₀.U] [IsAffine E₀.R] (b : Γ(E.U, ⊤)) :
    letI := E₀.s.appTop.hom.toAlgebra
    letI := f.appTop.hom.toAlgebra
    letI := (f' ≫ f).appTop.hom.toAlgebra
    (h'.comp h).ringHom (f'.appTop b) =
      Algebra.TensorProduct.map (AlgHom.id Γ(E₀.U, ⊤) Γ(E₀.R, ⊤)) (appTopAlgHom f' f)
        (h.ringHom b) := by
  let := E₀.s.appTop.hom.toAlgebra
  let := f.appTop.hom.toAlgebra
  let := (f' ≫ f).appTop.hom.toAlgebra
  have key : ((h'.comp h).relationIso.hom.hom.comp
      ((Algebra.TensorProduct.map (AlgHom.id Γ(E₀.U, ⊤) Γ(E₀.R, ⊤)) (appTopAlgHom f' f) :
        Γ(E₀.R, ⊤) ⊗[Γ(E₀.U, ⊤)] Γ(E.U, ⊤) →ₐ[Γ(E₀.U, ⊤)] Γ(E₀.R, ⊤) ⊗[Γ(E₀.U, ⊤)] Γ(E'.U, ⊤)) :
        Γ(E₀.R, ⊤) ⊗[Γ(E₀.U, ⊤)] Γ(E.U, ⊤) →+* Γ(E₀.R, ⊤) ⊗[Γ(E₀.U, ⊤)] Γ(E'.U, ⊤))) =
      g'.appTop.hom.comp h.relationIso.hom.hom := by
    refine RingEtaleGroupoid.tensor_ringHom_ext (fun c => ?_) (fun d => ?_)
    · change (h'.comp h).relationIso.hom (c ⊗ₜ appTopAlgHom f' f 1) =
        g'.appTop (h.relationIso.hom (c ⊗ₜ 1))
      rw [map_one, relationIso_hom_tmul_one, relationIso_hom_tmul_one]
      rfl
    · change (h'.comp h).relationIso.hom ((AlgHom.id Γ(E₀.U, ⊤) Γ(E₀.R, ⊤) 1) ⊗ₜ
          appTopAlgHom f' f d) = g'.appTop (h.relationIso.hom (1 ⊗ₜ d))
      rw [AlgHom.id_apply, relationIso_hom_one_tmul, relationIso_hom_one_tmul,
        appTopAlgHom_apply]
      change (f'.appTop ≫ E'.s.appTop) d = (E.s.appTop ≫ g'.appTop) d
      rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, h'.2.w]
  apply (ConcreteCategory.bijective_of_isIso (h'.comp h).relationIso.hom).1
  rw [relationIso_hom_ringHom]
  change E'.t.appTop (f'.appTop b) = ((h'.comp h).relationIso.hom.hom.comp
      ((Algebra.TensorProduct.map (AlgHom.id Γ(E₀.U, ⊤) Γ(E₀.R, ⊤)) (appTopAlgHom f' f) :
        Γ(E₀.R, ⊤) ⊗[Γ(E₀.U, ⊤)] Γ(E.U, ⊤) →ₐ[Γ(E₀.U, ⊤)] Γ(E₀.R, ⊤) ⊗[Γ(E₀.U, ⊤)] Γ(E'.U, ⊤)) :
        Γ(E₀.R, ⊤) ⊗[Γ(E₀.U, ⊤)] Γ(E.U, ⊤) →+* Γ(E₀.R, ⊤) ⊗[Γ(E₀.U, ⊤)] Γ(E'.U, ⊤))) (h.ringHom b)
  rw [key]
  change (f'.appTop ≫ E'.t.appTop) b = g'.appTop (h.relationIso.hom (h.ringHom b))
  rw [relationIso_hom_ringHom]
  change (f'.appTop ≫ E'.t.appTop) b = (E.t.appTop ≫ g'.appTop) b
  rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop, h'.1]

end IsCartesianHom

end Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
