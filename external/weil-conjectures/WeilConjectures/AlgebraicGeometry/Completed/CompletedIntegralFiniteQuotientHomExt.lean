/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
import WeilConjectures.AlgebraicGeometry.Completed.CompletedIntegralProjectionDivisibility

/-! # Uniqueness of normalized maps from completed coefficients to a finite quotient

Source: the finite-quotient uniqueness argument in the coefficient-tower comparison,
blueprint main-20261015, prose-09-21.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe t u w v
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale
open WeilConjectures

private theorem constRing_surj {C : Type w} [Category.{v} C]
    (J : GrothendieckTopology C) [HasSheafify J CommRingCat.{u}]
    [HasSheafify J (Type u)] [J.PreservesSheafification (forget CommRingCat.{u})]
    [J.HasSheafCompose (forget CommRingCat.{u})]
    {A B : CommRingCat.{u}} (f : A ⟶ B) (hf : Function.Surjective f)
    (U : Cᵒᵖ) :
    Function.Surjective (((constantSheaf J CommRingCat.{u}).map f).hom.app U) := by
  classical
  let e := constantCommuteCompose J (forget CommRingCat.{u})
  let s' := (constantSheaf J (Type u)).map (TypeCat.ofHom (Function.surjInv hf))
  have hs : s' ≫ (constantSheaf J (Type u)).map ((forget _).map f) = 𝟙 _ := by
    rw [← Functor.map_comp]
    trans (constantSheaf J (Type u)).map (𝟙 ((forget CommRingCat.{u}).obj B))
    · congr 1
      ext x
      exact Function.surjInv_eq hf x
    exact (constantSheaf J (Type u)).map_id _
  let r := e.hom.app B ≫ s' ≫ e.inv.app A
  have hr : r ≫ (sheafCompose J (forget CommRingCat.{u})).map
      ((constantSheaf J CommRingCat.{u}).map f) = 𝟙 _ := by
    dsimp only [r]
    rw [Category.assoc, Category.assoc]
    change e.hom.app B ≫ s' ≫ e.inv.app A ≫
      (constantSheaf J CommRingCat.{u} ⋙ sheafCompose J (forget CommRingCat.{u})).map f = _
    rw [← e.inv.naturality f]
    change e.hom.app B ≫ s' ≫
      (constantSheaf J (Type u)).map ((forget _).map f) ≫ e.inv.app B = _
    rw [← Category.assoc s', hs, Category.id_comp, e.hom_inv_id_app B]
  intro x
  refine ⟨r.hom.app U x, ?_⟩
  exact congrArg (fun h ↦ h.hom.app U x) hr

private theorem constantQuotient_surjective (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : AlgebraicGeometry.Scheme.{t})
    (n : ℕ) (U : T.ProEtᵒᵖ) :
    Function.Surjective
      ((WeilConjectures.integralConstantQuotientOfUniverses l E T n).hom.app U) := by
  have : LocallySmall.{max u (t + 1)} T.ProEt := locallySmall_max.{max u (t + 1), t, t + 1}
  have : HasColimitsOfSize.{t + 1, t + 1} CommRingCat.{max u (t + 1)} :=
    hasColimitsOfSizeShrink.{t + 1, t + 1, max u (t + 1), max u (t + 1)} _
  have : PreservesFilteredColimitsOfSize.{t + 1, t + 1} (forget CommRingCat.{max u (t + 1)}) :=
    preservesFilteredColimitsOfSize_shrink.{t + 1, max u (t + 1), t + 1, max u (t + 1)} _
  have : (AlgebraicGeometry.Scheme.ProEt.topology T).PreservesSheafification
      (forget CommRingCat.{max u (t + 1)}) :=
    GrothendieckTopology.instPreservesSheafification _ _
  apply constRing_surj.{max u (t + 1), t + 1, t}
  intro b
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective b.down
  refine ⟨ULift.up a, ?_⟩
  apply ULift.ext
  exact ha

private theorem completedIntegral_approximation
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{t})
    (n : ℕ) (U : T.ProEtᵒᵖ)
    (x : (completedIntegralCoefficientSheafUnrestricted l E T).obj.obj U) :
    ∃ (a : (integralConstantRingOfUniverses l E T).obj.obj U)
      (y : (completedIntegralCoefficientSheafUnrestricted l E T).obj.obj U),
      x = (integralConstantToCompletionOfUniverses l E T).hom.app U a +
        ((integralConstantToCompletionOfUniverses l E T).hom.app U
          ((toSheafify (Scheme.ProEt.topology T)
            ((Functor.const T.ProEtᵒᵖ).obj
              (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))))).app U
                (ULift.up (Padic.coefficientExtensionUniformizer l E)))) ^ (n + 1) * y := by
  let c := integralConstantToCompletionOfUniverses l E T
  let p : completedIntegralCoefficientSheafUnrestricted l E T ⟶
      integralCoefficientSheaf l E T n :=
    limit.π (integralCoefficientSheafSystem l E T) (op n)
  obtain ⟨a, ha⟩ := constantQuotient_surjective l E T n U (p.hom.app U x)
  have hcp : c ≫ p = integralConstantQuotientOfUniverses l E T n := limit.lift_π _ _
  have hz : p.hom.app U (x - c.hom.app U a) = 0 := by
    rw [map_sub]
    have hca := congrArg (fun h ↦ h.hom.app U a) hcp
    change p.hom.app U (c.hom.app U a) = _ at hca
    exact sub_eq_zero.mpr (hca.trans ha).symm
  obtain ⟨y, hy⟩ := completedIntegralProjection_divisible l E T n U
    (x - c.hom.app U a) hz
  refine ⟨a, y, ?_⟩
  change x = c.hom.app U a + _
  rw [← hy]
  exact (add_sub_cancel _ _).symm

/-- Maps into one finite constant quotient are determined by their normalized scalar map.
Source: blueprint main-20261015, coefficient convention in prose-09-21;
the uniqueness step of its completed-coefficient comparison.
(blueprint: lem-sp-completed-integral-finite-quotient-hom-ext)

Proof: Choose k with the (k+1)st uniformizer ideal contained in I. Constant
sheafification commutes with the underlying-set functor. A set-theoretic section of
the quotient map therefore gives surjectivity on every object's sections. Lift the
finite projection of x to a section a of the constant integer sheaf. The difference
x-c(a) has zero projection; `completedIntegralProjection_divisible` writes it as
c(pi)^(k+1)y. Scalar normalization and naturality of the sheafification unit imply
that both maps send c(pi)^(k+1) to zero: pi^(k+1) belongs to I. They also agree on
c(a). Applying the two ring maps to x=c(a)+c(pi)^(k+1)y gives equality on x.
Extensionality on site objects and sections gives equality of sheaf maps.
-/
theorem completedIntegralFiniteQuotientHom_ext
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{t})
    (I : Ideal (Padic.coefficientExtensionIntegers l E))
    (hI : ∃ k : ℕ, Padic.coefficientExtensionIdeal l E (k + 1) ≤ I) :
    let F := constantSheaf (Scheme.ProEt.topology T) CommRingCat.{max u (t + 1)} ⋙
      sheafCompose _ (forget₂ CommRingCat.{max u (t + 1)} RingCat.{max u (t + 1)})
    let R := CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E ⧸ I))
    let q := F.map (CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
      ((Ideal.Quotient.mk I).comp ULift.ringEquiv.toRingHom)))
    ∀ f g : WeilConjectures.completedIntegralCoefficientSheafUnrestricted l E T ⟶ F.obj R,
      WeilConjectures.integralConstantToCompletionOfUniverses l E T ≫ f = q →
      WeilConjectures.integralConstantToCompletionOfUniverses l E T ≫ g = q → f = g := by
  dsimp only
  intro f g hf hg
  obtain ⟨k, hk⟩ := hI
  ext U x
  obtain ⟨a, y, hxy⟩ := completedIntegral_approximation l E T k U x
  let π : (integralConstantRingOfUniverses l E T).obj.obj U := (toSheafify (Scheme.ProEt.topology T)
    ((Functor.const T.ProEtᵒᵖ).obj
      (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))))).app U
        (ULift.up (Padic.coefficientExtensionUniformizer l E))
  have hscalar (z : (integralConstantRingOfUniverses l E T).obj.obj U) :
      f.hom.app U ((integralConstantToCompletionOfUniverses l E T).hom.app U z) =
      g.hom.app U ((integralConstantToCompletionOfUniverses l E T).hom.app U z) := by
    exact congrArg (fun h ↦ h.hom.app U z) (hf.trans hg.symm)
  have hkill :
      f.hom.app U ((integralConstantToCompletionOfUniverses l E T).hom.app U π) ^
        (k + 1) = 0 := by
    rw [← map_pow, ← map_pow]
    have hscalarf := congrArg (fun h ↦ h.hom.app U (π ^ (k + 1))) hf
    trans ((constantSheaf (Scheme.ProEt.topology T) CommRingCat.{max u (t + 1)}).map
      (CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
        ((Ideal.Quotient.mk I).comp ULift.ringEquiv.toRingHom)))).hom.app U
      (π ^ (k + 1))
    · exact hscalarf
    change ((constantSheaf (Scheme.ProEt.topology T) CommRingCat.{max u (t + 1)}).map
      (CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
        ((Ideal.Quotient.mk I).comp ULift.ringEquiv.toRingHom)))).hom.app U
      (π ^ (k + 1)) = 0
    have hpow : π ^ (k + 1) =
        (toSheafify (Scheme.ProEt.topology T)
          ((Functor.const T.ProEtᵒᵖ).obj
            (CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))))).app U
              ((ULift.up (Padic.coefficientExtensionUniformizer l E)) ^ (k + 1)) :=
      ((toSheafify (Scheme.ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj
          (CommRingCat.of
            (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E))))).app U).hom.map_pow
        (ULift.up (Padic.coefficientExtensionUniformizer l E)) (k + 1) |>.symm
    rw [hpow]
    let φ : CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E)) ⟶
        CommRingCat.of (ULift.{t + 1} (Padic.coefficientExtensionIntegers l E ⧸ I)) :=
      CommRingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
        ((Ideal.Quotient.mk I).comp ULift.ringEquiv.toRingHom))
    have hn := toSheafify_naturality (Scheme.ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).map φ)
    have hn' := congrArg (fun h ↦ h.app U
      ((ULift.up (Padic.coefficientExtensionUniformizer l E)) ^ (k + 1))) hn
    dsimp at hn'
    refine hn'.symm.trans ?_
    have hzero : Ideal.Quotient.mk I
        (Padic.coefficientExtensionUniformizer l E ^ (k + 1)) = 0 := by
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      apply hk
      exact Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_singleton _)) (k + 1)
    have hφ : φ ((ULift.up (Padic.coefficientExtensionUniformizer l E)) ^ (k + 1)) = 0 := by
      apply ULift.ext
      change Ideal.Quotient.mk I
        (Padic.coefficientExtensionUniformizer l E ^ (k + 1)) = 0
      exact hzero
    rw [hφ, map_zero]
  rw [hxy, map_add, map_mul, map_pow, map_add, map_mul, map_pow]
  change _ + _ ^ (k + 1) * _ = _ + _ ^ (k + 1) * _
  rw [← hscalar π, hkill, zero_mul, zero_mul, add_zero, add_zero, hscalar a]

end AlgebraicGeometry.ProEtale
