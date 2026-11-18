import Langlands.GroupScheme.HomScheme.AdicAlgebraization
import Langlands.GroupScheme.Torus.MultiplicativeTypeAdicHomDescentStatement
import Langlands.GroupScheme.Torus.DiagonalizableBaseChange
import Langlands.AnthropicFLT.Theorems.Thm_IsAdicComplete_of_finite_of_isNoetherianRing

/-! # Actual formal Hom lifts on finite affine tests -/

noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.AdicAffinePoints

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.HomScheme.Adic

variable {A : Type u} [CommRing A] {I : Ideal A}
  {H G : GroupScheme (Spec (CommRingCat.of A))}

variable {B : Type u} [CommRing B]

/-- Effectivity on the extended-ideal quotients gives all formal-lift identities. -/
theorem isAlgebraization_of_restrict_pull (φ : A →+* B) (s : System I H G)
    (f : (baseChange (Spec.map (CommRingCat.ofHom φ))).obj H ⟶
      (baseChange (Spec.map (CommRingCat.ofHom φ))).obj G)
    (hf : System.restrict (I.map φ) _ _ f = System.pull φ s) :
    System.IsAlgebraization s (V := Over.mk (Spec.map (CommRingCat.ofHom φ))) f := by
  have hred (n : ℕ) :
      evaluate (Over.homMk (quotientMap (I.map φ) n) rfl :
        (Over.map (Spec.map (CommRingCat.ofHom φ))).obj
          (Over.mk (quotientMap (I.map φ) n)) ⟶
            Over.mk (Spec.map (CommRingCat.ofHom φ))) f =
        evaluate (quotientOver φ I n) (s.hom n) := by
    have hn := congrArg (fun k => flatten (Spec.map (CommRingCat.ofHom φ))
      (Over.mk (quotientMap (I.map φ) n)) (k.hom n)) hf
    simp only [System.restrict_hom, System.flatten_pull_hom] at hn
    erw [flatten_baseChange (Spec.map (CommRingCat.ofHom φ))
      (Over.mk (quotientMap (I.map φ) n)) f] at hn
    exact hn
  intro n U a u hu
  let b : U ⟶ Over.mk (quotientMap I n) := Over.homMk u hu
  let hp := isPullback_quotientSpecMap φ I n
  let k := hp.lift b.left a.left ((Over.w b).trans (Over.w a).symm)
  let c : U ⟶ (Over.map (Spec.map (CommRingCat.ofHom φ))).obj
      (Over.mk (quotientMap (I.map φ) n)) :=
    Over.homMk k (by
      change k ≫ (quotientMap (I.map φ) n ≫ Spec.map (CommRingCat.ofHom φ)) = U.hom
      rw [← Category.assoc, hp.lift_snd]
      exact Over.w a)
  have ha : c ≫ (Over.homMk (quotientMap (I.map φ) n) rfl :
      (Over.map (Spec.map (CommRingCat.ofHom φ))).obj
        (Over.mk (quotientMap (I.map φ) n)) ⟶
          Over.mk (Spec.map (CommRingCat.ofHom φ))) = a :=
    Over.OverMorphism.ext (hp.lift_snd _ _ _)
  have hb : c ≫ quotientOver φ I n = b :=
    Over.OverMorphism.ext (hp.lift_fst _ _ _)
  let q : (Over.map (Spec.map (CommRingCat.ofHom φ))).obj
      (Over.mk (quotientMap (I.map φ) n)) ⟶ Over.mk (Spec.map (CommRingCat.ofHom φ)) :=
    Over.homMk (quotientMap (I.map φ) n) rfl
  calc
    evaluate a f = evaluate c (evaluate q f) := by rw [← evaluate_comp, ha]
    _ = evaluate c (evaluate (quotientOver φ I n) (s.hom n)) := congrArg (evaluate c) (hred n)
    _ = _ := by rw [← evaluate_comp, hb]

/-- Injectivity on the extended-ideal quotients detects formal lifts over an affine test. -/
theorem eq_of_isAlgebraization_of_injective (φ : A →+* B) (s : System I H G)
    (hinj : Function.Injective (System.restrict (I.map φ)
      ((baseChange (Spec.map (CommRingCat.ofHom φ))).obj H)
      ((baseChange (Spec.map (CommRingCat.ofHom φ))).obj G)))
    (f g : RelativeHom H G (Over.mk (Spec.map (CommRingCat.ofHom φ))))
    (hf : s.IsAlgebraization f) (hg : s.IsAlgebraization g) : f = g := by
  apply hinj
  apply System.ext
  intro n
  apply (flattenEquiv (Spec.map (CommRingCat.ofHom φ))
    (Over.mk (quotientMap (I.map φ) n))).injective
  change flatten (Spec.map (CommRingCat.ofHom φ)) (Over.mk (quotientMap (I.map φ) n))
      ((baseChange (quotientMap (I.map φ) n)).map f) =
    flatten (Spec.map (CommRingCat.ofHom φ)) (Over.mk (quotientMap (I.map φ) n))
      ((baseChange (quotientMap (I.map φ) n)).map g)
  erw [flatten_baseChange (Spec.map (CommRingCat.ofHom φ))
    (Over.mk (quotientMap (I.map φ) n)) f,
    flatten_baseChange (Spec.map (CommRingCat.ofHom φ))
    (Over.mk (quotientMap (I.map φ) n)) g]
  let q : (Over.map (Spec.map (CommRingCat.ofHom φ))).obj
      (Over.mk (quotientMap (I.map φ) n)) ⟶ Over.mk (Spec.map (CommRingCat.ofHom φ)) :=
    Over.homMk (quotientMap (I.map φ) n) rfl
  exact (hf n q (quotientSpecMap φ I n) (quotientSpecMap_quotientMap φ I n)).trans
    (hg n q (quotientSpecMap φ I n) (quotientSpecMap_quotientMap φ I n)).symm

variable [IsNoetherianRing A] [IsAdicComplete I A] [IsAffineHom G.X.hom]

/-- The split comparison applies over every finite algebra, with its image adic ideal. -/
theorem restrict_bijective_finite_affine
    (hdiag : DiagonalizableAdicHomComparisonStatement.{u})
    (φ : A →+* B) (hfin : φ.Finite)
    (hH : RelativeMultiplicativeType.IsDiagonalizable
      ((baseChange (Spec.map (CommRingCat.ofHom φ))).obj H)) :
    Function.Bijective (System.restrict (I.map φ)
      ((baseChange (Spec.map (CommRingCat.ofHom φ))).obj H)
      ((baseChange (Spec.map (CommRingCat.ofHom φ))).obj G)) := by
  let : Algebra A B := φ.toAlgebra
  let : Module.Finite A B := hfin
  let : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  have hcomp : IsAdicComplete I B := IsAdicComplete.of_finite_of_isNoetherianRing I B
  let : IsAdicComplete (I.map φ) B := (IsAdicComplete.map_algebraMap_iff I B).mpr hcomp
  have : IsAffineHom ((baseChange (Spec.map (CommRingCat.ofHom φ))).obj G).X.hom := by
    change IsAffineHom (pullback.snd G.X.hom (Spec.map (CommRingCat.ofHom φ)))
    infer_instance
  exact hdiag B (I.map φ) _ _ hH

/-- A finite affine test splitting the source admits an algebraization of any formal system. -/
theorem exists_isAlgebraization_affine
    (hdiag : DiagonalizableAdicHomComparisonStatement.{u})
    (φ : A →+* B) (hfin : φ.Finite)
    (hH : RelativeMultiplicativeType.IsDiagonalizable
      ((baseChange (Spec.map (CommRingCat.ofHom φ))).obj H)) (s : System I H G) :
    ∃ a : RelativeHom H G (Over.mk (Spec.map (CommRingCat.ofHom φ))),
      s.IsAlgebraization a := by
  obtain ⟨a, ha⟩ := (restrict_bijective_finite_affine (I := I) hdiag φ hfin hH).surjective
    (System.pull φ s)
  exact ⟨a, isAlgebraization_of_restrict_pull φ s a ha⟩

/-- Algebraizations are unique on every finite affine test splitting the source. -/
theorem eq_of_isAlgebraization_affine
    (hdiag : DiagonalizableAdicHomComparisonStatement.{u})
    (φ : A →+* B) (hfin : φ.Finite)
    (hH : RelativeMultiplicativeType.IsDiagonalizable
      ((baseChange (Spec.map (CommRingCat.ofHom φ))).obj H)) (s : System I H G)
    (a b : RelativeHom H G (Over.mk (Spec.map (CommRingCat.ofHom φ))))
    (ha : s.IsAlgebraization a) (hb : s.IsAlgebraization b) : a = b := by
  exact eq_of_isAlgebraization_of_injective φ s
    (restrict_bijective_finite_affine (I := I) hdiag φ hfin hH).injective a b ha hb

/-- The unique algebraization of a formal system on a finite affine splitting test. -/
def finiteAffineAlgebraization
    (hdiag : DiagonalizableAdicHomComparisonStatement.{u})
    (φ : A →+* B) (hfin : φ.Finite)
    (hH : RelativeMultiplicativeType.IsDiagonalizable
      ((baseChange (Spec.map (CommRingCat.ofHom φ))).obj H)) (s : System I H G) :
    RelativeHom H G (Over.mk (Spec.map (CommRingCat.ofHom φ))) :=
  Classical.choose (exists_isAlgebraization_affine hdiag φ hfin hH s)

/-- The selected finite affine algebraization has every prescribed formal reduction. -/
theorem isAlgebraization_finiteAffineAlgebraization
    (hdiag : DiagonalizableAdicHomComparisonStatement.{u})
    (φ : A →+* B) (hfin : φ.Finite)
    (hH : RelativeMultiplicativeType.IsDiagonalizable
      ((baseChange (Spec.map (CommRingCat.ofHom φ))).obj H)) (s : System I H G) :
    s.IsAlgebraization (finiteAffineAlgebraization hdiag φ hfin hH s) :=
  Classical.choose_spec (exists_isAlgebraization_affine hdiag φ hfin hH s)

end Langlands.GroupScheme.HomScheme.Adic
