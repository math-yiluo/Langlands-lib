import Langlands.GroupScheme.FiniteFieldTorsorPoint.PointDescent
import Langlands.AbelianScheme.GroupScheme
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Rational points of torsors from Lang's theorem -/

noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.GroupScheme.FiniteFieldTorsorPoint

/-- Let a group scheme `H` locally of finite type over `S` act on `X` over `S` with
invertible shear map `(h, x) ↦ (h • x, x)`. If `X → S` is flat, surjective and
quasi-compact, then `X → S` is locally of finite type. -/
theorem locallyOfFiniteType_of_isIso_leftSMul {S : Scheme.{u}} (H : GroupScheme S)
    [LocallyOfFiniteType H.X.hom] (X : Over S) [ModObj H.X X] (hfl : Flat X.hom)
    (hs : Surjective X.hom) (hqc : QuasiCompact X.hom)
    (hiso : IsIso (ModObj.leftSMul H.X X)) :
    LocallyOfFiniteType X.hom := by
  have h1 : (ModObj.leftSMul H.X X).left ≫ pullback.snd X.hom X.hom =
      pullback.snd H.X.hom X.hom :=
    congrArg CommaMorphism.left (ModObj.leftSMul_snd (M := H.X) (X := X))
  have : IsIso (ModObj.leftSMul H.X X).left :=
    inferInstanceAs (IsIso ((Over.forget S).map (ModObj.leftSMul H.X X)))
  have h2 : LocallyOfFiniteType (pullback.snd X.hom X.hom) := by
    rw [← IsIso.inv_hom_id_assoc (ModObj.leftSMul H.X X).left (pullback.snd X.hom X.hom), h1]
    infer_instance
  exact MorphismProperty.of_pullback_snd_of_descendsAlong (P := @LocallyOfFiniteType)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (f := X.hom) (g := X.hom) ⟨⟨hs, hfl⟩, hqc⟩ h2

variable {k : Type u} [Field k] [Fintype k]

/-- A flat, surjective, quasi-compact scheme `X` over a finite field `k` with an action
of a group scheme `H` locally of finite type over `k` and invertible shear map has a
`k`-point, provided that every point `a` of `H` over the algebraic closure `K` of `k` has
the form `g⁻¹ * F(g)`, where `F` is the `k`-linear `q`-power Frobenius of `K`. -/
theorem torsor_point_of_lang (H : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType H.X.hom] (X : Over (Spec (CommRingCat.of k))) [ModObj H.X X]
    (hfl : Flat X.hom) (hs : Surjective X.hom) (hqc : QuasiCompact X.hom)
    (hiso : IsIso (ModObj.leftSMul H.X X))
    (hLang : ∀ a : ringTest k (AlgebraicClosure k) ⟶ H.X,
      ∃ g : ringTest k (AlgebraicClosure k) ⟶ H.X,
        a = g⁻¹ * (ringTestMap k (FiniteField.frobeniusAlgHom k (AlgebraicClosure k)) ≫ g)) :
    Nonempty (RingPoint k X k) := by
  set K := AlgebraicClosure k
  set F := ringTestMap k (FiniteField.frobeniusAlgHom k K)
  have := locallyOfFiniteType_of_isIso_leftSMul H X hfl hs hqc hiso
  have : Nonempty X.left := ⟨(hs.surj (Classical.arbitrary _)).choose⟩
  obtain ⟨p₀⟩ := nonempty_ringPoint_of_locallyOfFiniteType (X := X) K
  let p₀' : ringTest k K ⟶ X := p₀
  obtain ⟨a, ha, -⟩ := (ModObj.isIso_leftSMul_iff.mp hiso) (ringTest k K) p₀' (F ≫ p₀')
  obtain ⟨g, hg⟩ := hLang a⁻¹
  have hFg : F ≫ g = g * a⁻¹ := by
    rw [hg, mul_inv_cancel_left]
  refine nonempty_ringPoint_of_frobenius_fixed (K := K) (g • p₀' : ringTest k K ⟶ X) ?_
  change F ≫ (g • p₀') = g • p₀'
  rw [ModObj.comp_smul, ← ha, ← mul_smul, hFg, inv_mul_cancel_right]

end Langlands.GroupScheme.FiniteFieldTorsorPoint
