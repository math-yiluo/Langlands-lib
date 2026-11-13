import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.TensorProduct
import Mathlib.RingTheory.LocalRing.ResidueField.Fiber

/-! # The rank of relative differentials at a point of a fibre of relative dimension `n` -/

noncomputable section

universe u

open AlgebraicGeometry TensorProduct

namespace Langlands.GroupScheme.ReducedBaseSmooth

/-- If `k → F` is locally standard smooth of relative dimension `n`, then for every field `K`
with an `F`-algebra structure, `K ⊗[F] Ω[F⁄k]` has dimension `n` over `K`. -/
theorem finrank_tensor_kaehler_of_locally {k F K : Type u} [CommRing k] [CommRing F] [Field K]
    [Algebra k F] [Algebra F K] (n : ℕ)
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) (algebraMap k F)) :
    Module.finrank K (K ⊗[F] Ω[F⁄k]) = n := by
  classical
  obtain ⟨s, hs, hst⟩ := h
  have hex : ∃ t ∈ s, algebraMap F K t ≠ 0 := by
    by_contra! H
    have hle : Ideal.span s ≤ RingHom.ker (algebraMap F K) :=
      Ideal.span_le.mpr fun t ht => H t ht
    rw [hs, top_le_iff, Ideal.eq_top_iff_one, RingHom.mem_ker, map_one] at hle
    exact one_ne_zero hle
  obtain ⟨t, ht, htK⟩ := hex
  let Ft := Localization.Away t
  have hstd : Algebra.IsStandardSmoothOfRelativeDimension n k Ft := by
    rw [← RingHom.isStandardSmoothOfRelativeDimension_algebraMap,
      IsScalarTower.algebraMap_eq k F Ft]
    exact hst t ht
  have : Algebra.IsStandardSmooth k Ft :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth (n := n)
  let : Algebra Ft K :=
    (IsLocalization.Away.lift t (isUnit_iff_ne_zero.mpr htK) : Ft →+* K).toAlgebra
  have : IsScalarTower F Ft K := IsScalarTower.of_algebraMap_eq fun x =>
    (IsLocalization.Away.lift_eq t (isUnit_iff_ne_zero.mpr htK) x).symm
  have : Nontrivial Ft := (algebraMap Ft K).domain_nontrivial
  have : Algebra.FormallyEtale F Ft :=
    Algebra.FormallyEtale.of_isLocalization (Rₘ := Ft) (Submonoid.powers t)
  have hrank : Module.rank Ft Ω[Ft⁄k] = n :=
    Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential n
  have hfin : Module.finrank Ft Ω[Ft⁄k] = n := Module.finrank_eq_of_rank_eq hrank
  let e : K ⊗[F] Ω[F⁄k] ≃ₗ[K] K ⊗[Ft] Ω[Ft⁄k] :=
    (AlgebraTensorModule.cancelBaseChange F Ft K K Ω[F⁄k]).symm ≪≫ₗ
      AlgebraTensorModule.congr (LinearEquiv.refl K K)
        (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k F Ft)
  rw [e.finrank_eq, Module.finrank_baseChange, hfin]

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- Let `B` be an `R`-algebra, `p` a prime of `R` and `Q` a prime of `B` lying over `p`. If the
fibre `Spec (κ(p) ⊗[R] B) → Spec κ(p)` is smooth of relative dimension `n`, then
`κ(Q) ⊗[B] Ω[B⁄R]` has dimension `n` over `κ(Q)`. -/
theorem finrank_residueField_tensor_kaehler_eq {R B : Type u} [CommRing R] [CommRing B]
    [Algebra R B] (p : Ideal R) [p.IsPrime] (Q : Ideal B) [Q.IsPrime] [Q.LiesOver p] (n : ℕ)
    (h : SmoothOfRelativeDimension n
      (Spec.map (CommRingCat.ofHom (algebraMap p.ResidueField (p.Fiber B))))) :
    Module.finrank Q.ResidueField (Q.ResidueField ⊗[B] Ω[B⁄R]) = n := by
  classical
  have hloc : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n)
      (algebraMap p.ResidueField (p.Fiber B)) :=
    HasRingHomProperty.Spec_iff.mp h
  let φ : p.Fiber B →ₐ[R] Q.ResidueField := Algebra.TensorProduct.lift
    (Ideal.ResidueField.mapₐ p Q (Algebra.ofId R B) (Q.over_def p))
    (IsScalarTower.toAlgHom R B Q.ResidueField) (fun _ _ => .all _ _)
  let : Algebra (p.Fiber B) Q.ResidueField := φ.toRingHom.toAlgebra
  have : IsScalarTower B (p.Fiber B) Q.ResidueField := IsScalarTower.of_algebraMap_eq fun b => by
    change algebraMap B Q.ResidueField b = φ (1 ⊗ₜ b)
    simp [φ]
  have hK := finrank_tensor_kaehler_of_locally (K := Q.ResidueField) n hloc
  let e : Q.ResidueField ⊗[B] Ω[B⁄R] ≃ₗ[Q.ResidueField]
      Q.ResidueField ⊗[p.Fiber B] Ω[p.Fiber B⁄p.ResidueField] :=
    (AlgebraTensorModule.cancelBaseChange B (p.Fiber B) Q.ResidueField Q.ResidueField
      Ω[B⁄R]).symm ≪≫ₗ
      AlgebraTensorModule.congr (LinearEquiv.refl Q.ResidueField Q.ResidueField)
        (KaehlerDifferential.tensorKaehlerEquiv R p.ResidueField B (p.Fiber B))
  rw [e.finrank_eq, hK]

end Langlands.GroupScheme.ReducedBaseSmooth
