import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreCharts
import Langlands.AlgebraicGeometry.UnramifiedFunctor.ArtinianBaseChart
import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreChartsLocal
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite IsLocalRing

noncomputable section

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor.ArtinianBase

open Charts

variable {R : CommRingCat.{u}} {F : (Over (Spec R))ᵒᵖ ⥤ Type v}

section Spec

/-- Every morphism `ovR T' ⟶ ovR T` over `Spec R` is `homR` of an `R`-algebra map. -/
lemma exists_homR {T T' : Type u} [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']
    (g : ovR R T' ⟶ ovR R T) : ∃ φ : T →ₐ[R] T', homR φ = g := by
  let ψ := Spec.preimage g.left
  have hψ : Spec.map ψ = g.left := Spec.map_preimage _
  have hw := Over.w g
  have hcomm : CommRingCat.ofHom (algebraMap R T) ≫ ψ = CommRingCat.ofHom (algebraMap R T') := by
    apply Spec.map_injective
    rw [Spec.map_comp, hψ]
    exact hw
  refine ⟨{ ψ.hom with commutes' := fun r ↦ congrArg (fun f ↦ f.hom r) hcomm }, ?_⟩
  ext1
  exact hψ

lemma homR_injective {T T' : Type u} [CommRing T] [Algebra R T] [CommRing T'] [Algebra R T']
    {φ ψ : T →ₐ[R] T'} (h : homR φ = homR ψ) : φ = ψ := by
  have := Spec.map_injective (congrArg CommaMorphism.left h)
  ext x
  exact congrArg (fun f ↦ f.hom x) this

/-- Infinitesimal étaleness of `ξ ∈ F(Spec B)` from the ring-level lifting property. -/
lemma infinitesimallyEtaleAt_of_ring {B : Type u} [CommRing B] [Algebra R B]
    (ξ : F.obj (op (ovR R B)))
    (H : ∀ (A : Type u) [CommRing A] [Algebra R A] [IsLocalRing A] [IsArtinianRing A]
      (I : Ideal A), IsNilpotent I → ∀ (u₀ : B →ₐ[R] A ⧸ I) (v : F.obj (op (ovR R A))),
        res u₀ ξ = res (Ideal.Quotient.mkₐ R I) v →
          ∃! u : B →ₐ[R] A, (Ideal.Quotient.mkₐ R I).comp u = u₀ ∧ res u ξ = v)
    (y : (ovR R B).left) : InfinitesimallyEtaleAt F ξ y := by
  intro A _ _ _ f J hJ u₀ _ v hv
  obtain ⟨φ, rfl⟩ : ∃ φ, Spec.map φ = f := ⟨_, Spec.map_preimage f⟩
  let : Algebra R A := φ.hom.toAlgebra
  let e := towerIso (R := R) A (A ⧸ J)
  obtain ⟨φ₀, hφ₀⟩ := exists_homR (e.inv ≫ u₀)
  have h1 : u₀ = e.hom ≫ homR φ₀ := by rw [hφ₀, Iso.hom_inv_id_assoc]
  have h2 : algebraOverBase (Spec.map φ) (A ⧸ J) =
      e.hom ≫ homR (Ideal.Quotient.mkₐ R J) := by
    ext1
    simp [algebraOverBase, e, towerIso]
    rfl
  have hv' : res φ₀ ξ = res (Ideal.Quotient.mkₐ R J) v := by
    rw [h1, h2, op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply] at hv
    exact map_iso_injective e hv
  obtain ⟨u', ⟨hu'1, hu'2⟩, huniq⟩ := H A J hJ φ₀ v hv'
  refine ⟨homR u', ⟨?_, hu'2⟩, ?_⟩
  · rw [h2, Category.assoc, ← homR_comp, hu'1, h1]
  · rintro u ⟨hu1, hu2⟩
    obtain ⟨u'', rfl⟩ := exists_homR u
    have : (Ideal.Quotient.mkₐ R J).comp u'' = φ₀ := by
      apply homR_injective
      rw [homR_comp, hφ₀, ← hu1, h2, Category.assoc, Iso.inv_hom_id_assoc]
    rw [huniq u'' ⟨this, hu2⟩]

/-- A monomorphism criterion for `ξ ∈ F(Spec B)`, `B` of finite type and formally unramified
over `R`: it suffices that `ξ` separates `R`-algebra maps from `B` to fields. Two morphisms
`T ⟶ Spec B` with the same image in `F(T)` agree at every residue field of `T`, so their pair
maps every point into the open diagonal (`Charts.eq_of_forall_mem_range_diagonal`). -/
lemma isMonoElement_of_field {B : Type u} [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
    [Algebra.FormallyUnramified R B] (ξ : F.obj (op (ovR R B)))
    (H : ∀ (K : Type u) [Field K] [Algebra R K] (φ₁ φ₂ : B →ₐ[R] K),
      res φ₁ ξ = res φ₂ ξ → φ₁ = φ₂) : IsMonoElement F ξ := by
  intro T h₁ h₂ hh
  have : LocallyOfFiniteType (ovR R B).hom := Charts.locallyOfFiniteType_ovR B
  have : FormallyUnramified (ovR R B).hom := Charts.formallyUnramified_ovR B
  have w : h₁.left ≫ (ovR R B).hom = h₂.left ≫ (ovR R B).hom := by rw [Over.w h₁, Over.w h₂]
  ext1
  apply Charts.eq_of_forall_mem_range_diagonal (ovR R B).hom h₁.left h₂.left w
  intro z
  let K := T.left.residueField z
  let k := T.left.fromSpecResidueField z
  let t : Spec K ⟶ Spec R := k ≫ T.hom
  let φt := Spec.preimage t
  let : Algebra R K := φt.hom.toAlgebra
  let iK : ovR R K ≅ Over.mk t := Over.isoMk (Iso.refl _) (by
    change 𝟙 _ ≫ t = Spec.map _
    rw [Category.id_comp]
    exact (Spec.map_preimage t).symm)
  let πk : Over.mk t ⟶ T := Over.homMk k rfl
  have hk : k ≫ h₁.left = k ≫ h₂.left := by
    obtain ⟨φ₁, hφ₁⟩ := exists_homR (iK.hom ≫ πk ≫ h₁)
    obtain ⟨φ₂, hφ₂⟩ := exists_homR (iK.hom ≫ πk ≫ h₂)
    have hres : res φ₁ ξ = res φ₂ ξ := by
      simp only [res, hφ₁, hφ₂, op_comp, Functor.map_comp_apply, hh]
    have := H K φ₁ φ₂ hres
    have e := congrArg CommaMorphism.left (hφ₁.symm.trans (this ▸ hφ₂))
    simpa [iK, πk] using e
  have hz : k (IsLocalRing.closedPoint K) = z := Scheme.fromSpecResidueField_apply _ _
  rw [← hz]
  exact Charts.lift_mem_range_diagonal (ovR R B).hom h₁.left h₂.left w k hk _

end Spec

end Langlands.AlgebraicGeometry.UnramifiedFunctor.ArtinianBase
