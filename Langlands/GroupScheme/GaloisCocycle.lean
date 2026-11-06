import Langlands.GroupScheme.TorsorCocycle
import Langlands.GroupScheme.GaloisPointDescent
import Langlands.GroupScheme.Descent.FiniteGaloisTensor
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.GaloisCocycle

set_option backward.isDefEq.respectTransparency false

variable (k L : Type u) [Field k] [Field L] [Algebra k L]

/-- The actual coefficient spectrum over the base field. -/
abbrev cover : Over (Spec (CommRingCat.of k)) :=
  (algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k L))

/-- A coefficient automorphism as an endomorphism of the actual field cover. -/
def arrow (σ : L ≃ₐ[k] L) : cover k L ⟶ cover k L :=
  (algSpec (CommRingCat.of k)).map (CommAlgCat.ofHom σ.toAlgHom).op

@[simp] theorem arrow_one : arrow k L (1 : L ≃ₐ[k] L) = 𝟙 _ := by
  change (algSpec (CommRingCat.of k)).map (𝟙 _) = _
  exact CategoryTheory.Functor.map_id _ _

theorem arrow_mul (σ τ : L ≃ₐ[k] L) :
    arrow k L (σ * τ) = arrow k L σ ≫ arrow k L τ := by
  change (algSpec (CommRingCat.of k)).map
    ((CommAlgCat.ofHom σ.toAlgHom).op ≫ (CommAlgCat.ofHom τ.toAlgHom).op) = _
  exact CategoryTheory.Functor.map_comp _ _ _

variable {k L} {G : GroupScheme (Spec (CommRingCat.of k))}

/-- The value of a scheme cocycle on the identity and a Galois automorphism. -/
def value (ξ : Cocycle G (cover k L)) (σ : L ≃ₐ[k] L) :
    G.affinePoints (CommAlgCat.of k L) :=
  ξ.toFun (𝟙 _) (arrow k L σ)

/-- These values satisfy the crossed multiplicative cocycle identity. -/
theorem value_mul (ξ : Cocycle G (cover k L)) (σ τ : L ≃ₐ[k] L) :
    value ξ (σ * τ) =
      value ξ σ * GaloisPoint.conjugate k L G σ (value ξ τ) := by
  change ξ.toFun (𝟙 _) (arrow k L (σ * τ)) =
    ξ.toFun (𝟙 _) (arrow k L σ) * (arrow k L σ ≫ ξ.toFun (𝟙 _) (arrow k L τ))
  rw [arrow_mul, ξ.cocycle (𝟙 _) (arrow k L σ) (arrow k L σ ≫ arrow k L τ)]
  congr 1
  simpa only [Category.comp_id] using ξ.naturality (arrow k L σ) (𝟙 _) (arrow k L τ)

/-- A cochain's scheme coboundary has the same Galois coboundary convention. -/
theorem value_coboundary (f : cover k L ⟶ G.X) (σ : L ≃ₐ[k] L) :
    value (Cocycle.coboundary f) σ =
      f * (GaloisPoint.conjugate k L G σ f)⁻¹ := by
  change (𝟙 _ ≫ f) * (arrow k L σ ≫ f)⁻¹ = _
  rw [Category.id_comp]
  rfl

variable [FiniteDimensional k L] [IsGalois k L]

/-- Galois-indexed values determine a cocycle on every relative test scheme. -/
theorem toFun_eq_of_value_eq (ξ ξ₂ : Cocycle G (cover k L))
    (h : ∀ σ : L ≃ₐ[k] L, value ξ σ = value ξ₂ σ)
    {Z : Over (Spec (CommRingCat.of k))} (a b : Z ⟶ cover k L) :
    ξ.toFun a b = ξ₂.toFun a b := by
  let p := Descent.fieldMap k L
  let P : Over (Spec (CommRingCat.of k)) := Over.mk (Descent.fst p ≫ p)
  let a₀ : P ⟶ cover k L := Over.homMk (Descent.fst p)
  let b₀ : P ⟶ cover k L :=
    Over.homMk (Descent.snd p) pullback.condition.symm
  have hP : ξ.toFun a₀ b₀ = ξ₂.toFun a₀ b₀ := by
    apply Over.OverMorphism.ext
    apply (cancel_epi (Sigma.desc (Descent.finiteGaloisComponent k L))).mp
    apply Sigma.hom_ext
    intro i
    simp only [Sigma.ι_comp_desc_assoc]
    let t : cover k L ⟶ P := Over.homMk (Descent.finiteGaloisComponent k L i)
      (by
        change Descent.finiteGaloisComponent k L i ≫ Descent.fst p ≫ p = p
        rw [← Category.assoc, Descent.finiteGaloisComponent_fst, Category.id_comp])
    have ht₁ : t ≫ a₀ = 𝟙 _ := by
      apply Over.OverMorphism.ext
      exact Descent.finiteGaloisComponent_fst k L i
    have ht₂ : t ≫ b₀ = arrow k L (Descent.galoisIndexEquiv k L i) := by
      apply Over.OverMorphism.ext
      exact Descent.finiteGaloisComponent_snd k L i
    have hξ := ξ.naturality t a₀ b₀
    have hξ₂ := ξ₂.naturality t a₀ b₀
    rw [ht₁, ht₂] at hξ hξ₂
    exact congrArg (fun f => f.left) (hξ.symm.trans ((h _).trans hξ₂))
  let t : Z ⟶ P := Over.homMk
    (pullback.lift a.left b.left (a.w.trans b.w.symm))
    (by
      change pullback.lift a.left b.left _ ≫ Descent.fst p ≫ p = Z.hom
      rw [pullback.lift_fst_assoc]
      exact a.w)
  have ht₁ : t ≫ a₀ = a := by
    apply Over.OverMorphism.ext
    exact pullback.lift_fst _ _ _
  have ht₂ : t ≫ b₀ = b := by
    apply Over.OverMorphism.ext
    exact pullback.lift_snd _ _ _
  calc
    ξ.toFun a b = t ≫ ξ.toFun a₀ b₀ := by
      rw [← ht₁, ← ht₂]
      exact ξ.naturality t a₀ b₀
    _ = t ≫ ξ₂.toFun a₀ b₀ := by rw [hP]
    _ = ξ₂.toFun a b := by
      rw [← ht₁, ← ht₂]
      exact (ξ₂.naturality t a₀ b₀).symm

/-- Scheme triviality is exactly the Galois coboundary identity over the same field. -/
theorem isTrivial_iff (ξ : Cocycle G (cover k L)) :
    ξ.IsTrivial ↔ ∃ f : G.affinePoints (CommAlgCat.of k L),
      ∀ σ : L ≃ₐ[k] L,
        value ξ σ = f * (GaloisPoint.conjugate k L G σ f)⁻¹ := by
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨f, fun σ => ?_⟩
    change ξ.toFun (𝟙 _) (arrow k L σ) = f * (arrow k L σ ≫ f)⁻¹
    simpa only [Category.id_comp] using hf (𝟙 _) (arrow k L σ)
  · rintro ⟨f, hf⟩
    refine ⟨f, fun a b => ?_⟩
    exact toFun_eq_of_value_eq ξ (Cocycle.coboundary f)
      (fun σ => (hf σ).trans (value_coboundary f σ).symm) a b

section Commutative

variable [IsCommMonObj G.X]

/-- The actual additive coefficient points with their lifted-integral Galois action. -/
def pointRepresentation : Rep.{u} (ULift.{u} ℤ) (L ≃ₐ[k] L) :=
  Rep.of
    { toFun σ :=
        (GaloisPoint.conjugate k L G σ).toAdditive.toIntLinearMap.restrictScalars (ULift.{u} ℤ)
      map_one' := by
        apply LinearMap.ext
        intro x
        exact congrArg Additive.ofMul (GaloisPoint.conjugate_one k L G x.toMul)
      map_mul' σ τ := by
        apply LinearMap.ext
        intro x
        exact congrArg Additive.ofMul (GaloisPoint.conjugate_mul k L G σ τ x.toMul) }

/-- A scheme cocycle determines an ordinary additive group-cohomology cocycle. -/
def additiveCocycle (ξ : Cocycle G (cover k L)) :
    groupCohomology.cocycles₁ (pointRepresentation (G := G) (k := k) (L := L)) :=
  ⟨fun σ => Additive.ofMul (value ξ σ),
    (groupCohomology.mem_cocycles₁_iff _).mpr fun σ τ => by
      change Additive.ofMul (value ξ (σ * τ)) =
        Additive.ofMul (GaloisPoint.conjugate k L G σ (value ξ τ) * value ξ σ)
      exact congrArg Additive.ofMul ((value_mul ξ σ τ).trans (mul_comm _ _))⟩

/-- Vanishing of actual ordinary first cohomology trivializes the scheme cocycle. -/
theorem isTrivial_of_H1_isZero (ξ : Cocycle G (cover k L))
    (h : IsZero (groupCohomology (pointRepresentation (G := G) (k := k) (L := L)) 1)) :
    ξ.IsTrivial := by
  have := ModuleCat.isZero_iff_subsingleton.mp h
  have hm := (groupCohomology.H1π_eq_zero_iff (additiveCocycle ξ)).mp
    (Subsingleton.elim _ _)
  obtain ⟨x, hx⟩ := hm
  let z : G.affinePoints (CommAlgCat.of k L) :=
    (x : Additive (G.affinePoints (CommAlgCat.of k L))).toMul
  apply (isTrivial_iff ξ).mpr
  refine ⟨z⁻¹, fun σ => ?_⟩
  have hs := congrFun hx σ
  rw [groupCohomology.d₀₁_hom_apply] at hs
  have hs' : GaloisPoint.conjugate k L G σ z * z⁻¹ = value ξ σ :=
    congrArg (fun y : Additive (G.affinePoints (CommAlgCat.of k L)) => y.toMul) hs
  rw [← hs', map_inv, inv_inv, mul_comm]

end Commutative

end Langlands.GroupScheme.GaloisCocycle
