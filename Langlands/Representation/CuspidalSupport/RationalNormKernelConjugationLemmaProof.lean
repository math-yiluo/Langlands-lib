import Langlands.Representation.CuspidalSupport.RationalNormKernelConjugationLemmaStatement
import Langlands.Representation.CuspidalSupport.RationalNormKernelCentralFiniteIndex

/-!
# Renard VI.3.1, Lemma: proof

Generic group-theoretic facts about inverse conjugates `σ ∘ conj g` of a
representation `σ` of a normal subgroup `N`, followed by their application to the
actual norm kernel `⁰G = Plancherel.rationalCommonNormKernel G`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.CuspidalSupport

universe u uV uW

section Generic

variable {Γ : Type*} [Group Γ] (N : Subgroup Γ) [N.Normal]
  {k : Type*} [CommSemiring k]

/-- For `h ∈ N ⊔ Z(Γ)`, the inverse conjugates `σ ∘ conj (g h)` and `σ ∘ conj g` of a
representation `σ` of the normal subgroup `N` are equivalent, by `σ(n)` where
`h = n z` with `n ∈ N` and `z` central. -/
theorem nonempty_equiv_comp_conjNormal_mul_of_mem_sup_center
    {W : Type*} [AddCommMonoid W] [Module k W]
    (σ : Representation k N W) (g h : Γ) (hh : h ∈ N ⊔ Subgroup.center Γ) :
    Nonempty (Representation.Equiv
      (σ.comp (MulAut.conjNormal (H := N) (g * h)⁻¹).toMonoidHom)
      (σ.comp (MulAut.conjNormal (H := N) g⁻¹).toMonoidHom)) := by
  obtain ⟨n, hn, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hh
  let m : N := ⟨n, hn⟩
  have hzc := Subgroup.mem_center_iff.mp hz
  have hcomm : ∀ a : Γ, z⁻¹ * a * z = a := fun a => by
    rw [mul_assoc, hzc a, ← mul_assoc, inv_mul_cancel, one_mul]
  have key : ∀ x : N, MulAut.conjNormal (H := N) (g * (n * z))⁻¹ x =
      m⁻¹ * MulAut.conjNormal (H := N) g⁻¹ x * m := by
    intro x
    apply Subtype.ext
    conv_rhs => rw [← hcomm (↑(m⁻¹ * MulAut.conjNormal (H := N) g⁻¹ x * m))]
    simp only [MulAut.conjNormal_apply, Subgroup.coe_mul, Subgroup.coe_inv, m]
    group
  let e : W ≃ₗ[k] W := LinearEquiv.ofLinearMap (σ m) (σ m⁻¹)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]; rfl)
    (by rw [← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]; rfl)
  refine ⟨Representation.Equiv.mk e fun x => ?_⟩
  ext w
  simp only [LinearMap.coe_comp, Function.comp_apply, MonoidHom.coe_comp,
    MulEquiv.coe_toMonoidHom, LinearEquiv.coe_coe, e, LinearEquiv.coe_ofLinearMap, key]
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
  congr 2
  group

/-- If `N ⊔ Z(Γ)` has finite index, the inverse conjugates `σ ∘ conj g` of a
representation of `N` fall into finitely many equivalence classes: a set of coset
representatives of `Γ ⧸ (N ⊔ Z(Γ))` gives representatives. -/
theorem exists_finset_nonempty_equiv_comp_conjNormal
    {W : Type*} [AddCommMonoid W] [Module k W]
    (σ : Representation k N W) [(N ⊔ Subgroup.center Γ).FiniteIndex] :
    ∃ S : Finset Γ, ∀ g : Γ, ∃ s ∈ S, Nonempty (Representation.Equiv
      (σ.comp (MulAut.conjNormal (H := N) g⁻¹).toMonoidHom)
      (σ.comp (MulAut.conjNormal (H := N) s⁻¹).toMonoidHom)) := by
  classical
  let H := N ⊔ Subgroup.center Γ
  have : Fintype (Γ ⧸ H) := Fintype.ofFinite _
  refine ⟨Finset.univ.image fun q : Γ ⧸ H => q.out, fun g => ?_⟩
  obtain ⟨h, hs⟩ := QuotientGroup.mk_out_eq_mul H g
  refine ⟨(QuotientGroup.mk g : Γ ⧸ H).out, Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
  rw [hs]
  obtain ⟨e⟩ := nonempty_equiv_comp_conjNormal_mul_of_mem_sup_center N σ g h h.2
  exact ⟨e.symm⟩

/-- `π(g)` carries the span of the images of all intertwiners `σ → π|_N` onto the
span of the images of all intertwiners `σ ∘ conj g → π|_N`. -/
theorem map_span_intertwiningMap_range_eq
    {V W : Type*} [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
    (π : Representation k Γ V) (σ : Representation k N W) (g : Γ) :
    (Submodule.span k {x : V | ∃ (f : Representation.IntertwiningMap σ (π.comp N.subtype))
        (w : W), f w = x}).map (π g) =
      Submodule.span k {x : V | ∃ (f : Representation.IntertwiningMap
          (σ.comp (MulAut.conjNormal (H := N) g⁻¹).toMonoidHom) (π.comp N.subtype))
        (w : W), f w = x} := by
  rw [Submodule.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨f, w, rfl⟩, rfl⟩
    refine ⟨LinearMap.intertwiningMap_of_isIntertwiningMap _ _ ((π g) ∘ₗ f.toLinearMap)
      fun y v => ?_, w, rfl⟩
    simp only [LinearMap.coe_comp, Function.comp_apply, MonoidHom.coe_comp,
      MulEquiv.coe_toMonoidHom, Representation.IntertwiningMap.coe_toLinearMap,
      Subgroup.coe_subtype, f.isIntertwining, MulAut.conjNormal_apply, inv_inv]
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2
    group
  · rintro ⟨f, w, rfl⟩
    refine ⟨(π g⁻¹) (f w), ⟨LinearMap.intertwiningMap_of_isIntertwiningMap _ _
      ((π g⁻¹) ∘ₗ f.toLinearMap) fun y v => ?_, w, rfl⟩, ?_⟩
    · let y' : N := MulAut.conjNormal (H := N) g y
      have hy : MulAut.conjNormal (H := N) g⁻¹ y' = y := by
        apply Subtype.ext
        simp only [y', MulAut.conjNormal_apply, inv_inv]
        group
      have hf := LinearMap.congr_fun (f.isIntertwining' y') v
      simp only [LinearMap.coe_comp, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom,
        Function.comp_apply, hy, Subgroup.coe_subtype,
        Representation.IntertwiningMap.coe_toLinearMap] at hf
      simp only [LinearMap.coe_comp, Function.comp_apply, MonoidHom.coe_comp,
        Subgroup.coe_subtype, Representation.IntertwiningMap.coe_toLinearMap, hf, y',
        MulAut.conjNormal_apply]
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 2
      group
    · exact Representation.self_inv_apply _ g (f w)

end Generic

/-- Renard VI.3.1, Lemma: the inverse conjugates of an irreducible smooth
representation of `⁰G` fall into finitely many classes, and `π(g)` carries the
`σ`-isotypic part of `π|_{⁰G}` onto the `σ^g`-isotypic part. -/
theorem rationalNormKernelConjugationLemma :
    RationalNormKernelConjugationLemmaStatement.{u, uV, uW} := by
  intro F _ _ _ _ G hG
  have := hG.isAffineHom
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have : Smooth G.X.hom := hG.smooth
  let : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
  have : IsTopologicalGroup (GroupScheme.rationalPoints G) :=
    rationalPoint_isTopologicalGroup F G
  have : (Plancherel.rationalCommonNormKernel G ⊔
      Subgroup.center (GroupScheme.rationalPoints G)).FiniteIndex :=
    rationalCommonNormKernel_sup_center_finiteIndex F G hG
  refine ⟨fun σ _ => exists_finset_nonempty_equiv_comp_conjNormal _ σ.representation,
    fun π σ _ g => map_span_intertwiningMap_range_eq _ π.representation σ.representation g⟩

end Langlands.CuspidalSupport
