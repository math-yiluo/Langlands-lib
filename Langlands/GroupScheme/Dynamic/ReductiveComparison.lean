import Langlands.GroupScheme.Dynamic.TensorPoints
import Langlands.GroupScheme.HomogeneousQuotientComparison
import Langlands.GroupScheme.CentralIsogeny.Basic
import Langlands.GroupScheme.Reductive.UnipotentRadical

/-! # The comparison map to the reductive quotient, and the kernel condition

Let `G = Spec B` be a corepresented group over a field `k` with a cocharacter `χ`, let
`q : G ⟶ Q` be a quotient by `P_G(χ)`, and let `π : G_Ω ⟶ H` be a homomorphism. If the fibers
of the base change `q_Ω` are the cosets of `P(χ_Ω)` and `q_Ω` is flat, surjective and
quasi-compact, then `π ≫ q₀` descends along `q_Ω` for every quotient `q₀ : H ⟶ Q₀` by
`P_H(χ_Ω ≫ π)`. If the kernel of `π` is a closed unipotent normal subgroup, then the kernel
condition of `exists_extension_of_comparison` follows from the triviality statement for
`k`-points of `U_G(ν)` that become points of such a subgroup.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme

namespace Corepresented

open CommutativeAlgebra.GradedDVRIntegrality

variable {k : Type u} [Field k] {F : CommAlgCat.{u} (CommRingCat.of k) ⥤ GrpCat.{u}}
  {B : CommAlgCat.{u} (CommRingCat.of k)} {e : (F ⋙ forget GrpCat).CorepresentableBy B}
  {Ω : Type u} [Field Ω] [Algebra k Ω]
  {H : GroupScheme (Spec (CommRingCat.of Ω))} (π : baseChangeGroup F e Ω ⟶ H)

/-- **The comparison map.** -/
theorem exists_comparison_desc (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ groupScheme F e)
    {Q : Over (Spec (CommRingCat.of k))} (q : (groupScheme F e).X ⟶ Q)
    [Flat ((Over.pullback (scalarMap k Ω)).map q).left]
    [Surjective ((Over.pullback (scalarMap k Ω)).map q).left]
    [QuasiCompact ((Over.pullback (scalarMap k Ω)).map q).left]
    (hfΩ : ∀ (T : Over (Spec (CommRingCat.of Ω))) (g h : T ⟶ (baseChangeGroup F e Ω).X),
      g ≫ (Over.pullback (scalarMap k Ω)).map q = h ≫ (Over.pullback (scalarMap k Ω)).map q ↔
        g⁻¹ * h ∈ (Dynamic.parabolic
          (Dynamic.baseChangeCocharacter (scalarMap k Ω) χ)).carrier T)
    {Q₀ : Over (Spec (CommRingCat.of Ω))} (q₀ : H.X ⟶ Q₀)
    (hf₀ : ∀ (T : Over (Spec (CommRingCat.of Ω))) (g h : T ⟶ H.X),
      g ≫ q₀ = h ≫ q₀ ↔ g⁻¹ * h ∈ (Dynamic.parabolic
        (Dynamic.baseChangeCocharacter (scalarMap k Ω) χ ≫ π)).carrier T) :
    ∃ φ : (Over.pullback (scalarMap k Ω)).obj Q ⟶ Q₀,
      (Over.pullback (scalarMap k Ω)).map q ≫ φ = π.hom.hom ≫ q₀ := by
  refine ⟨HomogeneousQuotientComparison.desc ((Over.pullback (scalarMap k Ω)).map q)
    (π.hom.hom ≫ q₀) (fun T a b hab => ?_), HomogeneousQuotientComparison.fac_desc _ _ _⟩
  let a' : T ⟶ (baseChangeGroup F e Ω).X := a
  let b' : T ⟶ (baseChangeGroup F e Ω).X := b
  have hP := (hfΩ T a' b').1 hab
  have hP' := Dynamic.parabolic_le_comap (Dynamic.baseChangeCocharacter (scalarMap k Ω) χ) π T
    hP
  rw [SubgroupFunctor.mem_comap, MonObj.mul_comp, GrpObj.inv_comp] at hP'
  have h := (hf₀ T (a' ≫ π.hom.hom) (b' ≫ π.hom.hom)).2 hP'
  rw [Category.assoc, Category.assoc] at h
  exact h

/-- The base change of the counit is the identity point. -/
theorem bcPoint_counit {A : Type u} [CommRing A] [Algebra k A] [Algebra Ω A]
    [IsScalarTower k Ω A] :
    bcPoint F e Ω A ((Algebra.ofId k A).comp (counitAlgHom e)) = 1 := by
  apply (baseChangePointsEquiv (scalarMap k Ω) (groupScheme F e) (testOver Ω A)).injective
  rw [bcPoint, MulEquiv.apply_symm_apply, map_one]
  apply hom_ext_of_pointRing
  rw [pointRing_one]
  have hf : Spec.preimage ((Over.map (scalarMap k Ω)).obj (testOver Ω A)).hom =
      CommRingCat.ofHom (algebraMap k A) := by
    apply Spec.map_injective
    rw [Spec.map_preimage]
    exact specMap_algebraMap_comp_scalarMap Ω A
  erw [hf]
  refine CommRingCat.hom_ext (RingHom.ext fun b => ?_)
  change Spec.preimage (𝟙 _ ≫ Spec.map _) b = _
  rw [Category.id_comp, Spec.preimage_map]
  rfl

/-- The point of `G` over `Spec k` (with identity structure map) given by a `k`-point. -/
def rationalPoint (a : B →ₐ[k] k) : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ (groupScheme F e).X :=
  Over.homMk (Spec.map (CommRingCat.ofHom a.toRingHom)) (by
    change Spec.map _ ≫ Spec.map (CommRingCat.ofHom (algebraMap k B)) = 𝟙 _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id]
    congr 2
    exact RingHom.ext a.commutes)

theorem pointRing_rationalPoint (a : B →ₐ[k] k) :
    pointRing (rationalPoint (F := F) (e := e) a) = CommRingCat.ofHom a.toRingHom :=
  Spec.preimage_map _

/-- **The kernel condition.** Suppose the kernel of `π` has the same points as a subgroup
`i : U ⟶ G_Ω`. Suppose also that a `k`-point of `U_G(ν)` whose base change lies in `U` is
trivial. Then a contracting `k`-point `a` with `π(a_Ω) = π(ε_Ω)` is the counit. -/
theorem hker_of_kernel (ν : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ groupScheme F e)
    {U : GroupScheme (Spec (CommRingCat.of Ω))} (i : U ⟶ baseChangeGroup F e Ω)
    (hπ : SubgroupFunctor.range (kernelι π) = SubgroupFunctor.range i)
    (hc : ∀ u : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ (groupScheme F e).X,
      u ∈ (Dynamic.unipotent ν).carrier _ →
      (∃ y : Over.mk (𝟙 (Spec (CommRingCat.of Ω))) ⟶ U.X,
        baseChangePointsEquiv (scalarMap k Ω) (groupScheme F e)
          (Over.mk (𝟙 (Spec (CommRingCat.of Ω)))) (y ≫ i.hom.hom) = toUnit _ ≫ u) →
      u = 1) :
    ∀ a : B →ₐ[k] k, IsContracting (coaction ν).hom (counitAlgHom e) a →
      bcPoint F e Ω Ω ((Algebra.ofId k Ω).comp a) ≫ π.hom.hom =
        bcPoint F e Ω Ω ((Algebra.ofId k Ω).comp (counitAlgHom e)) ≫ π.hom.hom →
      a = counitAlgHom e := by
  intro a ha hπa
  have hu : rationalPoint (F := F) (e := e) a ∈ (Dynamic.unipotent ν).carrier _ := by
    rw [mem_unipotent_iff, pointRing_rationalPoint]
    refine ⟨fun b n hn => ha.1 b n hn, fun b => ?_⟩
    change a _ = 0
    rw [map_sub, sub_eq_zero]
    exact (ha.2 b).trans (a.commutes _).symm
  have hz1 : bcPoint F e Ω Ω ((Algebra.ofId k Ω).comp a) ≫ π.hom.hom = 1 := by
    rw [hπa, bcPoint_counit, MonObj.one_comp]
  have hzker := (mem_range_kernelι_iff π _).2 hz1
  rw [hπ] at hzker
  obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.1 hzker
  let e₀ : Over.mk (𝟙 (Spec (CommRingCat.of Ω))) ⟶ testOver Ω Ω :=
    Over.homMk (𝟙 _) (by
      change 𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap Ω Ω)) = 𝟙 _
      rw [Category.id_comp, Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id])
  have h1 := hc _ hu ⟨e₀ ≫ y, by
    rw [Category.assoc, hy, baseChangePointsEquiv_naturality, bcPoint,
      MulEquiv.apply_symm_apply]
    apply Over.OverMorphism.ext
    change 𝟙 _ ≫ 𝟙 _ ≫ Spec.map (CommRingCat.ofHom ((Algebra.ofId k Ω).comp a).toRingHom) =
      Spec.map (CommRingCat.ofHom (algebraMap k Ω)) ≫ Spec.map (CommRingCat.ofHom a.toRingHom)
    rw [Category.id_comp, Category.id_comp, ← Spec.map_comp]
    rfl⟩
  have h2 := congrArg pointRing h1
  rw [pointRing_rationalPoint, pointRing_one, Spec.preimage_id, Category.comp_id] at h2
  ext b
  exact congrArg (fun φ => φ.hom b) h2

end Corepresented

end Langlands.GroupScheme
