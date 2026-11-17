import Langlands.GroupScheme.IntegralModel.LieLattice
import Langlands.GroupScheme.IntegralModel.AffineWeilPoints
import Langlands.GroupScheme.Lie.Adjoint
import Langlands.GroupScheme.Lie.Functoriality

/-! # Integral points preserve the Lie lattice

Let `R` be a domain with fraction field `K` and `M : IntegralModel R K G` a supplied integral
model of an affine group `G` over `K`. The adjoint action of a rational point `g ∈ G(K)` on
`Lie(G)` is regarded as an `R`-linear endomorphism of the type synonym `GenericLie R G`. The Lie
map `M.lieMap : Lie(𝒢) → Lie(G)` intertwines the adjoint action of an integral section
`x ∈ 𝒢(R)` on `Lie(𝒢)` with the adjoint action of its generic point. Hence the adjoint action of
every integral point maps `M.lieLattice` onto itself. -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace GenericLie

variable (R : Type u) {K : Type u} [CommRing R] [Field K] [Algebra R K]
  {G : GroupScheme (Spec (CommRingCat.of K))} [IsAffineHom G.X.hom]

/-- The adjoint action of a rational point `g ∈ G(K)` on `Lie(G)`, through the coefficient point
`AffineWeil.sectionsCoeffEquiv K G g`, regarded as an `R`-linear map of the type synonym. -/
def adjoint (g : rationalPoints G) : GenericLie R G →ₗ[R] GenericLie R G :=
  (((equiv R G).symm.toLinearMap.comp
      (GroupScheme.adjoint G K (AffineWeil.sectionsCoeffEquiv K G g))).comp
    (equiv R G).toLinearMap).restrictScalars R

theorem adjoint_apply (g : rationalPoints G) (X : GenericLie R G) :
    adjoint R g X = (equiv R G).symm
      (GroupScheme.adjoint G K (AffineWeil.sectionsCoeffEquiv K G g) (equiv R G X)) := rfl

theorem adjoint_mul (g h : rationalPoints G) (X : GenericLie R G) :
    adjoint R (g * h) X = adjoint R g (adjoint R h X) := by
  simp only [adjoint_apply, map_mul, Module.End.mul_apply, LinearEquiv.apply_symm_apply]

theorem adjoint_one (X : GenericLie R G) : adjoint R 1 X = X := by
  simp only [adjoint_apply, map_one, Module.End.one_apply, LinearEquiv.symm_apply_apply]

end GenericLie

namespace IntegralModel

variable {R K : Type u} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  {G : GroupScheme (Spec (CommRingCat.of K))}

/-- The scheme-pullback comparison of coefficient points used by the Lie kernels is the inverse
of the pullback-adjunction comparison. -/
theorem affineBaseChangeEquiv_eq_symm (M : IntegralModel R K G)
    (q : Lie.AffinePoints M.genericFibre K) :
    Lie.affineBaseChangeEquiv R K M.group K q =
      (affinePointsBaseChangeMulEquiv R K K M.group).symm q := by
  apply Over.OverMorphism.ext
  rw [Lie.affineBaseChangeEquiv_left, affinePointsBaseChangeMulEquiv_symm_left]

/-- The coefficient point of the generic point of an integral section: coefficient change of its
`R`-coefficient point to `K`, then the pullback comparison and the generic isomorphism. -/
theorem sectionsCoeffEquiv_integralPointMap (M : IntegralModel R K G)
    (x : M.integralSections) :
    AffineWeil.sectionsCoeffEquiv K G (M.integralPointMap x) =
      (Lie.affineBaseChangeEquiv R K M.group K).symm
          (Lie.affineMap M.group (Algebra.ofId R K) (AffineWeil.sectionsCoeffEquiv R M.group x)) ≫
        M.genericIso.hom.hom.hom := by
  change AffineWeil.sectionsCoeffEquiv K G (rationalPoints.map M.genericIso.hom
    (baseChangeSectionHom (Spec.algebraMap R K) M.group x)) = _
  rw [AffineWeil.sectionsCoeffEquiv_target, AffineWeil.sectionsCoeffEquiv_baseChangeSectionHom]
  congr 1

variable [IsAffineHom G.X.hom] (M : IntegralModel R K G)

/-- The Lie map intertwines the adjoint action of an integral section `x ∈ 𝒢(R)` on `Lie(𝒢)`
with the adjoint action of its generic point `M.integralPointMap x ∈ G(K)` on `Lie(G)`. -/
theorem lieMap_adjoint (x : M.integralSections) (X : M.LieModule) :
    M.lieMap (GroupScheme.adjoint M.group (CommRingCat.of R)
        (AffineWeil.sectionsCoeffEquiv R M.group x) X) =
      GenericLie.adjoint R (M.integralPointMap x) (M.lieMap X) := by
  rw [lieMap_apply, lieMap_apply, adjoint_naturality, GenericLie.adjoint_apply,
    sectionsCoeffEquiv_integralPointMap]
  generalize lieKernelMapLinear M.group (Algebra.ofId R K) X = Y
  generalize Lie.affineMap M.group (Algebra.ofId R K)
    (AffineWeil.sectionsCoeffEquiv R M.group x) = h
  obtain ⟨Z, rfl⟩ := (Lie.kernelBaseChangeLinearEquiv R K M.group K).surjective Y
  obtain ⟨k, rfl⟩ := (Lie.affineBaseChangeEquiv R K M.group K).surjective h
  rw [← Lie.kernelBaseChangeLinearEquiv_adjoint, MulEquiv.symm_apply_apply]
  simp only [genericLieEquiv, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
    LinearEquiv.apply_symm_apply]
  congr 1
  exact lieKernelHomLinear_adjoint M.genericIso.hom k Z

/-- The adjoint action of an integral point maps the Lie lattice into itself. -/
theorem adjoint_mem_lieLattice {g : rationalPoints G} (hg : g ∈ M.integralPoints)
    {Y : GenericLie R G} (hY : Y ∈ M.lieLattice) :
    GenericLie.adjoint R g Y ∈ M.lieLattice := by
  obtain ⟨x, rfl⟩ := hg
  obtain ⟨X, rfl⟩ := hY
  exact ⟨_, M.lieMap_adjoint x X⟩

/-- The adjoint action of an integral point maps the Lie lattice onto itself. -/
theorem map_adjoint_lieLattice {g : rationalPoints G} (hg : g ∈ M.integralPoints) :
    M.lieLattice.map (GenericLie.adjoint R g) = M.lieLattice := by
  apply le_antisymm
  · rintro _ ⟨Y, hY, rfl⟩
    exact M.adjoint_mem_lieLattice hg hY
  · intro Y hY
    refine ⟨GenericLie.adjoint R g⁻¹ Y, M.adjoint_mem_lieLattice (inv_mem hg) hY, ?_⟩
    rw [← GenericLie.adjoint_mul, mul_inv_cancel, GenericLie.adjoint_one]

/-- The adjoint representation of the integral points `M.integralPoints ⊆ G(K)` on the Lie
lattice, by restriction of `GenericLie.adjoint`. -/
def lieLatticeAdjoint : M.integralPoints →* Module.End R M.lieLattice where
  toFun g := (GenericLie.adjoint R (g : rationalPoints G)).restrict
    (fun _ hY => M.adjoint_mem_lieLattice g.2 hY)
  map_one' := by
    apply LinearMap.ext
    intro Y
    apply Subtype.ext
    exact GenericLie.adjoint_one R (Y : GenericLie R G)
  map_mul' g h := by
    apply LinearMap.ext
    intro Y
    apply Subtype.ext
    exact GenericLie.adjoint_mul R (g : rationalPoints G) h Y

@[simp] theorem lieLatticeAdjoint_apply (g : M.integralPoints) (Y : M.lieLattice) :
    (M.lieLatticeAdjoint g Y : GenericLie R G) = GenericLie.adjoint R (g : rationalPoints G) Y :=
  rfl

/-- Under `M.lieLatticeEquiv : Lie(𝒢) ≃ M.lieLattice`, the adjoint action of an integral section
on `Lie(𝒢)` is the restricted adjoint action of its generic point. -/
theorem lieLatticeEquiv_adjoint (x : M.integralSections) (X : M.LieModule) :
    M.lieLatticeEquiv (GroupScheme.adjoint M.group (CommRingCat.of R)
        (AffineWeil.sectionsCoeffEquiv R M.group x) X) =
      M.lieLatticeAdjoint ⟨M.integralPointMap x, x, rfl⟩ (M.lieLatticeEquiv X) :=
  Subtype.ext (M.lieMap_adjoint x X)

end IntegralModel

end Langlands.GroupScheme
