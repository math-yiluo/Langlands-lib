import Langlands.AlgebraicGeometry.ModuleLocalHomPullbackProofs
import Langlands.Shimura.PEL.HodgeDeterminantBaseChange

/-! # Actual section pullback and determinant transport -/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u v w t s

namespace Langlands.Shimura.HodgeDeterminant

variable {R : Type u} [CommRing R] {S : Type v} [CommRing S]
    {M : Type w} [AddCommGroup M] [Module R M]
    {N : Type t} [AddCommGroup N] [Module S N]
    {I : Type s} [Fintype I] [DecidableEq I]

/-- Coordinates commute with a semilinear map that carries one basis to another. -/
theorem repr_semilinear_basis (g : R →+* S) (F : M →ₛₗ[g] N)
    (b : Module.Basis I R M) (c : Module.Basis I S N)
    (h : ∀ i, F (b i) = c i) (x : M) (j : I) :
    c.repr (F x) j = g (b.repr x j) := by
  rw [← b.sum_repr x, map_sum]
  simp only [F.map_smulₛₗ, h, map_sum, map_smul]
  simp [Finset.sum_apply, Finsupp.single_apply]

/-- Intertwining endomorphisms have coefficient-mapped matrices in compatible bases. -/
theorem toMatrix_semilinear_basis (g : R →+* S) (F : M →ₛₗ[g] N)
    (b : Module.Basis I R M) (c : Module.Basis I S N)
    (h : ∀ i, F (b i) = c i) (a : Module.End R M) (a' : Module.End S N)
    (ha : ∀ x, F (a x) = a' (F x)) :
    (LinearMap.toMatrix b b a).map g = LinearMap.toMatrix c c a' := by
  ext i j
  simp only [Matrix.map_apply, LinearMap.toMatrix_apply]
  rw [← h j, ← ha, repr_semilinear_basis g F b c h]

/-- Determinant-polynomial transport along an actual compatible semilinear map. -/
theorem polynomial_semilinear_basis {ι : Type*} [Fintype ι]
    (g : R →+* S) (F : M →ₛₗ[g] N)
    (b : Module.Basis I R M) (c : Module.Basis I S N)
    (h : ∀ i, F (b i) = c i)
    (a : ι → Module.End R M) (a' : ι → Module.End S N)
    (ha : ∀ i x, F (a i x) = a' i (F x)) :
    MvPolynomial.map g (polynomial b a) = polynomial c a' := by
  unfold polynomial
  rw [RingHom.map_det]
  congr 1
  apply Matrix.ext
  intro i j
  change MvPolynomial.map g (matrix b a i j) = matrix c a' i j
  simp only [matrix, map_sum, map_mul,
    MvPolynomial.map_C, MvPolynomial.map_X]
  apply Finset.sum_congr rfl
  intro k hk
  have hm := congrArg (fun p => p i j)
    (toMatrix_semilinear_basis g F b c h (a k) (a' k) (ha k))
  exact congrArg (fun r => MvPolynomial.C r * MvPolynomial.X k) hm

end Langlands.Shimura.HodgeDeterminant

namespace Langlands.Scheme.Modules

variable {X Y Z : AlgebraicGeometry.Scheme.{u}}

/-- Pull a section to the inverse-image open using the actual adjunction unit. -/
def sectionPullback (f : X ⟶ Y) (M : Y.Modules) (U : Y.Opens) :
    Γ(M, U) →ₛₗ[(f.app U).hom] Γ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M, f ⁻¹ᵁ U) where
  toFun x := ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app U x
  map_add' x y := map_add _ x y
  map_smul' r x :=
    (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val.app
      (op U)).hom.map_smul r x

/-- The semilinear section map commutes with restriction of the actual open. -/
theorem sectionPullback_restrict (f : X ⟶ Y) (M : Y.Modules)
    {V U : Y.Opens} (j : V ⟶ U) (x : Γ(M, U)) :
    sectionPullback f M V (M.presheaf.map j.op x) =
      ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M).presheaf.map
        ((TopologicalSpace.Opens.map f.base).map j).op (sectionPullback f M U x) :=
  PresheafOfModules.naturality_apply
    ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).val j.op x

/-- Pullback of sections intertwines every actual module-sheaf morphism. -/
theorem sectionPullback_naturality (f : X ⟶ Y) {M N : Y.Modules}
    (g : M ⟶ N) (U : Y.Opens) (x : Γ(M, U)) :
    sectionPullback f N U (g.app U x) =
      ((AlgebraicGeometry.Scheme.Modules.pullback f).map g).app (f ⁻¹ᵁ U)
        (sectionPullback f M U x) := by
  exact congrArg (fun k => k.app U x)
    ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).unit.naturality g)

/-- The identity comparison identifies actual identity pullback with the original section. -/
theorem sectionPullback_id (M : X.Modules) (U : X.Opens) (x : Γ(M, U)) :
    ((AlgebraicGeometry.Scheme.Modules.pullbackId X).hom.app M).app U
      (sectionPullback (𝟙 X) M U x) = x := by
  have h := unit_conjugateEquiv Adjunction.id
    (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X))
    (AlgebraicGeometry.Scheme.Modules.pullbackId X).hom M
  rw [AlgebraicGeometry.Scheme.Modules.conjugateEquiv_pullbackId_hom] at h
  exact (congrArg (fun k => k.app U x) h).symm

/-- The canonical composition comparison identifies successive section pullbacks. -/
theorem sectionPullback_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Z.Modules) (U : Z.Opens) (x : Γ(M, U)) :
    ((AlgebraicGeometry.Scheme.Modules.pullbackComp f g).hom.app M).app ((f ≫ g) ⁻¹ᵁ U)
      (sectionPullback f ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M) (g ⁻¹ᵁ U)
        (sectionPullback g M U x)) = sectionPullback (f ≫ g) M U x := by
  exact congrArg (fun k => k.app U x)
    (pullbackPushforwardAdjunction_unit_comp f g M)

/-- Evaluate a sheaf endomorphism as an actual linear endomorphism on any open. -/
def sectionEndomorphism (M : Y.Modules) (U : Y.Opens) :
    End M →+* Module.End Γ(Y, U) Γ(M, U) where
  toFun a := (a.val.app (op U)).hom
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

/-- Actual section actions have coefficient-mapped matrices in pulled-back bases. -/
theorem sectionPullback_toMatrix (f : X ⟶ Y) (M : Y.Modules) (U : Y.Opens)
    {I : Type v} [Fintype I] [DecidableEq I]
    (b : Module.Basis I Γ(Y, U) Γ(M, U))
    (c : Module.Basis I Γ(X, f ⁻¹ᵁ U)
      Γ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M, f ⁻¹ᵁ U))
    (h : ∀ i, sectionPullback f M U (b i) = c i) (a : End M) :
    (LinearMap.toMatrix b b (sectionEndomorphism M U a)).map (f.app U).hom =
      LinearMap.toMatrix c c
        (sectionEndomorphism _ (f ⁻¹ᵁ U)
          ((AlgebraicGeometry.Scheme.Modules.pullback f).map a)) :=
  Langlands.Shimura.HodgeDeterminant.toMatrix_semilinear_basis _ _ b c h _ _
    (sectionPullback_naturality f a U)

/-- Pulling a compatible finite section basis transports its determinant polynomial. -/
theorem sectionPullback_determinant (f : X ⟶ Y) (M : Y.Modules) (U : Y.Opens)
    {I : Type v} [Fintype I] [DecidableEq I] {ι : Type*} [Fintype ι]
    (b : Module.Basis I Γ(Y, U) Γ(M, U))
    (c : Module.Basis I Γ(X, f ⁻¹ᵁ U)
      Γ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M, f ⁻¹ᵁ U))
    (h : ∀ i, sectionPullback f M U (b i) = c i) (a : ι → End M) :
    MvPolynomial.map (f.app U).hom
        (Langlands.Shimura.HodgeDeterminant.polynomial b (fun i => sectionEndomorphism M U (a i))) =
      Langlands.Shimura.HodgeDeterminant.polynomial c
        (fun i => sectionEndomorphism _ (f ⁻¹ᵁ U)
          ((AlgebraicGeometry.Scheme.Modules.pullback f).map (a i))) :=
  Langlands.Shimura.HodgeDeterminant.polynomial_semilinear_basis _ _ b c h _ _
    (fun i => sectionPullback_naturality f (a i) U)

end Langlands.Scheme.Modules
