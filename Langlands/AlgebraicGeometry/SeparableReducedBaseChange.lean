import Langlands.AlgebraicGeometry.SmoothReducedProof

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.SeparableReducedBaseChange

/-- A smooth algebra over a reduced Noetherian ring is reduced. -/
lemma isReduced_of_smooth_algebra (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] [IsNoetherianRing A] [_root_.IsReduced A] [Algebra.Smooth A B] :
    _root_.IsReduced B := by
  let f : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A) :=
    Spec.map (CommRingCat.ofHom (algebraMap A B))
  have : Smooth f := (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
    (RingHom.smooth_algebraMap.mpr inferInstance)
  have : GeometricallyReduced f := SmoothReducedProof.geometricallyReduced_of_smooth f
  have : AlgebraicGeometry.IsReduced (Spec (CommRingCat.of B)) :=
    GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian f
  exact (affine_isReduced_iff (CommRingCat.of B)).mp this

/-- Algebraic separable field extension preserves a reduced Noetherian algebra. -/
lemma isReduced_tensor (k A L : Type u) [Field k] [CommRing A] [Algebra k A]
    [IsNoetherianRing A] [_root_.IsReduced A] [Field L] [Algebra k L]
    [Algebra.IsAlgebraic k L] [Algebra.IsSeparable k L] :
    _root_.IsReduced (A ⊗[k] L) := by
  apply _root_.IsReduced.tensorProduct_of_flat_of_forall_fg
  intro B hB
  let : Field B := (B.isField_of_algebraic).toField
  have : Algebra.IsSeparable k B := Algebra.isSeparable_tower_bot_of_isSeparable k B L
  have : Algebra.FiniteType k B := B.fg_iff_finiteType.mp hB
  have : Algebra.FormallyEtale k B := Algebra.FormallyEtale.of_isSeparable k B
  have : Algebra.FinitePresentation k B := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  have : Algebra.Etale k B := {}
  exact isReduced_of_smooth_algebra A (A ⊗[k] B)

/-- Affine reduced schemes remain reduced under algebraic separable extension. -/
lemma isReduced_pullback_of_isAffine (k L : Type u) [Field k] [Field L]
    [Algebra k L] [Algebra.IsAlgebraic k L] [Algebra.IsSeparable k L]
    {X : Scheme.{u}} [IsAffine X] [AlgebraicGeometry.IsReduced X]
    [IsLocallyNoetherian X] (f : X ⟶ Spec (CommRingCat.of k)) :
    AlgebraicGeometry.IsReduced
      (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k L)))) := by
  let g : CommRingCat.of k ⟶ Γ(X, ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop
  let : Algebra k Γ(X, ⊤) := g.hom.toAlgebra
  have : IsNoetherianRing Γ(X, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top X⟩
  have : _root_.IsReduced (Γ(X, ⊤) ⊗[k] L) := isReduced_tensor k Γ(X, ⊤) L
  have h : X.isoSpec.inv ≫ f = Spec.map g := by
    rw [← Scheme.isoSpec_inv_naturality, Scheme.isoSpec_Spec_inv, ← Spec.map_comp]
  let e : X ≅ Spec Γ(X, ⊤) := X.isoSpec
  let i : Over.mk f ≅ Over.mk (Spec.map g) :=
    Over.isoMk e (by rw [← h]; simp)
  let j := ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L)))).mapIso i)
  have : AlgebraicGeometry.IsReduced (pullback (Spec.map g)
      (Spec.map (CommRingCat.ofHom (algebraMap k L)))) :=
    isReduced_of_isOpenImmersion (pullbackSpecIso k Γ(X, ⊤) L).hom
  let j' : pullback f (Spec.map (CommRingCat.ofHom (algebraMap k L))) ≅
      pullback (Spec.map g) (Spec.map (CommRingCat.ofHom (algebraMap k L))) :=
    (Over.forget _).mapIso j
  exact isReduced_of_isOpenImmersion j'.hom

/-- Reduced locally Noetherian schemes remain reduced under algebraic separable extension. -/
lemma isReduced_pullback (k L : Type u) [Field k] [Field L]
    [Algebra k L] [Algebra.IsAlgebraic k L] [Algebra.IsSeparable k L]
    {X : Scheme.{u}} [AlgebraicGeometry.IsReduced X] [IsLocallyNoetherian X]
    (f : X ⟶ Spec (CommRingCat.of k)) :
    AlgebraicGeometry.IsReduced
      (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k L)))) := by
  apply +allowSynthFailures @AlgebraicGeometry.IsReduced.of_openCover
    (𝒰 := X.affineCover.pullback₁ (pullback.fst f
      (Spec.map (CommRingCat.ofHom (algebraMap k L)))))
  intro (i : X.affineCover.I₀)
  change AlgebraicGeometry.IsReduced (pullback
    (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    (X.affineCover.f i))
  have : AlgebraicGeometry.IsReduced (X.affineCover.X i) :=
    isReduced_of_isOpenImmersion (X.affineCover.f i)
  have := isReduced_pullback_of_isAffine k L (X.affineCover.f i ≫ f)
  let e := pullbackSymmetry
    (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k L))))
    (X.affineCover.f i) ≪≫ pullbackRightPullbackFstIso f
      (Spec.map (CommRingCat.ofHom (algebraMap k L))) (X.affineCover.f i)
  exact isReduced_of_isOpenImmersion e.hom

end Langlands.AlgebraicGeometry.SeparableReducedBaseChange
