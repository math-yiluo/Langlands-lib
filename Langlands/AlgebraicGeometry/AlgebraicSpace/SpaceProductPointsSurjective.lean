import Langlands.AlgebraicGeometry.AlgebraicSpace.ProductPointsGluing
import Langlands.AlgebraicGeometry.AlgebraicSpace.ProductPointsLocalLift
import Langlands.Global.AdelicSpaceLevelPointsStatement

/-!
# Points of separated finite type spaces with values in products of complete local rings

Let `X` be a separated algebraic space of finite type over `Spec C` and `O i` a family of complete
local `C`-algebras (for instance fields, or complete discrete valuation rings). Then the map
`X(∏ O i) → ∏ X(O i)` is bijective. Injectivity is the Library's
`separatedProductPoints_injective`. Surjectivity follows Conrad's proof of Proposition 5.2
(printed pp.13–14): lift every factor to a fixed affine étale chart after a finite free extension
of uniform rank, assemble the lifts on the affine chart, and descend along the product of the
extensions.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite Module
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology (RingPoint ringTest ringTestMap ringTestMap_comp
  ringTestMap_left affineSchemePointEquiv affineSchemePointEquiv_changeRing AlgPoint)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace SpaceProductPoints

section Atlas

variable {S : Scheme.{u}}

/-- The map of represented presheaves along a surjective morphism is surjective. -/
theorem isSurjective_map {U V : Over S} (j : U ⟶ V) (hj : Surjective j.left) :
    IsSurjective ((schemeYoneda S).map j) := by
  have : (MorphismProperty.inverseImage (@Surjective.{u}) (Over.forget S)).IsStableUnderBaseChange :=
    isStableUnderBaseChange_inverseImage_forget
  exact MorphismProperty.relative_map (P := MorphismProperty.inverseImage (@Surjective.{u})
    (Over.forget S)) hj

set_option backward.isDefEq.respectTransparency.types false in
/-- Surjective maps of presheaves are stable under composition. -/
theorem IsSurjective.comp {F G H : Presheaf S} {f : F ⟶ G} {g : G ⟶ H} (hf : IsSurjective f)
    (hg : IsSurjective g) : IsSurjective (f ≫ g) :=
  MorphismProperty.comp_mem (W := (MorphismProperty.inverseImage (@Surjective.{u})
    (Over.forget S)).relative (schemeYoneda S)) f g hf hg

/-- A separated algebraic space is quasi-separated. -/
theorem isQuasiSeparated_of_isSeparated {X : AlgebraicSpace S} (hX : IsSeparated X) :
    IsQuasiSeparated X := by
  refine MorphismProperty.relative_monotone ?_ _ hX
  intro A B f hf
  have : _root_.AlgebraicGeometry.IsClosedImmersion ((Over.forget S).map f) := hf
  exact (inferInstance : QuasiCompact ((Over.forget S).map f))

variable {C : Type u} [CommRing C] {X : AlgebraicSpace (Spec (CommRingCat.of C))}

/-- A space of finite type has an étale surjective chart from an affine scheme: a finite
disjoint union of affine opens of a quasi-compact atlas. -/
theorem exists_affine_atlas (hft : FiniteTypeOverRing C X) :
    ∃ (U : Over (Spec (CommRingCat.of C))) (a : (schemeYoneda _).obj U ⟶ X.presheaf),
      IsAffine U.left ∧ IsEtale a ∧ IsSurjective a := by
  obtain ⟨W, aW, ha, hs, hW⟩ := hft.exists_atlas
  have : QuasiCompact W.hom := hW.2
  have : CompactSpace W.left := QuasiCompact.compactSpace_of_compactSpace W.hom
  obtain ⟨t, ht⟩ : ∃ t : Finset W.left.affineOpens,
      ∀ x : W.left, ∃ V ∈ t, x ∈ (V : W.left.Opens) := by
    obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
      (fun V : W.left.affineOpens => ((V : W.left.Opens) : Set W.left))
      (fun V => V.1.isOpen) (fun x _ => by
        obtain ⟨V, hV, hx, -⟩ := exists_isAffineOpen_mem_and_subset
          (show x ∈ (⊤ : W.left.Opens) from trivial)
        exact Set.mem_iUnion.2 ⟨⟨V, hV⟩, hx⟩)
    refine ⟨t, fun x => ?_⟩
    have hx := ht (Set.mem_univ x)
    simp only [Set.mem_iUnion] at hx
    obtain ⟨V, hV, hx⟩ := hx
    exact ⟨V, hV, hx⟩
  let g : t → Scheme.{u} := fun V => (V.1 : W.left.Opens)
  have : ∀ V : t, IsAffine (g V) := fun V => V.1.2
  let J : ∐ g ⟶ W.left := Sigma.desc fun V => (V.1 : W.left.Opens).ι
  have : IsZariskiLocalAtSource @Etale.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale.{u})
  have hJ : Etale J := IsZariskiLocalAtSource.sigmaDesc fun _ => inferInstance
  have hJs : Surjective J := by
    refine ⟨fun x => ?_⟩
    obtain ⟨V, hVt, hxV⟩ := ht x
    have hr : x ∈ Set.range (V : W.left.Opens).ι := by
      rw [Scheme.Opens.range_ι]
      exact hxV
    obtain ⟨y, rfl⟩ := hr
    refine ⟨Sigma.ι g ⟨V, hVt⟩ y, ?_⟩
    rw [← Scheme.Hom.comp_apply, Sigma.ι_comp_desc]
  let U₀ : Over (Spec (CommRingCat.of C)) := Over.mk (J ≫ W.hom)
  let j : U₀ ⟶ W := Over.homMk J
  exact ⟨U₀, (schemeYoneda _).map j ≫ aW, inferInstanceAs (IsAffine (∐ g)),
    (isEtale_map j hJ).comp ha, IsSurjective.comp (isSurjective_map j hJs) hs⟩

end Atlas

section Main

variable {C : Type u} [CommRing C] {X : AlgebraicSpace (Spec (CommRingCat.of C))}

/-- Points of an affine scheme with values in a product ring are families of points. -/
theorem exists_pi_point {U : Over (Spec (CommRingCat.of C))} [IsAffine U.left] {ι : Type u}
    {B : ι → Type u} [∀ i, CommRing (B i)] [∀ i, Algebra C (B i)]
    (u : ∀ i, ringTest C (B i) ⟶ U) :
    ∃ u' : ringTest C (∀ i, B i) ⟶ U, ∀ i, ringTestMap C (Pi.evalAlgHom C B i) ≫ u' = u i := by
  let φ : AlgPoint C (PointTopology.AffineCoordinateRing C U) (∀ i, B i) :=
    AlgPoint.algHomEquiv.symm (AlgHom.pi fun i =>
      AlgPoint.algHomEquiv (affineSchemePointEquiv C U (B i) (u i)))
  refine ⟨(affineSchemePointEquiv C U _).symm φ, fun i => ?_⟩
  apply (affineSchemePointEquiv C U (B i)).injective
  change affineSchemePointEquiv C U (B i)
      (RingPoint.changeRing (Pi.evalAlgHom C B i) ((affineSchemePointEquiv C U _).symm φ)) = _
  rw [affineSchemePointEquiv_changeRing, Equiv.apply_symm_apply]
  rfl

/-- **Points of a separated space of finite type with values in a product of complete local
rings.** For a separated algebraic space `X` of finite type over `Spec C` and complete local
`C`-algebras `O i`, every family of points `x i ∈ X(O i)` comes from a point of `X(∏ O i)`. -/
theorem separatedProductPoints_surjective (hX : IsSeparated X) (hft : FiniteTypeOverRing C X)
    (ι : Type u) (O : ι → Type u) [∀ i, CommRing (O i)] [∀ i, IsLocalRing (O i)]
    [∀ i, IsAdicComplete (IsLocalRing.maximalIdeal (O i)) (O i)] [∀ i, Algebra C (O i)] :
    Function.Surjective (fun (p : RingPoints C X (∀ i, O i)) (i : ι) =>
      RingPoints.changeRing (Pi.evalAlgHom C O i) p) := by
  obtain ⟨U, a, hU, ha, hs⟩ := exists_affine_atlas hft
  obtain ⟨d, hd, hlift⟩ :=
    ProductPointsLocalLift.exists_local_lift a (isQuasiSeparated_of_isSeparated hX) ha hs
  have : NeZero d := ⟨hd.ne'⟩
  intro xs
  choose B instR instO instC instT b u hu using fun i => hlift (O i) (xs i)
  let _ : ∀ i, CommRing (B i) := instR
  let _ : ∀ i, Algebra (O i) (B i) := instO
  let _ : ∀ i, Algebra C (B i) := instC
  have _ : ∀ i, IsScalarTower C (O i) (B i) := instT
  obtain ⟨u', hu'⟩ := exists_pi_point (B := B) u
  let x' : RingPoints C X (∀ i, B i) := uliftYonedaEquiv.{u + 1} ((schemeYoneda _).map u' ≫ a)
  have hx'i : ∀ i, uliftYonedaEquiv.{u + 1}.symm
      (RingPoints.changeRing (Pi.evalAlgHom C B i) x') =
        (schemeYoneda _).map (ringTestMap C (IsScalarTower.toAlgHom C (O i) (B i))) ≫
          uliftYonedaEquiv.symm (xs i) := by
    intro i
    rw [ProductPointsLocalLift.uliftYonedaEquiv_symm_changeRing, Equiv.symm_apply_apply,
      ← Functor.map_comp_assoc, hu' i, hu i]
  have hdesc : ∀ i,
      RingPoints.changeRing ((Pi.evalAlgHom C _ i).comp (ProductPointsDescent.inlC C O B)) x' =
        RingPoints.changeRing ((Pi.evalAlgHom C _ i).comp (ProductPointsDescent.inrC C O B))
          x' := by
    intro i
    apply uliftYonedaEquiv.{u + 1}.symm.injective
    have hl : (Pi.evalAlgHom C _ i).comp (ProductPointsDescent.inlC C O B) =
        ((Algebra.TensorProduct.includeLeft (R := O i) (S := O i) (A := B i)
          (B := B i)).restrictScalars C).comp (Pi.evalAlgHom C B i) :=
      AlgHom.ext fun _ => rfl
    have hr : (Pi.evalAlgHom C _ i).comp (ProductPointsDescent.inrC C O B) =
        ((Algebra.TensorProduct.includeRight (R := O i) (A := B i)
          (B := B i)).restrictScalars C).comp (Pi.evalAlgHom C B i) :=
      AlgHom.ext fun _ => rfl
    rw [hl, hr, ← ProductPointsDescent.changeRing_changeRing,
      ← ProductPointsDescent.changeRing_changeRing,
      ProductPointsLocalLift.uliftYonedaEquiv_symm_changeRing _
        (RingPoints.changeRing (Pi.evalAlgHom C B i) x'),
      ProductPointsLocalLift.uliftYonedaEquiv_symm_changeRing _
        (RingPoints.changeRing (Pi.evalAlgHom C B i) x'), hx'i, ← Functor.map_comp_assoc,
      ← Functor.map_comp_assoc, ← ringTestMap_comp, ← ringTestMap_comp]
    congr 3
    ext r
    change algebraMap (O i) (B i) r ⊗ₜ[O i] (1 : B i) = (1 : B i) ⊗ₜ[O i] algebraMap (O i) (B i) r
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  obtain ⟨x, hx⟩ := ProductPointsDescent.exists_changeRing_eq C hX b x' hdesc
  refine ⟨x, funext fun i => ?_⟩
  obtain ⟨h₁, h₂, h₃⟩ := ProductPointsDescent.spec_properties (b i)
  have : Flat (ringTestMap C (IsScalarTower.toAlgHom C (O i) (B i))).left := h₁
  have : LocallyOfFinitePresentation
      (ringTestMap C (IsScalarTower.toAlgHom C (O i) (B i))).left := h₂
  have : Surjective (ringTestMap C (IsScalarTower.toAlgHom C (O i) (B i))).left := h₃
  apply ProductPointsDescent.pullback_injective X
    (ringTestMap C (IsScalarTower.toAlgHom C (O i) (B i)))
  change RingPoints.changeRing (IsScalarTower.toAlgHom C (O i) (B i))
      (RingPoints.changeRing (Pi.evalAlgHom C O i) x) =
    RingPoints.changeRing (IsScalarTower.toAlgHom C (O i) (B i)) (xs i)
  have he : (IsScalarTower.toAlgHom C (O i) (B i)).comp (Pi.evalAlgHom C O i) =
      (Pi.evalAlgHom C B i).comp (ProductPointsDescent.πC C O B) :=
    AlgHom.ext fun _ => rfl
  rw [ProductPointsDescent.changeRing_changeRing, he,
    ← ProductPointsDescent.changeRing_changeRing, hx]
  apply uliftYonedaEquiv.{u + 1}.symm.injective
  rw [hx'i, ProductPointsLocalLift.uliftYonedaEquiv_symm_changeRing]

/-- **Bijectivity.** -/
theorem separatedProductPoints_bijective (hX : IsSeparated X) (hft : FiniteTypeOverRing C X)
    (ι : Type u) (O : ι → Type u) [∀ i, CommRing (O i)] [∀ i, IsLocalRing (O i)]
    [∀ i, IsAdicComplete (IsLocalRing.maximalIdeal (O i)) (O i)] [∀ i, Algebra C (O i)] :
    Function.Bijective (fun (p : RingPoints C X (∀ i, O i)) (i : ι) =>
      RingPoints.changeRing (Pi.evalAlgHom C O i) p) :=
  ⟨separatedProductPoints_injective C X hX ι O, separatedProductPoints_surjective hX hft ι O⟩

end Main

end SpaceProductPoints

end Langlands.AlgebraicGeometry.AlgebraicSpace
