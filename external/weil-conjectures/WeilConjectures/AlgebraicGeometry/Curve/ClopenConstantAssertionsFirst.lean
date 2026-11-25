/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.AlgebraicGeometry.FiniteCoproductCohomologyAssembly

@[expose] public section
universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.IsCurve

/-- The first four curve assertions transfer across a finite clopen partition.
Source: the finite disjoint-union argument in the proof of the clopen constant
assertions lemma. The cohomology and stalk comparison maps decompose componentwise,
and vanishing and finiteness are preserved by finite products.
(blueprint: lem-pbc-k2-clopen-constant-assertions-first)
-/
theorem clopen_first_four (Λ : Type (u + 1)) [CommRing Λ]
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsCurve f] (M : ModuleCat.{u + 1} Λ)
    {ι : Type u} [Finite ι] (U : ι → X.Opens)
    (hU : ∀ i, IsClosed (U i : Set X))
    (hdisj : Pairwise (fun i j ↦ Disjoint (U i : Set X) (U j)))
    (hcov : ∀ x : X, ∃ i, x ∈ U i)
    (H : ∀ i, Assertions Λ ((U i).ι ≫ f)
      ((constantSheaf (U i).toScheme.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)) :
    VanishingAboveTwo Λ ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) ∧
    VanishingAboveOneOfIsAffine Λ
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) ∧
    VanishingAboveOneOfIsPrimaryTorsionSheaf Λ
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) k ∧
    FiniteOfInvertibleOrder Λ
      ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) k := by
  let V := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  have : PreservesLimits V := inferInstance
  have : X.smallEtaleTopology.PreservesSheafification V :=
    GrothendieckTopology.instPreservesSheafification X.smallEtaleTopology V
  have (i : ι) : (U i).toScheme.smallEtaleTopology.PreservesSheafification V :=
    GrothendieckTopology.instPreservesSheafification (U i).toScheme.smallEtaleTopology V
  let F := (sheafCompose X.smallEtaleTopology V).obj
    ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M)
  let e (i : ι) :=
    (Etale.upperStar AddCommGrpCat.{u + 1} (U i).ι).mapIso
      ((constantCommuteCompose X.smallEtaleTopology V).app M) ≪≫
    (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} (U i).ι).app (V.obj M) ≪≫
    ((constantCommuteCompose (U i).toScheme.smallEtaleTopology V).app M).symm
  let FM := (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M
  let Fi (i : ι) :=
    (constantSheaf (U i).toScheme.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M
  let em (i : ι) := (Scheme.upperStarConstantSheafIso
    (ModuleCat.{u + 1} Λ) (U i).ι).app M
  let es (i : ι) (Ω : Type u) [Field Ω] [IsSepClosed Ω]
      (s : Spec (.of Ω) ⟶ (U i).toScheme) :=
    (((Scheme.pointSmallEtale s).sheafFiber.mapIso (em i)).symm ≪≫
      (Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) (U i).ι s).app FM).toLinearEquiv
  have hcover : ⨆ i, U i = ⊤ := by
    apply TopologicalSpace.Opens.ext
    apply Set.eq_univ_of_forall
    intro x
    simpa using hcov x
  obtain ⟨hc⟩ := nonempty_isColimit_cofanMk_of (fun i ↦ (U i).ι)
    (by simpa using hcover) (by simpa using hdisj)
  let r (q : ℕ) := fun x : Sheaf.H F q ↦ fun i ↦
    ((Sheaf.functorH (U i).toScheme.smallEtaleTopology q).mapIso (e i)).hom
      (Etale.cohomologyMap (U i).ι F q x)
  have hr (q : ℕ) : Function.Bijective (r q) :=
    (Function.Bijective.piMap (fun i ↦ ConcreteCategory.bijective_of_isIso
      ((Sheaf.functorH (U i).toScheme.smallEtaleTopology q).mapIso (e i)).hom)).comp
      (Etale.finiteCoproductCohomologyAssembly
        (fun i ↦ (U i).toScheme) X (fun i ↦ (U i).ι) hc F q)
  have transfer (q : ℕ)
      (h : ∀ i, Subsingleton (Sheaf.H ((sheafCompose _ V).obj (Fi i)) q)) :
      Subsingleton (Sheaf.H F q) := by
    refine ⟨fun x y ↦ (hr q).1 ?_⟩
    funext i
    exact (h i).elim _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro q hq
    exact transfer q (fun i ↦ (H i).subsingleton_of_two_lt q hq)
  · intro hX q hq
    apply transfer q
    intro i
    have : IsClosedImmersion (U i).ι :=
      .of_isOpenImmersion _ (by simpa using hU i)
    have : IsAffine (U i).toScheme := isAffine_of_isAffineHom (U i).ι
    exact (H i).subsingleton_of_one_lt_of_isAffine q hq
  · intro p hp hchar hF q hq
    apply transfer q
    intro i
    have hFi : Scheme.IsPrimaryTorsionSheaf Λ (Fi i) p := by
      intro Ω _ _ s x
      obtain ⟨n, hn⟩ := hF Ω (s ≫ (U i).ι) (es i Ω s x)
      exact ⟨n, (es i Ω s).injective (by simpa only [map_nsmul, map_zero] using hn)⟩
    exact (H i).subsingleton_of_one_lt_of_isPrimaryTorsionSheaf p hFi q hq
  · intro hC hT q
    have hFi (i : ι) : Finite (Sheaf.H ((sheafCompose _ V).obj (Fi i)) q) := by
      have : Scheme.IsConstructibleSheaf
          ((Etale.upperStar (ModuleCat.{u + 1} Λ) (U i).ι).obj FM) :=
        Scheme.IsConstructibleSheaf.upperStar (U i).ι FM
      have : Scheme.IsConstructibleSheaf (Fi i) :=
        Scheme.IsConstructibleSheaf.of_iso
          (F := (Etale.upperStar (ModuleCat.{u + 1} Λ) (U i).ι).obj FM) (em i)
      have : Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) (Fi i) := by
        constructor
        intro Ω _ _ s x
        obtain ⟨n, hn, hu, hx⟩ :=
          Scheme.IsTorsionSheafOfInvertibleOrder.exists_isUnit_nsmul_eq_zero
            (S := Spec (.of k)) Ω (s ≫ (U i).ι) (es i Ω s x)
        exact ⟨n, hn, hu, (es i Ω s).injective
          (by simpa only [map_nsmul, map_zero] using hx)⟩
      exact (H i).finite_of_isTorsionSheafOfInvertibleOrder q
    have (i : ι) : Finite (Sheaf.H ((sheafCompose _ V).obj (Fi i)) q) := hFi i
    exact Finite.of_injective
      (β := ∀ i, Sheaf.H ((sheafCompose _ V).obj (Fi i)) q) (r q) (hr q).1
end AlgebraicGeometry.IsCurve
