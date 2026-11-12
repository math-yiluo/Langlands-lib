import Langlands.AlgebraicGeometry.SmoothEtaleSourceDescentProof
import Langlands.AlgebraicGeometry.PointManifold.General.StandardSmoothNeighborhoods
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.LinearAlgebra.TensorProduct.Basis

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.AlgebraicGeometry

private theorem standardSmoothBasis (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] (n : ℕ) [Algebra.IsStandardSmoothOfRelativeDimension n R A] :
    Nonempty (Module.Basis (Fin n) A (KaehlerDifferential R A)) := by
  classical
  obtain ⟨ι, σ, hσ, hι, P, hP⟩ :=
    (inferInstance : Algebra.IsStandardSmoothOfRelativeDimension n R A).out
  let := hσ
  let := hι
  let := Fintype.ofFinite ι
  let := Fintype.ofFinite σ
  have hc : Fintype.card ((Set.range P.map)ᶜ : Set ι) = n := by
    rw [Fintype.card_compl_set, Set.card_range_of_injective P.map_inj]
    simpa only [Algebra.Presentation.dimension, Nat.card_eq_fintype_card] using hP
  exact ⟨P.basisKaehler.reindex (Fintype.equivFinOfCardEq hc)⟩

/-- An etale algebra map preserves the dimensions of two standard-smooth algebras. -/
theorem standardSmooth_dimension_eq_of_formallyEtale
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B] [Nontrivial B]
    [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [Algebra.FormallyEtale A B] (m n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension m R A]
    [Algebra.IsStandardSmoothOfRelativeDimension n R B] : m = n := by
  obtain ⟨bA⟩ := standardSmoothBasis R A m
  obtain ⟨bB⟩ := standardSmoothBasis R B n
  have h := mk_eq_mk_of_basis'
    ((bA.baseChange B).map (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R A B)) bB
  simpa using h

/-- A smooth affine algebra has a finite standard-smooth presentation dimension. -/
theorem exists_standardSmooth_dimension (R A : Type u) [CommRing R] [CommRing A]
    [Algebra R A] [Algebra.IsStandardSmooth R A] :
    ∃ n : ℕ, Algebra.IsStandardSmoothOfRelativeDimension n R A := by
  obtain ⟨ι, σ, hσ, hι, ⟨P⟩⟩ := (inferInstance : Algebra.IsStandardSmooth R A).out
  let := hσ
  let := hι
  exact ⟨P.dimension, P.isStandardSmoothOfRelativeDimension rfl⟩

/-- Standard-smooth affine neighborhoods over a field, with their actual coordinate algebras. -/
theorem smooth_field_affine_neighborhood (k : Type u) [Field k]
    (X : Over (Spec (CommRingCat.of k))) [Smooth X.hom] (x : X.left) :
    ∃ (V : X.left.Opens) (hV : IsAffineOpen V) (_ : x ∈ V) (n : ℕ),
      letI : IsAffine (openOver k X V).left := hV
      Algebra.IsStandardSmoothOfRelativeDimension n k
        (AffineCoordinateRing k (openOver k X V)) := by
  obtain ⟨U, hU, V, hV, hx, e, hs⟩ := Smooth.exists_isStandardSmooth X.hom x
  let := (X.hom.appLE U V e).hom.toAlgebra
  let : Algebra.IsStandardSmooth Γ(Spec (CommRingCat.of k), U) Γ(X.left, V) := hs
  obtain ⟨n, hn⟩ := exists_standardSmooth_dimension Γ(Spec (CommRingCat.of k), U) Γ(X.left, V)
  have hUtop : U = ⊤ := by
    apply top_unique
    intro y _
    exact (Subsingleton.elim (X.hom x) y) ▸ e hx
  have hn' : (X.hom.appLE ⊤ V (by simp)).hom.IsStandardSmoothOfRelativeDimension n := by
    exact (X.hom.appLE_congr e hUtop rfl
      (fun f => RingHom.IsStandardSmoothOfRelativeDimension n f.hom)).mp hn
  let : IsAffine (openOver k X V).left := hV
  refine ⟨V, hV, hx, n, ?_⟩
  apply PointManifold.General.standardSmooth_coordinateRing_of_appTop
  rw [PointManifold.General.openOver_appTop]
  exact (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := n)).left
    _ V.topIso.symm.commRingCatIsoToRingEquiv hn'

/-- Relative dimensions of actual standard-smooth affine schemes agree along an etale map. -/
theorem affine_standardSmooth_dimension_eq_of_etale
    (k : Type u) [Field k]
    {X Y : Over (Spec (CommRingCat.of k))} [IsAffine X.left] [IsAffine Y.left]
    [Nonempty X.left] (f : X ⟶ Y) [Etale f.left] (m n : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension m k (AffineCoordinateRing k Y)]
    [Algebra.IsStandardSmoothOfRelativeDimension n k (AffineCoordinateRing k X)] : m = n := by
  let A := AffineCoordinateRing k Y
  let B := AffineCoordinateRing k X
  let phi : A →ₐ[k] B := affineCoordinatePullback k f
  let : Algebra A B := phi.toRingHom.toAlgebra
  let : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq
    (fun r => (phi.commutes r).symm)
  have het : RingHom.Etale f.left.appTop.hom :=
    (HasRingHomProperty.iff_of_isAffine (P := @Etale) (f := f.left)).mp inferInstance
  let : Algebra.Etale A B := het
  let : Nonempty (⊤ : X.left.Opens) := ⟨⟨Classical.choice inferInstance, trivial⟩⟩
  let : Nontrivial B := Scheme.component_nontrivial X.left ⊤
  exact standardSmooth_dimension_eq_of_formallyEtale k A B m n

/-- A standard-smooth affine target has the dimension of a smooth pure-dimensional
etale source at every source point. -/
theorem standardSmooth_dimension_eq_of_etale_source
    (k : Type u) [Field k]
    {W V : Over (Spec (CommRingCat.of k))} [IsAffine V.left]
    (p : W ⟶ V) [Etale p.left] (n m : ℕ) [SmoothOfRelativeDimension n W.hom]
    [Algebra.IsStandardSmoothOfRelativeDimension m k (AffineCoordinateRing k V)]
    (w : W.left) : m = n := by
  obtain ⟨O, hO, hwO, -⟩ := exists_isAffineOpen_mem_and_subset
    (X := W.left) (x := w) (U := ⊤) (by trivial)
  let : IsAffine (openOver k W O).left := hO
  let : SmoothOfRelativeDimension n (openOver k W O).hom := by
    change SmoothOfRelativeDimension n (O.ι ≫ W.hom)
    simpa using (inferInstance : SmoothOfRelativeDimension (0 + n) (O.ι ≫ W.hom))
  obtain ⟨s, hws, hs⟩ := PointManifold.General.exists_standardSmooth_basicOpen k
    (openOver k W O) n ⟨w, hwO⟩
  let Q := (openOver k W O).left.basicOpen (U := ⊤) s
  let : IsAffine (openOver k (openOver k W O) Q).left := (isAffineOpen_top _).basicOpen s
  let : Nonempty (openOver k (openOver k W O) Q).left := ⟨⟨⟨w, hwO⟩, hws⟩⟩
  let : Algebra.IsStandardSmoothOfRelativeDimension n k
      (AffineCoordinateRing k (openOver k (openOver k W O) Q)) := hs
  let f := openOverι k (openOver k W O) Q ≫ openOverι k W O ≫ p
  let : Etale f.left := by
    change Etale (Q.ι ≫ (O.ι ≫ p.left))
    exact MorphismProperty.comp_mem (@Etale) Q.ι (O.ι ≫ p.left) inferInstance
      (MorphismProperty.comp_mem (@Etale) O.ι p.left inferInstance inferInstance)
  exact affine_standardSmooth_dimension_eq_of_etale k f m n

/-- Constant relative dimension over a field descends along a surjective etale source map. -/
theorem smooth_field_relativeDimension_etale_source_descent
    (k : Type u) [Field k] {W X : Over (Spec (CommRingCat.of k))}
    (p : W ⟶ X) [Etale p.left] [Surjective p.left] (n : ℕ)
    [SmoothOfRelativeDimension n W.hom] : SmoothOfRelativeDimension n X.hom := by
  let : Smooth W.hom := SmoothOfRelativeDimension.smooth n W.hom
  have : Smooth (p.left ≫ X.hom) := by rw [Over.w p]; infer_instance
  let : Smooth X.hom := smooth_of_smooth_of_surjective_of_smooth_comp p.left X.hom
  constructor
  intro x
  obtain ⟨U, hU, V, hV, hx, e, hs⟩ := Smooth.exists_isStandardSmooth X.hom x
  let := (X.hom.appLE U V e).hom.toAlgebra
  let : Algebra.IsStandardSmooth Γ(Spec (CommRingCat.of k), U) Γ(X.left, V) := hs
  obtain ⟨m, hm⟩ := exists_standardSmooth_dimension Γ(Spec (CommRingCat.of k), U) Γ(X.left, V)
  have hUtop : U = ⊤ := by
    apply top_unique
    intro y _
    exact (Subsingleton.elim (X.hom x) y) ▸ e hx
  have hm' : (X.hom.appLE ⊤ V (by simp)).hom.IsStandardSmoothOfRelativeDimension m := by
    exact (X.hom.appLE_congr e hUtop rfl
      (fun f => RingHom.IsStandardSmoothOfRelativeDimension m f.hom)).mp hm
  let : IsAffine (openOver k X V).left := hV
  have hVstandard : Algebra.IsStandardSmoothOfRelativeDimension m k
      (AffineCoordinateRing k (openOver k X V)) := by
    apply PointManifold.General.standardSmooth_coordinateRing_of_appTop
    rw [PointManifold.General.openOver_appTop]
    exact (RingHom.isStandardSmoothOfRelativeDimension_respectsIso (n := m)).left
      _ V.topIso.symm.commRingCatIsoToRingEquiv hm'
  obtain ⟨w, hw⟩ := p.left.surjective x
  let D := p.left ⁻¹ᵁ V
  let pV : openOver k W D ⟶ openOver k X V :=
    Over.homMk (p.left.resLE V D le_rfl) (by
      change p.left.resLE V D le_rfl ≫ (V.ι ≫ X.hom) = D.ι ≫ W.hom
      rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, Over.w p])
  let : Etale pV.left := inferInstanceAs (Etale (p.left.resLE V D le_rfl))
  let : SmoothOfRelativeDimension n (openOver k W D).hom := by
    change SmoothOfRelativeDimension n (D.ι ≫ W.hom)
    simpa using (inferInstance : SmoothOfRelativeDimension (0 + n) (D.ι ≫ W.hom))
  let := hVstandard
  have hmn : m = n := standardSmooth_dimension_eq_of_etale_source k pV n m
    ⟨w, show p.left w ∈ V from hw ▸ hx⟩
  exact ⟨U, hU, V, hV, hx, e, hmn ▸ hm⟩

end Langlands.AlgebraicGeometry
