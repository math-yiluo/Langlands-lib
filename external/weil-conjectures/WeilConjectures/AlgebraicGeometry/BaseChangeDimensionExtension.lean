/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.Curve
public import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.Dimension
import WeilConjectures.AlgebraicGeometry.DimensionAffineOpenCover
import WeilConjectures.AlgebraicGeometry.DimensionBaseChange
import WeilConjectures.AlgebraicGeometry.BaseChangeConventions

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
private theorem topologicalKrullDim_eq_iSup_of_affine_openCover
    (X : Scheme.{u}) [Nonempty X] (U : X.OpenCover)
    [∀ i, IsAffine (U.X i)] :
    topologicalKrullDim X = ⨆ i, topologicalKrullDim (U.X i) := by
  rw [← Scheme.dim_eq_topologicalKrullDim X]
  rw [Scheme.dim_eq_iSup_ringKrullDim_of_affineOpenCover X
    (fun i ↦ (U.f i).opensRange) U.iSup_opensRange
    (fun i ↦ Γ(U.X i, ⊤))
    (fun i ↦ (U.f i).isoOpensRange.symm ≪≫ (U.X i).isoSpec)]
  apply iSup_congr
  intro i
  exact (((Scheme.homeoOfIso (U.X i).isoSpec).isHomeomorph.topologicalKrullDim_eq _).trans
    (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _)).symm

/-- Dimension is preserved by scalar extension along algebraically closed fields.

Source: blueprint `lem-sc-base-change-curve`, dimension paragraph; Stacks Tags 00P3
(finite type algebras under field extension) and 04MU (dimension on open covers).

Proof: Put `g = Spec(k') → Spec(k)` and let `p : C ×[Spec(k)] Spec(k') → C` be the
first projection. If `C` is empty then its pullback is empty, since `p` maps into `C`;
both topological Krull dimensions are bottom. Otherwise `g` is surjective: its target
has one point and its source is nonempty. Surjectivity survives base change, so `p`
is surjective and the pullback is nonempty.

Choose an affine open cover `U i ≅ Spec(A i)` of `C`. Since `f` is locally of finite
type, each `A i` is a finite type `k`-algebra. The inverse images `p⁻¹(U i)` form an
affine open cover of the pullback: restriction of a fibre product to an open is the
fibre product of the restriction, and the fibre product of affine spectra is
`Spec(A i ⊗[k] k')`. By the first clause of `dim_base_change` (00P3), the tensor
product and `A i` have equal ring Krull dimensions, including zero rings. Apply
`Scheme.dim_eq_iSup_ringKrullDim_of_affineOpenCover` to both nonempty schemes;
the equalities on every chart identify their suprema. Finally apply
`Scheme.dim_eq_topologicalKrullDim` on both schemes to get the asserted equality.
Thus the empty scheme and both zero- and one-dimensional curves are included.
(blueprint: base-change-dimension) -/
theorem baseChange_dim {k k' : Type u} {C : Scheme.{u}} [Field k] [Field k']
    [Algebra k k'] [IsAlgClosed k] [IsAlgClosed k']
    (f : C ⟶ Spec (.of k)) [IsCurve f] :
    topologicalKrullDim (pullback f
      (Spec.map (CommRingCat.ofHom (algebraMap k k'))) : Scheme.{u}) =
      topologicalKrullDim C := by
  classical
  let g := Spec.map (CommRingCat.ofHom (algebraMap k k'))
  let P := pullback f g
  cases isEmpty_or_nonempty C with
  | inl hC =>
    have : IsEmpty P := ⟨fun x ↦ hC.false ((pullback.fst f g) x)⟩
    change topologicalKrullDim P = topologicalKrullDim C
    rw [← Scheme.dim_eq_topologicalKrullDim P, ← Scheme.dim_eq_topologicalKrullDim C]
    simp [Scheme.dim]
  | inr hC =>
    have : Surjective g := inferInstance
    have : Nonempty P := (pullback.fst f g).surjective.nonempty
    let U := C.affineOpenCover
    let V := Scheme.Pullback.openCoverOfLeft U.openCover f g
    have : ∀ i, IsAffine (V.X i) := by
      intro i
      change IsAffine (pullback (U.f i ≫ f) g)
      infer_instance
    change topologicalKrullDim P = topologicalKrullDim C
    rw [topologicalKrullDim_eq_iSup_of_affine_openCover P V,
      topologicalKrullDim_eq_iSup_of_affine_openCover C U.openCover]
    apply iSup_congr
    intro i
    let A := U.X i
    let φ : CommRingCat.of k ⟶ A := Spec.preimage (U.f i ≫ f)
    let : Algebra k A := φ.hom.toAlgebra
    have hφ : Spec.map (CommRingCat.ofHom (algebraMap k A)) = U.f i ≫ f :=
      Spec.map_preimage _
    have : Algebra.FiniteType k A := by
      apply RingHom.finiteType_algebraMap.mp
      apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp
      rw [Spec.map_preimage]
      infer_instance
    let e : V.X i ≅ Spec (.of (TensorProduct k A k')) :=
      pullback.congrHom hφ.symm rfl ≪≫ pullbackSpecIso k A k'
    calc
      topologicalKrullDim (V.X i) = topologicalKrullDim (Spec (.of (TensorProduct k A k'))) :=
        (Scheme.homeoOfIso e).isHomeomorph.topologicalKrullDim_eq _
      _ = ringKrullDim (TensorProduct k A k') :=
        PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _
      _ = ringKrullDim A := dim_base_change.{u, u, u, u}.1 k k' A
      _ = topologicalKrullDim (U.openCover.X i) :=
        (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim A).symm

end AlgebraicGeometry
