import Langlands.GroupScheme.MatrixRepresentation.NormalFixedCoordinates
import Langlands.GroupScheme.HomDescent
import Langlands.GroupScheme.CentralIsogeny.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Unipotence of extensions of affine group schemes -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped Matrix CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace MatrixRepresentation

variable {k : Type u} [Field k]
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- A finite-dimensional subspace has split finite coordinate matrices. -/
theorem exists_fixed_coordinates (W : Submodule k (n → k)) :
    ∃ (B : Matrix n (Fin (Module.finrank k W)) k)
      (C : Matrix (Fin (Module.finrank k W)) n k),
      C * B = 1 ∧ (∀ s, (fun r => B r s) ∈ W) ∧
        ∀ v ∈ W, (B * C) *ᵥ v = v := by
  let b := Module.finBasis k W
  let f : (Fin (Module.finrank k W) → k) →ₗ[k] (n → k) :=
    W.subtype.comp b.equivFun.symm.toLinearMap
  have hf : LinearMap.ker f = ⊥ := LinearMap.ker_eq_bot.mpr
    (W.subtype_injective.comp b.equivFun.symm.injective)
  let p := f.leftInverse
  have hpf : p.comp f = LinearMap.id := LinearMap.leftInverse_comp_of_inj hf
  refine ⟨f.toMatrix', p.toMatrix', ?_, ?_, ?_⟩
  · rw [← LinearMap.toMatrix'_comp, hpf, LinearMap.toMatrix'_id]
  · intro s
    change f (Pi.single s 1) ∈ W
    exact (b.equivFun.symm (Pi.single s 1)).property
  · intro v hv
    let w : W := ⟨v, hv⟩
    have hw : f (b.equivFun w) = v := by simp [f, w]
    rw [← hw, ← Matrix.mulVec_mulVec, LinearMap.toMatrix'_mulVec,
      LinearMap.toMatrix'_mulVec]
    exact congrArg f (LinearMap.congr_fun hpf (b.equivFun w))

variable {G H : GroupScheme (Spec (CommRingCat.of k))}

/-- Coordinates whose columns are fixed by a subgroup give a trivial restriction
to that subgroup. -/
theorem restrictCoordinates_restrict_eq_trivial (ρ : MatrixRepresentation G n)
    (i : H ⟶ G) (B : Matrix n m k) (C : Matrix m n k)
    (hCB : C * B = 1) (hs : ρ.IsStableCoordinates B C)
    (hcols : ∀ s, (ρ.restrict i).IsFixedVector (fun r => B r s)) :
    (ρ.restrictCoordinates B C hCB hs).restrict i = trivial H m := by
  apply hom_ext_points
  intro T x
  apply (GeneralLinear.pointsEquiv m (CommRingCat.of k) T).injective
  change ((ρ.restrictCoordinates B C hCB hs).restrict i).pointMatrix T x =
    (trivial H m).pointMatrix T x
  rw [pointMatrix_restrict, restrictCoordinates_pointMatrix, trivial_pointMatrix]
  apply Units.ext
  change C.map (scalarMap T) *
    (ρ.pointMatrix T (x ≫ i.hom.hom) : Matrix n n Γ(T.left, ⊤)) *
      B.map (scalarMap T) = 1
  have hb : (ρ.pointMatrix T (x ≫ i.hom.hom) : Matrix n n Γ(T.left, ⊤)) *
      B.map (scalarMap T) = B.map (scalarMap T) := by
    ext r s
    exact congrFun (hcols s T x) r
  rw [Matrix.mul_assoc, hb, ← Matrix.map_mul, hCB,
    Matrix.map_one _ (map_zero _) (map_one _)]

variable {Q : GroupScheme (Spec (CommRingCat.of k))}

/-- The actual quotient representation on invariant coordinates fixed by the
full scheme-theoretic kernel. -/
def quotientFixedCoordinates (ρ : MatrixRepresentation G n) (q : G ⟶ Q)
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [QuasiCompact q.hom.hom.left]
    (B : Matrix n m k) (C : Matrix m n k)
    (hCB : C * B = 1) (hs : ρ.IsStableCoordinates B C)
    (hcols : ∀ s, (ρ.restrict (kernelι q)).IsFixedVector (fun r => B r s)) :
    MatrixRepresentation Q m :=
  FpqcHomDescent.hom q (ρ.restrictCoordinates B C hCB hs) (by
    change (ρ.restrictCoordinates B C hCB hs).restrict (kernelι q) =
      trivial (kernel q) m
    exact ρ.restrictCoordinates_restrict_eq_trivial (kernelι q) B C hCB hs hcols)

/-- Pullback of the quotient representation is the chosen fixed-coordinate
representation of the source. -/
@[reassoc]
theorem quotientFixedCoordinates_fac (ρ : MatrixRepresentation G n) (q : G ⟶ Q)
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [QuasiCompact q.hom.hom.left]
    (B : Matrix n m k) (C : Matrix m n k)
    (hCB : C * B = 1) (hs : ρ.IsStableCoordinates B C)
    (hcols : ∀ s, (ρ.restrict (kernelι q)).IsFixedVector (fun r => B r s)) :
    q ≫ ρ.quotientFixedCoordinates q B C hCB hs hcols =
      ρ.restrictCoordinates B C hCB hs :=
  FpqcHomDescent.fac _ _ _

end MatrixRepresentation

variable {k : Type u} [Field k]
  {G Q : GroupScheme (Spec (CommRingCat.of k))}

/-- An affine group scheme with unipotent affine kernel and unipotent fpqc
quotient is unipotent over the original field. -/
theorem isUnipotent_of_kernel_of_quotient (q : G ⟶ Q)
    [IsAffineHom G.X.hom] [IsAffineHom (kernel q).X.hom]
    [Flat q.hom.hom.left] [Surjective q.hom.hom.left]
    [QuasiCompact q.hom.hom.left]
    (hK : IsUnipotent (kernel q)) (hQ : IsUnipotent Q) : IsUnipotent G := by
  intro n _ _ _ ρ
  classical
  obtain ⟨v, hv, hfix⟩ := hK n (ρ.restrict (kernelι q))
  let W := (ρ.restrict (kernelι q)).fixedSubmodule
  let w : W := ⟨v, hfix⟩
  have hw : w ≠ 0 := fun h => hv (congrArg Subtype.val h)
  have hd : 0 < Module.finrank k W :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨w, hw⟩
  let : Nonempty (Fin (Module.finrank k W)) := ⟨⟨0, hd⟩⟩
  obtain ⟨B, C, hCB, hcols, hproj⟩ := MatrixRepresentation.exists_fixed_coordinates W
  have hN : (SubgroupFunctor.range (kernelι q)).IsNormal := by
    intro T g x _ hx
    apply (mem_range_kernelι_iff q _).mpr
    rw [MonObj.mul_comp, MonObj.mul_comp, GrpObj.inv_comp,
      (mem_range_kernelι_iff q x).mp hx]
    simp
  have hGa : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hKa : IsAffine (kernel q).X.left := isAffine_of_isAffineHom (kernel q).X.hom
  obtain ⟨A, ⟨jG⟩⟩ := (essImage_algSpec (G := G.X)).mpr hGa
  obtain ⟨D, ⟨jK⟩⟩ := (essImage_algSpec (G := (kernel q).X)).mpr hKa
  have hs : ρ.IsStableCoordinates B C :=
    ρ.isStableCoordinates_of_affine_model jG B C
      (ρ.normal_fixed_coordinates_affine (kernelι q) hN jK B C hcols hproj
        A.unop jG.hom)
  let r := ρ.restrictCoordinates B C hCB hs
  let d := ρ.quotientFixedCoordinates q B C hCB hs hcols
  obtain ⟨z, hz, hdz⟩ := hQ (Fin (Module.finrank k W)) d
  have hrz : r.IsFixedVector z := by
    have h := (MatrixRepresentation.isFixedVector_restrict_iff d q z).2 hdz
    change MatrixRepresentation.IsFixedVector (q ≫ d) z at h
    have hfac : q ≫ d = r := ρ.quotientFixedCoordinates_fac q B C hCB hs hcols
    rwa [hfac] at h
  refine ⟨B *ᵥ z, ?_, ρ.isFixedVector_mulVec_restrictCoordinates B C hCB hs hrz⟩
  intro hbz
  apply hz
  exact MatrixRepresentation.coordinateInclusion_injective B C hCB
    (hbz.trans (Matrix.mulVec_zero B).symm)

end Langlands.GroupScheme
