import Langlands.GroupScheme.Absolute.SemisimplePointMaximalTorusStatement
import Langlands.GroupScheme.Absolute.BorelMaximalTorusProof
import Langlands.GroupScheme.Absolute.BorelPointContainmentProof
import Langlands.GroupScheme.Absolute.SolvableSplitExtensionProof
import Langlands.GroupScheme.Absolute.SolvableTorusQuotientProof
import Langlands.GroupScheme.Absolute.TriangularTorusConjugacy
import Langlands.GroupScheme.AffineLinearEmbeddingProof
import Langlands.GroupScheme.MatrixRepresentation.CharacterSpanEmbedding
import Langlands.GroupScheme.MatrixRepresentation.RationalDualConjugateIrreducibility
import Langlands.GroupScheme.SubgroupIntersection
import Langlands.GroupScheme.Torus.MultiplicativeTypeSubgroups
import Langlands.GroupScheme.Trigonalizable.SectionConjugacySmoothProof
import Mathlib.LinearAlgebra.Eigenspace.Semisimple

/-! # Semisimple points lie in maximal tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Matrix
open scoped Matrix

namespace Langlands.GroupScheme

private theorem exists_eigenbasis {k : Type u} [Field k] [IsAlgClosed k] {n : ℕ}
    {f : Module.End k (Fin n → k)} (hf : f.IsSemisimple) :
    ∃ (b : Module.Basis (Fin n) k (Fin n → k)) (μ : Fin n → k),
      ∀ j, f (b j) = μ j • b j := by
  classical
  let S : Set (Fin n → k) := ⋃ a : k, (f.eigenspace a : Set (Fin n → k))
  have hS : Submodule.span k S = ⊤ := by
    simpa only [S, Submodule.span_iUnion, Submodule.span_eq] using hf.iSup_eigenspace_eq_top
  let b₀ := Module.Basis.ofSpan hS.ge
  let e := b₀.indexEquiv (Pi.basisFun k (Fin n))
  let b := b₀.reindex e
  have hb (j : Fin n) : ∃ a : k, b j ∈ f.eigenspace a := by
    apply Set.mem_iUnion.mp
    exact Module.Basis.ofSpan_subset hS.ge ⟨e.symm j, (b₀.reindex_apply e j).symm⟩
  choose μ hμ using hb
  exact ⟨b, μ, fun j => Module.End.mem_eigenspace_iff.mp (hμ j)⟩

private theorem exists_diagonal_basis_change {k : Type u} [Field k] [IsAlgClosed k]
    {H : GroupScheme (Spec (CommRingCat.of k))} {n : ℕ} (ρ : MatrixRepresentation H (Fin n))
    (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X)
    (hx : Module.End.IsSemisimple (Matrix.toLin' (ρ.rationalMatrix x : Matrix (Fin n) (Fin n) k))) :
    ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶
        (GeneralLinear.groupScheme (Fin n) (CommRingCat.of k)).X,
      GeneralLinear.IsDiagonalGL ((ρ.conjugate g).rationalMatrix x) := by
  obtain ⟨b, μ, hb⟩ := exists_eigenbasis hx
  let c := MatrixRepresentation.basisCoordinateGL b
  let A : Matrix (Fin n) (Fin n) k := ρ.rationalMatrix x
  let D : Matrix (Fin n) (Fin n) k := Matrix.diagonal μ
  have hcols : A * (↑c⁻¹ : Matrix (Fin n) (Fin n) k) =
      (↑c⁻¹ : Matrix (Fin n) (Fin n) k) * D := by
    ext i j
    change (A * (↑c⁻¹ : Matrix (Fin n) (Fin n) k)) i j =
      ((↑c⁻¹ : Matrix (Fin n) (Fin n) k) * Matrix.diagonal μ) i j
    rw [Matrix.mul_diagonal]
    change (A *ᵥ b j) i = b j i * μ j
    simpa only [Matrix.toLin'_apply, Pi.smul_apply, smul_eq_mul, mul_comm (μ j) (b j i)]
      using congrFun (hb j) i
  refine ⟨MatrixRepresentation.basisCoordinatePoint b, fun i j hij => ?_⟩
  have hdiag :
      ((ρ.conjugate (MatrixRepresentation.basisCoordinatePoint b)).rationalMatrix x :
        Matrix (Fin n) (Fin n) k) = D := by
    rw [MatrixRepresentation.conjugate_rationalMatrix,
      MatrixRepresentation.rationalMatrix_basisCoordinatePoint]
    change (↑c : Matrix (Fin n) (Fin n) k) * A * (↑c⁻¹ : Matrix (Fin n) (Fin n) k) = D
    rw [Matrix.mul_assoc, hcols, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel,
      Units.val_one, Matrix.one_mul]
  rw [hdiag]
  exact Matrix.diagonal_apply_ne _ hij

/-- A semisimple matrix point lifts to the inverse image of a diagonal torus after
changing the basis of a closed matrix embedding. -/
private theorem exists_diagonalizable_subgroup_of_matrix {k : Type u} [Field k] [IsAlgClosed k]
    {H : GroupScheme (Spec (CommRingCat.of k))} {n : ℕ} (ρ : MatrixRepresentation H (Fin n))
    (hρ : IsClosedSubgroup ρ) (x : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ H.X)
    (hx : Module.End.IsSemisimple (Matrix.toLin' (ρ.rationalMatrix x : Matrix (Fin n) (Fin n) k))) :
    ∃ (L : GroupScheme (Spec (CommRingCat.of k))) (ℓ : L ⟶ H)
      (y : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ L.X),
      y ≫ ℓ.hom.hom = x ∧
        ∃ (Λ : Type u) (_ : AddCommGroup Λ) (_ : AddGroup.FG Λ),
          Nonempty (L ≅ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp) := by
  obtain ⟨g, hg⟩ := exists_diagonal_basis_change ρ x hx
  let R := CommRingCat.of k
  let ρ' := ρ.conjugate g
  have hρ' : IsClosedSubgroup ρ' := hρ.comp_iso ((GeneralLinear.groupScheme (Fin n) R).innerIso g)
  let d := GeneralLinear.diagonalTorus (Fin n) R
  let z := x ≫ ρ'.hom.hom
  have hz : GeneralLinear.IsDiagonalGL (GeneralLinear.pointsEquiv (Fin n) R _ z) := by
    intro i j hij
    have hentry := hg i j hij
    rw [MatrixRepresentation.rationalMatrix_apply, Matrix.GeneralLinearGroup.map_apply] at hentry
    exact (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.injective
      (hentry.trans (map_zero _).symm)
  let t := GeneralLinear.diagonalLocusLift z hz ≫ GeneralLinear.locusToDiagonalTorus (Fin n) R
  have ht : t ≫ d.hom.hom = z := by
    simp only [t, d, Category.assoc, GeneralLinear.locusToDiagonalTorus_comp]
    exact GeneralLinear.diagonalLocusLift_comp z hz
  let pb := subgroupIntersection_isPullback d ρ'
  exact ⟨subgroupIntersection d ρ', subgroupIntersectionSnd d ρ', pb.lift t x ht,
    pb.lift_snd t x ht,
    exists_diagonalizableIso_of_isClosedSubgroup_splitTorus
      (isSplitTorus_splitTorus (ULift.{u} (Fin n))) (subgroupIntersectionFst d ρ')
      (isClosedSubgroup_subgroupIntersectionFst d hρ')⟩

/-- Every semisimple rational point of a smooth connected affine group over an
algebraically closed field lies in a maximal torus (Milne 2017, Corollary 17.36). -/
theorem semisimplePointMaximalTorus : SemisimplePointMaximalTorusStatement.{u} := by
  intro k _ _ G _ _ _ x hx
  obtain ⟨B, i, b, hi, hb⟩ := borelPointContainment k G x
  obtain ⟨n, ρ, hρ⟩ := affineLinearEmbeddingStatement k G inferInstance inferInstance
  have hsem : Module.End.IsSemisimple (Matrix.toLin' ((ρ.restrict i).rationalMatrix b :
      Matrix (Fin n) (Fin n) k)) := by
    rw [MatrixRepresentation.rationalMatrix_restrict, hb]
    exact hx n ρ
  obtain ⟨L, ℓ, y, hy, hL⟩ :=
    exists_diagonalizable_subgroup_of_matrix (ρ.restrict i) (hi.isClosedSubgroup.comp hρ) b hsem
  let : Smooth B.X.hom := hi.smooth
  let : IsAffineHom B.X.hom := hi.isClosedSubgroup.isAffineHom
  let : ConnectedSpace B.X.left := hi.connectedSpace
  obtain ⟨T, j, _, hj, f, hf⟩ := borelMaximalTorus k G B i hi
  have hfmax : IsMaximalTorus f := IsMaximalTorus.of_comp hi.isClosedSubgroup (hf ▸ hj)
  obtain ⟨U, Q, a, q, ha, hUs, hUc, hU, hnorm, hq, hQ⟩ :=
    solvableTorusQuotient k B hi.isSolvableGroupScheme
  obtain ⟨σ, hσ⟩ := solvableSplitExtension k B hi.isSolvableGroupScheme
    U Q a q ha hUs hUc hU hnorm hq hQ
  have : IsIso (f ≫ q) := isIso_comp_of_section_of_isUnipotent
    hi.isSolvableGroupScheme hU hnorm hq.2.2.2 hQ σ hσ f hfmax
  let sectionHom := inv (f ≫ q) ≫ f
  have hsection : sectionHom ≫ q = 𝟙 _ := by
    change (inv (f ≫ q) ≫ f) ≫ q = 𝟙 _
    rw [Category.assoc, IsIso.inv_hom_id]
  let : Mono a.hom.hom := ha.mono_overHom
  let : Smooth U.X.hom := hUs
  let : IsAffineHom U.X.hom := ha.isAffineHom
  obtain ⟨v₀, hv⟩ := TrigonalizableSectionConjugacySmooth.exists_eq_comp_inner
    a q hq.2.2.2.symm hU ℓ hL sectionHom hsection
  let v := v₀ ≫ a.hom.hom
  let eG := G.innerIso (v ≫ i.hom.hom)
  let m := ℓ ≫ q ≫ inv (f ≫ q)
  have hfactor : ℓ = (m ≫ f) ≫ (B.innerIso v).hom := by
    simpa only [m, sectionHom, v, Category.assoc] using hv
  have hcomp : m ≫ (j ≫ eG.hom) = ℓ ≫ i := by
    calc
      _ = ((m ≫ f) ≫ (B.innerIso v).hom) ≫ i := by
        simp only [eG, ← hf, Category.assoc, innerIso_hom_comp i v]
      _ = _ := by rw [← hfactor]
  refine ⟨T, j ≫ eG.hom, y ≫ m.hom.hom, hj.comp_iso eG, ?_⟩
  rw [Category.assoc, ← Grp.comp_hom_hom, hcomp, Grp.comp_hom_hom, ← Category.assoc, hy, hb]

end Langlands.GroupScheme
