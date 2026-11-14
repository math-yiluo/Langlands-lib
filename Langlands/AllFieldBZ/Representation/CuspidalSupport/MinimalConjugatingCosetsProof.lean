import Langlands.AllFieldBZ.Representation.CuspidalSupport.JacquetInductionStatement
import Langlands.AllFieldBZ.Representation.Geometric.WeylStatement
import Langlands.AllFieldBZ.Representation.Geometric.WeylUniquenessProof
import Langlands.Representation.CuspidalSupport.MinimalConjugatingCosetsProof

/-!
# All-field port of `Langlands.Representation.CuspidalSupport.MinimalConjugatingCosetsProof`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.CuspidalSupport.MinimalConjugatingCosetsProof` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
namespace Langlands.AllFieldBZ.CuspidalSupport
open Langlands.CuspidalSupport hiding AssociatedJacquetFiltrationTheorem NonassociatedJacquetSubquotientsTheorem
open Langlands.GeneralLinear
open Langlands.Geometric hiding PadicParabolicBruhatTheorem PadicStandardIntersectionsTheorem
open Langlands.AllFieldBZ.Geometric
universe u

variable {n : ℕ} {R : Type u} [CommRing R]

private theorem _root_.Langlands.CuspidalSupport.map_conj_mul {G : Type*} [Group G] (H : Subgroup G) (x y : G) :
    H.map (MulAut.conj (x * y)).toMonoidHom =
      (H.map (MulAut.conj y).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext g
  simp [MulAut.conj_apply, mul_assoc]

variable {F : Type u} [Field F] {B C D : BlockShape n}

private theorem _root_.Langlands.CuspidalSupport.conjugatesLevi_mem_iff {w : Equiv.Perm (Fin n)}
    (hw : ConjugatesLevi (F := F) B C w) (g : GeneralLinear n F) :
    permutation n F w * g * (permutation n F w)⁻¹ ∈ C.leviSubgroup F ↔
      g ∈ B.leviSubgroup F := by
  rw [← hw]
  exact Subgroup.mem_map_iff_mem (MulAut.conj (permutation n F w)).injective

private theorem _root_.Langlands.CuspidalSupport.conjugatesLevi_self {w : Equiv.Perm (Fin n)}
    (hw : w ∈ blockWeyl B) : ConjugatesLevi (F := F) B B w := by
  apply Subgroup.mem_normalizer_iff_map_conj_eq.mp
  apply (B.leviSubgroup F).le_normalizer
  exact (permutation_mem_levi_iff B w).mpr hw

private theorem _root_.Langlands.CuspidalSupport.conjugatesLevi_of_doubleCoset {w v : Equiv.Perm (Fin n)}
    (hw : ConjugatesLevi (F := F) B C w)
    (h : DoubleCoset.mk (blockWeyl C) (blockWeyl B) w =
      DoubleCoset.mk (blockWeyl C) (blockWeyl B) v) :
    ConjugatesLevi (F := F) B C v := by
  obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.eq.mp h
  simpa only [mul_assoc] using
    conjugatesLevi_mul (conjugatesLevi_mul (conjugatesLevi_self hb) hw)
      (conjugatesLevi_self ha)

private theorem _root_.Langlands.CuspidalSupport.right_factor_of_doubleCoset {w v : Equiv.Perm (Fin n)}
    (hv : ConjugatesLevi (F := F) B C v)
    (h : DoubleCoset.mk (blockWeyl C) (blockWeyl B) v =
      DoubleCoset.mk (blockWeyl C) (blockWeyl B) w) :
    ∃ b : blockWeyl B, w = v * b.val := by
  obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.eq.mp h
  have hc : v⁻¹ * a * v ∈ blockWeyl B := by
    simpa only [inv_inv] using conjugatesLevi_weyl_mem (conjugatesLevi_inv hv) ha
  refine ⟨⟨(v⁻¹ * a * v) * b, (blockWeyl B).mul_mem hc hb⟩, ?_⟩
  simp [mul_assoc]

end Langlands.AllFieldBZ.CuspidalSupport
