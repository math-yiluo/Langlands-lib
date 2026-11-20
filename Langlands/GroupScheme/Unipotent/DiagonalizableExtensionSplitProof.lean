import Langlands.GroupScheme.Unipotent.DiagonalizableExtensionSplitStatement
import Langlands.GroupScheme.Unipotent.DiagonalizableExtensionSection
import Langlands.GroupScheme.Absolute.SolvableComplementOfQuotient
import Langlands.GroupScheme.Rational.LeviMultiplication

/-! # Extensions of a smooth connected unipotent group by a diagonalizable group split uniquely

Proof of `PerfectDiagonalizableUnipotentExtensionSplitStatement` (Milne 16.28). -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open RelativeRoot DiagonalizableUnipotentExtension

/-- **Milne 16.28.** Over a perfect field, an extension `e → D → G → U → e` of a smooth
connected unipotent group `U` by a diagonalizable group `D` has exactly one homomorphic
section `s`, the points of `D` and `s(U)` commute, and multiplication `D × U → G` is an
isomorphism. -/
theorem perfectDiagonalizableUnipotentExtensionSplit :
    PerfectDiagonalizableUnipotentExtensionSplitStatement.{u} := by
  intro k _ _ G _ _ D U i q hi hq hD hUs hUc hUu
  obtain ⟨Λ, _, _, ⟨eD⟩⟩ := hD
  have : Smooth U.X.hom := hUs
  have : IsClosedImmersion i.hom.hom.left := hi
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have : IsAffineHom D.X.hom :=
    isAffineHom_of_over_iso ((Grp.forget _).mapIso eD)
      (Diagonalizable.isAffineHom (CommRingCat.of k) Λ)
  have : LocallyOfFiniteType D.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  have : IsAffineHom q.hom.hom.left := hq.isAffineHom_of_isAffineHom_kernel i
  have : IsAffineHom U.X.hom := isAffineHom_quotient i q hi hq
  have hDm : IsMultiplicativeType D := isMultiplicativeType_of_iso_diagonalizable eD
  have hc : IsCentral i := isCentral i q hq hDm inferInstance inferInstance hUc
  have hiso : ∀ s : U ⟶ G, s ≫ q = 𝟙 U → IsIso (subgroupMultiplication i s) := by
    intro s hs
    have : IsIso (s ≫ q) := by
      rw [hs]
      infer_instance
    rw [isIso_subgroupMultiplication_reverse_iff]
    exact isIso_subgroupMultiplication_of_isIso_comp (s := s) (u := i) (q := q) inferInstance
      hq.2.2.2
  obtain ⟨s, hs⟩ := exists_section hUc hUu eD i hi hc q hq
  refine ⟨⟨s, hs, fun s' hs' => section_unique hUu hDm i hc q hq s s' hs hs'⟩,
    fun s' hs' => ⟨fun T x y => (commute_of_mem_center (hc T x) (y ≫ s'.hom.hom)).eq,
      hiso s' hs'⟩⟩

end Langlands.GroupScheme
