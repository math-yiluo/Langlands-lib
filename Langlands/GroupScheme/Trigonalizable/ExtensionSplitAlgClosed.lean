import Langlands.GroupScheme.Trigonalizable.TriangularEmbeddingWithDiagonalKernel
import Langlands.GroupScheme.Absolute.TriangularActualQuotientTower
import Langlands.GroupScheme.AffineHomImageProof
import Langlands.GroupScheme.AffineNormalSubgroupQuotientProof
import Langlands.GroupScheme.LinearKernelTowerSectionProof

/-! # Splitting of trigonalizable extensions over algebraically closed fields (Milne 16.26(a)) -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.TrigonalizableExtensionSplit

open TrigonalizableFlag

variable {k : Type u} [Field k]
  {G U : GroupScheme (Spec (CommRingCat.of k))} [LocallyOfFiniteType G.X.hom]
  [IsAffineHom G.X.hom] (i : U ⟶ G) {Λ : Type u} [AddCommGroup Λ] [AddGroup.FG Λ]
  (q : G ⟶ (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp)

/-- **Character-linear towers (Milne 16.21).** Over any field, the quotient map of an extension of
`D(Λ)` by a closed normal unipotent subgroup admits a finite character-linear kernel tower. -/
theorem admitsTower (hi : IsClosedSubgroup i) (hU : IsUnipotent U)
    (hN : (SubgroupFunctor.range i).IsNormal)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q) :
    LinearKernelTower.AdmitsTower (Diagonalizable.groupScheme (CommRingCat.of k) Λ) q := by
  have : IsClosedImmersion i.hom.hom.left := hi
  have : IsAffineHom U.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  obtain ⟨N, j, hj, hker⟩ := exists_triangular_embedding i q hU hN hq
  let f := j ≫ GeneralLinear.blockLimitHom (Fin N) (CommRingCat.of k) (fun a => -(a.val : ℤ))
  have hk : kernelι q ≫ f = 0 := by
    apply (Grp.forget _).map_injective
    change (kernelι q).hom.hom ≫ f.hom.hom = 1
    apply (mem_range_kernelι_iff f _).mp
    rw [hker, ← hq.2.2.2]
    exact SubgroupFunctor.mem_range.mpr ⟨𝟙 _, Category.id_comp _⟩
  have : Flat q.hom.hom.left := hq.1
  have : Surjective q.hom.hom.left := hq.2.1
  have : LocallyOfFinitePresentation q.hom.hom.left := hq.2.2.1
  have hfac : q ≫ FppfHomDescent.hom q f hk = f := FppfHomDescent.fac q f hk
  have hq' : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (kernelι f)) q := by
    rw [hker]
    exact hq
  exact TriangularLayer.admitsTower_diagonalizable_of_affine_image_and_normal_quotient
    affineHomImage affineNormalSubgroupQuotient j hj Λ _ q hfac hq'

/-- **Milne 16.26(a).** Over an algebraically closed field, the quotient map of an extension of
`D(Λ)` by a closed normal unipotent subgroup has a homomorphic section. -/
theorem exists_section_of_isAlgClosed [IsAlgClosed k] (hi : IsClosedSubgroup i)
    (hU : IsUnipotent U) (hN : (SubgroupFunctor.range i).IsNormal)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range i) q) :
    ∃ s : (Diagonalizable.groupScheme (CommRingCat.of k) Λ).toGrp ⟶ G, s ≫ q = 𝟙 _ :=
  LinearKernelTower.sectionExistence k Λ G q (admitsTower i q hi hU hN hq)

end Langlands.GroupScheme.TrigonalizableExtensionSplit
