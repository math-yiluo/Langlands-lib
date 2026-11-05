import Langlands.Geometry.Building.KPTorusIwahoriSurjectivityStatement
import Langlands.Geometry.Building.KPTorusNormNaturality
import Langlands.GroupScheme.Torus.SplitLatticeBaseChange

/-! # Surjectivity of the actual torus Iwahori norm subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Lifts of the coordinate cocharacters give a section of a map onto a split torus. -/
theorem IsSplitTorus.exists_section_of_surjective_cocharacters
    {S : Scheme.{u}} {T U : CommGroupScheme S} (hU : IsSplitTorus U.toGrp)
    (f : T ⟶ U)
    (hf : Function.Surjective (fun ν : cocharacterLattice T => ν ≫ f)) :
    ∃ s : U ⟶ T, s ≫ f = 𝟙 U := by
  classical
  obtain ⟨I, hI, ⟨e⟩⟩ := hU
  let : Finite I := hI
  let : Fintype I := Fintype.ofFinite I
  let eC : U ≅ splitTorus.commGroupScheme S I := CommGroupScheme.isoOfGroupIso e
  choose lifts hlifts using fun i : I => hf (splitTorus.single S I i ≫ eC.inv)
  have hsum : (∑ i, splitTorus.proj S I i ≫ lifts i) ≫ f = eC.inv := by
    calc
      (∑ i, splitTorus.proj S I i ≫ lifts i) ≫ f =
          ∑ i, splitTorus.proj S I i ≫ (lifts i ≫ f) := by
        simp only [Preadditive.sum_comp, Category.assoc]
      _ = ∑ i, splitTorus.proj S I i ≫ (splitTorus.single S I i ≫ eC.inv) := by
        simp only [hlifts]
      _ = (∑ i, splitTorus.proj S I i ≫ splitTorus.single S I i) ≫ eC.inv := by
        simp only [Preadditive.sum_comp, Category.assoc]
      _ = eC.inv := by rw [splitTorus.sum_proj_comp_single, Category.id_comp]
  refine ⟨eC.hom ≫ ∑ i, splitTorus.proj S I i ≫ lifts i, ?_⟩
  rw [Category.assoc, hsum, eC.hom_inv_id]

end Langlands.GroupScheme

namespace Langlands.Geometry.Building

open Langlands.GroupScheme GaloisPointComparison

/-- Cocharacter surjectivity onto a torus split over the given extension makes the actual
norm-image subgroups surjective, for any valuation on that extension. -/
theorem map_torusNormIwahori_eq_of_cocharacter_surjective
    (k L : Type u) [Field k] [Field L] [Algebra k L]
    [FiniteDimensional k L] [IsGalois k L]
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation L Γ₀)
    {T U : CommGroupScheme (Spec (CommRingCat.of k))}
    [IsAffine T.X.left] [IsAffine U.X.left] (f : T ⟶ U)
    (hU : IsSplitTorus (baseChanged k L U.toGrp))
    (hf : Function.Surjective
      (fun ν : cocharacterLattice ((CommGroupScheme.baseChange (baseMap k L)).obj T) =>
        ν ≫ (CommGroupScheme.baseChange (baseMap k L)).map f)) :
    (torusNormIwahori k L v T).map (rationalPoints.map (CommGroupScheme.groupHom f)) =
      torusNormIwahori k L v U := by
  obtain ⟨s, hs⟩ := hU.exists_section_of_surjective_cocharacters
    ((CommGroupScheme.baseChange (baseMap k L)).map f) hf
  apply le_antisymm (map_torusNormIwahori_le k L v f)
  intro t ht
  obtain ⟨x, hx, rfl⟩ := (mem_torusNormIwahori k L).mp ht
  refine ⟨rationalNorm k L T (rationalPoints.map (CommGroupScheme.groupHom s) x), ?_, ?_⟩
  · exact (mem_torusNormIwahori k L).mpr
      ⟨_, map_characterValuationKernel_le v (CommGroupScheme.groupHom s) ⟨x, hx, rfl⟩, rfl⟩
  · rw [rationalNorm_naturality]
    congr 1
    change rationalPoints.map (CommGroupScheme.groupHom
      (s ≫ (CommGroupScheme.baseChange (baseMap k L)).map f)) x = x
    rw [hs]
    rfl

/-- KP Lemma 2.5.20(1), in the exact published formulation over the maximal unramified
extension of an arbitrary nonarchimedean local field. -/
theorem torusIwahoriSurjectivity : TorusIwahoriSurjectivityStatement.{u} := by
  intro F _ _ _ _ T₂ T₃ _ _ f L _ _ _ hT₃ hf
  exact map_torusNormIwahori_eq_of_cocharacter_surjective
    (UnramifiedClosure F) L (intermediateValuation F L) f hT₃ hf

end Langlands.Geometry.Building
