import Langlands.GroupScheme.OrthogonalMatrix.VectorRootDatumMap
import Langlands.GroupScheme.Reductive.SplitCentralIsogeny
import Langlands.GroupScheme.Torus.HomKernelDiagonalizable

/-! # The actual vector central isogeny of a split type-D group -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.OrthogonalMatrix.TypeDNumbering

variable {k : Type u} [Field k] {n : ℕ}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {I : Type u} [Finite I]
    (P : RootDatum I (characterLattice T) (cocharacterLattice T)) [P.IsReduced]
    (B : P.Base) (hspan : P.corootSpan ℤ = ⊤) (hn : 4 ≤ n)
    (e : B.support ≃ Fin n) (i : T.toGrp ⟶ G)

/-- An actual vector isogeny, with the compatible torus map and its exact integral
character image at the prescribed numbered vertex zero. -/
structure VectorCentralIsogeny where
  map : G ⟶ identityComponent (groupScheme (Fin n) (CommRingCat.of k))
  torusMap : T ⟶ splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift (Fin n))
  central : IsCentralIsogeny map
  commutes : i ≫ map = CommGroupScheme.groupHom torusMap ≫ identityTorus (Fin n) k
  characterImage :
    (characterLattice.comapHom (CommGroupScheme.groupHom torusMap)).toIntLinearMap.range =
      P.rootSpan ℤ ⊔ Submodule.span ℤ
        {Langlands.RootDatum.fundamentalWeightBasis P B hspan (e.symm ⟨0, by omega⟩)}

/-- Realize the numbered vector morphism as a central isogeny of the actual groups. -/
def vectorCentralIsogeny (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp)
    (hi : IsMaximalTorus i) (hP : IsRootDatumOf i P)
    (he : ∀ a b : B.support, P.pairing a.val b.val = CartanMatrix.D n (e a) (e b)) :
    VectorCentralIsogeny P B hspan hn e i := by
  classical
  apply Classical.choice
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  let D := splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift (Fin n))
  obtain ⟨J, hJ, Q, f, hQ, hred, hfw, hfc, hrange⟩ :=
    exists_vectorRootDatum (k := k) P B hspan hn e he
  have hO := isConnectedReductive_identityComponent (Fin n) k
  obtain ⟨p, t, hpt, hw, hp⟩ := splitCentralIsogenyExistence k G _ hG hO T D hT
    (SymplecticMatrix.isSplitTorus_diagonalTorus (Fin n) k) i (identityTorus (Fin n) k)
    hi (isMaximalTorus_identityTorus (Fin n) k) I J P Q hP hQ f hfw hfc
  have hmap : (characterLattice.comapHom (CommGroupScheme.groupHom t)).toIntLinearMap =
      f.weightMap := by
    ext χ
    exact (hw χ).symm
  exact ⟨⟨p, t, hp, hpt, by rw [hmap, hrange]⟩⟩

omit [IsAffineHom G.X.hom] [Finite I] [P.IsReduced] in
/-- Every character in the actual torus pullback image kills the full kernel on
all test schemes, including schemes with nilpotents. -/
theorem VectorCentralIsogeny.character_kills_kernel
    (s : VectorCentralIsogeny P B hspan hn e i) (χ : characterLattice T)
    (hχ : χ ∈ (characterLattice.comapHom
      (CommGroupScheme.groupHom s.torusMap)).toIntLinearMap.range)
    (U : Over (Spec (CommRingCat.of k))) (x : U ⟶ T.X)
    (hx : x ≫ (i ≫ s.map).hom.hom = 1) :
    x ≫ (CommGroupScheme.groupHom χ).hom.hom = 1 := by
  have : IsClosedImmersion (identityTorus (Fin n) k).hom.hom.left :=
    isClosedSubgroup_identityTorus (Fin n) k
  have : Mono (identityTorus (Fin n) k).hom.hom := Over.mono_of_mono_left _
  have ht : x ≫ (CommGroupScheme.groupHom s.torusMap).hom.hom = 1 := by
    apply (cancel_mono (identityTorus (Fin n) k).hom.hom).mp
    rw [s.commutes, Grp.comp_hom_hom, ← Category.assoc] at hx
    simpa only [MonObj.one_comp] using hx
  obtain ⟨ψ, rfl⟩ := hχ
  change x ≫ (CommGroupScheme.groupHom
    (characterLattice.comapHom (CommGroupScheme.groupHom s.torusMap) ψ)).hom.hom = 1
  rw [characterLattice.comapHom_groupHom, Grp.comp_hom_hom, ← Category.assoc,
    ht, MonObj.one_comp]

omit [IsAffineHom G.X.hom] [Finite I] [P.IsReduced] in
/-- The fundamental weight at numbered vertex zero kills the full kernel on the
supplied maximal torus. -/
theorem VectorCentralIsogeny.fundamentalWeight_kills_kernel
    (s : VectorCentralIsogeny P B hspan hn e i)
    (U : Over (Spec (CommRingCat.of k))) (x : U ⟶ T.X)
    (hx : x ≫ (i ≫ s.map).hom.hom = 1) :
    x ≫ (CommGroupScheme.groupHom
      (Langlands.RootDatum.fundamentalWeightBasis P B hspan
        (e.symm ⟨0, by omega⟩))).hom.hom = 1 := by
  apply VectorCentralIsogeny.character_kills_kernel P B hspan hn e i s _ _ U x hx
  rw [s.characterImage]
  exact Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton _))

end Langlands.GroupScheme.OrthogonalMatrix.TypeDNumbering
