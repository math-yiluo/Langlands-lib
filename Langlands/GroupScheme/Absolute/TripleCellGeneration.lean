import Langlands.GroupScheme.Absolute.TripleCell
import Langlands.GroupScheme.SmoothConnectedGeometryProof
import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-! # Closed generation and homomorphism extensionality from the triple cell -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic

section General

variable {S : Scheme.{u}} {G H M Z U : GroupScheme S}

/-- Three-factor multiplication commutes with every group-scheme homomorphism. -/
theorem tripleCellMultiplication_comp_hom
    (iM : M ⟶ G) (iZ : Z ⟶ G) (iU : U ⟶ G) (f : G ⟶ H) :
    tripleCellMultiplication iM iZ iU ≫ f.hom.hom =
      tripleCellMultiplication (iM ≫ f) (iZ ≫ f) (iU ≫ f) := by
  simp only [tripleCellMultiplication, SubgroupFunctor.cellMultiplication,
    MonObj.mul_comp, MonObj.comp_mul, Category.assoc, Grp.comp_hom_hom]

/-- A subgroup functor containing the three factors contains the universal
three-factor product, on the cell itself as test scheme. -/
theorem tripleCellMultiplication_mem
    (iM : M ⟶ G) (iZ : Z ⟶ G) (iU : U ⟶ G) (F : SubgroupFunctor G)
    (hM : SubgroupFunctor.range iM ≤ F)
    (hZ : SubgroupFunctor.range iZ ≤ F)
    (hU : SubgroupFunctor.range iU ≤ F) :
    tripleCellMultiplication iM iZ iU ∈ F.carrier (M.X ⊗ (Z.X ⊗ U.X)) := by
  simp only [tripleCellMultiplication, SubgroupFunctor.cellMultiplication, MonObj.comp_mul]
  apply (F.carrier _).mul_mem
  · apply hM
    exact ⟨fst M.X (Z.X ⊗ U.X), rfl⟩
  · apply (F.carrier _).mul_mem
    · apply hZ
      apply SubgroupFunctor.mem_range.mpr
      exact ⟨snd M.X (Z.X ⊗ U.X) ≫ fst Z.X U.X, Category.assoc _ _ _⟩
    · apply hU
      apply SubgroupFunctor.mem_range.mpr
      exact ⟨snd M.X (Z.X ⊗ U.X) ≫ snd Z.X U.X, Category.assoc _ _ _⟩

end General

section Field

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]

private theorem integral_smoothConnectedAffine : IsIntegral G.X.left := by
  have : GeometricallyIntegral G.X.hom :=
    smoothConnectedAffineGeometry.1 k G inferInstance inferInstance inferInstance
  exact GeometricallyIntegral.isIntegral_of_subsingleton G.X.hom

variable (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    {M Z U : GroupScheme (Spec (CommRingCat.of k))}
    {iM : M ⟶ G} {iZ : Z ⟶ G} {iU : U ⟶ G}
    (hM : (unipotent (CommGroupScheme.groupHom
      (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ χ)).IsRepresentedBy iM)
    (hZ : (centralizer χ).IsRepresentedBy iZ)
    (hU : (unipotent χ).IsRepresentedBy iU)

include hM hZ hU

/-- The actual three-factor cell is dense in a smooth connected affine group. -/
theorem isDominant_tripleCellMultiplication :
    IsDominant (tripleCellMultiplication iM iZ iU).left := by
  have : IsIntegral G.X.left := integral_smoothConnectedAffine
  have : IsOpenImmersion (tripleCellMultiplication iM iZ iU).left :=
    isOpenImmersion_tripleCellMultiplication χ hM hZ hU
  have : Nonempty (M.X ⊗ (Z.X ⊗ U.X)).left :=
    ⟨(lift (1 : 𝟙_ _ ⟶ M.X)
      (lift (1 : 𝟙_ _ ⟶ Z.X) (1 : 𝟙_ _ ⟶ U.X))).left
        (Classical.arbitrary (Spec (CommRingCat.of k)))⟩
  exact ⟨IsOpenMap.denseRange_of_isPreirreducibleSpace _
    (tripleCellMultiplication iM iZ iU).left.isOpenEmbedding.isOpenMap⟩

/-- The dense triple cell is scheme-theoretically dense, since the ambient
smooth connected group is reduced. -/
theorem isSchemeTheoreticallyDominant_tripleCellMultiplication :
    IsSchemeTheoreticallyDominant (tripleCellMultiplication iM iZ iU).left := by
  have : IsIntegral G.X.left := integral_smoothConnectedAffine
  have := isDominant_tripleCellMultiplication χ hM hZ hU
  exact IsSchemeTheoreticallyDominant.of_isDominant _

/-- A closed subgroup containing all three represented dynamic factors is the
whole smooth connected affine group. The closed subgroup need not be smooth. -/
theorem isIso_of_contains_tripleCell
    {D : GroupScheme (Spec (CommRingCat.of k))} (d : D ⟶ G) (hd : IsClosedSubgroup d)
    (hDM : SubgroupFunctor.range iM ≤ SubgroupFunctor.range d)
    (hDZ : SubgroupFunctor.range iZ ≤ SubgroupFunctor.range d)
    (hDU : SubgroupFunctor.range iU ≤ SubgroupFunctor.range d) : IsIso d := by
  have : IsIntegral G.X.left := integral_smoothConnectedAffine
  have : IsClosedImmersion d.hom.hom.left := hd
  obtain ⟨a, ha⟩ := SubgroupFunctor.mem_range.mp
    (tripleCellMultiplication_mem iM iZ iU (SubgroupFunctor.range d) hDM hDZ hDU)
  have : IsDominant (a.left ≫ d.hom.hom.left) := by
    rw [← Over.comp_left, ha]
    exact isDominant_tripleCellMultiplication χ hM hZ hU
  have : IsDominant d.hom.hom.left := IsDominant.of_comp a.left d.hom.hom.left
  have : Surjective d.hom.hom.left :=
    surjective_of_isDominant_of_isClosed_range _
      d.hom.hom.left.isClosedEmbedding.isClosed_range
  have : IsIso d.hom.hom.left := isIso_of_isClosedImmersion_of_surjective _
  have : IsIso ((Over.forget _).map d.hom.hom) := ‹IsIso d.hom.hom.left›
  have : IsIso d.hom.hom := isIso_of_reflects_iso _ (Over.forget _)
  have : IsIso ((Mon.forget _).map d.hom) := ‹IsIso d.hom.hom›
  have : IsIso d.hom := isIso_of_reflects_iso _ (Mon.forget _)
  have : IsIso ((Grp.forget₂Mon _).map d) := ‹IsIso d.hom›
  exact isIso_of_reflects_iso d (Grp.forget₂Mon _)

/-- Homomorphisms to a separated group scheme agree if they agree on the
opposite unipotent, centralizer and unipotent factors. -/
theorem hom_ext_of_tripleCell
    {H : GroupScheme (Spec (CommRingCat.of k))} [IsSeparated H.X.hom]
    (f g : G ⟶ H) (eM : iM ≫ f = iM ≫ g) (eZ : iZ ≫ f = iZ ≫ g)
    (eU : iU ≫ f = iU ≫ g) : f = g := by
  have : IsIntegral G.X.left := integral_smoothConnectedAffine
  have := isDominant_tripleCellMultiplication χ hM hZ hU
  have hcell : tripleCellMultiplication iM iZ iU ≫ f.hom.hom =
      tripleCellMultiplication iM iZ iU ≫ g.hom.hom := by
    rw [tripleCellMultiplication_comp_hom, tripleCellMultiplication_comp_hom, eM, eZ, eU]
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  exact ext_of_isDominant_of_isSeparated H.X.hom (by rw [Over.w, Over.w])
    (tripleCellMultiplication iM iZ iU).left (congrArg Over.Hom.left hcell)

end Field

section Intrinsic

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]

/-- The intrinsic dynamic functors generate a smooth connected affine group
as a closed subgroup, without choosing their representatives in the statement. -/
theorem isIso_of_contains_dynamicFactors
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    {D : GroupScheme (Spec (CommRingCat.of k))} (d : D ⟶ G) (hd : IsClosedSubgroup d)
    (hM : unipotent (CommGroupScheme.groupHom
      (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ χ) ≤ SubgroupFunctor.range d)
    (hZ : centralizer χ ≤ SubgroupFunctor.range d)
    (hU : unipotent χ ≤ SubgroupFunctor.range d) : IsIso d := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let χ' := CommGroupScheme.groupHom
    (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ χ
  have hMr := Affine.isRepresentedBy_unipotentHom χ'
  have hZr := Affine.isRepresentedBy_centralizerHom χ
  have hUr := Affine.isRepresentedBy_unipotentHom χ
  exact isIso_of_contains_tripleCell χ hMr hZr hUr d hd
    (by rw [hMr.2]; exact hM) (by rw [hZr.2]; exact hZ) (by rw [hUr.2]; exact hU)

/-- The actual group-scheme isomorphism furnished by closed generation by the
three intrinsic dynamic factors. Its forward map is the given inclusion. -/
def isoOfContainsDynamicFactors
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    {D : GroupScheme (Spec (CommRingCat.of k))} (d : D ⟶ G) (hd : IsClosedSubgroup d)
    (hM : unipotent (CommGroupScheme.groupHom
      (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ χ) ≤ SubgroupFunctor.range d)
    (hZ : centralizer χ ≤ SubgroupFunctor.range d)
    (hU : unipotent χ ≤ SubgroupFunctor.range d) : D ≅ G := by
  have := isIso_of_contains_dynamicFactors χ d hd hM hZ hU
  exact asIso d

@[simp]
theorem isoOfContainsDynamicFactors_hom
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    {D : GroupScheme (Spec (CommRingCat.of k))} (d : D ⟶ G) (hd : IsClosedSubgroup d)
    (hM : unipotent (CommGroupScheme.groupHom
      (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ χ) ≤ SubgroupFunctor.range d)
    (hZ : centralizer χ ≤ SubgroupFunctor.range d)
    (hU : unipotent χ ≤ SubgroupFunctor.range d) :
    (isoOfContainsDynamicFactors χ d hd hM hZ hU).hom = d := rfl

end Intrinsic

end Langlands.GroupScheme.Dynamic
