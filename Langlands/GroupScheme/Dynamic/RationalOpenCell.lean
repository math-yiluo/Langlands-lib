import Langlands.AlgebraicGeometry.PointTopology.RationalSchemePoints
import Langlands.GroupScheme.Absolute.OppositeCellProof
import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.GroupScheme.Dynamic.LimitMap

/-! # The rational opposite cell is an identity neighborhood

For a smooth affine group over a topological field and a cocharacter `χ`, the
products `a * b * c` with `a` in `U(χ⁻¹)(k)`, `b` in `Z(χ)(k)` and `c` in
`U(χ)(k)`, each factor in a prescribed identity neighborhood, form an identity
neighborhood of `G(k)` for the scheme-chart topology. The proof uses the
published opposite open cell `U(χ⁻¹) × P(χ) → G` and a limit morphism
`P(χ) → Z(χ)` of the universal point of a representative of `P(χ)`. -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry Topology
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic

open Langlands.AlgebraicGeometry.PointTopology

variable (k : Type u) [Field k] [TopologicalSpace k] [IsTopologicalRing k] [IsOpenUnits k]

section General

variable {G : GroupScheme (Spec (CommRingCat.of k))} [IsSeparated G.X.hom]
  (χ χ' : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
  {O P : GroupScheme (Spec (CommRingCat.of k))}

omit [TopologicalSpace k] [IsTopologicalRing k] [IsOpenUnits k] in
/-- A point of a product `O × P` mapping into `U(χ')` and `P(χ)` splits as an
element of `U(χ')(k)`, an element of `Z(χ)(k)` and an element of `U(χ)(k)`. Here
`L` is a limit of the universal point of `P`. -/
theorem cell_point_decomposition (iO : O ⟶ G) (iP : P ⟶ G)
    (hO : (unipotent χ').IsRepresentedBy iO) {L : P.X ⟶ G.X}
    (hL : HasLimit χ iP.hom.hom L) (w : RationalPoint k (O.X ⊗ P.X)) :
    w ≫ fst O.X P.X ≫ iO.hom.hom ∈ (unipotent χ').carrier (Over.mk (𝟙 _)) ∧
      w ≫ snd O.X P.X ≫ L ∈ (centralizer χ).carrier (Over.mk (𝟙 _)) ∧
      w ≫ ((snd O.X P.X ≫ L)⁻¹ * (snd O.X P.X ≫ iP.hom.hom)) ∈
        (unipotent χ).carrier (Over.mk (𝟙 _)) ∧
      w ≫ ((fst O.X P.X ≫ iO.hom.hom) * (snd O.X P.X ≫ iP.hom.hom)) =
        (w ≫ fst O.X P.X ≫ iO.hom.hom) * (w ≫ snd O.X P.X ≫ L) *
          (w ≫ ((snd O.X P.X ≫ L)⁻¹ * (snd O.X P.X ≫ iP.hom.hom))) := by
  have hl : HasLimit χ (w ≫ snd O.X P.X ≫ iP.hom.hom) (w ≫ snd O.X P.X ≫ L) := by
    simpa only [Category.assoc] using hL.comp χ (w ≫ snd O.X P.X)
  have hlZ : w ≫ snd O.X P.X ≫ L ∈ (centralizer χ).carrier (Over.mk (𝟙 _)) :=
    hl.mem_centralizer χ
  have hpl : (w ≫ snd O.X P.X ≫ iP.hom.hom) * (w ≫ snd O.X P.X ≫ L)⁻¹ ∈
      (unipotent χ).carrier (Over.mk (𝟙 _)) := by
    have h := hl.mul χ (hasLimit_of_mem_centralizer χ hlZ).inv
    rwa [mul_inv_cancel] at h
  have hlp : (w ≫ snd O.X P.X ≫ L)⁻¹ * (w ≫ snd O.X P.X ≫ iP.hom.hom) ∈
      (unipotent χ).carrier (Over.mk (𝟙 _)) := by
    have h := (Subgroup.mem_normalizer_iff.mp
      (centralizer_le_normalizer_unipotent χ _ (inv_mem hlZ)) _).mp hpl
    rwa [inv_inv, mul_assoc, mul_assoc, inv_mul_cancel, mul_one] at h
  have hoO : w ≫ fst O.X P.X ≫ iO.hom.hom ∈ (unipotent χ').carrier (Over.mk (𝟙 _)) :=
    hO.2 ▸ SubgroupFunctor.mem_range.mpr ⟨w ≫ fst O.X P.X, Category.assoc _ _ _⟩
  refine ⟨hoO, hlZ, ?_, ?_⟩
  · simpa only [MonObj.comp_mul, GrpObj.comp_inv] using hlp
  · simp only [MonObj.comp_mul, GrpObj.comp_inv]
    group

/-- **Opposite cell neighborhoods from an open immersion.** If the product map
`O × P → G` of representatives of `U(χ')` and `P(χ)` is an open immersion, then
products of identity neighborhoods restricted to `U(χ')(k)`, `Z(χ)(k)` and
`U(χ)(k)` are identity neighborhoods in the scheme-chart topology. -/
theorem cell_mem_nhds_one_of_isOpenImmersion (iO : O ⟶ G) (iP : P ⟶ G)
    (hO : (unipotent χ').IsRepresentedBy iO) (hP : (parabolic χ).IsRepresentedBy iP)
    (hcell : IsOpenImmersion
      ((fst O.X P.X ≫ iO.hom.hom) * (snd O.X P.X ≫ iP.hom.hom)).left) :
    letI := rationalSchemeTopology k G.X
    ∀ A ∈ 𝓝 (1 : RationalPoint k G.X), ∀ B ∈ 𝓝 (1 : RationalPoint k G.X),
      ∀ C ∈ 𝓝 (1 : RationalPoint k G.X),
      {x : RationalPoint k G.X |
        ∃ a ∈ A ∩ ((unipotent χ').carrier (Over.mk (𝟙 _)) : Set (RationalPoint k G.X)),
        ∃ b ∈ B ∩ ((centralizer χ).carrier (Over.mk (𝟙 _)) : Set (RationalPoint k G.X)),
        ∃ c ∈ C ∩ ((unipotent χ).carrier (Over.mk (𝟙 _)) : Set (RationalPoint k G.X)),
          x = a * b * c} ∈ 𝓝 (1 : RationalPoint k G.X) := by
  let := rationalSchemeTopology k G.X
  let := rationalSchemeTopology k (O.X ⊗ P.X)
  intro A hA B hB C hC
  have hpar : iP.hom.hom ∈ (parabolic χ).carrier P.X :=
    hP.2 ▸ SubgroupFunctor.mem_range.mpr ⟨𝟙 _, Category.id_comp _⟩
  obtain ⟨L, hL⟩ := exists_hasLimit χ hpar
  set fO : O.X ⊗ P.X ⟶ G.X := fst O.X P.X ≫ iO.hom.hom with hfO
  set fP : O.X ⊗ P.X ⟶ G.X := snd O.X P.X ≫ iP.hom.hom with hfP
  set fL : O.X ⊗ P.X ⟶ G.X := snd O.X P.X ≫ L with hfL
  set fC : O.X ⊗ P.X ⟶ G.X := fL⁻¹ * fP with hfC
  let e : RationalPoint k (O.X ⊗ P.X) := lift 1 1
  have heO : e ≫ fO = 1 := by
    simp only [e, fO, lift_fst_assoc, MonObj.one_comp]
  have heP : e ≫ fP = 1 := by
    simp only [e, fP, lift_snd_assoc, MonObj.one_comp]
  have heL : e ≫ fL = 1 := by
    have h1 : HasLimit χ (e ≫ fP) (e ≫ fL) := by
      simpa only [fP, fL, Category.assoc] using hL.comp χ (e ≫ snd O.X P.X)
    rw [heP] at h1
    exact h1.unique χ (hasLimit_of_mem_centralizer χ (one_mem _))
  have heC : e ≫ fC = 1 := by
    simp only [fC, MonObj.comp_mul, GrpObj.comp_inv, heL, heP, inv_one, mul_one]
  have hem : e ≫ (fO * fP) = 1 := by
    rw [MonObj.comp_mul, heO, heP, mul_one]
  let W : Set (RationalPoint k (O.X ⊗ P.X)) :=
    (fun w => w ≫ fO) ⁻¹' A ∩ (fun w => w ≫ fL) ⁻¹' B ∩ (fun w => w ≫ fC) ⁻¹' C
  have hW : W ∈ 𝓝 e := by
    refine Filter.inter_mem (Filter.inter_mem ?_ ?_) ?_
    · exact (continuous_rationalSchemePointMap k fO).continuousAt.preimage_mem_nhds
        (by rwa [heO])
    · exact (continuous_rationalSchemePointMap k fL).continuousAt.preimage_mem_nhds
        (by rwa [heL])
    · exact (continuous_rationalSchemePointMap k fC).continuousAt.preimage_mem_nhds
        (by rwa [heC])
  have : IsOpenImmersion (fO * fP).left := hcell
  have himage : (fun w : RationalPoint k (O.X ⊗ P.X) => w ≫ (fO * fP)) '' W ∈
      𝓝 (1 : RationalPoint k G.X) := by
    have h := (isOpenEmbedding_rationalSchemePointMap k (fO * fP)).isOpenMap.image_mem_nhds hW
    rwa [hem] at h
  refine Filter.mem_of_superset himage ?_
  rintro x ⟨w, ⟨⟨hwA, hwB⟩, hwC⟩, rfl⟩
  obtain ⟨hoO, hlZ, hcU, hdec⟩ := cell_point_decomposition k χ χ' iO iP hO hL w
  exact ⟨w ≫ fO, ⟨hwA, hoO⟩, w ≫ fL, ⟨hwB, hlZ⟩, w ≫ fC, ⟨hwC, hcU⟩, hdec⟩

end General

/-- **The rational opposite cell is an identity neighborhood.** For a smooth
affine separated group over a topological field and a cocharacter `χ`, every
product of identity neighborhoods restricted to `U(χ⁻¹)(k)`, `Z(χ)(k)` and
`U(χ)(k)` is an identity neighborhood in the scheme-chart topology. -/
theorem opposite_cell_mem_nhds_one (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [IsSeparated G.X.hom]
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) :
    letI := rationalSchemeTopology k G.X
    ∀ A ∈ 𝓝 (1 : RationalPoint k G.X), ∀ B ∈ 𝓝 (1 : RationalPoint k G.X),
      ∀ C ∈ 𝓝 (1 : RationalPoint k G.X),
      {x : RationalPoint k G.X |
        ∃ a ∈ A ∩ ((unipotent (CommGroupScheme.groupHom
            (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ χ)).carrier
            (Over.mk (𝟙 _)) : Set (RationalPoint k G.X)),
        ∃ b ∈ B ∩ ((centralizer χ).carrier (Over.mk (𝟙 _)) : Set (RationalPoint k G.X)),
        ∃ c ∈ C ∩ ((unipotent χ).carrier (Over.mk (𝟙 _)) : Set (RationalPoint k G.X)),
          x = a * b * c} ∈ 𝓝 (1 : RationalPoint k G.X) := by
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  exact cell_mem_nhds_one_of_isOpenImmersion k χ _
    (Affine.unipotentHom _) (Affine.parabolicHom χ)
    (Affine.isRepresentedBy_unipotentHom _) (Affine.isRepresentedBy_parabolicHom χ)
    (oppositeCellStatement k G χ _ _ _ _
      (Affine.isRepresentedBy_unipotentHom _) (Affine.isRepresentedBy_parabolicHom χ))

end Langlands.GroupScheme.Dynamic
