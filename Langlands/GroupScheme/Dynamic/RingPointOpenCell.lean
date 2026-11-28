import Langlands.GroupScheme.Dynamic.RationalOpenCell
import Langlands.GroupScheme.AffinePointRingPointComparison

/-! # The opposite cell on points with values in a local topological ring

Let `G` be a smooth affine separated group scheme over a field `k`, `χ : 𝔾_m → G` a cocharacter and
`S` a local `k`-algebra which is a topological ring with open units (for example a completion of
a number field at an archimedean place). For identity neighborhoods `A`, `B`, `C` of `G(S)`, the
products `a b c` with `a ∈ A ∩ U(χ⁻¹)(S)`, `b ∈ B ∩ Z(χ)(S)` and `c ∈ C ∩ U(χ)(S)` form an
identity neighborhood of `G(S)`. This extends the rational-point statement
`Dynamic.opposite_cell_mem_nhds_one` of `Dynamic.RationalOpenCell` from `S = k` to `S`-points
of `G` itself, without base change, using the scheme-point topology of `S`-points. -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry Topology Opposite
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.Dynamic

open Langlands.AlgebraicGeometry.PointTopology

variable (k : Type u) [Field k]

section General

variable {G : GroupScheme (Spec (CommRingCat.of k))} [IsSeparated G.X.hom]
  (χ χ' : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
  {O P : GroupScheme (Spec (CommRingCat.of k))}

/-- A point, over an arbitrary test scheme, of a product `O × P` mapping into `U(χ')` and
`P(χ)` splits as a point of `U(χ')`, a point of `Z(χ)` and a point of `U(χ)`. Here `L` is a
limit of the universal point of `P`. -/
theorem cell_point_decomposition_test (iO : O ⟶ G) (iP : P ⟶ G)
    (hO : (unipotent χ').IsRepresentedBy iO) {L : P.X ⟶ G.X}
    (hL : HasLimit χ iP.hom.hom L) {Y : Over (Spec (CommRingCat.of k))}
    (w : Y ⟶ O.X ⊗ P.X) :
    w ≫ fst O.X P.X ≫ iO.hom.hom ∈ (unipotent χ').carrier Y ∧
      w ≫ snd O.X P.X ≫ L ∈ (centralizer χ).carrier Y ∧
      w ≫ ((snd O.X P.X ≫ L)⁻¹ * (snd O.X P.X ≫ iP.hom.hom)) ∈ (unipotent χ).carrier Y ∧
      w ≫ ((fst O.X P.X ≫ iO.hom.hom) * (snd O.X P.X ≫ iP.hom.hom)) =
        (w ≫ fst O.X P.X ≫ iO.hom.hom) * (w ≫ snd O.X P.X ≫ L) *
          (w ≫ ((snd O.X P.X ≫ L)⁻¹ * (snd O.X P.X ≫ iP.hom.hom))) := by
  have hl : HasLimit χ (w ≫ snd O.X P.X ≫ iP.hom.hom) (w ≫ snd O.X P.X ≫ L) := by
    simpa only [Category.assoc] using hL.comp χ (w ≫ snd O.X P.X)
  have hlZ : w ≫ snd O.X P.X ≫ L ∈ (centralizer χ).carrier Y :=
    hl.mem_centralizer χ
  have hpl : (w ≫ snd O.X P.X ≫ iP.hom.hom) * (w ≫ snd O.X P.X ≫ L)⁻¹ ∈
      (unipotent χ).carrier Y := by
    have h := hl.mul χ (hasLimit_of_mem_centralizer χ hlZ).inv
    rwa [mul_inv_cancel] at h
  have hlp : (w ≫ snd O.X P.X ≫ L)⁻¹ * (w ≫ snd O.X P.X ≫ iP.hom.hom) ∈
      (unipotent χ).carrier Y := by
    have h := (Subgroup.mem_normalizer_iff.mp
      (centralizer_le_normalizer_unipotent χ _ (inv_mem hlZ)) _).mp hpl
    rwa [inv_inv, mul_assoc, mul_assoc, inv_mul_cancel, mul_one] at h
  have hoO : w ≫ fst O.X P.X ≫ iO.hom.hom ∈ (unipotent χ').carrier Y :=
    hO.2 ▸ SubgroupFunctor.mem_range.mpr ⟨w ≫ fst O.X P.X, Category.assoc _ _ _⟩
  refine ⟨hoO, hlZ, ?_, ?_⟩
  · simpa only [MonObj.comp_mul, GrpObj.comp_inv] using hlp
  · simp only [MonObj.comp_mul, GrpObj.comp_inv]
    group

variable (S : Type u) [CommRing S] [Algebra k S] [TopologicalSpace S] [IsTopologicalRing S]
  [IsLocalRing S] [IsOpenUnits S]

/-- **Opposite cell neighborhoods on `S`-points from an open immersion.** If the product map
`O × P → G` of representatives of `U(χ')` and `P(χ)` is an open immersion, then products of
identity neighborhoods of `G(S)` restricted to `U(χ')(S)`, `Z(χ)(S)` and `U(χ)(S)` are identity
neighborhoods for the scheme-point topology. -/
theorem ringCell_mem_nhds_one_of_isOpenImmersion (iO : O ⟶ G) (iP : P ⟶ G)
    (hO : (unipotent χ').IsRepresentedBy iO) (hP : (parabolic χ).IsRepresentedBy iP)
    (hcell : IsOpenImmersion
      ((fst O.X P.X ≫ iO.hom.hom) * (snd O.X P.X ≫ iP.hom.hom)).left) :
    letI : TopologicalSpace (ringTest k S ⟶ G.X) := schemePointTopology k G.X S
    ∀ A ∈ 𝓝 (1 : ringTest k S ⟶ G.X), ∀ B ∈ 𝓝 (1 : ringTest k S ⟶ G.X),
      ∀ C ∈ 𝓝 (1 : ringTest k S ⟶ G.X),
      {x : ringTest k S ⟶ G.X |
        ∃ a ∈ A ∩ ((unipotent χ').carrier (ringTest k S) : Set (ringTest k S ⟶ G.X)),
        ∃ b ∈ B ∩ ((centralizer χ).carrier (ringTest k S) : Set (ringTest k S ⟶ G.X)),
        ∃ c ∈ C ∩ ((unipotent χ).carrier (ringTest k S) : Set (ringTest k S ⟶ G.X)),
          x = a * b * c} ∈ 𝓝 (1 : ringTest k S ⟶ G.X) := by
  let tG : TopologicalSpace (ringTest k S ⟶ G.X) := schemePointTopology k G.X S
  let tOP : TopologicalSpace (ringTest k S ⟶ O.X ⊗ P.X) :=
    schemePointTopology k (O.X ⊗ P.X) S
  let tG' : TopologicalSpace (RingPoint k G.X S) := schemePointTopology k G.X S
  let tOP' : TopologicalSpace (RingPoint k (O.X ⊗ P.X) S) :=
    schemePointTopology k (O.X ⊗ P.X) S
  intro A hA B hB C hC
  have hpar : iP.hom.hom ∈ (parabolic χ).carrier P.X :=
    hP.2 ▸ SubgroupFunctor.mem_range.mpr ⟨𝟙 _, Category.id_comp _⟩
  obtain ⟨L, hL⟩ := exists_hasLimit χ hpar
  set fO : O.X ⊗ P.X ⟶ G.X := fst O.X P.X ≫ iO.hom.hom with hfO
  set fP : O.X ⊗ P.X ⟶ G.X := snd O.X P.X ≫ iP.hom.hom with hfP
  set fL : O.X ⊗ P.X ⟶ G.X := snd O.X P.X ≫ L with hfL
  set fC : O.X ⊗ P.X ⟶ G.X := fL⁻¹ * fP with hfC
  let e : ringTest k S ⟶ O.X ⊗ P.X := lift 1 1
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
  have hcont : ∀ f : O.X ⊗ P.X ⟶ G.X,
      Continuous (fun w : ringTest k S ⟶ O.X ⊗ P.X => w ≫ f) := fun f =>
    schemePointContinuity_proof k S (O.X ⊗ P.X) G.X f
  let W : Set (ringTest k S ⟶ O.X ⊗ P.X) :=
    (fun w => w ≫ fO) ⁻¹' A ∩ (fun w => w ≫ fL) ⁻¹' B ∩ (fun w => w ≫ fC) ⁻¹' C
  have hW : W ∈ 𝓝 e := by
    refine Filter.inter_mem (Filter.inter_mem ?_ ?_) ?_
    · exact (hcont fO).continuousAt.preimage_mem_nhds (by rwa [heO])
    · exact (hcont fL).continuousAt.preimage_mem_nhds (by rwa [heL])
    · exact (hcont fC).continuousAt.preimage_mem_nhds (by rwa [heC])
  have : IsOpenImmersion (fO * fP).left := hcell
  have himage : (fun w : ringTest k S ⟶ O.X ⊗ P.X => w ≫ (fO * fP)) '' W ∈
      𝓝 (1 : ringTest k S ⟶ G.X) := by
    have h := (isOpenEmbedding_schemePointMap k S (fO * fP)).isOpenMap.image_mem_nhds hW
    rwa [hem] at h
  refine Filter.mem_of_superset himage ?_
  rintro x ⟨w, ⟨⟨hwA, hwB⟩, hwC⟩, rfl⟩
  obtain ⟨hoO, hlZ, hcU, hdec⟩ := cell_point_decomposition_test k χ χ' iO iP hO hL w
  exact ⟨w ≫ fO, ⟨hwA, hoO⟩, w ≫ fL, ⟨hwB, hlZ⟩, w ≫ fC, ⟨hwC, hcU⟩, hdec⟩

end General

variable (S : Type u) [CommRing S] [Algebra k S] [TopologicalSpace S] [IsTopologicalRing S]
  [IsLocalRing S] [IsOpenUnits S]

/-- **The opposite cell on `S`-points is an identity neighborhood.** For a smooth affine
separated group `G` over a field `k`, a cocharacter `χ` and a local topological `k`-algebra `S`
with open units, every product of identity neighborhoods of `G(S)` restricted to `U(χ⁻¹)(S)`,
`Z(χ)(S)` and `U(χ)(S)` is an identity neighborhood of `G(S)` in its evaluation topology. -/
theorem affinePoints_opposite_cell_mem_nhds_one (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [IsSeparated G.X.hom]
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) :
    letI : TopologicalSpace (G.affinePoints (CommAlgCat.of k S)) :=
      G.affinePointsTopologicalSpace (CommAlgCat.of k S)
    ∀ A ∈ 𝓝 (1 : G.affinePoints (CommAlgCat.of k S)),
      ∀ B ∈ 𝓝 (1 : G.affinePoints (CommAlgCat.of k S)),
      ∀ C ∈ 𝓝 (1 : G.affinePoints (CommAlgCat.of k S)),
      {x : G.affinePoints (CommAlgCat.of k S) |
        ∃ a ∈ A ∩ ((unipotent (CommGroupScheme.groupHom
            (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ χ)).carrier
            ((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k S))) :
              Set (G.affinePoints (CommAlgCat.of k S))),
        ∃ b ∈ B ∩ ((centralizer χ).carrier
            ((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k S))) :
              Set (G.affinePoints (CommAlgCat.of k S))),
        ∃ c ∈ C ∩ ((unipotent χ).carrier
            ((algSpec (CommRingCat.of k)).obj (op (CommAlgCat.of k S))) :
              Set (G.affinePoints (CommAlgCat.of k S))),
          x = a * b * c} ∈ 𝓝 (1 : G.affinePoints (CommAlgCat.of k S)) := by
  let tA : TopologicalSpace (G.affinePoints (CommAlgCat.of k S)) :=
    G.affinePointsTopologicalSpace (CommAlgCat.of k S)
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  intro A hA B hB C hC
  have hcell := ringCell_mem_nhds_one_of_isOpenImmersion k χ _ S
    (Affine.unipotentHom _) (Affine.parabolicHom χ)
    (Affine.isRepresentedBy_unipotentHom _) (Affine.isRepresentedBy_parabolicHom χ)
    (oppositeCellStatement k G χ _ _ _ _
      (Affine.isRepresentedBy_unipotentHom _) (Affine.isRepresentedBy_parabolicHom χ))
  let e := G.affinePointsRingPointHomeomorph (CommAlgCat.of k S)
  have htop : schemePointTopology k G.X S =
      (inferInstance : TopologicalSpace (RingPoint k G.X S)) :=
    schemePointTopology_eq_affine k G.X S
  have hid : ∀ x : G.affinePoints (CommAlgCat.of k S),
      (e x : ringTest k S ⟶ G.X) = x := fun x =>
    G.affinePointsRingPointHomeomorph_apply (CommAlgCat.of k S) x
  have hto : ∀ s : Set (G.affinePoints (CommAlgCat.of k S)),
      s ∈ 𝓝 (1 : G.affinePoints (CommAlgCat.of k S)) →
      (s : Set (ringTest k S ⟶ G.X)) ∈
        @nhds (ringTest k S ⟶ G.X) (schemePointTopology k G.X S) 1 := by
    intro s hs
    have h := e.isOpenMap.image_mem_nhds hs
    have himg : e '' s = (s : Set (ringTest k S ⟶ G.X)) := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        rw [hid]
        exact hy
      · intro hx
        exact ⟨x, hx, hid x⟩
    rw [himg, hid] at h
    rw [htop]
    exact h
  have hfrom : ∀ s : Set (ringTest k S ⟶ G.X),
      s ∈ @nhds (ringTest k S ⟶ G.X) (schemePointTopology k G.X S) 1 →
      (s : Set (G.affinePoints (CommAlgCat.of k S))) ∈
        𝓝 (1 : G.affinePoints (CommAlgCat.of k S)) := by
    intro s hs
    rw [htop] at hs
    have hs' : s ∈ 𝓝 (e 1) := by rwa [hid]
    have h := e.continuous.continuousAt.preimage_mem_nhds hs'
    have hpre : e ⁻¹' s = (s : Set (G.affinePoints (CommAlgCat.of k S))) := by
      ext x
      change e x ∈ s ↔ x ∈ s
      rw [hid]
      exact Iff.rfl
    rwa [hpre] at h
  exact hfrom _ (hcell A (hto A hA) B (hto B hB) C (hto C hC))

end Langlands.GroupScheme.Dynamic
