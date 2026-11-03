import Langlands.GroupScheme.ConjugacyBaseChange
import Langlands.GroupScheme.Torus.LatticeGalois
import Langlands.GroupScheme.Rational.RelativeWeylCharacterAction

/-! # Actual normalizer, centralizer and relative Weyl group transport -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {B : Scheme.{u}} {T T' : CommGroupScheme B} {G H : GroupScheme B}
variable {i : T.toGrp ⟶ G} {j : T'.toGrp ⟶ H}

/-- The inverse square for the supplied acting-group and ambient-group isomorphisms. -/
theorem torusTransport_inverse_square (e : T ≅ T') (f : G ≅ H)
    (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j) :
    j ≫ f.inv = CommGroupScheme.groupHom e.inv ≫ i := by
  rw [Iso.comp_inv_eq, Category.assoc, h, ← Category.assoc]
  change j = CommGroupScheme.groupHom (e.inv ≫ e.hom) ≫ j
  rw [Iso.inv_hom_id]
  exact (Category.id_comp j).symm

/-- A point normalizing the source embedding normalizes the target embedding
after applying the supplied ambient isomorphism. -/
theorem IsNormalizingPoint.transport (e : T ≅ T') (f : G ≅ H)
    (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j)
    {n : Over.mk (𝟙 B) ⟶ G.X} {σ : T ≅ T} (hn : IsNormalizingPoint i n σ) :
    IsNormalizingPoint j (n ≫ f.hom.hom.hom) (e.symm ≪≫ σ ≪≫ e) := by
  have hj : j = CommGroupScheme.groupHom e.inv ≫ i ≫ f.hom := by
    rw [h]
    change j = CommGroupScheme.groupHom (e.inv ≫ e.hom) ≫ j
    rw [Iso.inv_hom_id]
    exact (Category.id_comp j).symm
  change j ≫ (H.innerIso (n ≫ f.hom.hom.hom)).hom = _
  calc
    _ = (CommGroupScheme.groupHom e.inv ≫ i ≫ f.hom) ≫
        (H.innerIso (n ≫ f.hom.hom.hom)).hom := by rw [← hj]
    _ = CommGroupScheme.groupHom e.inv ≫
        (i ≫ (G.innerIso n).hom) ≫ f.hom := by
      rw [Category.assoc, Category.assoc, ← innerIso_hom_comp]
      simp only [Category.assoc]
    _ = CommGroupScheme.groupHom e.inv ≫
        (CommGroupScheme.groupHom σ.hom ≫ i) ≫ f.hom := by rw [hn]
    _ = _ := by
      simp only [Category.assoc, h]
      rfl

/-- Centralizing points are preserved by the same ambient map. -/
theorem mem_centralizerPoints_transport (e : T ≅ T') (f : G ≅ H)
    (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j)
    {n : Over.mk (𝟙 B) ⟶ G.X} (hn : n ∈ centralizerPoints i) :
    n ≫ f.hom.hom.hom ∈ centralizerPoints j := by
  change IsNormalizingPoint j (n ≫ f.hom.hom.hom) (Iso.refl T')
  have hn' := (show IsNormalizingPoint i n (Iso.refl T) from hn).transport e f h
  simpa only [Iso.refl_trans, Iso.symm_self_id] using hn'

/-- Centralizing the entire acting group is reflected and preserved. -/
theorem mem_centralizerPoints_transport_iff (e : T ≅ T') (f : G ≅ H)
    (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j)
    (n : Over.mk (𝟙 B) ⟶ G.X) :
    n ≫ f.hom.hom.hom ∈ centralizerPoints j ↔ n ∈ centralizerPoints i := by
  constructor
  · intro hn
    have hn' := mem_centralizerPoints_transport e.symm f.symm
      (torusTransport_inverse_square e f h) hn
    simpa only [Iso.symm_hom, Category.assoc, ← Grp.comp_hom_hom, Iso.hom_inv_id,
      Grp.id_hom_hom, Category.comp_id] using hn'
  · exact mem_centralizerPoints_transport e f h

/-- Normalizing points are reflected and preserved by the actual ambient map. -/
theorem mem_normalizerPoints_transport_iff (e : T ≅ T') (f : G ≅ H)
    (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j)
    (n : Over.mk (𝟙 B) ⟶ G.X) :
    n ≫ f.hom.hom.hom ∈ normalizerPoints j ↔ n ∈ normalizerPoints i := by
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨e ≪≫ σ ≪≫ e.symm, ?_⟩
    have hn := hσ.transport e.symm f.symm (torusTransport_inverse_square e f h)
    simpa only [Iso.symm_symm_eq, Iso.symm_hom, Category.assoc, ← Grp.comp_hom_hom,
      Iso.hom_inv_id, Grp.id_hom_hom, Category.comp_id] using hn
  · rintro ⟨σ, hσ⟩
    exact ⟨e.symm ≪≫ σ ≪≫ e, hσ.transport e f h⟩

/-- The ambient isomorphism restricts to the actual base normalizer point groups. -/
def normalizerPointsTransportEquiv (e : T ≅ T') (f : G ≅ H)
    (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j) :
    normalizerPoints i ≃* normalizerPoints j where
  toFun n := ⟨n.val ≫ f.hom.hom.hom,
    (mem_normalizerPoints_transport_iff e f h n.val).mpr n.property⟩
  invFun n := ⟨n.val ≫ f.inv.hom.hom,
    (mem_normalizerPoints_transport_iff e.symm f.symm
      (torusTransport_inverse_square e f h) n.val).mpr n.property⟩
  left_inv n := Subtype.ext (by
    simp only [Category.assoc, ← Grp.comp_hom_hom, Iso.hom_inv_id,
      Grp.id_hom_hom, Category.comp_id])
  right_inv n := Subtype.ext (by
    simp only [Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id,
      Grp.id_hom_hom, Category.comp_id])
  map_mul' n m := Subtype.ext (MonObj.mul_comp _ _ _)

@[simp] theorem normalizerPointsTransportEquiv_apply (e : T ≅ T') (f : G ≅ H)
    (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j)
    (n : normalizerPoints i) :
    (normalizerPointsTransportEquiv e f h n : Over.mk (𝟙 B) ⟶ H.X) =
      n.val ≫ f.hom.hom.hom := rfl

@[simp] theorem normalizerPointsTransportEquiv_symm_apply (e : T ≅ T') (f : G ≅ H)
    (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j)
    (n : normalizerPoints j) :
    ((normalizerPointsTransportEquiv e f h).symm n : Over.mk (𝟙 B) ⟶ G.X) =
      n.val ≫ f.inv.hom.hom := rfl

/-- The same ambient isomorphism restricts to the full centralizer point groups. -/
def centralizerPointsTransportEquiv (e : T ≅ T') (f : G ≅ H)
    (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j) :
    centralizerPoints i ≃* centralizerPoints j where
  toFun (n : centralizerPoints i) := ⟨n.val ≫ f.hom.hom.hom,
    mem_centralizerPoints_transport (i := i) (j := j) e f h n.property⟩
  invFun (n : centralizerPoints j) := ⟨n.val ≫ f.inv.hom.hom,
    mem_centralizerPoints_transport (i := j) (j := i) e.symm f.symm
      (torusTransport_inverse_square e f h) n.property⟩
  left_inv n := Subtype.ext (by
    simp only [Category.assoc, ← Grp.comp_hom_hom, Iso.hom_inv_id,
      Grp.id_hom_hom, Category.comp_id])
  right_inv n := Subtype.ext (by
    simp only [Category.assoc, ← Grp.comp_hom_hom, Iso.inv_hom_id,
      Grp.id_hom_hom, Category.comp_id])
  map_mul' n m := Subtype.ext (MonObj.mul_comp _ _ _)

/-- The full-character actions intertwine under the actual torus lattice identification. -/
theorem weylAction_transport [Mono i.hom.hom.left] [Mono j.hom.hom.left]
    (e : T ≅ T') (f : G ≅ H)
    (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j)
    (n : normalizerPoints i) (χ : characterLattice T) :
    weylAction j (normalizerPointsTransportEquiv e f h n) (characterLattice.congr e χ) =
      characterLattice.congr e (weylAction i n χ) := by
  rw [weylAction_eq j (n := normalizerPointsTransportEquiv e f h n)
    ((isNormalizingPoint_normalizingAut i n).transport e f h)]
  simp only [Iso.trans_inv, Iso.symm_inv, characterLattice.congr_apply,
    Category.assoc, Iso.hom_inv_id_assoc, weylAction_apply]

section Relative

variable {k : Type u} [Field k]
variable {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
variable {G H : GroupScheme (Spec (CommRingCat.of k))}
variable {i : T.toGrp ⟶ G} {j : T'.toGrp ⟶ H}

/-- The transported normalizer identifies its centralizer subgroup exactly. -/
theorem normalizerPointsTransportEquiv_map_centralizer
    (e : T ≅ T') (f : G ≅ H)
    (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j) :
    ((centralizerPoints i).subgroupOf (normalizerPoints i)).map
        (normalizerPointsTransportEquiv e f h).toMonoidHom =
      (centralizerPoints j).subgroupOf (normalizerPoints j) := by
  ext n
  rw [Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact mem_centralizerPoints_transport e f h hm
  · intro hn
    refine ⟨(normalizerPointsTransportEquiv e f h).symm n, ?_,
      (normalizerPointsTransportEquiv e f h).apply_symm_apply n⟩
    exact mem_centralizerPoints_transport e.symm f.symm
      (torusTransport_inverse_square e f h) hn

/-- An equivalence of the actual rational Weyl quotients `N(k)/Z(k)`.
This is a quotient of base points. -/
def relativeWeylTransportEquiv (e : T ≅ T') (f : G ≅ H)
    (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j) :
    relativeWeylGroup i ≃* relativeWeylGroup j :=
  QuotientGroup.congr _ _ (normalizerPointsTransportEquiv e f h)
    (normalizerPointsTransportEquiv_map_centralizer e f h)

@[simp] theorem relativeWeylTransportEquiv_mk (e : T ≅ T') (f : G ≅ H)
    (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j)
    (n : normalizerPoints i) :
    relativeWeylTransportEquiv e f h (QuotientGroup.mk n) =
      QuotientGroup.mk (normalizerPointsTransportEquiv e f h n) := rfl

/-- The rational Weyl quotient equivalence intertwines the entire character actions. -/
theorem relativeWeylCharacterAction_transport
    [Mono i.hom.hom.left] [Mono j.hom.hom.left]
    (e : T ≅ T') (f : G ≅ H)
    (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j)
    (w : relativeWeylGroup i) (χ : characterLattice T) :
    relativeWeylCharacterAction j (relativeWeylTransportEquiv e f h w)
        (characterLattice.congr e χ) =
      characterLattice.congr e (relativeWeylCharacterAction i w χ) := by
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective w
  exact weylAction_transport e f h n χ

end Relative

end Langlands.GroupScheme
