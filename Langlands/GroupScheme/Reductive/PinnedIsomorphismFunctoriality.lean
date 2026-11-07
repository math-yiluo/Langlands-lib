import Langlands.GroupScheme.Reductive.PinnedIsomorphismExistence
import Langlands.GroupScheme.Reductive.PinnedIsomorphismProof

/-! # Functorial actual pinned lifts -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.SplitPinning

variable {k : Type u} [Field k]
  {G H C : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [IsAffineHom H.X.hom] [IsAffineHom C.X.hom]
  {p : SplitPinning G} {q : SplitPinning H} {r : SplitPinning C}

namespace Iso

/-- The identity actual pinned isomorphism. -/
def refl (p : SplitPinning G) : SplitPinning.Iso p p where
  torusIso := CategoryTheory.Iso.refl _
  groupIso := CategoryTheory.Iso.refl _
  square := by
    change p.inclusion ≫ 𝟙 G = 𝟙 p.torus.toGrp ≫ p.inclusion
    simp
  indexEquiv := Equiv.refl _
  root_eq := by
    intro a
    change (𝟙 p.torus) ≫ p.rootDatum.root a = p.rootDatum.root a
    exact Category.id_comp _
  coroot_eq := by
    intro a
    change p.rootDatum.coroot a ≫ 𝟙 p.torus = p.rootDatum.coroot a
    exact Category.comp_id _
  simple_iff := by intro a; rfl
  rootVector_eq := by
    intro a
    apply Additive.toMul.injective
    apply Subtype.ext
    simp only [lieKernelHomLinear_val, CategoryTheory.Iso.refl_hom,
      Grp.id_hom_hom, Category.comp_id]
    rfl

/-- Composition of actual pinned isomorphisms, in diagrammatic order. -/
def trans (f : SplitPinning.Iso p q) (g : SplitPinning.Iso q r) :
    SplitPinning.Iso p r where
  torusIso := f.torusIso ≪≫ g.torusIso
  groupIso := f.groupIso ≪≫ g.groupIso
  square := by
    rw [CategoryTheory.Iso.trans_hom, ← Category.assoc, f.square,
      Category.assoc, g.square, ← Category.assoc]
    rfl
  indexEquiv := f.indexEquiv.trans g.indexEquiv
  root_eq := by
    intro a
    change (g.torusIso.inv ≫ f.torusIso.inv) ≫ p.rootDatum.root a = _
    rw [Category.assoc]
    change characterLattice.congr g.torusIso
      (characterLattice.congr f.torusIso (p.rootDatum.root a)) = _
    rw [f.root_eq]
    exact g.root_eq _
  coroot_eq := by
    intro a
    change p.rootDatum.coroot a ≫ (f.torusIso.hom ≫ g.torusIso.hom) = _
    rw [← Category.assoc]
    change cocharacterLattice.congr g.torusIso
      (cocharacterLattice.congr f.torusIso (p.rootDatum.coroot a)) = _
    rw [f.coroot_eq]
    exact g.coroot_eq _
  simple_iff := fun a => (f.simple_iff a).trans (g.simple_iff _)
  rootVector_eq := by
    intro a
    rw [CategoryTheory.Iso.trans_hom, Lie.targetMapLinear_comp,
      LinearMap.comp_apply, f.rootVector_eq, g.rootVector_eq]
    rfl

/-- The actual torus map and root-index equivalence determine a pinned isomorphism. -/
theorem ext_torus_index {f g : SplitPinning.Iso p q}
    (ht : f.torusIso = g.torusIso) (hi : f.indexEquiv = g.indexEquiv) : f = g :=
  PinnedIsomorphism.iso_ext p q pinnedAutomorphismRigidity ht hi

@[simp]
theorem refl_trans (f : SplitPinning.Iso p q) : (refl p).trans f = f :=
  ext_torus_index (by simp [trans, refl]) (by ext; rfl)

@[simp]
theorem trans_refl (f : SplitPinning.Iso p q) : f.trans (refl q) = f :=
  ext_torus_index (by simp [trans, refl]) (by ext; rfl)

end Iso

/-- A lift with the prescribed full character map and index map is the chosen lift.
The perfect pairing already forces the prescribed cocharacter map. -/
theorem eq_isoOfRootDatumEquiv
    (e : RootPairing.Equiv p.rootDatum q.rootDatum)
    (hsimple : ∀ a, a ∈ p.base.support ↔ e.indexEquiv a ∈ q.base.support)
    (f : SplitPinning.Iso p q)
    (hchar : (characterLattice.congr f.torusIso).toIntLinearEquiv = e.weightEquiv)
    (hindex : f.indexEquiv = e.indexEquiv) :
    f = p.isoOfRootDatumEquiv q e hsimple := by
  apply Iso.ext_torus_index
  · apply p.isSplitTorus.iso_ext_of_character_congr
    ext χ
    exact (DFunLike.congr_fun hchar χ).trans
      (DFunLike.congr_fun (p.isoOfRootDatumEquiv_character q e hsimple) χ).symm
  · rw [hindex, isoOfRootDatumEquiv_indexEquiv]

/-- The chosen actual lift of the identity root-datum equivalence is the identity. -/
@[simp]
theorem isoOfRootDatumEquiv_id (p : SplitPinning G) :
    p.isoOfRootDatumEquiv p (RootPairing.Equiv.id p.rootDatum) (fun _ => Iff.rfl) =
      Iso.refl p := by
  symm
  apply eq_isoOfRootDatumEquiv
  · ext χ
    change (𝟙 p.torus) ≫ χ = χ
    exact Category.id_comp _
  · rfl

/-- Chosen actual lifts compose exactly, including their torus and root-index data. -/
theorem isoOfRootDatumEquiv_comp
    (e : RootPairing.Equiv p.rootDatum q.rootDatum)
    (d : RootPairing.Equiv q.rootDatum r.rootDatum)
    (he : ∀ a, a ∈ p.base.support ↔ e.indexEquiv a ∈ q.base.support)
    (hd : ∀ a, a ∈ q.base.support ↔ d.indexEquiv a ∈ r.base.support) :
    p.isoOfRootDatumEquiv r (RootPairing.Equiv.comp d e)
        (fun a => (he a).trans (hd _)) =
      (p.isoOfRootDatumEquiv q e he).trans (q.isoOfRootDatumEquiv r d hd) := by
  symm
  apply eq_isoOfRootDatumEquiv
  · ext χ
    change ((q.isoOfRootDatumEquiv r d hd).torusIso.inv ≫
      (p.isoOfRootDatumEquiv q e he).torusIso.inv) ≫ χ =
        d.weightEquiv (e.weightEquiv χ)
    rw [Category.assoc]
    change characterLattice.congr (q.isoOfRootDatumEquiv r d hd).torusIso
      (characterLattice.congr (p.isoOfRootDatumEquiv q e he).torusIso χ) =
        d.weightEquiv (e.weightEquiv χ)
    have h : characterLattice.congr (p.isoOfRootDatumEquiv q e he).torusIso χ =
        e.weightEquiv χ :=
      DFunLike.congr_fun (p.isoOfRootDatumEquiv_character q e he) χ
    rw [h]
    exact DFunLike.congr_fun (q.isoOfRootDatumEquiv_character r d hd) _
  · ext a
    simp only [Iso.trans, Equiv.trans_apply, isoOfRootDatumEquiv_indexEquiv]
    rfl

end Langlands.GroupScheme.SplitPinning
