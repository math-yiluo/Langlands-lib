import Langlands.GroupScheme.Reductive.RootDatum
import Langlands.GroupScheme.Rational.CrossTorusLieTransport
import Langlands.GroupScheme.Rational.CrossTorusWeylTransport
import Mathlib.LinearAlgebra.RootSystem.Hom

/-! # Actual root data under torus and ambient group isomorphisms -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

/-! ### Transport along an isomorphism of the ambient group -/

section AmbientIso

variable {k : Type u} [Field k] {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G H : GroupScheme (Spec (CommRingCat.of k))}

/-- A normalizing point stays normalizing after an isomorphism of the ambient groups. -/
theorem IsNormalizingPoint.comp_iso {i : T.toGrp ⟶ G} {n : Over.mk (𝟙 _) ⟶ G.X} {σ : T ≅ T}
    (h : IsNormalizingPoint i n σ) (Φ : G ≅ H) :
    IsNormalizingPoint (i ≫ Φ.hom) (n ≫ Φ.hom.hom.hom) σ := by
  unfold IsNormalizingPoint at h ⊢
  rw [Category.assoc, ← innerIso_hom_comp, ← Category.assoc, h, Category.assoc]

variable [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]

/-- A root datum of a torus stays its root datum after an isomorphism of the ambient groups. -/
theorem IsRootDatumOf.comp_iso {J : Type*} {i : T.toGrp ⟶ G}
    {P : RootDatum J (characterLattice T) (cocharacterLattice T)} (hP : IsRootDatumOf i P)
    (Φ : G ≅ H) : IsRootDatumOf (i ≫ Φ.hom) P := by
  refine ⟨hP.1, ?_, fun α => ?_⟩
  · have hs : i ≫ Φ.hom = CommGroupScheme.groupHom (Iso.refl T).hom ≫ (i ≫ Φ.hom) :=
      (Category.id_comp _).symm
    have hchar : ⇑(characterLattice.congr (Iso.refl T)) = id := by
      funext a
      exact Category.id_comp a
    rw [hP.2.1, ← roots_image_of_transport (Iso.refl T) Φ hs, hchar, Set.image_id]
  · obtain ⟨n, σ, hn, hσ⟩ := hP.2.2 α
    exact ⟨n ≫ Φ.hom.hom.hom, σ, hn.comp_iso Φ, hσ⟩

end AmbientIso

/-! ### Transport along isomorphisms of the torus and ambient group -/

variable {k : Type u} [Field k]
    {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
    {J : Type v}
    (e : T ≅ T')
    (P : RootDatum J (characterLattice T) (cocharacterLattice T))

/-- Push forward both lattices of a root datum through the actual torus isomorphism. -/
def torusTransportRootDatum :
    RootDatum J (characterLattice T') (cocharacterLattice T') :=
  P.map (Equiv.refl J) (characterLattice.congr e).toIntLinearEquiv
    (cocharacterLattice.congr e).toIntLinearEquiv

@[simp] theorem torusTransportRootDatum_root (j : J) :
    (torusTransportRootDatum e P).root j = characterLattice.congr e (P.root j) := rfl

@[simp] theorem torusTransportRootDatum_coroot (j : J) :
    (torusTransportRootDatum e P).coroot j = cocharacterLattice.congr e (P.coroot j) := rfl

@[simp] theorem torusTransportRootDatum_pairing
    (χ : characterLattice T) (ν : cocharacterLattice T) :
    (torusTransportRootDatum e P).toLinearMap
      (characterLattice.congr e χ) (cocharacterLattice.congr e ν) =
        P.toLinearMap χ ν := by
  change P.toLinearMap
    ((characterLattice.congr e).symm (characterLattice.congr e χ))
    ((cocharacterLattice.congr e).symm (cocharacterLattice.congr e ν)) = _
  rw [AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]

/-- The transported reflections intertwine the torus character equivalence. -/
theorem torusTransportRootDatum_reflection (j : J) (χ : characterLattice T) :
    (torusTransportRootDatum e P).reflection j (characterLattice.congr e χ) =
      characterLattice.congr e (P.reflection j χ) := by
  have hsub : ∀ y z : characterLattice T, characterLattice.congr e (y - z) =
      characterLattice.congr e y - characterLattice.congr e z := fun y z =>
    (characterLattice.congr e).toAddMonoidHom.map_sub y z
  have hzsmul : ∀ (n : ℤ) (y : characterLattice T), characterLattice.congr e (n • y) =
      n • characterLattice.congr e y := fun n y =>
    (characterLattice.congr e).toAddMonoidHom.map_zsmul n y
  simp only [RootPairing.reflection_apply, RootPairing.coroot', LinearMap.flip_apply,
    torusTransportRootDatum_root, torusTransportRootDatum_coroot,
    torusTransportRootDatum_pairing, hsub, hzsmul]

variable {P} {G H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    {i : T.toGrp ⟶ G} {i' : T'.toGrp ⟶ H}
    (f : G ≅ H)
    (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ i')

include f h in
/-- Transport along an actual torus and ambient-group isomorphism preserves
all three clauses of the actual-root-datum predicate. -/
theorem IsRootDatumOf.torusTransport (hP : IsRootDatumOf i P) :
    IsRootDatumOf i' (torusTransportRootDatum e P) := by
  refine ⟨?_, ?_, ?_⟩
  · ext χ ν
    obtain ⟨χ, rfl⟩ := (characterLattice.congr e).surjective χ
    obtain ⟨ν, rfl⟩ := (cocharacterLattice.congr e).surjective ν
    rw [torusTransportRootDatum_pairing, hP.1, latticePairing_congr]
  · rw [← roots_image_of_transport e f h, ← hP.2.1]
    change Set.range ((characterLattice.congr e) ∘ P.root) = _
    exact Set.range_comp _ _
  · intro j
    obtain ⟨n, τ, hn, hτ⟩ := hP.2.2 j
    refine ⟨_, _, hn.transport e f h, ?_⟩
    apply LinearEquiv.ext
    intro χ'
    obtain ⟨χ, rfl⟩ := (characterLattice.congr e).surjective χ'
    rw [torusTransportRootDatum_reflection, ← hτ]
    simp only [characterAut_apply, characterLattice.congr_apply, Iso.trans_inv,
      Iso.symm_inv, Category.assoc, Iso.hom_inv_id_assoc]

end Langlands.GroupScheme
