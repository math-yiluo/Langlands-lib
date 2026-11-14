import Langlands.GroupScheme.OrthogonalMatrix.CoverTorusTransport
import Langlands.GroupScheme.ClosedSubgroupMonomorphism

/-! # Character descent through the orthogonal-cover torus comparison -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.OrthogonalMatrix.StandardTorusTransport

variable {k : Type u} [Field k] {l : Type} [Fintype l] [DecidableEq l] [Nontrivial l]
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {i : T.toGrp ⟶ G}
  {pi : G ⟶ identityComponent (groupScheme l (CommRingCat.of k))}
  (c : StandardTorusTransport i pi)

/-- The comparison map has exactly the kernel of the original supplied cover
on every relative test scheme. -/
theorem comp_torusMap_eq_one_iff (U : Over (Spec (CommRingCat.of k)))
    (t : U ⟶ T.X) :
    t ≫ (CommGroupScheme.groupHom c.torusMap).hom.hom = 1 ↔
      t ≫ (i ≫ pi).hom.hom = 1 := by
  let H := identityComponent (groupScheme l (CommRingCat.of k))
  have : Mono (identityTorus l k).hom.hom :=
    (isClosedSubgroup_identityTorus l k).mono_overHom
  have : IsIso (H.innerIso c.point).hom.hom.hom :=
    (Grp.forget _).map_isIso (H.innerIso c.point).hom
  have hs : (t ≫ (i ≫ pi).hom.hom) ≫ (H.innerIso c.point).hom.hom.hom =
      (t ≫ (CommGroupScheme.groupHom c.torusMap).hom.hom) ≫
        (identityTorus l k).hom.hom := by
    simpa only [Grp.comp_hom_hom, Category.assoc] using
      congrArg (fun f => t ≫ f.hom.hom) c.square
  constructor
  · intro ht
    apply (cancel_mono (H.innerIso c.point).hom.hom.hom).mp
    rw [MonObj.one_comp, hs, ht, MonObj.one_comp]
  · intro ht
    apply (cancel_mono (identityTorus l k).hom.hom).mp
    rw [MonObj.one_comp, ← hs, ht, MonObj.one_comp]

/-- A character descends to standard orthogonal coordinates exactly when it
kills the original supplied cover kernel, retaining all relative test schemes. -/
theorem exists_character_comp_eq_iff (chi : characterLattice T) :
    (∃ psi : characterLattice
        (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift l)),
      c.torusMap ≫ psi = chi) ↔
      ∀ (U : Over (Spec (CommRingCat.of k))) (t : U ⟶ T.X),
        t ≫ (i ≫ pi).hom.hom = 1 →
          t ≫ (CommGroupScheme.groupHom chi).hom.hom = 1 := by
  have := c.flat
  have := c.surjective
  have := c.quasiCompact
  have h := characterLattice.exists_comp_eq_iff_kills_kernel
    (CommGroupScheme.groupHom c.torusMap) chi
  constructor
  · rintro ⟨psi, hpsi⟩ U t ht
    exact h.mp ⟨psi, congrArg CommGroupScheme.groupHom hpsi⟩ U t
      ((c.comp_torusMap_eq_one_iff U t).mpr ht)
  · intro hk
    obtain ⟨psi, hpsi⟩ := h.mpr fun U t ht => hk U t
      ((c.comp_torusMap_eq_one_iff U t).mp ht)
    exact ⟨psi, congrArg Additive.ofMul hpsi⟩

/-- Choose the character in standard coordinates descending a character which
kills the full original cover kernel. -/
def descendCharacter (chi : characterLattice T)
    (hk : ∀ (U : Over (Spec (CommRingCat.of k))) (t : U ⟶ T.X),
      t ≫ (i ≫ pi).hom.hom = 1 →
        t ≫ (CommGroupScheme.groupHom chi).hom.hom = 1) :
    characterLattice (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift l)) :=
  Classical.choose ((c.exists_character_comp_eq_iff chi).mpr hk)

@[simp] theorem torusMap_comp_descendCharacter (chi : characterLattice T)
    (hk : ∀ (U : Over (Spec (CommRingCat.of k))) (t : U ⟶ T.X),
      t ≫ (i ≫ pi).hom.hom = 1 →
        t ≫ (CommGroupScheme.groupHom chi).hom.hom = 1) :
    c.torusMap ≫ c.descendCharacter chi hk = chi :=
  Classical.choose_spec ((c.exists_character_comp_eq_iff chi).mpr hk)

end Langlands.GroupScheme.OrthogonalMatrix.StandardTorusTransport
