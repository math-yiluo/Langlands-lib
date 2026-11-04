import Langlands.GroupScheme.Rational.CrossTorusWeylTransport
import Langlands.GroupScheme.Torus.SplitLatticeBaseChange
import Langlands.GroupScheme.Torus.WeylImageFiniteStatement
import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic

/-! # Transport of the full character-lattice Weyl image -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Transport

variable {S : Scheme.{u}} {T T' : CommGroupScheme S} {G H : GroupScheme S}
  {i : T.toGrp ⟶ G} {j : T'.toGrp ⟶ H}

/-- Conjugation of integral character automorphisms by the actual lattice
identification induced by an isomorphism of commutative group schemes. -/
def characterAutomorphismTransport (e : T ≅ T') :
    (characterLattice T ≃ₗ[ℤ] characterLattice T) ≃*
      (characterLattice T' ≃ₗ[ℤ] characterLattice T') :=
  ((LinearMap.GeneralLinearGroup.generalLinearEquiv ℤ (characterLattice T)).symm.trans
    (LinearMap.GeneralLinearGroup.congrLinearEquiv
      (characterLattice.congr e).toIntLinearEquiv)).trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv ℤ (characterLattice T'))

@[simp]
theorem characterAutomorphismTransport_apply (e : T ≅ T')
    (a : characterLattice T ≃ₗ[ℤ] characterLattice T) (χ : characterLattice T') :
    characterAutomorphismTransport e a χ =
      characterLattice.congr e (a ((characterLattice.congr e).symm χ)) := rfl

/-- The transported full-character action is conjugate to the source action. -/
theorem characterAutomorphismTransport_weylAction
    [Mono i.hom.hom.left] [Mono j.hom.hom.left]
    (e : T ≅ T') (f : G ≅ H)
    (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j)
    (n : normalizerPoints i) :
    characterAutomorphismTransport e (weylAction i n) =
      weylAction j (normalizerPointsTransportEquiv e f h n) := by
  apply LinearEquiv.ext
  intro χ'
  obtain ⟨χ, rfl⟩ := (characterLattice.congr e).surjective χ'
  rw [characterAutomorphismTransport_apply, AddEquiv.symm_apply_apply]
  exact (weylAction_transport e f h n χ).symm

/-- Conjugation identifies the actual full Weyl-image subgroups. -/
theorem weylImage_map_transport
    [Mono i.hom.hom.left] [Mono j.hom.hom.left]
    (e : T ≅ T') (f : G ≅ H)
    (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j) :
    (weylImage i).map (characterAutomorphismTransport e).toMonoidHom =
      weylImage j := by
  ext a
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨n, rfl⟩ := hb
    exact ⟨normalizerPointsTransportEquiv e f h n,
      (characterAutomorphismTransport_weylAction e f h n).symm⟩
  · rintro ⟨n, rfl⟩
    refine ⟨weylAction i ((normalizerPointsTransportEquiv e f h).symm n),
      ⟨_, rfl⟩, ?_⟩
    change characterAutomorphismTransport e
      (weylAction i ((normalizerPointsTransportEquiv e f h).symm n)) = _
    rw [characterAutomorphismTransport_weylAction e f h,
      MulEquiv.apply_symm_apply]

/-- The full Weyl images are multiplicatively equivalent under an actual
commuting square of acting-group and ambient-group isomorphisms. -/
def weylImageTransportEquiv
    [Mono i.hom.hom.left] [Mono j.hom.hom.left]
    (e : T ≅ T') (f : G ≅ H)
    (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j) :
    weylImage i ≃* weylImage j :=
  ((characterAutomorphismTransport e).subgroupMap (weylImage i)).trans
    (MulEquiv.subgroupCongr (weylImage_map_transport e f h))

/-- Finiteness of the entire Weyl image is invariant under such a square. -/
theorem finite_weylImage_iff_of_transport
    [Mono i.hom.hom.left] [Mono j.hom.hom.left]
    (e : T ≅ T') (f : G ≅ H)
    (h : i ≫ f.hom = CommGroupScheme.groupHom e.hom ≫ j) :
    Finite (weylImage i) ↔ Finite (weylImage j) := by
  let a := weylImageTransportEquiv e f h
  constructor
  · intro hi
    have := hi
    exact Finite.of_surjective a a.surjective
  · intro hj
    have := hj
    exact Finite.of_injective a a.injective

end Transport

/-- To prove full Weyl-image finiteness for arbitrary closed split tori, it
suffices to prove it for the standard split tori of every finite rank. -/
theorem splitTorusWeylImageFinite_of_standard
    (hstandard : ∀ (k : Type u) [Field k]
      (G : GroupScheme (Spec (CommRingCat.of k)))
      [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
      (I : Type u) [Finite I] (j : splitTorus (Spec (CommRingCat.of k)) I ⟶ G)
      (hj : IsClosedSubgroup j),
      haveI : IsClosedImmersion j.hom.hom.left := hj
      Finite (weylImage (T := splitTorus.commGroupScheme _ I) j)) :
    SplitTorusWeylImageFiniteStatement.{u} := by
  intro k _ G _ _ T hT i hi
  have : IsClosedImmersion i.hom.hom.left := hi
  obtain ⟨I, hI, ⟨e⟩⟩ := hT
  let eC : T ≅ splitTorus.commGroupScheme (Spec (CommRingCat.of k)) I :=
    CommGroupScheme.isoOfGroupIso e
  let j := e.inv ≫ i
  have hj : IsClosedSubgroup j := by
    change IsClosedImmersion (e.inv.hom.hom.left ≫ i.hom.hom.left)
    infer_instance
  have : IsClosedImmersion j.hom.hom.left := hj
  have hsquare : i ≫ (Iso.refl G).hom = CommGroupScheme.groupHom eC.hom ≫ j := by
    change i ≫ 𝟙 G = e.hom ≫ e.inv ≫ i
    rw [Iso.hom_inv_id_assoc, Category.comp_id]
  exact (finite_weylImage_iff_of_transport eC (Iso.refl G) hsquare).mpr
    (hstandard k G I j hj)

end Langlands.GroupScheme
