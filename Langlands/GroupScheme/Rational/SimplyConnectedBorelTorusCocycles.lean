import Langlands.GroupScheme.Rational.GaloisPinningCorootAction
import Langlands.GroupScheme.Reductive.StarActionQuasiSplitProof
import Langlands.GroupScheme.Absolute.GeometricBorelBaseChange
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof
import Langlands.GroupScheme.Torus.FundamentalWeightPermutation
import Langlands.GroupScheme.Torus.InducedWeilDecompositionProof
import Langlands.GroupScheme.Torus.WeilRestrictionSemilocalCocycle
import Langlands.GroupScheme.Reductive.InnerStarWeights

/-! # Induced maximal tori of Borel subgroups of simply connected groups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 850000

section BorelTorus

variable {F : Type u} [Field F] {B G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {T : CommGroupScheme (Spec (CommRingCat.of F))}

/-- A maximal torus of a rational Borel in a simply connected group
is induced, with the Galois-permuted basis of fundamental weights. -/
theorem isInducedTorus_of_borelMaximalTorus
    (hsc : IsSimplyConnected G) (i : B ⟶ G) (hi : IsGeometricBorelSubgroup i)
    (t : T.toGrp ⟶ B) (ht : IsMaximalTorus (t ≫ i)) : IsInducedTorus T := by
  classical
  let hG := hsc.isSemisimple.isConnectedReductive
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom B.X.hom := hi.1.isClosedSubgroup.isAffineHom
  let : Smooth B.X.hom := hi.1.smooth
  obtain ⟨E, _, _, _, _, hTE⟩ := torusFiniteGaloisSplitting F T.toGrp ht.1
  let b := algebraBaseMap F E
  let C := GroupScheme.baseChange b
  let TE := (CommGroupScheme.baseChange b).obj T
  let GE := C.obj G
  let BE := C.obj B
  let g := t ≫ i
  let gE : TE.toGrp ⟶ GE := C.map g
  let : IsAffineHom GE.X.hom := inferInstanceAs (IsAffineHom (pullback.snd G.X.hom b))
  let : IsAffineHom BE.X.hom := inferInstanceAs (IsAffineHom (pullback.snd B.X.hom b))
  let : LocallyOfFiniteType GE.X.hom := inferInstanceAs (LocallyOfFiniteType (pullback.snd G.X.hom b))
  have hGE := connectedReductiveFieldExtensionStatement F E G hG
  have hmax : IsMaximalTorus (T := TE) gE := (maximalTorusBaseChange F E G T g ht.1 ht.2.1).mp ht
  have hsplit : IsSplitTorus TE.toGrp := hTE
  obtain ⟨J, hJ, P, hP, hred⟩ := rootDatumExistence E GE hGE TE hsplit gE hmax
  let : Finite J := hJ
  let : P.IsReduced := hred
  have hcomp : C.map t ≫ C.map i = gE := (C.map_comp t i).symm
  have hB := (hi.baseChange hG b).1
  obtain ⟨ν, hνreg, hrep⟩ :=
    (regularCocharacterBorel E GE hGE TE gE hsplit hmax).2.2 BE (C.map i) (C.map t) hB hcomp
  have hν (a : J) : P.root' a ν ≠ 0 := by
    change P.toLinearMap (P.root a) ν ≠ 0
    rw [hP.1]
    exact hνreg _ (by rw [← hP.2.1]; exact Set.mem_range_self a)
  let Δ := IsRootDatumOf.regularCocharacterBase F E (P := P) ν hν
  have hpos (a : J) : Δ.IsPos a ↔ P.root a ∈ roots (C.map t) := by
    rw [IsRootDatumOf.regularCocharacterBase_isPos F E g hP ν hν a,
      StarActionQuasiSplit.mem_roots_iff_of_isRepresentedBy_parabolic_of_comp hsplit (C.map i) (C.map t)
        gE hcomp ν hrep hνreg]
    have hr : P.root a ∈ roots gE := by rw [← hP.2.1]; exact Set.mem_range_self a
    exact ⟨fun h => ⟨hr, h⟩, fun h => h.2⟩
  let p : GaloisPinningData F E G :=
    { torus := T
      inclusion := g
      isConnectedReductive := hGE
      isSplitTorus := hsplit
      isMaximalTorus := hmax
      rootIndex := J
      rootDatum := P
      isRootDatum := hP
      isReduced := hred
      base := Δ
      pinning := RootPinning.ofSplitMaximalTorus hGE hsplit gE hmax P hP Δ }
  let hspan : P.corootSpan ℤ = ⊤ := p.corootSpan_eq_top_of_simplyConnected hsc
  let W := Langlands.RootDatum.fundamentalWeightBasis P Δ hspan
  refine ⟨E, inferInstance, inferInstance, inferInstance, inferInstance, hTE, Δ.support, W, ?_⟩
  intro σ a
  let e := IsRootDatumOf.galoisSimpleRootIndexAction F E g hP Δ t hpos σ
  refine ⟨e a, ?_⟩
  apply Langlands.RootDatum.fundamentalWeightBasis_permutation P Δ hspan
    (characterLattice.galoisRepresentation F E T σ)
    (cocharacterLattice.galoisRepresentation F E T σ) e
  · intro x y
    rw [hP.1]
    exact latticePairing_galoisRepresentation F E T σ x y
  · intro j
    exact (p.galoisAction_coroot σ j.val).symm

end BorelTorus

namespace Cocycle

variable {F : Type u} [Field F] {T : CommGroupScheme (Spec (CommRingCat.of F))}
  {U : Over (Spec (CommRingCat.of F))}
  [IsAffineHom U.hom] [Flat U.hom] [Surjective U.hom]

/-- Cocycles in an induced torus over a field are trivial on the same
affine faithfully flat cover, by the Weil form of Hilbert 90. -/
theorem isTrivial_of_isInducedTorus (ξ : Cocycle T.toGrp U) (hT : IsInducedTorus T) :
    ξ.IsTrivial := by
  have h := hT
  obtain ⟨E, _, _, _, _, hTE, _⟩ := h
  obtain ⟨n, M, ⟨e⟩⟩ := inducedTorusWeilDecomposition F E T hTE hT
  let f : T.toGrp ≅ WeilGm.groupScheme (CommRingCat.of F) (∀ i, M i) :=
    ⟨CommGroupScheme.groupHom e.hom, CommGroupScheme.groupHom e.inv,
      congrArg CommGroupScheme.groupHom e.hom_inv_id,
      congrArg CommGroupScheme.groupHom e.inv_hom_id⟩
  exact Cocycle.isTrivial_of_weilPresentation_of_semilocal
    (A := CommRingCat.of F) (B := CommRingCat.of (∀ i, M i)) ξ f

end Cocycle
end Langlands.GroupScheme
