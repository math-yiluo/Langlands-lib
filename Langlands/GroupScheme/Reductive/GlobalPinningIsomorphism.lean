import Langlands.GroupScheme.Reductive.GlobalPinningComparisonDescent
import Langlands.GroupScheme.Reductive.RepresentationWeightsFibreComparison
import Mathlib.AlgebraicGeometry.Cover.Sigma

/-! # Based global isomorphisms from coherent actual root frames -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme.CoordinateRootDatum

section Torus

variable {I J I' J' : Type u} [Fintype I] [Fintype I']
    {P : RootDatum J (I → ℤ) (I → ℤ)} {Q : RootDatum J' (I' → ℤ) (I' → ℤ)}
    (θ : RootPairing.Equiv Q P)

/-- The full character-lattice equivalence gives the actual coordinate-torus
isomorphism on every scheme. -/
def datumTorusIso (S : Scheme.{u}) : splitTorus S I ≅ splitTorus S I' := by
  classical
  exact LocalSplitCell.exponentEquivGroupIso S θ.weightEquiv.symm

/-- The coordinate-torus isomorphism commutes with actual base change. -/
theorem datumTorusIso_baseChange {S T : Scheme.{u}} (a : T ⟶ S) :
    (baseChange a).map (datumTorusIso θ S).hom =
      (splitTorus.baseChangeIso a I).hom ≫ (datumTorusIso θ T).hom ≫
        (splitTorus.baseChangeIso a I').inv := by
  classical
  exact splitTorus.baseChange_groupHom_exponentEquivIso S a θ.weightEquiv.symm

/-- The entire torus character formula holds on every relative test scheme. -/
theorem datumTorusIso_characters (S : Scheme.{u})
    (U : Over S) (x : U ⟶ (splitTorus S I).X) (m : I' → ℤ) :
    ∏ j, splitTorus.pointsEquiv I' U
        (x ≫ (datumTorusIso θ S).hom.hom.hom) j ^ m j =
      ∏ i, splitTorus.pointsEquiv I U x i ^ θ.weightMap m i := by
  classical
  have ht : (datumTorusIso θ S).hom ≫
      CommGroupScheme.groupHom (splitTorus.exponentCharacter S I' m) =
        CommGroupScheme.groupHom (splitTorus.exponentCharacter S I (θ.weightMap m)) := by
    change CommGroupScheme.groupHom
      (splitTorus.exponentHom S I I' θ.weightMap ≫
        splitTorus.exponentCharacter S I' m) = _
    exact congrArg CommGroupScheme.groupHom
      (splitTorus.exponentHom_comp_exponentCharacter S I I' θ.weightMap m)
  rw [← splitTorus.pointsEquiv_exponentCharacter,
    Category.assoc, ← Grp.comp_hom_hom, ht,
    splitTorus.pointsEquiv_exponentCharacter]

end Torus

section Pairing

variable {S : Scheme.{u}} [Nonempty S] {I J : Type u} [Fintype I]
    {G : GroupScheme S} [IsAffineHom G.X.hom]
    (t : splitTorus S I ⟶ G) (P : RootDatum J (I → ℤ) (I → ℤ))
    (hP : IsGlobalCoordinateRootDatumOf I G t P)

include hP in
/-- One actual residue-field realization determines the whole coordinate
pairing over a nonempty base. -/
theorem pairing_of_globalCoordinateRootDatum (m n : I → ℤ) :
    P.toLinearMap m n = ∑ i, m i * n i := by
  let s : S := Classical.ofNonempty
  exact pairing_of_isRootDatumOf (S.residueField s) P _
    (hP.2.2 (S.residueField s) (S.fromSpecResidueField s)) m n

end Pairing

private def pinningAffineCover (S : Scheme.{u}) :
    S.Cover.{u} Scheme.etalePrecoverage :=
  Scheme.Cover.mkOfCovers S
    (fun i : S.affineOpenCover.I₀ => Spec (S.affineOpenCover.X i))
    S.affineOpenCover.f
    (fun s => ⟨S.affineOpenCover.idx s, S.affineOpenCover.covers s⟩)
    (fun _ => inferInstance)

private instance pinningProjection_etale (S : Scheme.{u}) :
    Etale (Descent.CoverIsomorphism.projection S.affineOpenCover.f) :=
  (pinningAffineCover S).sigma.map_prop PUnit.unit

private instance pinningProjection_surjective (S : Scheme.{u}) :
    Surjective (Descent.CoverIsomorphism.projection S.affineOpenCover.f) := by
  constructor
  intro s
  obtain ⟨i, x, hx⟩ := (pinningAffineCover S).sigma.exists_eq s
  exact ⟨x, hx⟩

section Groups

variable {S : Scheme.{u}} {I J I' J' : Type u}
    [Fintype I] [Fintype J] [Fintype I'] [Fintype J']
    {G H : GroupScheme S} [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    (t : splitTorus S I ⟶ G) (t' : splitTorus S I' ⟶ H)
    (P : RootDatum J (I → ℤ) (I → ℤ)) (Q : RootDatum J' (I' → ℤ) (I' → ℤ))
    (hG : IsReductive G) (ht : IsClosedSubgroup t)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) t)
    (hP : IsGlobalCoordinateRootDatumOf I G t P)
    (hH : IsReductive H) (ht' : IsClosedSubgroup t')
    (hmax' : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I') t')
    (hQ : IsGlobalCoordinateRootDatumOf I' H t' Q)
    (F : AffineRootFrames t P) (hF : AffineRootFrames.IsCoherent t P F)
    (F' : AffineRootFrames t' Q) (hF' : AffineRootFrames.IsCoherent t' Q F')
    (b : P.Base) (c : Q.Base)
    (θ : RootPairing.Equiv Q P)
    (hθ : ∀ s : J', s ∈ c.support ↔ θ.indexEquiv s ∈ b.support)
    (hAffine : AffinePinnedIsomorphismTheoremStatement.{u})

/-- The actual global group isomorphism, using the canonical affine cover.
Only the actual root frames and the affine theorem remain supplied inputs. -/
def globalPinnedIso : G ≅ H := by
  let R : S.affineOpenCover.I₀ → Type u := fun i => S.affineOpenCover.X i
  let a : ∀ i, Spec (CommRingCat.of (R i)) ⟶ S := S.affineOpenCover.f
  letI : Etale (Descent.CoverIsomorphism.projection a) := pinningProjection_etale S
  letI : Surjective (Descent.CoverIsomorphism.projection a) :=
    pinningProjection_surjective S
  exact globalIsoOfCoherentFrames t t' P Q hG ht hmax hP hH ht' hmax' hQ
    F hF F' hF' b c θ hθ hAffine R a

/-- The global isomorphism recovers the normalized canonical comparison on
each member of the canonical affine cover. -/
theorem globalPinnedIso_on_member (i : S.affineOpenCover.I₀) :
    (baseChange (S.affineOpenCover.f i)).mapIso
        (globalPinnedIso t t' P Q hG ht hmax hP hH ht' hmax' hQ
          F hF F' hF' b c θ hθ hAffine) =
      affineFrameIsoFamily t t' P Q hG ht hmax hP hH ht' hmax' hQ
        F F' b c θ hθ hAffine
        (fun i => (S.affineOpenCover.X i : Type u)) S.affineOpenCover.f i := by
  let R : S.affineOpenCover.I₀ → Type u := fun i => S.affineOpenCover.X i
  let a : ∀ i, Spec (CommRingCat.of (R i)) ⟶ S := S.affineOpenCover.f
  let : Etale (Descent.CoverIsomorphism.projection a) := pinningProjection_etale S
  let : Surjective (Descent.CoverIsomorphism.projection a) :=
    pinningProjection_surjective S
  exact globalIsoOfCoherentFrames_on_member t t' P Q hG ht hmax hP hH ht' hmax' hQ
    F hF F' hF' b c θ hθ hAffine R a i

section LocalTorus

variable (R : Type u) [CommRing R] (a : Spec (CommRingCat.of R) ⟶ S)

local notation "M" => pinnedAffineModelOfFrames t P hG ht hmax hP F b R a
local notation "N" => pinnedAffineModelOfFrames t' Q hH ht' hmax' hQ F' c R a

/-- Normalization retains the exact full-lattice torus square on every
common scheme mapping to one affine chart. -/
theorem affineFrameIsoOver_torus {T : Scheme.{u}}
    (f : T ⟶ Spec (CommRingCat.of R)) (k : T ⟶ S) (hf : f ≫ a = k) :
    BasedBorelTransport.baseChangeInclusion k t ≫
        (affineFrameIsoOver t t' P Q hG ht hmax hP hH ht' hmax' hQ
          F F' b c θ hθ hAffine R a f k hf).hom =
      (datumTorusIso θ T).hom ≫ BasedBorelTransport.baseChangeInclusion k t' := by
  let e := @AffinePinnedModel.fixedComparison M N θ hθ T hAffine f f
  have he := e.property.1
  change (M).inclusionOver f ≫ e.val.hom =
    (datumTorusIso θ T).hom ≫ (N).inclusionOver f at he
  unfold affineFrameIsoOver Descent.comparisonInOriginal
  rw [← normalizedInclusion_pullbackComparison t a f k hf,
    ← normalizedInclusion_pullbackComparison t' a f k hf]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]
  simpa only [Category.assoc, AffinePinnedModel.inclusionOver,
    BasedBorelTransport.baseChangeInclusion, e] using
    congrArg (fun z => z ≫ (Descent.pullbackComparison a f k hf H).hom) he

end LocalTorus

/-- The descended global isomorphism induces precisely the specified map on
the entire split torus, including central lattice directions. -/
theorem globalPinnedIso_torus :
    t ≫ (globalPinnedIso t t' P Q hG ht hmax hP hH ht' hmax' hQ
        F hF F' hF' b c θ hθ hAffine).hom =
      (datumTorusIso θ S).hom ≫ t' := by
  apply hom_ext_of_pointwise_fppf_baseChange
  intro s
  let i := S.affineOpenCover.idx s
  let a := S.affineOpenCover.f i
  refine ⟨Spec (S.affineOpenCover.X i), a, inferInstance, inferInstance,
    S.affineOpenCover.covers s, ?_⟩
  simp only [Functor.map_comp]
  change (baseChange a).map t ≫
      ((baseChange a).mapIso
        (globalPinnedIso t t' P Q hG ht hmax hP hH ht' hmax' hQ
          F hF F' hF' b c θ hθ hAffine)).hom =
    (baseChange a).map (datumTorusIso θ S).hom ≫ (baseChange a).map t'
  rw [globalPinnedIso_on_member]
  apply (cancel_epi (splitTorus.baseChangeIso a I).inv).mp
  rw [datumTorusIso_baseChange]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  simpa only [affineFrameIsoFamily, BasedBorelTransport.baseChangeInclusion,
    Category.assoc, CommRingCat.of_carrier, a] using
    (affineFrameIsoOver_torus t t' P Q hG ht hmax hP hH ht' hmax' hQ
      F F' b c θ hθ hAffine (S.affineOpenCover.X i) a (𝟙 _) a (Category.id_comp _))

variable [Nonempty S]

/-- The global isomorphism with its complete based-coordinate transport
data, from supplied coherent actual root frames and the affine theorem. -/
def basedIsoOfCoherentFrames : BasedCoordinateIso t t' P Q b c where
  groupIso := globalPinnedIso t t' P Q hG ht hmax hP hH ht' hmax' hQ
    F hF F' hF' b c θ hθ hAffine
  torusIso := datumTorusIso θ S
  rootEquiv := θ
  sourcePairing := pairing_of_globalCoordinateRootDatum t P hP
  targetPairing := pairing_of_globalCoordinateRootDatum t' Q hQ
  simple_iff := hθ
  square := globalPinnedIso_torus t t' P Q hG ht hmax hP hH ht' hmax' hQ
    F hF F' hF' b c θ hθ hAffine
  characters := datumTorusIso_characters θ S

end Groups

end Langlands.GroupScheme.CoordinateRootDatum
