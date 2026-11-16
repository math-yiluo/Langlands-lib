import Langlands.GroupScheme.Reductive.EtaleLocalSplitProof
import Langlands.GroupScheme.Torus.Relative

/-! # Local split coordinates aligned with a supplied maximal torus -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

local instance suppliedSplit_affinePullback {S S' : Scheme.{u}}
    (G : GroupScheme S) [IsAffineHom G.X.hom] (a : S' ⟶ S) :
    IsAffineHom ((GroupScheme.baseChange a).obj G).X.hom :=
  MorphismProperty.pullback_snd G.X.hom a inferInstance

/-- A supplied torus inclusion has split coordinates when an actual coordinate
isomorphism identifies it with a closed fibrewise maximal split torus carrying
one full fibrewise root datum and free actual root-weight lines. -/
def HasSplitMaximalTorusCoordinates
    {R : Type u} [CommRing R]
    {T : CommGroupScheme (Spec (CommRingCat.of R))}
    {G : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
    (i : T.toGrp ⟶ G) : Prop :=
  ∃ (I : Type u) (_ : Fintype I)
    (e : splitTorus (Spec (CommRingCat.of R)) I ≅ T.toGrp),
    IsClosedSubgroup (e.hom ≫ i) ∧
    IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) (e.hom ≫ i) ∧
    ∃ (J : Type u) (P : RootDatum J (I → ℤ) (I → ℤ)),
      IsFibrewiseRootDatumOf I G (e.hom ≫ i) P ∧
      ∀ α : J, Nonempty
        (splitTorus.exponentWeightSpace I G (e.hom ≫ i) (P.root α)
          ≃ₗ[CommRingCat.of R] CommRingCat.of R)

/-- Split coordinates transport through simultaneous source and ambient
isomorphisms that respect the supplied inclusion. -/
theorem HasSplitMaximalTorusCoordinates.of_isos
    {R : Type u} [CommRing R]
    {T T' : CommGroupScheme (Spec (CommRingCat.of R))}
    {G H : GroupScheme (Spec (CommRingCat.of R))}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    {i : T.toGrp ⟶ G} {j : T'.toGrp ⟶ H}
    (hi : HasSplitMaximalTorusCoordinates i)
    (eT : T'.toGrp ≅ T.toGrp) (eG : G ≅ H)
    (hj : j = eT.hom ≫ i ≫ eG.hom) :
    HasSplitMaximalTorusCoordinates j := by
  obtain ⟨I, hI, e, hc, hm, J, P, hP, hl⟩ := hi
  let : Fintype I := hI
  subst j
  refine ⟨I, hI, e ≪≫ eT.symm, ?_⟩
  have he : (e ≪≫ eT.symm).hom ≫ (eT.hom ≫ i ≫ eG.hom) =
      (e.hom ≫ i) ≫ eG.hom := by
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
  rw [he]
  refine ⟨hc.comp_iso eG, hm.comp_iso eG, J, P,
    IsFibrewiseRootDatumOf.comp_ambientIso (e.hom ≫ i) eG hP, ?_⟩
  intro α
  obtain ⟨l⟩ := hl α
  exact ⟨(splitTorus.exponentWeightAmbientEquiv (e.hom ≫ i) eG
    (P.root α)).symm.trans l⟩

/-- A supplied closed coordinate maximal torus acquires full split data on
an affine open neighbourhood of every point. -/
theorem exists_affine_open_splitCoordinates_of_coordinateTorus
    {R : Type u} [CommRing R]
    (I : Type u) [Fintype I]
    (G : GroupScheme (Spec (CommRingCat.of R))) (hG : IsReductive G)
    (i : splitTorus (Spec (CommRingCat.of R)) I ⟶ G)
    (hi : IsClosedSubgroup i)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) i)
    (p : Spec (CommRingCat.of R)) :
    haveI := hG.isAffineHom
    ∃ (A : CommRingCat.{u}) (a : Spec A ⟶ Spec (CommRingCat.of R)),
      IsOpenImmersion a ∧ p ∈ Set.range a ∧
      HasSplitMaximalTorusCoordinates
        (T := (CommGroupScheme.baseChange a).obj (splitTorus.commGroupScheme _ I))
        ((GroupScheme.baseChange a).map i) := by
  classical
  let := hG.isAffineHom
  let := hG.smooth
  obtain ⟨J, hJ, P, U, hred, hU, hpU, hrank, hP⟩ :=
    exists_open_coordinateRootDatum I G hG i hmax p
  let : Finite J := hJ
  obtain ⟨r, hr, hsub, hrootLines⟩ :=
    splitTorus.exists_principal_exponentWeightLines I G i P.root p U hU hpU hrank
  let A := Localization.Away r
  let a := algebraBaseMap R A
  have ha : IsOpenImmersion a := by
    dsimp [a, algebraBaseMap]
    infer_instance
  refine ⟨CommRingCat.of A, a, ha, ?_, I, inferInstance,
    (splitTorus.baseChangeIso a I).symm,
    (hi.baseChange a).iso_comp (splitTorus.baseChangeIso a I).symm,
    hmax.baseChange_coordinates a, J, P, ?_, hrootLines⟩
  · change p ∈ Set.range (PrimeSpectrum.comap (algebraMap R A))
    rw [PrimeSpectrum.localization_away_comap_range A r]
    exact hr
  · exact fibrewiseRootDatumOf_principalRestriction I G i P hred U hP r hsub

/-- A supplied relative maximal torus in a reductive group admits aligned
full split coordinates on an affine étale neighbourhood of every base point. -/
theorem exists_etale_affine_splitCoordinates_of_suppliedTorus
    {S : Scheme.{u}} (G : GroupScheme S) (hG : IsReductive G)
    (T : CommGroupScheme S) (i : T.toGrp ⟶ G)
    (hT : RelativeTorus.IsTorus T.toGrp) (hi : IsClosedSubgroup i)
    (hmax : IsFibrewiseMaximalTorus i) (s : S) :
    haveI := hG.isAffineHom
    ∃ (R : CommRingCat.{u}) (f : Spec R ⟶ S),
      Etale f ∧ s ∈ Set.range f ∧
      HasSplitMaximalTorusCoordinates
        (T := (CommGroupScheme.baseChange f).obj T) ((GroupScheme.baseChange f).map i) := by
  classical
  let := hG.isAffineHom
  let := hG.smooth
  obtain ⟨𝒰, h𝒰⟩ := hT
  obtain ⟨k, y, hy⟩ := 𝒰.exists_eq s
  let V := 𝒰.X k
  let l := V.affineOpenCover.idx y
  obtain ⟨z, hz⟩ := V.affineOpenCover.covers y
  let R := V.affineOpenCover.X l
  let b := V.affineOpenCover.f l
  let c := b ≫ 𝒰.f k
  let : Etale (𝒰.f k) := 𝒰.map_prop k
  have hTc : IsSplitTorus ((GroupScheme.baseChange c).obj T.toGrp) :=
    IsSplitTorus.of_iso (baseChangeCompIso (𝒰.f k) b T.toGrp)
      ((h𝒰 k).baseChange b)
  obtain ⟨I, hI, ⟨e⟩⟩ := hTc
  let : Fintype I := Fintype.ofFinite I
  let H := (GroupScheme.baseChange c).obj G
  let j : splitTorus (Spec R) I ⟶ H := e.inv ≫ (GroupScheme.baseChange c).map i
  have hj : IsClosedSubgroup j := (hi.baseChange c).iso_comp e.symm
  have hmj : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) j :=
    (hmax.baseChange c).iso_comp
      (T := (CommGroupScheme.baseChange c).obj T)
      (T' := splitTorus.commGroupScheme _ I) e.symm
  obtain ⟨A, a, ha, ⟨w, hw⟩, hsplit⟩ :=
    exists_affine_open_splitCoordinates_of_coordinateTorus I H (hG.baseChange c) j hj hmj z
  let : IsOpenImmersion a := ha
  refine ⟨A, a ≫ c, inferInstance, ?_, ?_⟩
  · refine ⟨w, ?_⟩
    change (𝒰.f k) (b (a w)) = s
    rw [hw]
    rw [hz, hy]
  · let eT : ((CommGroupScheme.baseChange (a ≫ c)).obj T).toGrp ≅
        ((CommGroupScheme.baseChange a).obj (splitTorus.commGroupScheme (Spec R) I)).toGrp :=
      baseChangeCompIso c a T.toGrp ≪≫ (GroupScheme.baseChange a).mapIso e
    apply hsplit.of_isos eT (baseChangeCompIso c a G).symm
    dsimp only [eT, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, j]
    rw [Functor.map_comp, Category.assoc, Category.assoc, ← Functor.map_comp_assoc,
      Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp,
      ← reassoc_of% (baseChangeCompIso_hom_naturality c a i),
      Iso.hom_inv_id, Category.comp_id]

end Langlands.GroupScheme
