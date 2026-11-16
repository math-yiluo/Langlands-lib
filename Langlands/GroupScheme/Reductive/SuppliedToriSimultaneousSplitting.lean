import Langlands.GroupScheme.Reductive.SuppliedTorusLocalSplitting

/-! # Simultaneous local splitting of two supplied maximal tori -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme

local instance simultaneousSplit_affinePullback {S S' : Scheme.{u}}
    (G : GroupScheme S) [IsAffineHom G.X.hom] (a : S' ⟶ S) :
    IsAffineHom ((GroupScheme.baseChange a).obj G).X.hom :=
  MorphismProperty.pullback_snd G.X.hom a inferInstance

local instance simultaneousSplit_smoothPullback {S S' : Scheme.{u}}
    (G : GroupScheme S) [Smooth G.X.hom] (a : S' ⟶ S) :
    Smooth ((GroupScheme.baseChange a).obj G).X.hom :=
  MorphismProperty.pullback_snd G.X.hom a inferInstance

/-- Aligned full split data and free actual root lines persist under
arbitrary scalar extension. -/
theorem HasSplitMaximalTorusCoordinates.baseChange
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    {T : CommGroupScheme (Spec (CommRingCat.of R))}
    {G : GroupScheme (Spec (CommRingCat.of R))}
    [IsAffineHom G.X.hom] [Smooth G.X.hom]
    {i : T.toGrp ⟶ G} (hi : HasSplitMaximalTorusCoordinates i) :
    HasSplitMaximalTorusCoordinates
      (T := (CommGroupScheme.baseChange (algebraBaseMap R A)).obj T)
      ((GroupScheme.baseChange (algebraBaseMap R A)).map i) := by
  classical
  obtain ⟨I, hI, e, hc, hm, J, P, hP, hl⟩ := hi
  let : Fintype I := hI
  let a := algebraBaseMap R A
  let eA : splitTorus (Spec (CommRingCat.of A)) I ≅ (GroupScheme.baseChange a).obj T.toGrp :=
    (splitTorus.baseChangeIso a I).symm ≪≫ (GroupScheme.baseChange a).mapIso e
  have heA : eA.hom ≫ (GroupScheme.baseChange a).map i =
      splitTorus.baseChangeHom (K := A) G I (e.hom ≫ i) := by
    simp only [eA, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
      splitTorus.baseChangeHom, Functor.map_comp, Category.assoc]
    rfl
  refine ⟨I, hI, eA, ?_⟩
  rw [heA]
  refine ⟨(hc.baseChange a).iso_comp (splitTorus.baseChangeIso a I).symm,
    hm.baseChange_coordinates a, J, P, hP.baseChange, ?_⟩
  intro α
  obtain ⟨l⟩ := hl α
  exact ⟨(splitTorus.exponentWeightBaseChangeEquiv (K := A) G I
    (e.hom ≫ i) (P.root α)).symm.trans
      ((TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl A A) l).trans
        (TensorProduct.AlgebraTensorModule.rid R A A))⟩

/-- The scalar-extension result applies to every morphism of affine schemes,
with its original coefficient map. -/
theorem HasSplitMaximalTorusCoordinates.baseChange_affine
    {R A : CommRingCat.{u}}
    {T : CommGroupScheme (Spec R)} {G : GroupScheme (Spec R)}
    [IsAffineHom G.X.hom] [Smooth G.X.hom]
    {i : T.toGrp ⟶ G} (hi : HasSplitMaximalTorusCoordinates i)
    (a : Spec A ⟶ Spec R) :
    HasSplitMaximalTorusCoordinates
      (T := (CommGroupScheme.baseChange a).obj T) ((GroupScheme.baseChange a).map i) := by
  let φ := Spec.preimage a
  let : Algebra R A := φ.hom.toAlgebra
  have ha : algebraBaseMap R A = a := Spec.map_preimage a
  rw [← ha]
  exact hi.baseChange

/-- Successive aligned split data transport to the direct pullback of the
original torus inclusion. -/
theorem HasSplitMaximalTorusCoordinates.flatten_baseChange
    {S : Scheme.{u}} {R A : CommRingCat.{u}}
    {T : CommGroupScheme S} {G : GroupScheme S} [IsAffineHom G.X.hom]
    (i : T.toGrp ⟶ G) (c : Spec R ⟶ S) (a : Spec A ⟶ Spec R)
    (hi : HasSplitMaximalTorusCoordinates
      (T := (CommGroupScheme.baseChange a).obj ((CommGroupScheme.baseChange c).obj T))
      ((GroupScheme.baseChange a).map ((GroupScheme.baseChange c).map i))) :
    HasSplitMaximalTorusCoordinates
      (T := (CommGroupScheme.baseChange (a ≫ c)).obj T)
      ((GroupScheme.baseChange (a ≫ c)).map i) := by
  apply hi.of_isos (baseChangeCompIso c a T.toGrp) (baseChangeCompIso c a G).symm
  apply (cancel_mono (baseChangeCompIso c a G).hom).mp
  simpa only [Iso.symm_hom, Category.assoc, Iso.inv_hom_id, Category.comp_id] using
    baseChangeCompIso_hom_naturality c a i

/-- At every point there is one affine étale neighbourhood on which both
specified torus inclusions have aligned full split data. -/
def HaveCommonEtaleLocalSplitCoordinates
    {S : Scheme.{u}} {T U : CommGroupScheme S} {G H : GroupScheme S}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]
    (i : T.toGrp ⟶ G) (j : U.toGrp ⟶ H) : Prop :=
  ∀ s : S, ∃ (R : CommRingCat.{u}) (f : Spec R ⟶ S),
    Etale f ∧ s ∈ Set.range f ∧
    HasSplitMaximalTorusCoordinates
      (T := (CommGroupScheme.baseChange f).obj T) ((GroupScheme.baseChange f).map i) ∧
    HasSplitMaximalTorusCoordinates
      (T := (CommGroupScheme.baseChange f).obj U) ((GroupScheme.baseChange f).map j)

/-- Two supplied relative maximal tori in reductive groups split
simultaneously near each point, over an arbitrary base. -/
theorem commonEtaleLocalSplitCoordinates_of_suppliedTori
    {S : Scheme.{u}} (G H : GroupScheme S) (hG : IsReductive G) (hH : IsReductive H)
    (T U : CommGroupScheme S) (i : T.toGrp ⟶ G) (j : U.toGrp ⟶ H)
    (hT : RelativeTorus.IsTorus T.toGrp) (hi : IsClosedSubgroup i)
    (hmax : IsFibrewiseMaximalTorus i)
    (hU : RelativeTorus.IsTorus U.toGrp) (hj : IsClosedSubgroup j)
    (hmax' : IsFibrewiseMaximalTorus j) :
    haveI := hG.isAffineHom
    haveI := hH.isAffineHom
    HaveCommonEtaleLocalSplitCoordinates i j := by
  let := hG.isAffineHom
  let := hH.isAffineHom
  let := hG.smooth
  let := hH.smooth
  intro s
  obtain ⟨R, c, hc, ⟨p, hp⟩, hsplit⟩ :=
    exists_etale_affine_splitCoordinates_of_suppliedTorus G hG T i hT hi hmax s
  let : Etale c := hc
  obtain ⟨A, a, ha, ⟨q, hq⟩, hsplit'⟩ :=
    exists_etale_affine_splitCoordinates_of_suppliedTorus
      ((GroupScheme.baseChange c).obj H) (hH.baseChange c)
      ((CommGroupScheme.baseChange c).obj U) ((GroupScheme.baseChange c).map j)
      (hU.baseChange c) (hj.baseChange c) (hmax'.baseChange c) p
  let : Etale a := ha
  refine ⟨A, a ≫ c, inferInstance, ⟨q, ?_⟩,
    (hsplit.baseChange_affine a).flatten_baseChange i c a,
    hsplit'.flatten_baseChange j c a⟩
  change c (a q) = s
  rw [hq, hp]

end Langlands.GroupScheme
