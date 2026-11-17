import Langlands.GroupScheme.Reductive.GlobalPinningFrames
import Langlands.GroupScheme.Dynamic.PresentationComparison

/-! # Actual transitions between affine pinned charts of one group -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.CoordinateRootDatum

section Inclusion

variable {S U V : Scheme.{u}} {I : Type u} [Fintype I]
    {G : GroupScheme S} (t : splitTorus S I ⟶ G)

/-- Successive coordinate normalization commutes with the original-group
comparison, including a specified equality of base maps. -/
theorem normalizedInclusion_pullbackComparison
    (a : U ⟶ S) (f : V ⟶ U) (k : V ⟶ S) (hf : f ≫ a = k) :
    BasedBorelTransport.baseChangeInclusion f
        (BasedBorelTransport.baseChangeInclusion a t) ≫
        (Descent.pullbackComparison a f k hf G).hom =
      BasedBorelTransport.baseChangeInclusion k t := by
  subst k
  simp only [BasedBorelTransport.baseChangeInclusion, Descent.pullbackComparison,
    eqToIso_refl, Iso.trans_refl, Iso.symm_hom]
  rw [splitTorus.baseChangeTorusHom_comp]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

end Inclusion

section Points

variable {S U U' T Z : Scheme.{u}} (G : GroupScheme S)
    (a : U ⟶ S) (a' : U' ⟶ S) (f : T ⟶ U) (g : T ⟶ U') (k : T ⟶ S)
    (hf : f ≫ a = k) (hg : g ≫ a' = k)

/-- The actual chart comparison identifies points with the same original
group projection and the same common-base projection. -/
theorem chartComparison_points
    (v : Z ⟶ ((baseChange f).obj ((baseChange a).obj G)).X.left)
    (w : Z ⟶ ((baseChange g).obj ((baseChange a').obj G)).X.left)
    (hproj : v ≫ pullback.fst ((baseChange a).obj G).X.hom f ≫ pullback.fst G.X.hom a =
      w ≫ pullback.fst ((baseChange a').obj G).X.hom g ≫ pullback.fst G.X.hom a')
    (hbase : v ≫ ((baseChange f).obj ((baseChange a).obj G)).X.hom =
      w ≫ ((baseChange g).obj ((baseChange a').obj G)).X.hom) :
    v ≫ (Descent.pullbackComparison a f k hf G ≪≫
      (Descent.pullbackComparison a' g k hg G).symm).hom.hom.hom.left = w := by
  let d := Descent.pullbackComparison a' g k hg G
  let c := Descent.pullbackComparison a f k hf G
  change v ≫ (c ≪≫ d.symm).hom.hom.hom.left = w
  have hcd : (c ≪≫ d.symm).hom ≫ d.hom = c.hom := by simp
  have hcdl := congrArg (fun z => z.hom.hom.left) hcd
  change (c ≪≫ d.symm).hom.hom.hom.left ≫ d.hom.hom.hom.left =
    c.hom.hom.hom.left at hcdl
  apply (cancel_mono d.hom.hom.hom.left).mp
  apply pullback.hom_ext
  · simp only [Category.assoc]
    rw [← Category.assoc (c ≪≫ d.symm).hom.hom.hom.left d.hom.hom.hom.left, hcdl]
    simpa only [c, d, Category.assoc, Descent.pullbackComparison_hom_fst] using hproj
  · have hc := Over.w c.hom.hom.hom
    have hd := Over.w d.hom.hom.hom
    change c.hom.hom.hom.left ≫ ((baseChange k).obj G).X.hom =
      ((baseChange f).obj ((baseChange a).obj G)).X.hom at hc
    change d.hom.hom.hom.left ≫ ((baseChange k).obj G).X.hom =
      ((baseChange g).obj ((baseChange a').obj G)).X.hom at hd
    simp only [Category.assoc]
    rw [← Category.assoc (c ≪≫ d.symm).hom.hom.hom.left d.hom.hom.hom.left, hcdl]
    change v ≫ c.hom.hom.hom.left ≫ ((baseChange k).obj G).X.hom =
      w ≫ d.hom.hom.hom.left ≫ ((baseChange k).obj G).X.hom
    rw [hc, hd]
    exact hbase

end Points

section Charts

variable {S : Scheme.{u}} {I J : Type u} [Fintype I] [Fintype J]
    {G : GroupScheme S} [IsAffineHom G.X.hom]
    (t : splitTorus S I ⟶ G) (P : RootDatum J (I → ℤ) (I → ℤ))
    (hG : IsReductive G) (ht : IsClosedSubgroup t)
    (hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) t)
    (hP : IsGlobalCoordinateRootDatumOf I G t P)
    (F : AffineRootFrames t P) (b : P.Base)
    (R R' : Type u) [CommRing R] [CommRing R']
    (a : Spec (CommRingCat.of R) ⟶ S) (a' : Spec (CommRingCat.of R') ⟶ S)

local notation "M" => pinnedAffineModelOfFrames t P hG ht hmax hP F b R a
local notation "N" => pinnedAffineModelOfFrames t P hG ht hmax hP F b R' a'

variable {T : Scheme.{u}} (f : T ⟶ Spec (CommRingCat.of R))
    (g : T ⟶ Spec (CommRingCat.of R')) (k : T ⟶ S)
    (hf : f ≫ a = k) (hg : g ≫ a' = k)

/-- The original group supplies the actual transition between its two
affine pulled-back pinned models on any common test scheme. -/
def affineFrameComparison : @AffinePinnedModel.Comparison M N T f g :=
  Descent.pullbackComparison a f k hf G ≪≫
    (Descent.pullbackComparison a' g k hg G).symm

/-- The transition fixes the original normalized coordinate torus exactly. -/
theorem affineFrameComparison_torus :
    (M).inclusionOver f ≫
        (affineFrameComparison t P hG ht hmax hP F b R R' a a' f g k hf hg).hom =
      (N).inclusionOver g := by
  change BasedBorelTransport.baseChangeInclusion f
      (BasedBorelTransport.baseChangeInclusion a t) ≫
        (Descent.pullbackComparison a f k hf G).hom ≫
        (Descent.pullbackComparison a' g k hg G).inv =
    BasedBorelTransport.baseChangeInclusion g
      (BasedBorelTransport.baseChangeInclusion a' t)
  rw [← Category.assoc, normalizedInclusion_pullbackComparison t a f k hf]
  rw [← normalizedInclusion_pullbackComparison t a' g k hg]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The same transition respects the canonical based positive-coroot
cocharacters of the models. -/
theorem affineFrameComparison_cocharacter :
    AffinePinnedModel.PreservesCocharacter
      (affineFrameComparison t P hG ht hmax hP F b R R' a a' f g k hf hg) := by
  change BasedBorelTransport.cocharacter ((M).inclusionOver f) P b ≫
      (affineFrameComparison t P hG ht hmax hP F b R R' a a' f g k hf hg).hom =
    BasedBorelTransport.cocharacter ((N).inclusionOver g) P b
  unfold BasedBorelTransport.cocharacter
  rw [Category.assoc, affineFrameComparison_torus]

variable (hF : AffineRootFrames.IsCoherent t P F)

include hF in
/-- The pinning point from one affine chart projects to the single direct
frame point in the original group. -/
theorem rootVectorPoint_projection
    (A : Type u) [CommRing A] [Algebra R A]
    (x : Spec (CommRingCat.of A) ⟶ T)
    (hx : algebraBaseMap R A = x ≫ f) (s : b.support) :
    (M).rootVectorPoint f A x hx s ≫
        pullback.fst (M).group.X.hom f ≫ pullback.fst G.X.hom a =
      AffineRootFrames.point t P F A (algebraBaseMap R A ≫ a) s := by
  rw [AffinePinnedModel.rootVectorPoint_fst_assoc]
  exact hF R A a s

include hF in
/-- Coherent original root frames make the actual transition identify the
same simple pinning vectors on every affine coefficient test. -/
theorem affineFrameComparison_pinning
    (A : Type u) [CommRing A] [Algebra R A] [Algebra R' A]
    (x : Spec (CommRingCat.of A) ⟶ T)
    (hx : algebraBaseMap R A = x ≫ f) (hx' : algebraBaseMap R' A = x ≫ g)
    (s : b.support) :
    (M).rootVectorPoint f A x hx s ≫
        (affineFrameComparison t P hG ht hmax hP F b R R' a a' f g k hf hg).hom.hom.hom.left =
      (N).rootVectorPoint g A x hx' s := by
  apply chartComparison_points G a a' f g k hf hg
  · rw [rootVectorPoint_projection t P hG ht hmax hP F b R a f hF,
      rootVectorPoint_projection t P hG ht hmax hP F b R' a' g hF]
    have ha : algebraBaseMap R A ≫ a = x ≫ k := by
      rw [hx, Category.assoc, hf]
    have ha' : algebraBaseMap R' A ≫ a' = x ≫ k := by
      rw [hx', Category.assoc, hg]
    rw [ha, ha']
  · exact ((M).rootVectorPoint_snd f A x hx s).trans
      ((N).rootVectorPoint_snd g A x hx' s).symm

end Charts

end Langlands.GroupScheme.CoordinateRootDatum
