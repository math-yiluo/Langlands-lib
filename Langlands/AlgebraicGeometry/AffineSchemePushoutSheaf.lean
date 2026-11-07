import Langlands.AlgebraicGeometry.AffineSchemePushoutLocalization
import Mathlib.AlgebraicGeometry.Spec
import Mathlib.Topology.Sheaves.Functors
import Mathlib.Topology.Sheaves.Limits
import Mathlib.Topology.Sheaves.SheafCondition.Sites

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

universe u

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AlgebraicGeometry.AffineSchemePushout

section Pushforward

variable {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]

/-- The structure sheaf of a spectrum, pushed onto the base spectrum. -/
def overSheaf (i : A →+* B) :
    TopCat.Sheaf CommRingCat (PrimeSpectrum.Top A) :=
  (TopCat.Sheaf.pushforward CommRingCat (Spec.topMap (CommRingCat.ofHom i))).obj
    (Spec.structureSheaf B)

instance overSheafAlgebra (i : A →+* B) (U : (Opens (PrimeSpectrum.Top A))ᵒᵖ) :
    Algebra B ((overSheaf i).obj.obj U) :=
  StructureSheaf.openAlgebra B _

/-- A map of structure sheaves over a fixed base spectrum. -/
def overSheafMap (i : A →+* B) (j : A →+* C) (f : B →+* C)
    (h : f.comp i = j) : overSheaf i ⟶ overSheaf j where
  hom :=
    { app := fun U => CommRingCat.ofHom <|
        StructureSheaf.comap f
          ((Opens.map (Spec.topMap (CommRingCat.ofHom i))).obj U.unop)
          ((Opens.map (Spec.topMap (CommRingCat.ofHom j))).obj U.unop)
          (fun p hp => by
            change PrimeSpectrum.comap i (PrimeSpectrum.comap f p) ∈ U.unop
            rw [← PrimeSpectrum.comap_comp_apply, h]
            exact hp)
      naturality := fun {_ _} _ => by ext; rfl }

theorem comap_comp_algebraMap (f : A →+* B) (U : Opens (PrimeSpectrum.Top A))
    (V : Opens (PrimeSpectrum.Top B))
    (h : V.1 ⊆ PrimeSpectrum.comap f ⁻¹' U.1) :
    (StructureSheaf.comap f U V h).comp (algebraMap A _) =
      (algebraMap B _).comp f := by
  apply RingHom.ext
  intro a
  apply Subtype.ext
  funext x
  dsimp
  rw [StructureSheaf.comap_apply]
  exact Localization.localRingHom_to_map _ _ _ _ _

theorem overSheafMap_comp {D : Type u} [CommRing D]
    (i : A →+* B) (j : A →+* C) (k : A →+* D)
    (f : B →+* C) (g : C →+* D) (hf : f.comp i = j) (hg : g.comp j = k) :
    overSheafMap i j f hf ≫ overSheafMap j k g hg =
      overSheafMap i k (g.comp f) (by rw [RingHom.comp_assoc, hf, hg]) := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply CommRingCat.hom_ext
  exact (StructureSheaf.comap_comp _ _ _ _ _ _ _).symm

end Pushforward

section Pullback

variable {B C D : Type u} [CommRing B] [CommRing C] [CommRing D]
  (f : B →+* D) (g : C →+* D)

local notation "P" => f.pullback g
local notation "i" => f.pullbackFst g
local notation "j" => f.pullbackSnd g
local notation "k" => f.comp i

/-- The first map from the two pushed structure sheaves to the common sheaf. -/
def overSheafFst : overSheaf i ⟶ overSheaf k :=
  overSheafMap i k f rfl

/-- The second map from the two pushed structure sheaves to the common sheaf. -/
def overSheafSnd : overSheaf j ⟶ overSheaf k :=
  overSheafMap j k g (RingHom.pullback_comm_sq f g).symm

def overSheafInl : Spec.structureSheaf P ⟶ overSheaf i :=
  ⟨(Spec.sheafedSpaceMap (CommRingCat.ofHom i)).hom.c⟩

def overSheafInr : Spec.structureSheaf P ⟶ overSheaf j :=
  ⟨(Spec.sheafedSpaceMap (CommRingCat.ofHom j)).hom.c⟩

theorem overSheaf_square :
    overSheafInl f g ≫ overSheafFst f g =
      overSheafInr f g ≫ overSheafSnd f g := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply CommRingCat.hom_ext
  change (StructureSheaf.comap _ _ _ _).comp (StructureSheaf.comap _ _ _ _) =
    (StructureSheaf.comap _ _ _ _).comp (StructureSheaf.comap _ _ _ _)
  rw [← StructureSheaf.comap_comp, ← StructureSheaf.comap_comp]
  congr 1
  exact RingHom.pullback_comm_sq f g

theorem isPullback_basicOpen (a : P) :
    IsPullback ((overSheafInl f g).hom.app (op (PrimeSpectrum.basicOpen a)))
      ((overSheafInr f g).hom.app (op (PrimeSpectrum.basicOpen a)))
      ((overSheafFst f g).hom.app (op (PrimeSpectrum.basicOpen a)))
      ((overSheafSnd f g).hom.app (op (PrimeSpectrum.basicOpen a))) := by
  let B' := ((overSheaf i).obj.obj (op (PrimeSpectrum.basicOpen a)))
  let C' := ((overSheaf j).obj.obj (op (PrimeSpectrum.basicOpen a)))
  let D' := ((overSheaf k).obj.obj (op (PrimeSpectrum.basicOpen a)))
  let A' := (Spec.structureSheaf P).obj.obj (op (PrimeSpectrum.basicOpen a))
  let f' := ((overSheafFst f g).hom.app (op (PrimeSpectrum.basicOpen a))).hom
  let g' := ((overSheafSnd f g).hom.app (op (PrimeSpectrum.basicOpen a))).hom
  let i' := ((overSheafInl f g).hom.app (op (PrimeSpectrum.basicOpen a))).hom
  let j' := ((overSheafInr f g).hom.app (op (PrimeSpectrum.basicOpen a))).hom
  have hB : IsLocalization.Away a.1.1 B' :=
    StructureSheaf.IsLocalization.to_basicOpen B _
  have hC : IsLocalization.Away a.1.2 C' :=
    StructureSheaf.IsLocalization.to_basicOpen C _
  have hD : IsLocalization.Away (f a.1.1) D' :=
    StructureSheaf.IsLocalization.to_basicOpen D _
  exact @isPullback_localization B C D B' C' D' _ _ _ _ _ _ _ _ _ f g f' g'
    (comap_comp_algebraMap _ _ _ _) (comap_comp_algebraMap _ _ _ _) a hB hC hD
    A' _ _ (StructureSheaf.IsLocalization.to_basicOpen P a) i' j'
    (comap_comp_algebraMap _ _ _ _) (comap_comp_algebraMap _ _ _ _)
    (CommRingCat.hom_ext_iff.mp (NatTrans.congr_app
      (congrArg (fun t => t.hom) (overSheaf_square f g)) _))

/-- The comparison with the sheaf pullback on the spectrum of the pullback ring. -/
def sheafPullbackComparison :
    Spec.structureSheaf P ⟶ pullback (overSheafFst f g) (overSheafSnd f g) :=
  pullback.lift (overSheafInl f g) (overSheafInr f g) (overSheaf_square f g)

instance sheafPullbackComparison_basicOpen_isIso (a : P) :
    IsIso ((sheafPullbackComparison f g).hom.app (op (PrimeSpectrum.basicOpen a))) := by
  let E := TopCat.Sheaf.forget CommRingCat (PrimeSpectrum.Top P) ⋙
    (evaluation _ CommRingCat).obj (op (PrimeSpectrum.basicOpen a))
  have h := ((IsPullback.of_hasPullback (overSheafFst f g) (overSheafSnd f g)).map
    (TopCat.Sheaf.forget CommRingCat (PrimeSpectrum.Top P))).map
    ((evaluation _ CommRingCat).obj (op (PrimeSpectrum.basicOpen a)))
  let e := (isPullback_basicOpen f g a).isoIsPullback _ _ h
  have he : (sheafPullbackComparison f g).hom.app (op (PrimeSpectrum.basicOpen a)) =
      e.hom := by
    apply h.hom_ext
    · change E.map (sheafPullbackComparison f g) ≫ E.map (pullback.fst _ _) = _
      rw [← E.map_comp]
      simp only [sheafPullbackComparison, pullback.lift_fst]
      exact ((isPullback_basicOpen f g a).isoIsPullback_hom_fst _ _ h).symm
    · change E.map (sheafPullbackComparison f g) ≫ E.map (pullback.snd _ _) = _
      rw [← E.map_comp]
      simp only [sheafPullbackComparison, pullback.lift_snd]
      exact ((isPullback_basicOpen f g a).isoIsPullback_hom_snd _ _ h).symm
  rw [he]
  infer_instance

instance sheafPullbackComparison_isIso : IsIso (sheafPullbackComparison f g) :=
  TopCat.Sheaf.isIso_iff_isIso_basis PrimeSpectrum.isBasis_basic_opens
    (fun _ => inferInstance)

/-- The structure sheaf of a ring pullback is the pullback of the pushed structure sheaves. -/
theorem isPullback_overSheaf :
    IsPullback (overSheafInl f g) (overSheafInr f g)
      (overSheafFst f g) (overSheafSnd f g) := by
  apply (IsPullback.of_hasPullback (overSheafFst f g) (overSheafSnd f g)).of_iso'
    (asIso (sheafPullbackComparison f g)) (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simpa only [asIso_hom, Iso.refl_hom, Category.comp_id, sheafPullbackComparison] using
      pullback.lift_fst (overSheafInl f g) (overSheafInr f g) (overSheaf_square f g)
  · simpa only [asIso_hom, Iso.refl_hom, Category.comp_id, sheafPullbackComparison] using
      pullback.lift_snd (overSheafInl f g) (overSheafInr f g) (overSheaf_square f g)
  · simp
  · simp

/-- The same pullback square after forgetting sheafness. -/
theorem isPullback_overPresheaf :
    IsPullback (overSheafInl f g).hom (overSheafInr f g).hom
      (overSheafFst f g).hom (overSheafSnd f g).hom :=
  (isPullback_overSheaf f g).map (TopCat.Sheaf.forget CommRingCat (PrimeSpectrum.Top P))

end Pullback

end Langlands.AlgebraicGeometry.AffineSchemePushout
