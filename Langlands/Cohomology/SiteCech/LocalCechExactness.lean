import Langlands.Cohomology.SiteCech.ObjectwiseCechExactness
import Langlands.Cohomology.SiteCech.FreeSections
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.CategoryTheory.Subfunctor.Image

/-! # Local exactness of free Čech augmentations -/

noncomputable section

namespace Langlands.Cohomology.SiteCech

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

universe u v w

section PostMono

variable {A : Type u} [Category.{v} A] [HasFiniteLimits A] {X Y Z : A}
variable (p : X ⟶ Y) (m : Y ⟶ Z) [Mono m]

/-- The comparison of arrows obtained by postcomposing with a monomorphism. -/
def cechPostMonoMap : Arrow.mk p ⟶ Arrow.mk (p ≫ m) :=
  Arrow.homMk (𝟙 X) m (by simp)

set_option backward.isDefEq.respectTransparency false in
/-- A monomorphism on the base does not change a nonempty Čech term. -/
def cechPostMonoTermIso (n : ℕ) :
    (Arrow.mk p).cechNerve.obj (op ⦋n⦌) ≅
      (Arrow.mk (p ≫ m)).cechNerve.obj (op ⦋n⦌) where
  hom := (Arrow.mapCechNerve (cechPostMonoMap p m)).app (op ⦋n⦌)
  inv := WidePullback.lift (arrows := fun _ : Fin (n + 1) => p)
    (WidePullback.π (fun _ : Fin (n + 1) => p ≫ m) 0 ≫ p)
    (fun j => WidePullback.π (fun _ : Fin (n + 1) => p ≫ m) j)
    (by
      intro j
      apply (cancel_mono m).1
      simp only [Category.assoc, WidePullback.π_arrow])
  hom_inv_id := by
    apply WidePullback.hom_ext
    · intro j
      simp [cechPostMonoMap, Arrow.mapCechNerve]
    · simp [cechPostMonoMap, Arrow.mapCechNerve]
  inv_hom_id := by
    apply WidePullback.hom_ext
    · intro j
      simp [cechPostMonoMap, Arrow.mapCechNerve]
    · simp [cechPostMonoMap, Arrow.mapCechNerve]

/-- The actual map of Čech nerves is an isomorphism after a monomorphism
on the base. -/
theorem isIso_mapCechNerve_postMono :
    IsIso (Arrow.mapCechNerve (cechPostMonoMap p m)) := by
  have : ∀ n, IsIso ((Arrow.mapCechNerve (cechPostMonoMap p m)).app n) :=
    fun n => (cechPostMonoTermIso p m n.unop.len).isIso_hom
  exact NatIso.isIso_of_isIso_app _

end PostMono

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)

/-- Maps into a sheaf are equal if they agree after a locally surjective arrow. -/
theorem hom_ext_of_locally_surjective {P Q Z : Cᵒᵖ ⥤ Type w}
    (f : P ⟶ Q) [Presheaf.IsLocallySurjective J f] (hZ : Presheaf.IsSheaf J Z)
    {a b : Q ⟶ Z} (h : f ≫ a = f ≫ b) : a = b := by
  ext U x
  apply (((isSheaf_iff_isSheaf_of_type J Z).1 hZ).isSeparated _
    (Presheaf.imageSieve_mem J f x)).ext
  intro V g hg
  obtain ⟨y, hy⟩ := hg
  change Z.map g.op (a.app U x) = Z.map g.op (b.app U x)
  calc
    _ = a.app (op V) (Q.map g.op x) := (NatTrans.naturality_apply a g.op x).symm
    _ = a.app (op V) (f.app (op V) y) := congrArg (a.app (op V)) hy.symm
    _ = b.app (op V) (f.app (op V) y) :=
      congrArg (fun k : P ⟶ Z => k.app (op V) y) h
    _ = b.app (op V) (Q.map g.op x) := congrArg (b.app (op V)) hy
    _ = _ := NatTrans.naturality_apply b g.op x

variable (R : Type w) [CommRing R] [HasSheafify J (ModuleCat.{w} R)]

/-- The free sheaf map of a locally surjective presheaf arrow is an epimorphism. -/
theorem epi_freeSheaf_map_of_locally_surjective {P Q : Cᵒᵖ ⥤ Type w}
    (f : P ⟶ Q) [Presheaf.IsLocallySurjective J f] :
    Epi ((freeSheafFunctor J R).map f) where
  left_cancellation a b h := by
    rename_i Z
    apply ((freeSheafAdjunction J R).homEquiv _ _).injective
    apply hom_ext_of_locally_surjective J f
      (Presheaf.isSheaf_comp_of_isSheaf J _ (forget (ModuleCat.{w} R)) Z.property)
    simpa only [← Adjunction.homEquiv_naturality_left] using
      congrArg ((freeSheafAdjunction J R).homEquiv _ _) h

/-- The free sheaf map of an objectwise injective presheaf arrow is a monomorphism. -/
theorem mono_freeSheaf_map_of_injective {P Q : Cᵒᵖ ⥤ Type w}
    (f : P ⟶ Q) (h : ∀ U, Function.Injective (f.app U)) :
    Mono ((freeSheafFunctor J R).map f) := by
  have : ∀ U, Mono (((freeModulePresheafFunctor R).map f).app U) := by
    intro U
    apply (ModuleCat.mono_iff_injective _).2
    exact Finsupp.mapDomain_injective (h U)
  have : Mono ((freeModulePresheafFunctor R).map f) := NatTrans.mono_of_mono_app _
  change Mono ((presheafToSheaf J (ModuleCat.{w} R)).map
    ((freeModulePresheafFunctor R).map f))
  infer_instance

/-- A locally surjective, objectwise injective arrow becomes an isomorphism
under the free module sheaf functor. -/
theorem isIso_freeSheaf_map_of_injective_of_locally_surjective {P Q : Cᵒᵖ ⥤ Type w}
    (f : P ⟶ Q) (h : ∀ U, Function.Injective (f.app U))
    [Presheaf.IsLocallySurjective J f] : IsIso ((freeSheafFunctor J R).map f) := by
  have := epi_freeSheaf_map_of_locally_surjective J R f
  have := mono_freeSheaf_map_of_injective J R f h
  exact isIso_of_mono_of_epi _

/-- The map from the arrow onto its range to the original presheaf arrow. -/
def rangeArrowComparison (f : Arrow (Cᵒᵖ ⥤ Type w)) :
    Arrow.mk (Subfunctor.toRange f.hom) ⟶ f :=
  Arrow.homMk (𝟙 _) (Subfunctor.range f.hom).ι (Subfunctor.toRange_ι f.hom).symm

/-- Factoring through the range does not change the augmented free sheaf nerve
of a locally surjective presheaf arrow. -/
def freeRangeAugmentedCechIso (f : Arrow (Cᵒᵖ ⥤ Type w))
    [Presheaf.IsLocallySurjective J f.hom] :
    freeAugmentedCechNerve J R (Arrow.mk (Subfunctor.toRange f.hom)) ≅
      freeAugmentedCechNerve J R f := by
  have hlocal : Presheaf.IsLocallySurjective J (Subfunctor.range f.hom).ι :=
    Presheaf.isLocallySurjective_of_isLocallySurjective_fac J (Subfunctor.toRange_ι f.hom)
  have htarget : IsIso ((freeSheafFunctor J R).map (Subfunctor.range f.hom).ι) :=
    isIso_freeSheaf_map_of_injective_of_locally_surjective J R _ (fun _ => Subtype.val_injective)
  have hnerve : IsIso (Arrow.mapCechNerve (rangeArrowComparison f)) :=
    isIso_mapCechNerve_postMono (Subfunctor.toRange f.hom) (Subfunctor.range f.hom).ι
  let α := (SimplicialObject.Augmented.whiskeringObj _ _ (freeSheafFunctor J R)).map
    (Arrow.mapAugmentedCechNerve (rangeArrowComparison f))
  exact Comma.isoMk
    (Functor.isoWhiskerRight (asIso (Arrow.mapCechNerve (rangeArrowComparison f)))
      (freeSheafFunctor J R))
    (@asIso _ _ _ _ _ htarget) α.w

/-- Naturality of the actual augmentation identifies the range augmentation
with the original one. -/
def freeRangeAugmentationArrowIso (f : Arrow (Cᵒᵖ ⥤ Type w))
    [Presheaf.IsLocallySurjective J f.hom] :
    Arrow.mk (freeCechAugmentation J R (Arrow.mk (Subfunctor.toRange f.hom))) ≅
      Arrow.mk (freeCechAugmentation J R f) :=
  Arrow.isoMk
    ((SimplicialObject.Augmented.drop ⋙ AlgebraicTopology.alternatingFaceMapComplex _).mapIso
      (freeRangeAugmentedCechIso J R f))
    ((SimplicialObject.Augmented.point ⋙ ChainComplex.single₀ _).mapIso
      (freeRangeAugmentedCechIso J R f))
    (AlgebraicTopology.AlternatingFaceMapComplex.ε.naturality
      (freeRangeAugmentedCechIso J R f).hom)

/-- The actual free sheaf Čech augmentation of a locally surjective presheaf
arrow is a quasi-isomorphism, without products in the site category. -/
theorem quasiIso_freeCechAugmentation_of_locally_surjective
    (f : Arrow (Cᵒᵖ ⥤ Type w)) [Presheaf.IsLocallySurjective J f.hom] :
    QuasiIso (freeCechAugmentation J R f) := by
  apply (quasiIso_iff_of_arrow_mk_iso _ _ (freeRangeAugmentationArrowIso J R f)).1
  apply quasiIso_freeCechAugmentation_of_objectwise_surjective R J
  intro U x
  obtain ⟨y, hy⟩ := x.property
  exact ⟨y, Subtype.ext hy⟩

end Langlands.Cohomology.SiteCech
