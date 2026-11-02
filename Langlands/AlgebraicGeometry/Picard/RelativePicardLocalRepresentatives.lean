import Langlands.AlgebraicGeometry.Picard.RelativePicardSheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective

/-! # Local representatives of the actual fppf Picard sheaf -/

universe u

open CategoryTheory AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.RelativePicard

variable {S X : Scheme.{u}} (f : X ⟶ S)

instance toClassSheaf_isLocallyInjective :
    Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S) (toClassSheaf f) := by
  change Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S)
    (toSheafify (Scheme.fppfTopology.over S) (classPresheaf f))
  infer_instance

instance toClassSheaf_isLocallySurjective :
    Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (toClassSheaf f) := by
  change Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
    (toSheafify (Scheme.fppfTopology.over S) (classPresheaf f))
  infer_instance

/-- The sieve of tests on which a sheaf section has an ordinary class representative. -/
def representativeSieve (T : Over S) (s : (classSheafPresheaf f).obj (op T)) : Sieve T :=
  Presheaf.imageSieve (toClassSheaf f) s

/-- Membership means existence of an actual line bundle, not just an abstract class. -/
lemma representativeSieve_iff {T U : Over S}
    (s : (classSheafPresheaf f).obj (op T)) (g : U ⟶ T) :
    representativeSieve f T s g ↔
      ∃ L : LineBundle ((relativeSpace f).obj U),
        sheafClassOf f U L = (classSheafPresheaf f).map g.op s := by
  change (∃ q, (toClassSheaf f).app (op U) q =
    (classSheafPresheaf f).map g.op s) ↔ _
  constructor
  · rintro ⟨q, hq⟩
    obtain ⟨L, hL⟩ := exists_representative f U q
    exact ⟨L, by simpa only [sheafClassOf, hL] using hq⟩
  · rintro ⟨L, hL⟩
    exact ⟨classOf f U L, hL⟩

/-- Every section of the actual sheaf has fppf-local line-bundle representatives. -/
lemma representativeSieve_mem (T : Over S)
    (s : (classSheafPresheaf f).obj (op T)) :
    representativeSieve f T s ∈ (Scheme.fppfTopology.over S) T := by
  change Presheaf.imageSieve (toClassSheaf f) s ∈ _
  exact Presheaf.imageSieve_mem _ _ _

/-- Local representability of a section commutes with every base change. -/
lemma representativeSieve_pullback {T U : Over S}
    (s : (classSheafPresheaf f).obj (op T)) (g : U ⟶ T) :
    (representativeSieve f T s).pullback g =
      representativeSieve f U ((classSheafPresheaf f).map g.op s) :=
  Presheaf.pullback_imageSieve _ _ _

/-- An actual chosen local representative on an arrow of the representative sieve. -/
def localRepresentative {T U : Over S}
    (s : (classSheafPresheaf f).obj (op T)) (g : U ⟶ T)
    (hg : representativeSieve f T s g) : LineBundle ((relativeSpace f).obj U) :=
  ((representativeSieve_iff f s g).mp hg).choose

lemma localRepresentative_spec {T U : Over S}
    (s : (classSheafPresheaf f).obj (op T)) (g : U ⟶ T)
    (hg : representativeSieve f T s g) :
    sheafClassOf f U (localRepresentative f s g hg) =
      (classSheafPresheaf f).map g.op s :=
  ((representativeSieve_iff f s g).mp hg).choose_spec

/-- Two arbitrary sheaf sections admit representatives on one common covering sieve. -/
lemma commonRepresentativeSieve_mem (T : Over S)
    (s t : (classSheafPresheaf f).obj (op T)) :
    representativeSieve f T s ⊓ representativeSieve f T t ∈
      (Scheme.fppfTopology.over S) T :=
  (Scheme.fppfTopology.over S).intersection_covering
    (representativeSieve_mem f T s) (representativeSieve_mem f T t)

/-- The sieve of tests where the pullbacks of two actual line bundles are isomorphic. -/
def isomorphismSieve (T : Over S)
    (L M : LineBundle ((relativeSpace f).obj T)) : Sieve T :=
  Presheaf.equalizerSieve (F := classPresheaf f) (classOf f T L) (classOf f T M)

lemma isomorphismSieve_iff {T U : Over S}
    (L M : LineBundle ((relativeSpace f).obj T)) (g : U ⟶ T) :
    isomorphismSieve f T L M g ↔
      Nonempty ((LineBundle.pullback ((relativeSpace f).map g)).obj L ≅
        (LineBundle.pullback ((relativeSpace f).map g)).obj M) := by
  change (classPresheaf f).map g.op (classOf f T L) =
    (classPresheaf f).map g.op (classOf f T M) ↔ _
  rw [map_classOf, map_classOf]
  change
    (classOf f U ((LineBundle.pullback ((relativeSpace f).map g)).obj L) :
      Group ((relativeSpace f).obj U)) =
        classOf f U ((LineBundle.pullback ((relativeSpace f).map g)).obj M) ↔ _
  exact classOf_eq_iff_iso f U _ _

/-- Equality of sheaf sections can be tested on any fppf-covering sieve. -/
lemma sheafSection_ext {T : Over S} (s t : (classSheafPresheaf f).obj (op T))
    (R : Sieve T) (hR : R ∈ (Scheme.fppfTopology.over S) T)
    (h : ∀ (U : Over S) (g : U ⟶ T), R g →
      (classSheafPresheaf f).map g.op s = (classSheafPresheaf f).map g.op t) :
    s = t := by
  apply (((isSheaf_iff_isSheaf_of_type _ _).mp
    (classSheafPresheaf_isSheaf f)).isSeparated R hR).ext
  exact h

/-- Actual bundles have equal fppf Picard classes exactly when they are locally isomorphic. -/
lemma sheafClassOf_eq_iff_isomorphismSieve_mem (T : Over S)
    (L M : LineBundle ((relativeSpace f).obj T)) :
    sheafClassOf f T L = sheafClassOf f T M ↔
      isomorphismSieve f T L M ∈ (Scheme.fppfTopology.over S) T := by
  constructor
  · intro h
    exact Presheaf.equalizerSieve_mem _ (toClassSheaf f) _ _ h
  · intro h
    apply sheafSection_ext f _ _ (isomorphismSieve f T L M) h
    intro U g hg
    rw [map_sheafClassOf, map_sheafClassOf]
    apply congrArg ((toClassSheaf f).app (op U))
    exact (classOf_eq_iff_iso f U _ _).mpr ((isomorphismSieve_iff f L M g).mp hg)

variable (G : Sheaf (Scheme.fppfTopology.over S) (Type (u + 1)))
  (η : classPresheaf f ⟶ G.obj)

/-- A locally bijective class map induces an isomorphism from the actual Picard sheaf. -/
lemma isIso_classLift_of_locallyBijective
    [Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S) η]
    [Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) η] :
    IsIso (classLift f G η) := by
  have hfac := toClassSheaf_classLift f G η
  have hsurj : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
      (toClassSheaf f ≫ classLift f G η) := by
    rw [hfac]
    infer_instance
  have hinj : Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S)
      (toClassSheaf f ≫ classLift f G η) := by
    rw [hfac]
    infer_instance
  have : Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S)
      (classLift f G η) := Presheaf.isLocallySurjective_of_isLocallySurjective _
        (toClassSheaf f) (classLift f G η)
  have : Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S)
      (classLift f G η) := Presheaf.isLocallyInjective_of_isLocallyInjective_of_isLocallySurjective _
        (toClassSheaf f) (classLift f G η)
  let α : classSheaf f ⟶ G := ObjectProperty.homMk (classLift f G η)
  have : Sheaf.IsLocallyInjective α := by
    change Presheaf.IsLocallyInjective (Scheme.fppfTopology.over S) (classLift f G η)
    infer_instance
  have : Sheaf.IsLocallySurjective α := by
    change Presheaf.IsLocallySurjective (Scheme.fppfTopology.over S) (classLift f G η)
    infer_instance
  have : IsIso α := (Sheaf.isLocallyBijective_iff_isIso α).mp
    ⟨inferInstance, inferInstance⟩
  exact (inferInstance : IsIso
    ((sheafToPresheaf (Scheme.fppfTopology.over S) (Type (u + 1))).map α))

end Langlands.AlgebraicGeometry.Picard.RelativePicard
