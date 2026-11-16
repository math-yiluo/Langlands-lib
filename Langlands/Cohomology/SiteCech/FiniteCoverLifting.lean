import Langlands.Cohomology.SiteCech.FreeSections
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Limits.Shapes.Products

/-! # Lifting coefficient maps over finite basis covers -/

noncomputable section

namespace Langlands.Cohomology.SiteCech

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w a

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable {ι : Type a} (B : ι → C)

/-- A finite covering family with domains in a specified family of site objects. -/
structure FiniteBasisCover (U : C) where
  size : ℕ
  index : Fin size → ι
  arrow : ∀ j, B (index j) ⟶ U
  covering : Sieve.ofArrows (fun j => B (index j)) arrow ∈ J U

/-- Every covering sieve of each basis object contains a finite basis cover. -/
def HasFiniteBasisCoverRefinements : Prop :=
  ∀ i (S : Sieve (B i)), S ∈ J (B i) →
    ∃ c : FiniteBasisCover J B (B i), ∀ j, S (c.arrow j)

variable (R : Type w) [CommRing R] [HasSheafify J (ModuleCat.{w} R)]
variable [LocallySmall.{w} C]

/-- The coproduct of free representable module sheaves on a finite basis cover. -/
def FiniteBasisCover.freeSource {U : C} (c : FiniteBasisCover J B U) :
    Sheaf J (ModuleCat.{w} R) :=
  ∐ (fun j => (freeSheafFunctor J R).obj (shrinkYoneda.{w}.obj (B (c.index j))))

/-- The map of free module sheaves induced by the covering arrows. -/
def FiniteBasisCover.freeAugmentation {U : C} (c : FiniteBasisCover J B U) :
    c.freeSource J B R ⟶
      (freeSheafFunctor J R).obj (shrinkYoneda.{w}.obj U) :=
  Sigma.desc (fun j => (freeSheafFunctor J R).map (shrinkYoneda.{w}.map (c.arrow j)))

/-- Local section lifts on the arrows of a finite cover assemble into a lift of
the corresponding free augmentation. -/
theorem FiniteBasisCover.exists_free_lift_of_imageSieve
    {U : C} (c : FiniteBasisCover J B U)
    {F Q : Sheaf J (ModuleCat.{w} R)} (f : F ⟶ Q)
    (s : (freeSheafFunctor J R).obj (shrinkYoneda.{w}.obj U) ⟶ Q)
    (hc : ∀ j, Presheaf.imageSieve f.hom (freeRepresentableHomEquiv J R U Q s)
      (c.arrow j)) :
    ∃ t : c.freeSource J B R ⟶ F, t ≫ f = c.freeAugmentation J B R ≫ s := by
  choose x hx using hc
  let t := fun j => (freeRepresentableHomEquiv J R (B (c.index j)) F).symm (x j)
  dsimp only [FiniteBasisCover.freeSource, FiniteBasisCover.freeAugmentation]
  refine ⟨Sigma.desc t, ?_⟩
  apply Sigma.hom_ext
  intro j
  simp only [Sigma.ι_comp_desc_assoc]
  apply (freeRepresentableHomEquiv J R (B (c.index j)) Q).injective
  rw [freeRepresentableHomEquiv_naturality_right,
    freeRepresentableHomEquiv_naturality_left]
  simpa only [t, Equiv.apply_symm_apply] using hx j

variable [J.WEqualsLocallyBijective (ModuleCat.{w} R)]

/-- An epimorphism admits a finite-cover lift of every map from a free basis
object when finite basis covers refine covering sieves. -/
theorem exists_finiteBasisCover_lift
    (hB : HasFiniteBasisCoverRefinements J B)
    {F Q : Sheaf J (ModuleCat.{w} R)} (f : F ⟶ Q) [Epi f]
    (i : ι) (s : (freeSheafFunctor J R).obj (shrinkYoneda.{w}.obj (B i)) ⟶ Q) :
    ∃ (c : FiniteBasisCover J B (B i)) (t : c.freeSource J B R ⟶ F),
      t ≫ f = c.freeAugmentation J B R ≫ s := by
  have : Sheaf.IsLocallySurjective f :=
    (Sheaf.isLocallySurjective_iff_epi' (φ := f)).2 inferInstance
  obtain ⟨c, hc⟩ := hB i _
    (Presheaf.imageSieve_mem J f.hom (freeRepresentableHomEquiv J R (B i) Q s))
  obtain ⟨t, ht⟩ := c.exists_free_lift_of_imageSieve J B R f s hc
  exact ⟨c, t, ht⟩

/-- The short exact coefficient form of finite-cover local lifting. -/
theorem exists_finiteBasisCover_lift_of_shortExact
    (hB : HasFiniteBasisCoverRefinements J B)
    (S : ShortComplex (Sheaf J (ModuleCat.{w} R))) (hS : S.ShortExact)
    (i : ι)
    (s : (freeSheafFunctor J R).obj (shrinkYoneda.{w}.obj (B i)) ⟶ S.X₃) :
    ∃ (c : FiniteBasisCover J B (B i)) (t : c.freeSource J B R ⟶ S.X₂),
      t ≫ S.g = c.freeAugmentation J B R ≫ s := by
  have := hS.epi_g
  exact exists_finiteBasisCover_lift J B R hB S.g i s

end Langlands.Cohomology.SiteCech
