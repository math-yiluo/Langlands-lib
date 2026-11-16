import Langlands.Cohomology.SiteCech.FreeSections
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Preadditive.Injective.Resolution

/-! # Cocycle sections of exact sheaf complexes are locally boundaries -/

noncomputable section

namespace Langlands.Cohomology.SiteCech

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable (R : Type w) [CommRing R] [HasSheafify J (ModuleCat.{w} R)]
variable [LocallySmall.{w} C]

/-- Regard a section killed by the second arrow of a short complex as a section
of its sheaf of cycles. -/
def cycleSection (S : ShortComplex (Sheaf J (ModuleCat.{w} R))) {U : C}
    (s : S.X₂.obj.obj (op U)) (hs : S.g.hom.app (op U) s = 0) :
    S.cycles.obj.obj (op U) :=
  freeRepresentableHomEquiv J R U S.cycles
    (S.liftCycles ((freeRepresentableHomEquiv J R U S.X₂).symm s) (by
      apply (freeRepresentableHomEquiv J R U S.X₃).injective
      rw [freeRepresentableHomEquiv_naturality_right]
      change _ = 0
      simpa only [Equiv.apply_symm_apply] using hs))

/-- The cycle section has the original section as its image. -/
theorem cycleSection_i (S : ShortComplex (Sheaf J (ModuleCat.{w} R))) {U : C}
    (s : S.X₂.obj.obj (op U)) (hs : S.g.hom.app (op U) s = 0) :
    S.iCycles.hom.app (op U) (cycleSection J R S s hs) = s := by
  unfold cycleSection
  rw [← freeRepresentableHomEquiv_naturality_right, S.liftCycles_i]
  exact Equiv.apply_symm_apply _ _

variable [J.WEqualsLocallyBijective (ModuleCat.{w} R)]

/-- In an exact short complex of module sheaves, every section killed by the
second arrow is locally in the image of the first arrow. -/
theorem imageSieve_mem_of_exact (S : ShortComplex (Sheaf J (ModuleCat.{w} R)))
    (hS : S.Exact) {U : C} (s : S.X₂.obj.obj (op U))
    (hs : S.g.hom.app (op U) s = 0) :
    Presheaf.imageSieve S.f.hom s ∈ J U := by
  have : Epi S.toCycles := hS.epi_toCycles
  have : Sheaf.IsLocallySurjective S.toCycles :=
    (Sheaf.isLocallySurjective_iff_epi' (φ := S.toCycles)).2 inferInstance
  refine J.superset_covering ?_
    (Presheaf.imageSieve_mem J S.toCycles.hom (cycleSection J R S s hs))
  intro V a ha
  obtain ⟨t, ht⟩ := ha
  refine ⟨t, ?_⟩
  have h := congrArg (fun z => S.iCycles.hom.app (op V) z) ht
  have hf := congrArg (fun k : S.X₁ ⟶ S.X₂ => k.hom.app (op V) t) S.toCycles_i
  change S.iCycles.hom.app (op V) (S.toCycles.hom.app (op V) t) =
    S.f.hom.app (op V) t at hf
  rw [hf, NatTrans.naturality_apply, cycleSection_i] at h
  exact h

/-- Every positive-degree cocycle section in an injective resolution is a
boundary on a covering sieve. -/
theorem imageSieve_mem_of_injectiveResolution
    {F : Sheaf J (ModuleCat.{w} R)} (I : InjectiveResolution F) (n : ℕ)
    {U : C} (s : (I.cocomplex.X (n + 1)).obj.obj (op U))
    (hs : (I.cocomplex.d (n + 1) (n + 2)).hom.app (op U) s = 0) :
    Presheaf.imageSieve (I.cocomplex.d n (n + 1)).hom s ∈ J U :=
  imageSieve_mem_of_exact J R _ (I.exact_succ n) s hs

end Langlands.Cohomology.SiteCech
