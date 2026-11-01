import Langlands.Algebra.RegularTensorContractionStatements

/-!
# Naturality of the original regular-tensor comparison

Intrinsic whole-map consequences of the original contraction and the published
comparison interfaces. These lemmas do not assume a nondegenerate ambient module.
-/

set_option autoImplicit false

namespace Langlands.Algebra.RegularTensorContraction

universe uA uM uN

variable (A : Type uA) [NonUnitalRing A]
  {M : Type uM} [AddCommGroup M] [NonUnitalModule A M]
  {N : Type uN} [AddCommGroup N] [NonUnitalModule A N]

/-- The actual tensor map intertwines the complete contraction maps. -/
theorem contraction_naturality (f : NonUnitalModuleHom A M N) :
    ContractionNaturality A f := by
  let _ := NonUnitalModule.rightRegular A
  apply NonUnitalModuleTensor.hom_ext A
  intro a m
  change a • f m = f (a • m)
  exact (f.map_smul a m).symm

/-- Both comparison directions are natural for every pair of actual witnesses. -/
theorem comparison_naturality (hA : IsIdempotented A)
    (f : NonUnitalModuleHom A M N) : ComparisonNaturality A hA f := by
  let _ := tensorModule A M
  let _ := tensorModule A N
  intro FM GM FN GN hM hN
  have hF :
      (NonUnitalModuleHom.restrictNondegeneratePart hA f).toAddMonoidHom.comp
          FM.toAddMonoidHom = FN.toAddMonoidHom.comp (tensorMap A f) := by
    apply AddMonoidHom.ext
    intro t
    apply Subtype.ext
    change f (FM t).val = (FN (tensorMap A f t)).val
    have hm : (FM t).val = contraction A M t :=
      DFunLike.congr_fun hM.1 t
    have hn : (FN (tensorMap A f t)).val =
        contraction A N (tensorMap A f t) :=
      DFunLike.congr_fun hN.1 (tensorMap A f t)
    have hc : contraction A N (tensorMap A f t) = f (contraction A M t) :=
      DFunLike.congr_fun (contraction_naturality A f) t
    exact (congrArg f hm).trans (hc.symm.trans hn.symm)
  refine ⟨hF, ?_⟩
  apply AddMonoidHom.ext
  intro m
  have hn : GN (FN (tensorMap A f (GM m))) = tensorMap A f (GM m) :=
    congrArg (fun k : NonUnitalModuleHom A (Tensor A N) (Tensor A N) =>
      k (tensorMap A f (GM m))) hN.2.1
  have hm : FM (GM m) = m :=
    congrArg (fun k : NonUnitalModuleHom A (nondegeneratePart hA M)
      (nondegeneratePart hA M) => k m) hM.2.2.1
  change tensorMap A f (GM m) =
    GN (NonUnitalModuleHom.restrictNondegeneratePart hA f m)
  calc
    tensorMap A f (GM m) = GN (FN (tensorMap A f (GM m))) := hn.symm
    _ = GN (NonUnitalModuleHom.restrictNondegeneratePart hA f (FM (GM m))) :=
      congrArg GN (DFunLike.congr_fun hF (GM m)).symm
    _ = GN (NonUnitalModuleHom.restrictNondegeneratePart hA f m) := by rw [hm]

/-! Complete unapplied types, including unequal universes in both directions. -/

example : ∀ (A : Type uA) [NonUnitalRing A]
    {M : Type uM} [AddCommGroup M] [NonUnitalModule A M]
    {N : Type uN} [AddCommGroup N] [NonUnitalModule A N]
    (f : NonUnitalModuleHom A M N), ContractionNaturality A f :=
  @contraction_naturality

example : ∀ (A : Type uA) [NonUnitalRing A]
    {M : Type uM} [AddCommGroup M] [NonUnitalModule A M]
    {N : Type uN} [AddCommGroup N] [NonUnitalModule A N]
    (hA : IsIdempotented A) (f : NonUnitalModuleHom A M N),
      ComparisonNaturality A hA f :=
  @comparison_naturality

example : ∀ (A : Type 0) [NonUnitalRing A]
    {M : Type 1} [AddCommGroup M] [NonUnitalModule A M]
    {N : Type 2} [AddCommGroup N] [NonUnitalModule A N]
    (f : NonUnitalModuleHom A M N), ContractionNaturality A f :=
  @contraction_naturality.{0, 1, 2}

example : ∀ (A : Type 0) [NonUnitalRing A]
    {M : Type 1} [AddCommGroup M] [NonUnitalModule A M]
    {N : Type 2} [AddCommGroup N] [NonUnitalModule A N]
    (hA : IsIdempotented A) (f : NonUnitalModuleHom A M N),
      ComparisonNaturality A hA f :=
  @comparison_naturality.{0, 1, 2}

example : ∀ (A : Type 2) [NonUnitalRing A]
    {M : Type 1} [AddCommGroup M] [NonUnitalModule A M]
    {N : Type 0} [AddCommGroup N] [NonUnitalModule A N]
    (f : NonUnitalModuleHom A M N), ContractionNaturality A f :=
  @contraction_naturality.{2, 1, 0}

example : ∀ (A : Type 2) [NonUnitalRing A]
    {M : Type 1} [AddCommGroup M] [NonUnitalModule A M]
    {N : Type 0} [AddCommGroup N] [NonUnitalModule A N]
    (hA : IsIdempotented A) (f : NonUnitalModuleHom A M N),
      ComparisonNaturality A hA f :=
  @comparison_naturality.{2, 1, 0}

end Langlands.Algebra.RegularTensorContraction
