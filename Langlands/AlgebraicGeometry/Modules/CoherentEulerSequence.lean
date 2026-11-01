import Langlands.AlgebraicGeometry.Modules.CoherentGraphSupport
import Langlands.AlgebraicGeometry.Modules.ProperCoherentCohomologyFiniteProof
import Langlands.AlgebraicGeometry.Modules.EulerCharacteristicAdditivityProof
import Langlands.AlgebraicGeometry.Modules.EulerCharacteristicBasicProof
import Langlands.AlgebraicGeometry.Modules.TensorPowerIsomorphisms
import Langlands.AlgebraicGeometry.Picard.LineBundleInverse
import Langlands.AlgebraicGeometry.Picard.TensorRankOneProof
import Mathlib.CategoryTheory.Products.Bifunctor

/-! # Euler sequences of coherent modules twisted by line bundles -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Modules

open Langlands.Scheme.Modules

variable {X : Scheme.{u}}

/-- Tensor by a fixed actual module sheaf in the second variable. -/
def tensorBy (L : X.Modules) : X.Modules ⥤ X.Modules :=
  CategoryTheory.Prod.sectL X.Modules L ⋙ tensorFunctor X

/-- The fixed-variable explicit tensor agrees with the localized monoidal tensor. -/
def tensorRightIsoTensorBy (L : X.Modules) :
    MonoidalCategory.tensorRight L ≅ tensorBy L :=
  NatIso.ofComponents (fun M => (localizedTensorNatIso X).app (M, L)) (by
    intro M N φ
    change MonoidalCategory.whiskerRight φ L ≫ (localizedTensorNatIso X).hom.app (N, L) =
      (localizedTensorNatIso X).hom.app (M, L) ≫ (tensorFunctor X).map
        (CategoryTheory.Prod.mkHom φ (𝟙 L))
    have h := (localizedTensorNatIso X).hom.naturality
      (CategoryTheory.Prod.mkHom φ (𝟙 L))
    simpa only [MonoidalCategory.tensor_map, MonoidalCategory.tensorHom_id] using h)

/-- Tensoring with a line bundle is an equivalence of actual module categories. -/
lemma tensorBy_isEquivalence (L : X.Modules) (hL : Picard.IsLocallyFreeRankOne L) :
    (tensorBy L).IsEquivalence := by
  have : (MonoidalCategory.tensorLeft L).IsEquivalence :=
    (Picard.tensorInvertible_iff_tensorLeft_isEquivalence X L).1
      (Picard.LineBundle.toInvertibleSheaf ⟨L, hL⟩).property
  have : (MonoidalCategory.tensorRight L).IsEquivalence :=
    Functor.isEquivalence_of_iso (BraidedCategory.tensorLeftIsoTensorRight L)
  exact Functor.isEquivalence_of_iso (tensorRightIsoTensorBy L)

/-- Tensoring a short exact sequence with a line bundle preserves short exactness. -/
lemma shortExact_tensorBy (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (L : X.Modules) (hL : Picard.IsLocallyFreeRankOne L) :
    letI := tensorBy_isEquivalence L hL
    (S.map (tensorBy L)).ShortExact := by
  have := tensorBy_isEquivalence L hL
  exact hS.map_of_exact (tensorBy L)

namespace DerivedSections

variable {K : Type u} [Field K]
    (f : X ⟶ Spec (CommRingCat.of K)) [IsProper f]

/-- Proper coherent modules over a field have finite actual cohomology. -/
lemma hasFiniteCohomology_of_coherent (M : X.Modules) [M.IsQuasicoherent]
    (hM : HasFiniteAffineSections M) : HasFiniteCohomology f M :=
  properCoherentCohomologyFinite K X f inferInstance M inferInstance hM

/-- The Euler characteristic with its actual proper-coherent finiteness proof. -/
def coherentEulerCharacteristic (M : X.Modules) [M.IsQuasicoherent]
    (hM : HasFiniteAffineSections M) : ℤ :=
  eulerCharacteristic f M (hasFiniteCohomology_of_coherent f M hM)

/-- Actual Euler characteristics of a coherent module twisted by all powers of a line bundle. -/
def coherentEulerSequence (M : X.Modules) [M.IsQuasicoherent]
    (hM : HasFiniteAffineSections M) (L : Picard.LineBundle X) : ℕ → ℚ := fun n => by
  have hL := Picard.tensorPow_isLocallyFreeRankOne X L n
  have := QuasicoherentLocal.isQuasicoherent_tensor_lineBundle M _ hL
  exact (coherentEulerCharacteristic f (tensorObj M (tensorPow L.obj n))
    (hM.tensor_lineBundle hL) : ℚ)

/-- Actual Euler characteristics are invariant under coherent module isomorphisms. -/
lemma coherentEulerCharacteristic_iso {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent]
    (hM : HasFiniteAffineSections M) (hN : HasFiniteAffineSections N) (i : M ≅ N) :
    coherentEulerCharacteristic f M hM = coherentEulerCharacteristic f N hN :=
  eulerCharacteristic_eq_of_iso f _ _ i

/-- Actual twisted Euler sequences are invariant under coherent module isomorphisms. -/
lemma coherentEulerSequence_iso {M N : X.Modules}
    [M.IsQuasicoherent] [N.IsQuasicoherent]
    (hM : HasFiniteAffineSections M) (hN : HasFiniteAffineSections N)
    (L : Picard.LineBundle X) (i : M ≅ N) :
    coherentEulerSequence f M hM L = coherentEulerSequence f N hN L := by
  ext n
  have hL := Picard.tensorPow_isLocallyFreeRankOne X L n
  have := QuasicoherentLocal.isQuasicoherent_tensor_lineBundle M _ hL
  have := QuasicoherentLocal.isQuasicoherent_tensor_lineBundle N _ hL
  exact congrArg (Int.cast : ℤ → ℚ) (coherentEulerCharacteristic_iso f
    (hM.tensor_lineBundle hL) (hN.tensor_lineBundle hL)
    ((tensorFunctor X).mapIso (i.prod (Iso.refl _))))

/-- The coherent Euler characteristic is additive on short exact sequences. -/
lemma coherentEulerCharacteristic_add (S : ShortComplex X.Modules) (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]
    (h₁ : HasFiniteAffineSections S.X₁) (h₂ : HasFiniteAffineSections S.X₂)
    (h₃ : HasFiniteAffineSections S.X₃) :
    coherentEulerCharacteristic f S.X₂ h₂ =
      coherentEulerCharacteristic f S.X₁ h₁ + coherentEulerCharacteristic f S.X₃ h₃ :=
  eulerCharacteristicAdditivity K X f S hS _ _ _

/-- The actual twisted Euler sequence is additive on short exact sequences. -/
lemma coherentEulerSequence_add (S : ShortComplex X.Modules) (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent]
    (h₁ : HasFiniteAffineSections S.X₁) (h₂ : HasFiniteAffineSections S.X₂)
    (h₃ : HasFiniteAffineSections S.X₃) (L : Picard.LineBundle X) :
    coherentEulerSequence f S.X₂ h₂ L =
      coherentEulerSequence f S.X₁ h₁ L + coherentEulerSequence f S.X₃ h₃ L := by
  ext n
  have hL := Picard.tensorPow_isLocallyFreeRankOne X L n
  have := tensorBy_isEquivalence (tensorPow L.obj n) hL
  have := QuasicoherentLocal.isQuasicoherent_tensor_lineBundle S.X₁ _ hL
  have := QuasicoherentLocal.isQuasicoherent_tensor_lineBundle S.X₂ _ hL
  have := QuasicoherentLocal.isQuasicoherent_tensor_lineBundle S.X₃ _ hL
  let T := S.map (tensorBy (tensorPow L.obj n))
  have : T.X₁.IsQuasicoherent := inferInstanceAs
    (tensorObj S.X₁ (tensorPow L.obj n)).IsQuasicoherent
  have : T.X₂.IsQuasicoherent := inferInstanceAs
    (tensorObj S.X₂ (tensorPow L.obj n)).IsQuasicoherent
  have : T.X₃.IsQuasicoherent := inferInstanceAs
    (tensorObj S.X₃ (tensorPow L.obj n)).IsQuasicoherent
  have h := coherentEulerCharacteristic_add f T (shortExact_tensorBy S hS _ hL)
    (h₁.tensor_lineBundle hL) (h₂.tensor_lineBundle hL) (h₃.tensor_lineBundle hL)
  change (coherentEulerCharacteristic f T.X₂ _ : ℚ) =
    (coherentEulerCharacteristic f T.X₁ _ : ℚ) + (coherentEulerCharacteristic f T.X₃ _ : ℚ)
  exact_mod_cast h

/-- The Euler characteristic of a zero coherent module vanishes. -/
lemma coherentEulerCharacteristic_zero (M : X.Modules) [M.IsQuasicoherent]
    (hM : HasFiniteAffineSections M) (hz : IsZero M) :
    coherentEulerCharacteristic f M hM = 0 := by
  exact (eulerCharacteristicBasic K X f).2.2.2.1 M _ (fun n =>
    NoetherianVanishing.isZero_relativeCohomology_of_isZero f hz n)

/-- A zero coherent module has the zero twisted Euler sequence. -/
lemma coherentEulerSequence_zero (M : X.Modules) [M.IsQuasicoherent]
    (hM : HasFiniteAffineSections M) (L : Picard.LineBundle X) (hz : IsZero M) :
    coherentEulerSequence f M hM L = 0 := by
  ext n
  have hL := Picard.tensorPow_isLocallyFreeRankOne X L n
  have := QuasicoherentLocal.isQuasicoherent_tensor_lineBundle M _ hL
  have hz' := ((HasSupportDimensionLT.of_isZero hz 0).tensor_lineBundle hL).isZero
  change (coherentEulerCharacteristic f (tensorObj M (tensorPow L.obj n))
    (hM.tensor_lineBundle hL) : ℚ) = 0
  exact_mod_cast coherentEulerCharacteristic_zero f _ (hM.tensor_lineBundle hL) hz'

/-- Twisting the coefficient module once shifts its Euler sequence by one. -/
lemma coherentEulerSequence_shift (M : X.Modules) [M.IsQuasicoherent]
    (hM : HasFiniteAffineSections M) (L : Picard.LineBundle X) (n : ℕ) :
    letI := QuasicoherentLocal.isQuasicoherent_tensor_lineBundle M L.obj L.property
    coherentEulerSequence f (tensorObj M L.obj) (hM.tensor_lineBundle L.property) L n =
      coherentEulerSequence f M hM L (n + 1) := by
  have := QuasicoherentLocal.isQuasicoherent_tensor_lineBundle M L.obj L.property
  have hLn := Picard.tensorPow_isLocallyFreeRankOne X L n
  have hLs := Picard.tensorPow_isLocallyFreeRankOne X L (n + 1)
  have := QuasicoherentLocal.isQuasicoherent_tensor_lineBundle (tensorObj M L.obj) _ hLn
  have := QuasicoherentLocal.isQuasicoherent_tensor_lineBundle M _ hLs
  exact congrArg (Int.cast : ℤ → ℚ) (coherentEulerCharacteristic_iso f
    ((hM.tensor_lineBundle L.property).tensor_lineBundle hLn) (hM.tensor_lineBundle hLs)
    (tensorAssociator M L.obj (tensorPow L.obj n)))

end DerivedSections

end Langlands.AlgebraicGeometry.Modules
