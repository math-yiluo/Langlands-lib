import Langlands.AlgebraicGeometry.Picard.ArtinianH2PrimitiveInjectivityStatement
import Langlands.AlgebraicGeometry.Picard.FieldH2PrimitiveInjectivityStatement
import Langlands.AlgebraicGeometry.Picard.ElementaryArtinianIdealCohomologyNaturalityStatement
import Langlands.AlgebraicGeometry.Modules.CohomologyPullbackCompositionProof
import Langlands.AlgebraicGeometry.Modules.CohomologyPullbackIdentityProof
import Langlands.AlgebraicGeometry.Modules.PullbackUnitProofs
import Langlands.AbelianScheme.Basic

/-! # Reduction of Artinian ideal H² primitive injectivity to the residue field -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.MonObj

namespace Langlands.AbelianScheme.ArtinianH2Reduction

open Langlands.AlgebraicGeometry.Modules.DerivedSections
open Langlands.AlgebraicGeometry.Picard.ElementaryArtinianIdealCohomology

section structurePull

variable {K : Type u} [Field K]

set_option backward.isDefEq.respectTransparency false in
/-- Structure-module pullback along an identity is the identity. -/
lemma structurePull_id (X : Over (Spec (CommRingCat.of K))) (n : ℕ) :
    structurePull (𝟙 X) n = LinearMap.id := by
  unfold structurePull
  rw [← ModuleCat.hom_id]
  congr 1
  have h : (Langlands.Scheme.Modules.pullbackUnitIso (𝟙 X : X ⟶ X).left).hom =
      (Scheme.Modules.pullbackId X.left).hom.app (SheafOfModules.unit X.left.ringCatSheaf) :=
    Langlands.Scheme.Modules.pullbackUnitIdentity X.left
  rw [h]
  exact relativeCohomologyPullback_identity _ n

set_option backward.isDefEq.respectTransparency false in
/-- Structure-module pullback is contravariantly functorial. -/
lemma structurePull_comp {X Y Z : Over (Spec (CommRingCat.of K))} (h : Y ⟶ X) (k : Z ⟶ Y)
    (n : ℕ) : structurePull (k ≫ h) n = (structurePull k n).comp (structurePull h n) := by
  unfold structurePull
  rw [← ModuleCat.hom_comp]
  congr 1
  have hc : (Scheme.Modules.pullbackComp k.left h.left).hom.app
        (SheafOfModules.unit X.left.ringCatSheaf) ≫
      (Langlands.Scheme.Modules.pullbackUnitIso (k ≫ h).left).hom =
      (Scheme.Modules.pullback k.left).map (Langlands.Scheme.Modules.pullbackUnitIso h.left).hom ≫
        (Langlands.Scheme.Modules.pullbackUnitIso k.left).hom :=
    Langlands.Scheme.Modules.pullbackUnitComposition Z.left Y.left X.left k.left h.left
  rw [← relativeCohomologyPullback_comp h k]
  simp only [Category.assoc, ← Functor.map_comp, hc]
  rw [Functor.map_comp, relativeCohomologyPullback_naturality_assoc]

/-- Structure-module pullback along an isomorphism is injective. -/
lemma structurePull_injective_of_iso {X Y : Over (Spec (CommRingCat.of K))} (e : Y ≅ X)
    (n : ℕ) : Function.Injective (structurePull e.hom n) := by
  have h := structurePull_comp e.hom e.inv n
  rw [e.inv_hom_id, structurePull_id] at h
  exact Function.LeftInverse.injective (g := structurePull e.inv n)
    fun x => (LinearMap.congr_fun h x).symm

end structurePull

section residue

variable {R : CommRingCat.{u}} {K : Type u} [Field K]
  (s : Spec (CommRingCat.of K) ⟶ Spec R) (A : AbelianScheme (Spec R))

open scoped CategoryTheory.Obj

/-- Base change of the self-product, compared with the self-product of the base change. -/
def prodIso : (Over.pullback s).obj (A.X ⨯ A.X) ≅
    ((AbelianScheme.baseChange s).obj A).X ⨯ ((AbelianScheme.baseChange s).obj A).X :=
  PreservesLimitPair.iso (Over.pullback s) A.X A.X

lemma prodIso_hom_fst :
    (prodIso s A).hom ≫ Limits.prod.fst = (Over.pullback s).map Limits.prod.fst :=
  prodComparison_fst (Over.pullback s) A.X A.X

lemma prodIso_hom_snd :
    (prodIso s A).hom ≫ Limits.prod.snd = (Over.pullback s).map Limits.prod.snd :=
  prodComparison_snd (Over.pullback s) A.X A.X

set_option backward.isDefEq.respectTransparency false in
lemma prodIso_hom_mul :
    (prodIso s A).hom ≫ (Limits.prod.fst * Limits.prod.snd) =
      (Over.pullback s).map (Limits.prod.fst * Limits.prod.snd : A.X ⨯ A.X ⟶ A.X) := by
  rw [Functor.map_mul, ← prodIso_hom_fst, ← prodIso_hom_snd]
  exact MonObj.comp_mul _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- The field case for the base change of `A` gives injectivity of the reduced
coproduct on the base change of the original group-law diagram. -/
lemma residue_injective (hField : FieldH2PrimitiveInjectivityStatement.{u}) :
    Function.Injective
      (structurePull ((Over.pullback s).map
          (Limits.prod.fst * Limits.prod.snd : A.X ⨯ A.X ⟶ A.X)) 2 -
        structurePull ((Over.pullback s).map (Limits.prod.fst : A.X ⨯ A.X ⟶ A.X)) 2 -
        structurePull ((Over.pullback s).map (Limits.prod.snd : A.X ⨯ A.X ⟶ A.X)) 2) := by
  have hK := hField K ((AbelianScheme.baseChange s).obj A)
  rw [← prodIso_hom_mul, ← prodIso_hom_fst, ← prodIso_hom_snd,
    structurePull_comp, structurePull_comp, structurePull_comp,
    ← LinearMap.comp_sub, ← LinearMap.comp_sub]
  exact (structurePull_injective_of_iso (prodIso s A) 2).comp hK

end residue

/-- A binary product of flat proper schemes over `S` is flat and proper over `S`. -/
lemma prod_flat_proper {S : Scheme.{u}} (X Y : Over S)
    [Flat X.hom] [IsProper X.hom] [Flat Y.hom] [IsProper Y.hom] :
    Flat (X ⨯ Y).hom ∧ IsProper (X ⨯ Y).hom := by
  have hP : IsPullback (prod.fst (X := X) (Y := Y)).left
      (prod.snd (X := X) (Y := Y)).left X.hom Y.hom :=
    Over.isPullback_of_binaryFan_isLimit
      (BinaryFan.mk (prod.fst (X := X) (Y := Y)) (prod.snd (X := X) (Y := Y)))
      (prodIsProd X Y)
  have : Flat (prod.fst (X := X) (Y := Y)).left :=
    MorphismProperty.of_isPullback hP.flip inferInstance
  have : IsProper (prod.fst (X := X) (Y := Y)).left :=
    MorphismProperty.of_isPullback hP.flip inferInstance
  rw [← (prod.fst (X := X) (Y := Y)).w]
  exact ⟨inferInstance, inferInstance⟩

end Langlands.AbelianScheme.ArtinianH2Reduction

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard.ElementaryArtinianIdealCohomology
  Langlands.AlgebraicGeometry.Picard.StructureKernelModule ArtinianH2Reduction

/-- The elementary-ideal naturality statement and the field case together imply
the Artinian reduced-coproduct injectivity statement. -/
def ArtinianH2PrimitiveInjectivityReductionStatement : Prop :=
  NaturalityStatement.{u} → FieldH2PrimitiveInjectivityStatement.{u} →
    ArtinianH2PrimitiveInjectivityStatement.{u}

set_option backward.isDefEq.respectTransparency false in
/-- Coordinatewise reduction of the Artinian statement to the residue field. -/
theorem ArtinianH2PrimitiveInjectivityStatement.of_naturality :
    ArtinianH2PrimitiveInjectivityReductionStatement.{u} := by
  intro hN hField B' B _ _ _ _ _ _ φ hφ hker A j P p1 p2 m i iP compatible pull km k1 k2
    hm h1 h2
  obtain ⟨hPf, hPp⟩ := prod_flat_proper A.X A.X
  obtain ⟨d, eX, eY, hnat⟩ := hN B' B φ hφ hker A.X P 2
  intro x y hxy
  apply eX.injective
  funext l
  apply residue_injective (residueBaseMap φ) A hField
  have key : ∀ (f : P ⟶ A.X)
      (k : kernelModule i ⟶ (Scheme.Modules.pushforward f.left).obj (kernelModule iP)),
      compatible f k → ∀ z, eY (pull f k z) l =
        structurePull ((residuePullback φ).map f) 2 (eX z l) :=
    fun f k hk z => hnat f k hk z l
  have hl := congrArg (fun z => eY z l) hxy
  simp only [LinearMap.sub_apply, map_sub, Pi.sub_apply] at hl
  rw [key m km hm, key m km hm, key p1 k1 h1, key p1 k1 h1,
    key p2 k2 h2, key p2 k2 h2] at hl
  simpa only [LinearMap.sub_apply] using hl

end Langlands.AbelianScheme
