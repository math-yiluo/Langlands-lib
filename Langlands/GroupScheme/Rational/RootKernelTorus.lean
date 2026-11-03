import Langlands.GroupScheme.Rational.RootSubgroup
import Langlands.GroupScheme.Rational.MaximalSplitTorusSubgroup
import Langlands.GroupScheme.Rational.BruhatCoveringReduction

/-! # Tori and normalizing points in full root-kernel centralizers -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section NormalizerTransport

variable {B : Scheme.{u}} {T : CommGroupScheme B} {H G : GroupScheme B}
    {iH : T.toGrp ⟶ H}

/-- A homomorphism carries a normalizing point to a normalizing point with the
same torus automorphism. -/
theorem IsNormalizingPoint.comp {n : Over.mk (𝟙 B) ⟶ H.X} {σ : T ≅ T}
    (hn : IsNormalizingPoint iH n σ) (j : H ⟶ G) :
    IsNormalizingPoint (iH ≫ j) (n ≫ j.hom.hom) σ := by
  change (iH ≫ j) ≫ (G.innerIso (n ≫ j.hom.hom)).hom =
    CommGroupScheme.groupHom σ.hom ≫ (iH ≫ j)
  rw [Category.assoc, ← innerIso_hom_comp, ← Category.assoc, hn, Category.assoc]

/-- Transport the actual rational normalizing points along a factorization of
the torus embedding. -/
def normalizerPointsMap (iH : T.toGrp ⟶ H) (j : H ⟶ G)
    (iG : T.toGrp ⟶ G) (hij : iH ≫ j = iG) :
    normalizerPoints iH →* normalizerPoints iG where
  toFun n := ⟨n.val ≫ j.hom.hom, by
    obtain ⟨σ, hσ⟩ := n.property
    exact ⟨σ, hij ▸ hσ.comp j⟩⟩
  map_one' := Subtype.ext (MonObj.one_comp _)
  map_mul' n m := Subtype.ext (MonObj.mul_comp n.val m.val _)

@[simp] theorem normalizerPointsMap_val (iH : T.toGrp ⟶ H) (j : H ⟶ G)
    (iG : T.toGrp ⟶ G) (hij : iH ≫ j = iG) (n : normalizerPoints iH) :
    (normalizerPointsMap iH j iG hij n).val = n.val ≫ j.hom.hom := rfl

/-- A monomorphic ambient inclusion preserves distinct normalizing points. -/
theorem normalizerPointsMap_injective (iH : T.toGrp ⟶ H) (j : H ⟶ G)
    (iG : T.toGrp ⟶ G) (hij : iH ≫ j = iG) [Mono j.hom.hom] :
    Function.Injective (normalizerPointsMap iH j iG hij) := by
  intro n m h
  apply Subtype.ext
  exact (cancel_mono j.hom.hom).mp (congrArg Subtype.val h)

/-- The transported normalizing point has exactly the same action on the
entire character lattice. -/
theorem weylAction_normalizerPointsMap (iH : T.toGrp ⟶ H) (j : H ⟶ G)
    (iG : T.toGrp ⟶ G) (hij : iH ≫ j = iG)
    [Mono iH.hom.hom.left] [Mono iG.hom.hom.left] (n : normalizerPoints iH) :
    weylAction iG (normalizerPointsMap iH j iG hij n) = weylAction iH n := by
  apply LinearEquiv.ext
  intro χ
  exact weylAction_eq iG
    (hij ▸ (isNormalizingPoint_normalizingAut iH n).comp j) χ

end NormalizerTransport

namespace RelativeRoot

variable {B : Scheme.{u}} {T : CommGroupScheme B} {G C : GroupScheme B}
    (i : T.toGrp ⟶ G) (a : characterLattice T)

/-- Centralizing the whole torus centralizes its full character kernel on
every test and every refinement. -/
theorem torusCentralizer_le_kernelCentralizer :
    torusCentralizer i ≤ kernelCentralizer i a := by
  intro U g hg
  rw [mem_kernelCentralizer]
  intro V b c
  simpa only [Grp.comp_hom_hom, Category.assoc] using
    hg V b (c ≫ (characterKernelι a).hom.hom)

/-- The torus is contained in the all-test centralizer of the full kernel of
every character, without a smoothness or primitivity hypothesis. -/
theorem range_le_kernelCentralizer :
    SubgroupFunctor.range i ≤ kernelCentralizer i a :=
  (range_le_torusCentralizer i).trans (torusCentralizer_le_kernelCentralizer i a)

variable (j : C ⟶ G) (hj : (kernelCentralizer i a).IsRepresentedBy j)

/-- The actual torus inclusion into a represented full kernel centralizer. -/
def kernelCentralizerTorus : T.toGrp ⟶ C :=
  hj.factorHom i (range_le_kernelCentralizer i a)

@[simp] theorem kernelCentralizerTorus_comp :
    kernelCentralizerTorus i a j hj ≫ j = i :=
  hj.factorHom_comp i (range_le_kernelCentralizer i a)

/-- Normalizers inside the represented centralizer map to actual ambient
normalizers of the original torus. -/
def kernelCentralizerNormalizerMap :
    normalizerPoints (kernelCentralizerTorus i a j hj) →* normalizerPoints i :=
  normalizerPointsMap _ j i (kernelCentralizerTorus_comp i a j hj)

@[simp] theorem kernelCentralizerNormalizerMap_val
    (n : normalizerPoints (kernelCentralizerTorus i a j hj)) :
    (kernelCentralizerNormalizerMap i a j hj n).val = n.val ≫ j.hom.hom := rfl

/-- These ambient points retain all-test centralization of the full kernel. -/
theorem kernelCentralizerNormalizerMap_mem
    (n : normalizerPoints (kernelCentralizerTorus i a j hj)) :
    (kernelCentralizerNormalizerMap i a j hj n).val ∈
      (kernelCentralizer i a).carrier (Over.mk (𝟙 B)) := by
  rw [kernelCentralizerNormalizerMap_val, ← hj.2]
  exact ⟨n.val, rfl⟩

/-- Transport out of the kernel centralizer preserves the whole-character
Weyl action. -/
theorem weylAction_kernelCentralizerNormalizerMap
    [Mono i.hom.hom.left]
    [Mono (kernelCentralizerTorus i a j hj).hom.hom.left]
    (n : normalizerPoints (kernelCentralizerTorus i a j hj)) :
    weylAction i (kernelCentralizerNormalizerMap i a j hj n) =
      weylAction (kernelCentralizerTorus i a j hj) n :=
  weylAction_normalizerPointsMap _ j i (kernelCentralizerTorus_comp i a j hj) n

end RelativeRoot

section Field

variable {k : Type u} [Field k]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}
    {G C : GroupScheme (Spec (CommRingCat.of k))}
    {i : T.toGrp ⟶ G} (hi : IsMaximalSplitTorus i)
    (a : characterLattice T) (j : C ⟶ G)
    (hj : (RelativeRoot.kernelCentralizer i a).IsRepresentedBy j)
    (hjc : IsClosedSubgroup j)

include hi hjc

/-- An ambient maximal split torus remains maximal split in the closed
representative of the full character-kernel centralizer. -/
theorem IsMaximalSplitTorus.kernelCentralizerTorus :
    IsMaximalSplitTorus (RelativeRoot.kernelCentralizerTorus i a j hj) :=
  IsMaximalSplitTorus.isMaximalSplitTorus_factorHom hi hj hjc
    (RelativeRoot.range_le_kernelCentralizer i a)

end Field

end Langlands.GroupScheme
