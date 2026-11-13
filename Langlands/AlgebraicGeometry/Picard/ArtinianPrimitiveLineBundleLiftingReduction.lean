import Langlands.AlgebraicGeometry.Picard.ArtinianPrimitiveLineBundleLiftingFromPrerequisites
import Langlands.AlgebraicGeometry.Picard.ArtinianPrimitiveLineBundleLiftingStatement
import Langlands.AlgebraicGeometry.Picard.ArtinianH2PrimitiveInjectivityStatement
import Langlands.AlgebraicGeometry.Picard.SquareZeroObstructionMorphismNaturalityStatement
import Langlands.AlgebraicGeometry.Picard.StructureKernelMorphism
import Langlands.AlgebraicGeometry.Picard.AffineBaseChangeKernel
import Langlands.AlgebraicGeometry.Picard.SquareZeroPicardObstruction
import Langlands.AlgebraicGeometry.Picard.LineBundleInverse
import Langlands.AlgebraicGeometry.Picard.Functor
import Langlands.AlgebraicGeometry.Modules.PullbackTensorProof

/-! # Lifting primitive line bundles from obstruction naturality and ideal-H² injectivity -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.MonObj CategoryTheory.Obj

namespace Langlands.AbelianScheme.ArtinianPrimitiveLineBundleLiftingReduction

open Langlands.AlgebraicGeometry.Picard
open Langlands.AlgebraicGeometry.Picard.StructureKernelModule
open Langlands.Scheme.Modules Langlands.AlgebraicGeometry.Modules.DerivedSections

/-- Assume naturality of square-zero Picard obstructions under morphisms of thickenings
and injectivity of the reduced coproduct `μ^* - p₁^* - p₂^*` on the ideal H² of an
elementary Artinian thickening. Then a line bundle on the special fibre `A₀` of an
abelian scheme over a local Artinian ring whose multiplication pullback is isomorphic to
the tensor product of its two projection pullbacks lifts along `A₀ ⟶ A`. -/
theorem artinianPrimitiveLineBundleLifting_of
    (naturality : SquareZeroObstructionMorphismNaturalityStatement.{u})
    (injectivity : ArtinianH2PrimitiveInjectivityStatement.{u}) :
    ArtinianPrimitiveLineBundleLiftingStatement.{u} := by
  intro B' B _ _ _ _ _ _ φ hφ hm A j A₀ L hL
  obtain ⟨e⟩ := hL
  let i : A₀.X.left ⟶ A.X.left := pullback.fst A.X.hom j
  have : IsClosedImmersion i := AffineBaseChangeKernel.isClosedImmersion φ A.X.hom hφ
  have hi : i.ker ^ 2 = ⊥ := AffineBaseChangeKernel.ker_sq φ A.X.hom hφ hm
  have : CompactSpace A.X.left := QuasiCompact.compactSpace_of_compactSpace A.X.hom
  have : CompactSpace A₀.X.left := QuasiCompact.compactSpace_of_compactSpace i
  suffices ho : SquareZeroPicardObstruction.obstructionMap i hi L.classOf = 0 by
    obtain ⟨M, ⟨e'⟩⟩ := (SquareZeroPicardObstruction.lineBundle_lift_iff i hi L).mpr ho
    exact ⟨M, ⟨ObjectProperty.isoMk _ e'⟩⟩
  -- The product over the Artinian base and its special fibre.
  let P : Over (Spec (CommRingCat.of B')) := A.X ⨯ A.X
  let p1 : P ⟶ A.X := Limits.prod.fst
  let p2 : P ⟶ A.X := Limits.prod.snd
  let m : P ⟶ A.X := p1 * p2
  let iP : pullback P.hom j ⟶ P.left := pullback.fst P.hom j
  have : IsClosedImmersion iP := AffineBaseChangeKernel.isClosedImmersion φ P.hom hφ
  have hiP : iP.ker ^ 2 = ⊥ := AffineBaseChangeKernel.ker_sq φ P.hom hφ hm
  have : CompactSpace P.left :=
    QuasiCompact.compactSpace_of_compactSpace (Over.prodLeftIsoPullback A.X A.X).hom
  have : CompactSpace (Over.pullback j |>.obj P).left :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.fst P.hom j)
  let g : (P ⟶ A.X) → (pullback P.hom j ⟶ A₀.X.left) := fun f ↦ ((Over.pullback j).map f).left
  have w : ∀ f : P ⟶ A.X, iP ≫ f.left = g f ≫ i := fun f ↦ by
    simp only [g, iP, i, Over.pullback_map_left]
    exact (pullback.lift_fst _ _ _).symm
  let k : ∀ f : P ⟶ A.X,
      kernelModule i ⟶ (Scheme.Modules.pushforward f.left).obj (kernelModule iP) :=
    fun f ↦ StructureKernelMorphism.kernelModuleMap f.left i iP (g f) (w f)
  have hk : ∀ f : P ⟶ A.X, k f ≫ (Scheme.Modules.pushforward f.left).map (kernelModuleι iP) =
      kernelModuleι i ≫ unitToPushforwardUnit f.left :=
    fun f ↦ StructureKernelMorphism.kernelModuleMap_ι f.left i iP (g f) (w f)
  have hnat := fun f : P ⟶ A.X ↦
    naturality (CommRingCat.of B') A.X P f A₀.X.left (pullback P.hom j) i iP (g f) hi hiP
      (w f) (k f) (hk f) L.classOf
  -- Primitivity in the Picard group of the special fibre of `P`.
  let E : (Over.pullback j).obj P ⟶ A₀.X ⨯ A₀.X :=
    prod.lift ((Over.pullback j).map p1) ((Over.pullback j).map p2)
  have hE1 : E ≫ Limits.prod.fst = (Over.pullback j).map p1 := prod.lift_fst _ _
  have hE2 : E ≫ Limits.prod.snd = (Over.pullback j).map p2 := prod.lift_snd _ _
  have hEm : E ≫ ((Limits.prod.fst : A₀.X ⨯ A₀.X ⟶ A₀.X) * Limits.prod.snd) =
      (Over.pullback j).map m := by
    rw [MonObj.comp_mul, hE1, hE2]
    exact (Functor.map_mul (Over.pullback j) p1 p2).symm
  have hprim := ArtinianPrimitiveLineBundleLifting.pullback_classOf_eq_add _ _ _ L e
  have hadd : Group.pullback (g m) L.classOf =
      Group.pullback (g p1) L.classOf + Group.pullback (g p2) L.classOf := by
    have h1 : g p1 = E.left ≫ (Limits.prod.fst : A₀.X ⨯ A₀.X ⟶ A₀.X).left := by
      rw [← Over.comp_left, hE1]
    have h2 : g p2 = E.left ≫ (Limits.prod.snd : A₀.X ⨯ A₀.X ⟶ A₀.X).left := by
      rw [← Over.comp_left, hE2]
    have h3 : g m = E.left ≫
        ((Limits.prod.fst : A₀.X ⨯ A₀.X ⟶ A₀.X) * Limits.prod.snd).left :=
      (congrArg CommaMorphism.left hEm).symm
    rw [h1, h2, h3, Group.pullback_comp, Group.pullback_comp, Group.pullback_comp,
      AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, AddMonoidHom.comp_apply, hprim,
      map_add]
  -- Injectivity on the ideal H² of the special fibre of `A`.
  let ρ := SquareZeroRelativeObstructionNaturality.relativeIdealCohomologyAddEquiv A.X.hom i 2
  let ρP := SquareZeroRelativeObstructionNaturality.relativeIdealCohomologyAddEquiv P.hom iP 2
  let pull := fun (f : P ⟶ A.X)
      (κ : kernelModule i ⟶ (Scheme.Modules.pushforward f.left).obj (kernelModule iP)) ↦
    (relativeCohomologyPullback f (kernelModule i) 2 ≫
      (relativeCohomology P.hom 2).map
        (((Scheme.Modules.pullbackPushforwardAdjunction f.left).homEquiv _ _).symm κ)).hom
  have key : ∀ f : P ⟶ A.X,
      pull f (k f) (ρ (SquareZeroPicardObstruction.obstructionMap i hi L.classOf)) =
        ρP (SquareZeroPicardObstruction.obstructionMap iP hiP
          (Group.pullback (g f) L.classOf)) :=
    fun f ↦ (hnat f).symm
  have hinj : Function.Injective (pull m (k m) - pull p1 (k p1) - pull p2 (k p2)) :=
    injectivity B' B φ hφ hm A (k m) (k p1) (k p2) (hk m) (hk p1) (hk p2)
  apply ρ.injective
  rw [map_zero]
  apply hinj
  rw [map_zero, LinearMap.sub_apply, LinearMap.sub_apply, key m, key p1, key p2, hadd,
    map_add, map_add]
  abel

end Langlands.AbelianScheme.ArtinianPrimitiveLineBundleLiftingReduction
