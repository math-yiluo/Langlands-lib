import Langlands.GroupScheme.GaloisCocycleRefinement
import Langlands.GroupScheme.Rational.NumberFieldTotallyComplexQuasiSplitTypeE6
import Langlands.GroupScheme.Reductive.RootDatumExistence
import Langlands.GroupScheme.Reductive.RootDatumGaloisCoroots
import Langlands.GroupScheme.Reductive.TitsIndexFieldExtensionCartan
import Langlands.GroupScheme.SimplyConnected.SimplyConnectedFieldExtensionProof
import Langlands.GroupScheme.SimplyConnected.SplitNecessity
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof
import Langlands.GroupScheme.Torus.FiniteGaloisTorusPermutationIndex
import Langlands.LinearAlgebra.CartanE6SylowPermutation
import Mathlib.FieldTheory.SeparableDegree

/-! # A uniform exponent for cocycles of maximal tori in type E6 -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option maxRecDepth 1600

/-- For a simply connected absolutely almost simple group of type E6 over a
characteristic-zero field, `2^13 * 3^8` kills every finite Galois cocycle of
each actual maximal torus on its original cover. -/
def TypeE6MaximalTorusUniformPowerStatement : Prop :=
  ∀ (F : Type u) [Field F] [CharZero F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (d : TitsIndexData G) (e : d.Vertex ≃ Fin 6), IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
    (∀ a b, d.cartan a b = CartanMatrix.E 6 (e a) (e b)) →
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G), IsMaximalTorus i →
      ∀ (L : Type u) [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
        (ξ : Cocycle T.toGrp (GaloisCocycle.cover F L)),
        (ξ.map (CommGroupScheme.groupHom ((2 ^ 13 * 3 ^ 8 : ℕ) • 𝟙 T))).IsTrivial

theorem typeE6MaximalTorusUniformPower : TypeE6MaximalTorusUniformPowerStatement.{u} := by
  classical
  intro F _ _ G _ _ d e hsc _ hcart T i hi L _ _ _ _ ξ
  let : Smooth G.X.hom := d.isSemisimple.isConnectedReductive.smooth
  have hTL := IsTorus.baseChange_of_isAlgebraic F L T.toGrp hi.1
  obtain ⟨N, hN, hAN, hfinN, hgalN, hsplitN⟩ := torusFiniteGaloisSplitting L _ hTL
  let : Algebra F N := ((algebraMap L N).comp (algebraMap F L)).toAlgebra
  let : IsScalarTower F L N := IsScalarTower.of_algebraMap_eq' rfl
  let : FiniteDimensional F N := FiniteDimensional.trans F L N
  let : Algebra.IsSeparable F N := Algebra.IsSeparable.trans F L N
  let f : N →ₐ[F] SeparableClosure F := IsSepClosed.lift
  let : Algebra N (SeparableClosure F) := f.toRingHom.toAlgebra
  let : IsScalarTower F N (SeparableClosure F) :=
    IsScalarTower.of_algebraMap_eq' f.comp_algebraMap.symm
  let E := IntermediateField.normalClosure F N (SeparableClosure F)
  let : Algebra L E := ((algebraMap N E).comp (algebraMap L N)).toAlgebra
  let : IsScalarTower F L E := IsScalarTower.of_algebraMap_eq' (by
    change algebraMap F E =
      (algebraMap N E).comp ((algebraMap L N).comp (algebraMap F L))
    rw [← IsScalarTower.algebraMap_eq F L N, ← IsScalarTower.algebraMap_eq F N E])
  let : FiniteDimensional L E := FiniteDimensional.right F L E
  let : IsGalois L E := IsGalois.tower_top_of_isGalois F L E
  let : IsAffine T.toGrp.X.left := SplittingAssembly.isAffine_of_isTorus T.toGrp hi.1
  let GE := (GroupScheme.baseChange (algebraBaseMap F E)).obj G
  let TE := (CommGroupScheme.baseChange (algebraBaseMap F E)).obj T
  let iE : TE.toGrp ⟶ GE := (GroupScheme.baseChange (algebraBaseMap F E)).map i
  have hsplitN' := (IsSplitTorus.baseChange_fieldTower_iff F L N T.toGrp).mpr hsplitN
  have hsplit : IsSplitTorus TE.toGrp := hsplitN'.baseChange_fieldTower F N E T.toGrp
  have hGE : IsConnectedReductive GE :=
    connectedReductiveFieldExtensionStatement F E G d.isSemisimple.isConnectedReductive
  let : IsAffineHom GE.X.hom := hGE.isAffineHom
  have hiE : IsMaximalTorus iE := (maximalTorusBaseChange F E G T i hi.1 hi.2.1).mp hi
  obtain ⟨J, hJ, P, hP, hred⟩ := rootDatumExistence E GE hGE TE hsplit iE hiE
  have hSpan : P.corootSpan ℤ = ⊤ :=
    splitSimplyConnectedCorootSpan E GE (isSimplyConnectedFieldExtension F E G hsc)
      TE hsplit iE hiE J P hP hred
  obtain ⟨b, aEquiv, hb⟩ := d.exists_base_cartanEquiv_of_split_maximalTorus hsplit hiE hP
  let eE := aEquiv.symm.trans e
  have hCartan (a c : b.support) : P.pairing a.val c.val = CartanMatrix.E 6 (eE a) (eE c) := by
    have hh := hb (aEquiv.symm a) (aEquiv.symm c)
    rw [aEquiv.apply_symm_apply, aEquiv.apply_symm_apply] at hh
    exact (P.algebraMap_pairingIn ℤ a.val c.val).symm.trans
      (hh.trans (hcart (aEquiv.symm a) (aEquiv.symm c)))
  let ρ := IsRootDatumOf.galoisRootDatumActionOfClosedSplitTorus F E i hsplit hiE.2.1 hP
  obtain ⟨H, hidx, B, hB⟩ :=
    Langlands.CartanE6Root.typeE6PermutationSubgroup P b eE hCartan hSpan (E ≃ₐ[F] E) ρ
  let liftIndex : Fin 6 ≃ ULift.{u} (Fin 6) := Equiv.ulift.symm
  let n : ℕ := 2 ^ 13 * 3 ^ 8
  apply GaloisCocycle.isTrivial_of_refine F L E
  refine finiteGaloisTorusPermutationIndex F E T hsplit H _ (B.reindex liftIndex)
    (fun σ hσ j => ?_) n hidx (ξ.refine (GaloisCocycle.coverMap F L E))
  obtain ⟨k, hk⟩ := hB σ hσ (liftIndex.symm j)
  refine ⟨liftIndex k, ?_⟩
  rw [Module.Basis.reindex_apply, Module.Basis.reindex_apply, Equiv.symm_apply_apply]
  exact hk

/-- The uniform power proves the two- and three-primary order bound. -/
theorem typeE6MaximalTorusCocycleOrder : TypeE6MaximalTorusCocycleOrderStatement.{u} := by
  intro F _ _ G _ _ d e hsc hs hcart T i hi L _ _ _ _ ξ
  exact ⟨13, 8, typeE6MaximalTorusUniformPower F G d e hsc hs hcart T i hi L ξ⟩

end Langlands.GroupScheme
