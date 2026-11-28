import Langlands.GroupScheme.Rational.GaloisBorelFaceRoots
import Langlands.GroupScheme.Rational.GaloisPinningCorootAction
import Langlands.GroupScheme.Rational.SimpleBaseFactorSurjectivity
import Langlands.GroupScheme.Rational.QuasiSplitSplittingReduction
import Langlands.GroupScheme.Torus.WeilRestrictionNormOneCocharacters

/-! # Galois permutation of the actual factors of a derived Levi face -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.RootDatumNegation

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 850000

namespace GaloisBorelFaceDerived.RootModel

variable {F E : Type u} [Field F] [Field E] [Algebra F E]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {p : GaloisPinningData F E G}
  {ν : cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap F E)).obj p.torus)}
  {L : GaloisBorelFaceDerived p ν} (R : L.RootModel)

local notation "b" => algebraBaseMap F E
local notation "BG" => GroupScheme.baseChange b
local notation "BC" => CommGroupScheme.baseChange b
local notation "DE" => Functor.obj BG L.derived
local notation "TDE" => Functor.obj BC L.torus
local notation "tDE" => CategoryTheory.Functor.map BG L.torusInclusion
local notation "τ" => CategoryTheory.Functor.map BC L.torusMap

attribute [local instance] derivedAffine derivedFiniteType

local instance upperAffine : IsAffineHom (DE).X.hom :=
  inferInstanceAs (IsAffineHom (CategoryTheory.Limits.pullback.snd L.derived.X.hom b))

local instance upperSmooth : Smooth (DE).X.hom :=
  letI : Smooth L.derived.X.hom := L.isSimplyConnected.isSemisimple.isConnectedReductive.smooth
  inferInstanceAs (Smooth (CategoryTheory.Limits.pullback.snd L.derived.X.hom b))

/-- The root-index comparison intertwines the ordinary Galois actions. -/
theorem indexEquiv_galois (σ : E ≃ₐ[F] E) (a : R.rootIndex) :
    (R.face.indexEquiv ((R.pinning.galoisAction σ).indexEquiv a)).val =
      (p.galoisAction σ).indexEquiv (R.face.indexEquiv a).val := by
  have h (r : R.rootIndex) : R.rootDatum.coroot r ≫ τ =
      p.rootDatum.coroot (R.face.indexEquiv r).val :=
    (R.coweightMap_eq (R.rootDatum.coroot r)).symm.trans (R.face.coroot_eq r)
  have hσ : R.rootDatum.coroot ((R.pinning.galoisAction σ).indexEquiv a) =
      cocharacterLattice.galoisRepresentation F E L.torus σ (R.rootDatum.coroot a) :=
    R.pinning.galoisAction_coroot σ a
  have hp : p.rootDatum.coroot ((p.galoisAction σ).indexEquiv (R.face.indexEquiv a).val) =
      cocharacterLattice.galoisRepresentation F E p.torus σ
        (p.rootDatum.coroot (R.face.indexEquiv a).val) :=
    p.galoisAction_coroot σ _
  apply p.rootDatum.coroot.injective
  rw [← h, hσ, hp, ← cocharacterLattice.galoisRepresentation_postcompose, h]

variable (D : SimplyConnectedAlmostSimpleProduct
    ((GroupScheme.baseChange (algebraBaseMap F E)).obj L.derived))
  (hD : IsSemisimple ((GroupScheme.baseChange (algebraBaseMap F E)).obj L.derived))

/-- The actual geometric factor containing a selected simple root. -/
def factorIndex (a : R.face.base.support) : D.Index :=
  D.rootDatumFactorIndex hD R.isSplit tDE R.pinning.isMaximalTorus R.isRootDatum a.val

omit [LocallyOfFiniteType G.X.hom] in
/-- Equality of actual factors is exactly connectivity in the induced
Cartan diagram. -/
theorem factorIndex_eq_iff (a c : R.face.base.support) :
    R.factorIndex D hD a = R.factorIndex D hD c ↔
      Relation.EqvGen (fun x y : R.face.base.support =>
        x ≠ y ∧ R.rootDatum.pairing x.val y.val ≠ 0) a c :=
  D.rootDatumFactorIndex_eq_iff_cartanConnected hD R.pinning.toSplitPinning a c

omit [LocallyOfFiniteType G.X.hom] in
/-- Every actual geometric factor has a vertex in the induced simple base. -/
theorem factorIndex_surjective : Function.Surjective (R.factorIndex D hD) :=
  D.rootDatumFactorIndex_surjective_on_base hD R.pinning.toSplitPinning

/-- When the ambient action is signed star, negating a root makes no
difference to the actual factor that it determines. -/
theorem factorIndex_galois
    (σ : E ≃ₐ[F] E) (a c : R.face.base.support)
    (hs : p.galoisAction σ = (p.starAction σ).val ∨
      p.galoisAction σ = negAut p.toSplitPinning.rootDatum * (p.starAction σ).val)
    (hc : (R.simpleEquiv c).val = p.starSupport σ (R.simpleEquiv a).val) :
    R.factorIndex D hD c = D.galoisFactorIndex σ (R.factorIndex D hD a) := by
  let A : R.rootDatum.Aut := R.pinning.galoisAction σ
  have he : (R.face.indexEquiv (A.indexEquiv a.val)).val =
      (p.galoisAction σ).indexEquiv (R.face.indexEquiv a.val).val :=
    R.indexEquiv_galois σ a.val
  have hstar : ((p.starAction σ).val.indexEquiv (R.face.indexEquiv a.val).val) =
      (R.face.indexEquiv c.val).val := by
    exact (congrArg (fun x : p.base.support => x.val) hc).symm
  have hDgal := D.rootDatumFactorIndex_galois hD R.pinning σ a.val
  change
    D.rootDatumFactorIndex hD R.isSplit tDE R.pinning.isMaximalTorus R.isRootDatum
      (A.indexEquiv a.val) = D.galoisFactorIndex σ (R.factorIndex D hD a) at hDgal
  have hinj : Function.Injective (fun r => (R.face.indexEquiv r).val) :=
    Subtype.val_injective.comp R.face.indexEquiv.injective
  rcases hs with hs | hs
  · have h : A.indexEquiv a.val = c.val := hinj (he.trans (by rw [hs]; exact hstar))
    rw [h] at hDgal
    exact hDgal
  · have hc' : (p.galoisAction σ).indexEquiv (R.face.indexEquiv a.val).val =
        p.rootDatum.reflectionPerm (R.face.indexEquiv c.val).val (R.face.indexEquiv c.val).val := by
      rw [hs]
      change (negAut p.toSplitPinning.rootDatum).indexEquiv
        ((p.starAction σ).val.indexEquiv (R.face.indexEquiv a.val).val) = _
      rw [hstar]
      rfl
    have h : A.indexEquiv a.val = R.rootDatum.reflectionPerm c.val c.val :=
      hinj (he.trans (hc'.trans (R.face.reflectionPerm_eq c.val c.val)))
    rw [h, D.rootDatumFactorIndex_reflection] at hDgal
    exact hDgal

end GaloisBorelFaceDerived.RootModel

end Langlands.GroupScheme
