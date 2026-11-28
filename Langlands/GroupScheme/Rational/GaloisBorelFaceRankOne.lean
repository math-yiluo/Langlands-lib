import Langlands.GroupScheme.Rational.GaloisBorelFaceFactors
import Langlands.GroupScheme.Reductive.PinningBaseChange
import Langlands.GroupScheme.Reductive.PinnedIsoAlignment
import Langlands.GroupScheme.Reductive.SeparablyClosedAlmostSimpleAbsoluteProof
import Langlands.GroupScheme.SimplyConnected.AlmostSimpleFactorDescentProperties
import Langlands.GroupScheme.SimplyConnected.SimplyConnectedFieldExtensionProof
import Langlands.GroupScheme.GaloisPointTowerBaseChange

/-! # Absolute rank one for the singleton Cartan factors -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 850000

section TitsIndex

variable {F E : Type u} [Field F] [Field E] [Algebra F E]
  [Algebra.IsAlgebraic F E] [IsSepClosed E]
  {H : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom H.X.hom]
  [LocallyOfFiniteType H.X.hom]
  {K : GroupScheme (Spec (CommRingCat.of E))} [IsAffineHom K.X.hom]

/-- A supplied split geometric pinning gives the number of absolute simple
vertices of any actual Tits index of the original group. -/
theorem TitsIndexData.nonempty_vertexEquiv_of_geometricPinning (d : TitsIndexData H)
    (q : SplitPinning K) (e : (GroupScheme.baseChange (algebraBaseMap F E)).obj H ≅ K) :
    Nonempty (d.Vertex ≃ q.base.support) := by
  let E₀ := SeparableClosure F
  let j : E₀ →ₐ[F] E := IsSepClosed.lift
  let : Algebra E₀ E := j.toRingHom.toAlgebra
  let : IsScalarTower F E₀ E := IsScalarTower.of_algebraMap_eq fun a => (j.commutes a).symm
  let : Algebra.IsAlgebraic E₀ E := Algebra.IsAlgebraic.tower_top (K := F) E₀
  let b₀ := algebraBaseMap F E₀
  let c := algebraBaseMap E₀ E
  let H₀ := (GroupScheme.baseChange b₀).obj H
  let : IsAffineHom H₀.X.hom :=
    inferInstanceAs (IsAffineHom (CategoryTheory.Limits.pullback.snd H.X.hom b₀))
  let : IsAffineHom ((GroupScheme.baseChange c).obj H₀).X.hom :=
    inferInstanceAs (IsAffineHom (CategoryTheory.Limits.pullback.snd H₀.X.hom c))
  let p := d.pinning.toSplitPinning
  let pE := p.baseChange (F := E)
  let w : (GroupScheme.baseChange c).obj H₀ ≅ K :=
    GaloisPointComparison.towerBaseChangeIso F E₀ E H ≪≫ e
  obtain ⟨_, _, f, _, _, hf⟩ := pE.exists_inner_comp_based q w
  exact ⟨(p.baseChangeSimpleEquiv (F := E)).trans (f.indexEquiv.subtypeEquiv hf)⟩

end TitsIndex

namespace GaloisBorelFaceDerived.RootModel

variable {F E : Type u} [Field F] [Field E] [Algebra F E]
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  [LocallyOfFiniteType G.X.hom] {p : GaloisPinningData F E G}
  {ν : cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap F E)).obj p.torus)}
  {L : GaloisBorelFaceDerived p ν} (R : L.RootModel)

local notation "b" => algebraBaseMap F E
local notation "BG" => GroupScheme.baseChange b
local notation "DE" => Functor.obj BG L.derived
local notation "tDE" => CategoryTheory.Functor.map BG L.torusInclusion

attribute [local instance] derivedAffine derivedFiniteType

private local instance rankOneUpperAffine : IsAffineHom (DE).X.hom :=
  inferInstanceAs (IsAffineHom (CategoryTheory.Limits.pullback.snd L.derived.X.hom b))

variable (D : SimplyConnectedAlmostSimpleProduct
    ((GroupScheme.baseChange (algebraBaseMap F E)).obj L.derived))
  (hD : IsSemisimple ((GroupScheme.baseChange (algebraBaseMap F E)).obj L.derived))

local instance factorAffine (i : D.Index) : IsAffineHom (D.factor i).X.hom :=
  (D.isAlmostSimple i).isSemisimple.isConnectedReductive.isAffineHom

omit [LocallyOfFiniteType G.X.hom] in
/-- In a diagonal Cartan diagram, distinct simple vertices give distinct
geometric almost-simple factors. -/
theorem factorIndex_injective_of_diagonal
    (hdiag : ∀ a c : R.face.base.support, a ≠ c → R.rootDatum.pairing a.val c.val = 0) :
    Function.Injective (R.factorIndex D hD) := by
  intro a c h
  have he := (R.factorIndex_eq_iff D hD a c).mp h
  clear h
  induction he with
  | rel a c h => exact False.elim (h.2 (hdiag a c h.1))
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

omit [LocallyOfFiniteType G.X.hom] in
/-- The chosen actual factor of a diagonal simple face has a one-vertex
split pinning. -/
theorem exists_rankOneFactorPinning
    (hdiag : ∀ a c : R.face.base.support, a ≠ c → R.rootDatum.pairing a.val c.val = 0)
    (a : R.face.base.support) :
    ∃ q : SplitPinning (D.factor (R.factorIndex D hD a)), Nonempty (q.base.support ≃ Fin 1) := by
  let i := R.factorIndex D hD a
  let M := D.factorMaximalTorus hD.isConnectedReductive tDE R.isSplit R.pinning.isMaximalTorus i
  let hA := (D.isAlmostSimple i).isSemisimple.isConnectedReductive
  obtain ⟨J, hJ, P, hP, hred⟩ :=
    rootDatumExistence E (D.factor i) hA M.torus M.split M.subgroupHom M.isMaximalTorus
  let : Finite J := hJ
  let : P.IsReduced := hred
  let B := M.inducedBase D hD R.pinning.toSplitPinning hP
  let q : SplitPinning (D.factor i) :=
    { isConnectedReductive := hA
      torus := M.torus
      inclusion := M.subgroupHom
      isSplitTorus := M.split
      isMaximalTorus := M.isMaximalTorus
      rootIndex := J
      rootDatum := P
      isRootDatum := hP
      isReduced := hred
      base := B
      pinning := RootPinning.ofSplitMaximalTorus hA M.split M.subgroupHom M.isMaximalTorus P hP B }
  let e : B.support ≃ {c : R.face.base.support // R.factorIndex D hD c = i} :=
    M.simpleRootIndexEquiv D hD R.pinning.toSplitPinning hP
  let a₀ : B.support := e.symm ⟨a, rfl⟩
  have hall (c : B.support) : c = a₀ := by
    apply e.injective
    rw [Equiv.apply_symm_apply]
    exact Subtype.ext (R.factorIndex_injective_of_diagonal D hD hdiag (e c).property)
  exact ⟨q, ⟨{
    toFun := fun _ => 0
    invFun := fun _ => a₀
    left_inv := fun c => (hall c).symm
    right_inv := fun _ => Subsingleton.elim _ _ }⟩⟩

omit [LocallyOfFiniteType G.X.hom] in
/-- A derived face with one simple vertex is absolutely almost-simple.
Every actual geometric factor has a simple vertex, so its geometric product
has a single factor. -/
theorem isAbsolutelyAlmostSimple_of_singleton [IsSepClosed E]
    (e : R.face.base.support ≃ Fin 1) :
    IsAbsolutelyAlmostSimple L.derived := by
  let hsc := isSimplyConnectedFieldExtension F E L.derived L.isSimplyConnected
  let D := hsc.almostSimpleProduct
  let hD := hsc.isSemisimple
  let a := e.symm 0
  let i := R.factorIndex D hD a
  have hall (j : D.Index) : j = i := by
    obtain ⟨c, rfl⟩ := R.factorIndex_surjective D hD j
    exact congrArg (R.factorIndex D hD) (e.injective (Subsingleton.elim _ _))
  let g : (DE) ≅ D.factor i :=
    { hom := D.projection i
      inv := D.inclusion i
      hom_inv_id := by
        apply (cancel_mono D.iso.hom).mp
        apply Pi.hom_ext
        intro j
        obtain rfl := hall j
        simp only [SimplyConnectedAlmostSimpleProduct.projection,
          SimplyConnectedAlmostSimpleProduct.inclusion, Category.assoc,
          Iso.inv_hom_id_assoc, piFactorInclusionHom_π_self, Category.comp_id,
          Category.id_comp]
      inv_hom_id := D.inclusion_projection i }
  exact IsAbsolutelyAlmostSimple.of_fieldExtension (K := E)
    (separablyClosedAlmostSimpleAbsolute E (DE) ((D.isAlmostSimple i).of_iso g))

end GaloisBorelFaceDerived.RootModel
end Langlands.GroupScheme
